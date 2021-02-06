/-
Copyright 2021 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
 -/
import measure_theory.measurable_space

import measure_theory.measure_space
import measure_theory.outer_measure
import measure_theory.lebesgue_measure
import measure_theory.integration

import measure_theory.borel_space
import data.set.countable
import formal_ml.nnreal
import formal_ml.sum
import formal_ml.lattice
import formal_ml.measurable_space
import formal_ml.classical
import data.equiv.list
import formal_ml.prod_measure
import formal_ml.finite_pi_measure
import formal_ml.probability_space
import formal_ml.random_variable_identical
import formal_ml.prod_probability_space

/-
  This file proves that two IID distributions are identical.

  This result is subtle (i.e., why isn't it just by definition).
  IID variables can be constructed as IID, at which point they are 
  obviously IID. However, they can be observed to be IID.

  

  Notice that, given X_1 and X_2, and Y_1 and Y_2, all coin flips.

  if X_1 is identical to Y_1, and X_2 is identical to Y_2, it is
  not enough to show that every event has the same probability. For
  example, maybe `Pr[ X_1 =ᵣ X_2] ≠ Pr[Y_1 =ᵣ Y_2]`. This kind of
  reasoning gives us a deeper understanding of the proof of VCD, which
  are based upon constructing an IID distribution through shuffling
  and subsampling.

-/




def pi_base {δ:Type*} {π:δ → Type*} [M:Π (a:δ), measurable_space (π a)]
  (S:set (Π (a:δ), π a)):Prop := ∃ (f:Π (a:δ), set (π a)), (∀ i, measurable_set (f i)) ∧
  set.pi set.univ f = S


lemma pi_base.closed_inter
  {δ:Type*} {π:δ → Type*} [M:Π (a:δ), measurable_space (π a)]
  (S T:set (Π (a:δ), π a)):pi_base S → pi_base T → pi_base (S ∩ T) :=
begin
  intros hS hT,
  cases hS with fS hS,
  cases hT with fT hT,
  apply exists.intro (λ i, (fS i) ∩ (fT i)),
  split,
  { intros i, apply measurable_set.inter, apply hS.left, apply hT.left },
  rw ← hS.right,
  rw ← hT.right,
  ext ω, split; intros h1; simp at h1; simp [h1],
end

lemma pi_base.empty
  {δ:Type*} [nonempty δ] {π:δ → Type*} [M:Π (a:δ), measurable_space (π a)]:
  pi_base (∅:set (Π (a : δ), π a)) := begin
  apply exists.intro (λ (d:δ), (∅:set (π d))),
  simp [set.pi], 
end

lemma pi_base.univ
  {δ:Type*} [nonempty δ] {π:δ → Type*} [M:Π (a:δ), measurable_space (π a)]:
  pi_base (set.univ:set (Π (a : δ), π a)) := begin
  apply exists.intro (λ (d:δ), (set.univ:set (π d))),
  simp [set.pi], 
end

lemma pi_base.closed_compl 
  {δ:Type*} [fintype δ] [nonempty δ] {π:δ → Type*} [M:Π (a:δ), measurable_space (π a)]
    (s : set (Π (a : δ), π a)):
    pi_base s →
    (set.disjoint_union_closure pi_base) sᶜ  := begin
  classical,
  intros h1,
  simp [pi_base] at h1,
  cases h1 with f h1,
  let f':(δ → bool) → set (Π (a : δ), π a) := 
    (λ x, if (∀ (d:δ), x d) then ∅  else 
   (set.pi (@set.univ δ) (λ (d:δ), if (x d) then (f d) else (f d)ᶜ))),  
  begin
    have h2:sᶜ = set.Union f',
    { rw ← h1.right, simp [f'], ext; split; intros h2_1;
      simp at h2_1; simp [h2_1],
      { let i:δ → bool := (λ (d:δ), x d ∈ (f d)),
        apply exists.intro i,
        rw if_neg,
        simp [set.pi, i],
        intros d,
        cases classical.em (x d ∈ f d) with h2_2 h2_2,
        rw if_pos h2_2, apply h2_2,
        rw if_neg h2_2, apply h2_2,
        intros contra,
        cases h2_1 with d h2_1,
        apply h2_1,
        have contra_2 := contra d,
        simp [i] at contra_2,
        apply contra_2 },
      { cases h2_1 with i h2_1,
        cases classical.em (∀ (d : δ), (i d)) with h2_3 h2_3,
        { exfalso, rw if_pos h2_3 at h2_1, apply h2_1 },
        rw if_neg h2_3 at h2_1,
        rw classical.not_forall_iff_exists_not at h2_3,
        cases h2_3 with d h2_3,
        apply exists.intro d,
        simp [set.pi] at h2_1,
        have h2_4 := h2_1 d,
        rw if_neg h2_3 at h2_4,
        apply h2_4 } },
    rw h2,
    apply set.disjoint_union_closure_intro,
    intros b,
    { simp [f',pi_base],
      cases classical.em (∀ (d : δ), (b d)) with h3 h3,
      rw if_pos,
      apply pi_base.empty,
      apply h3,
      rw if_neg,
      { apply exists.intro (λ (d : δ), ite ↥(b d) (f d) (f d)ᶜ),
        rw and.comm,
        split,
        refl,
        intros d,
        simp,
        cases classical.em (b d) with h4 h4,
        rw if_pos,
        apply h1.left,
        apply h4,
        rw if_neg,
        apply measurable_set.compl,
        apply h1.left, apply h4 },
      apply h3 },
    intros b b' h_ne,
    simp [function.on_fun], rw disjoint_iff,
    simp,
    rw ← set.subset_empty_iff,
    rw set.subset_def,
    intros ω h_contra,
    exfalso,
    simp [f'] at h_contra,
    cases h_contra with h_contra_1 h_contra_2,
    cases classical.em (∀ (d : δ), (b d)) with h5 h5,
    { rw if_pos at h_contra_1,
      apply h_contra_1,
      apply h5 },
    rw if_neg h5 at h_contra_1,
    cases classical.em (∀ (d : δ), (b' d)) with h6 h6,
    { rw if_pos h6 at h_contra_2,
      apply h_contra_2 },
    rw if_neg h6 at h_contra_2,
    apply h_ne,
    simp [set.pi] at h_contra_1,
    simp [set.pi] at h_contra_2,
    ext i,
    have h_contra_1_i := h_contra_1 i,
    have h_contra_2_i := h_contra_2 i,
    destruct (b i); destruct (b' i);
    intros h_b'_i h_b_i;
    simp [h_b_i, h_b'_i];
    simp [h_b_i] at h_contra_1_i;
    simp [h_b'_i] at h_contra_2_i,
    apply h_contra_1_i h_contra_2_i,
    apply h_contra_2_i h_contra_1_i,
  end 
end


lemma set.pi_as_preimage {δ:Type*} {π:δ → Type*} {f:Π (a:δ), set (π a)}:
  (set.pi set.univ f) = (⋂ (i:δ), (λ (d:Π (a:δ), π a), d i) ⁻¹' (f i)) := begin
  ext,split;intros A1; simp at A1; simp [A1],
end

lemma pi_base.measurable_set {δ:Type*} [encodable δ] {π:δ → Type*} 
  [M:Π (a:δ), measurable_space (π a)]
  (S:set (Π (a:δ), π a)):pi_base S → measurable_set S :=
begin
  intros hS,
  cases hS with fS hS,
  cases hS with h_meas h_def,
  rw ← h_def,
  rw set.pi_as_preimage,
  apply measurable_set.Inter,
  intros b,
  have h_proj_meas:measurable (λ (d : Π (a : δ), π a), d b),
  { apply measurable_pi_apply },
  apply h_proj_meas,
  apply h_meas,
end

lemma pi_base.covers_generate {δ:Type*} [encodable δ] {π:δ → Type*} 
  [M:Π (a:δ), measurable_space (π a)]
  (S:set (Π (a:δ), π a)):
  S ∈  
     (⋃ (i : δ),
       (measurable_space.comap (λ (b : Π (a : δ), (λ (a : δ), π a) a), b i)
          ((λ (a : δ), M a) i)).measurable_set') → 
  pi_base S := begin
  intros h1,
  simp [pi_base],
  simp at h1,
  cases h1 with d h1,
  simp [measurable_space.comap] at h1,
  cases h1 with s h1,
  cases h1 with h1 h3,
  have h2:∀ (d':δ), ∃ (T:set (π d')), measurable_set T ∧
     (∀ (s':(Π (a:δ), π a)), s' ∈ S → s' d' ∈ T) ∧ (d' = d → T == s),
  { intros d',
    cases classical.em (d = d') with h2_1 h2_1,
    { subst d', apply exists.intro s, 
      split,
      apply h1,
      split, 
      intros s' h4, rw ← h3 at h4,
      simp at h4, apply h4, intros h5, refl },
    { apply exists.intro set.univ,
      split,
      apply measurable_set.univ,
      split,
      intros s' h6,
      simp,
      intros h2_1_not, exfalso, apply h2_1, rw h2_1_not, },
   },
   have h7 := classical.axiom_of_choice h2,
   cases h7 with f h7,
   apply exists.intro f,
   split,
   { intros d',
     apply (h7 d').left },
   { ext ω,
     simp [set.pi],split; intros h8,
     { rw ← h3,
       have h9:d = d := rfl,
       have h10 := (h7 d).right.right h9,
       simp at h10, rw ← h10, 
       simp, apply h8 },
     { intros d',
       have h11 := (h7 d').right.left ω h8, apply h11 } },
end

lemma pi_base_eq_measurable_space_pi {δ:Type*} [encodable δ] {π:δ → Type*} 
  [M:Π (a:δ), measurable_space (π a)]:
 @measurable_space.pi δ π M  = measurable_space.generate_from pi_base :=
begin
  apply le_antisymm;
  apply measurable_space.generate_from_le;
  intros a h_a,
  { simp [measurable_space.generate_from],
    apply measurable_space.generate_measurable.basic,
    apply pi_base.covers_generate,
    simp at h_a, simp, cases h_a with i h_a, apply exists.intro i, apply h_a },
  { apply pi_base.measurable_set, apply h_a },
end

lemma pi_base_eq {δ:Type*} [fintype δ] {π:δ → Type*} [M:Π (a:δ), measurable_space (π a)]
  (S:measurable_setB (@measurable_space.pi δ π M)):pi_base S.val →
  ∃ (f:Π (b:δ), measurable_setB (M b)), (set.pi_measurable set.univ f) = S := begin
  intros h1,
  unfold pi_base at h1,
  cases h1 with g h1,
  cases h1 with h1 h2,
  let f := (λ (b:δ), @measurable_setB.mk _ _ (g b) (h1 b)),
  begin
     apply exists.intro f,
     apply subtype.eq,
     rw ← h2,
     simp [set.pi, set.pi_measurable, f],
     ext ω,split;intros h1; simp at h1; simp [h1]; intros i; apply h1,
  end
end

lemma pi_base_is_semialgebra {δ:Type*} [fintype δ] [nonempty δ] {π:δ → Type*} 
  [M:Π (a:δ), measurable_space (π a)]:set.is_semialgebra (@pi_base δ π M) := {
  univ := pi_base.univ,
  empty := pi_base.empty,
  compl := pi_base.closed_compl,
  inter := pi_base.closed_inter,
}

lemma pi_union_all {Ω δ:Type*} [fintype δ] 
  {P:probability_space Ω}
  {π:δ → Type*} [M:Π (a:δ), measurable_space (π a)]
  (f:Π (b:δ), measurable_setB (M b))
  {X:Π (b:δ), P →ᵣ (M b)}:
  (pi.random_variable_combine X ∈ᵣ (set.pi_measurable set.univ f)) =
  (∀ᵣ (b:δ), (X b) ∈ᵣ (f b)) := begin
  apply event.eq,
  simp [pi.random_variable_combine, set.pi_measurable, pi.measurable_fun],
  ext ω, split; intros h1; simp at h1; simp [h1],
end

  
lemma random_variable_independent_all {Ω β:Type*} {P:probability_space Ω} [fintype β]
  {γ:β → Type*} {M:Π (b:β), measurable_space (γ b)}
   (S:Π (b:β), measurable_setB (M b))
   {X:Π (b:β), P →ᵣ (M b)}:
   random_variable_independent X →
   Pr[∀ᵣ (b : β), X b ∈ᵣ S b] =  finset.univ.prod (λ (b:β), Pr[X b ∈ᵣ S b]) := begin
  intros h1,
  simp [random_variable_independent] at h1,
  have h2 := h1 S,
  simp [independent_events] at h2,
  have h3 := h2 finset.univ,
  rw h3,
  refl,
end
 
lemma IID_identical_joint_base' {Ω₁ Ω₂ β γ:Type*} [fintype β] 
  {P₁:probability_space Ω₁}
  {P₂:probability_space Ω₂}
  {M:measurable_space γ} 
  {X₁:β → P₁ →ᵣ M}  {X₂:β  → P₂ →ᵣ M}
  (S:measurable_setB (@measurable_space.pi β (λ _, γ) (λ _, M))):
  pi_base S.val →
  (∀ (b:β), random_variable_identical (X₁ b) (X₂ b)) →
  (random_variables_IID X₁) →
  (random_variables_IID X₂) →
  (Pr[pi.random_variable_combine X₁ ∈ᵣ S] =
   Pr[pi.random_variable_combine X₂ ∈ᵣ S]) :=
begin
  intros h1 h2 h3 h4,
  have h5:=pi_base_eq S h1,
  cases h5 with f h5,
  rw ← h5,
  rw pi_union_all,
  rw pi_union_all,
  rw random_variable_independent_all,
  rw random_variable_independent_all,
  have h6:(λ (b : β), Pr[X₁ b ∈ᵣ f b]) = (λ (b : β), Pr[X₂ b ∈ᵣ f b]),
  { ext1 b, apply h2, },
  rw h6,
  apply h4.left,
  apply h3.left,
end


lemma IID_identical_joint' {Ω₁ Ω₂ β γ:Type*} [fintype β] [nonempty β] 
  {P₁:probability_space Ω₁}
  {P₂:probability_space Ω₂}
  {M:measurable_space γ} 
  {X₁:β → P₁ →ᵣ M}  {X₂:β  → P₂ →ᵣ M}:
  (∀ (b:β), random_variable_identical (X₁ b) (X₂ b)) →
  (random_variables_IID X₁) →
  (random_variables_IID X₂) →
  random_variable_identical (pi.random_variable_combine X₁)
                            (pi.random_variable_combine X₂)
  :=
begin
  intros h1 h2 h3,
  haveI:encodable β := fintype.encodable β,
  apply random_variable_identical_on_semialgebra' pi_base, 
  --apply pi_base
  apply pi_base.closed_inter,
  apply pi_base.closed_compl,
  apply pi_base.empty,
  apply pi_base.univ,
  { 
    apply pi_base_eq_measurable_space_pi },
  intros T h_T,
  apply IID_identical_joint_base',
  apply h_T,
  apply h1,
  apply h2,
  apply h3,
end



lemma IID_identical_joint {Ω₁ Ω₂ β γ:Type*} [fintype β] [nonempty β]
  {P₁:probability_space Ω₁}
  {P₂:probability_space Ω₂}
  {M:measurable_space γ} 
  {X₁:β → P₁ →ᵣ M}  {X₂:β  → P₂ →ᵣ M}: 
  (∃ (b₁ b₂:β), random_variable_identical (X₁ b₁) (X₂ b₂)) →
  (random_variables_IID X₁) →
  (random_variables_IID X₂) →
  random_variable_identical (pi.random_variable_combine X₁)
                            (pi.random_variable_combine X₂) :=
begin
  intros h1 h2 h3,
  apply IID_identical_joint',
  intros b,
  cases h1 with b₁ h1,
  cases h1 with b₂ h1,
  have h4:random_variable_identical (X₁ b) (X₁ b₁),
  { apply h2.right },
  apply random_variable_identical.trans h4,
  apply random_variable_identical.trans h1,
  apply h3.right,
  apply h2,
  apply h3,
end

