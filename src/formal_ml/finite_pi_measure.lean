/-
Copyright 2020 Google LLC

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
import formal_ml.ennreal
import formal_ml.sum
import formal_ml.lattice
import formal_ml.measurable_space
import formal_ml.classical
import formal_ml.core
import formal_ml.characteristic
import formal_ml.measure
import data.equiv.list


noncomputable def pi.outer_measure {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} [M:∀ a, measurable_space (β a)] 
  (μ:Π a, measure_theory.outer_measure (β a)):measure_theory.outer_measure (Π a, β a) := 
  measure_theory.outer_measure.of_function
  (λ P:set (Π a, β a), finset.univ.prod (λ (a:α), (μ a) ((λ (p:Π a, β a), p a) '' P)))
begin
  simp,
  rw finset.card_pos,
  rw finset.univ_nonempty_iff,
  apply N,
end 

section pi

open_locale classical


lemma ennreal.prod_le_prod {α:Type*} {f g:α → ennreal} {s:finset α}:(∀ a∈ s, f a ≤ g a) → s.prod f ≤ s.prod g :=
begin
  apply finset.induction_on s,
  { intros h_le, simp, apply le_refl _ },
  { intros a s' h_not_mem h_ind h_le,
    rw finset.prod_insert h_not_mem, rw finset.prod_insert h_not_mem,
    apply ennreal.mul_le_mul,
    apply h_le, simp,
    apply h_ind, intros a' h_le_a',
    apply h_le, simp [h_le_a'], },
end


lemma finset.insert_erase_univ {α:Type*} [F:fintype α] {d:α}:
insert d (finset.univ.erase d) = finset.univ :=
begin
  rw finset.insert_erase,
  apply finset.mem_univ,
end


noncomputable def pi.measure {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} [M:∀ a, measurable_space (β a)] 
  (μ:Π a, measure_theory.measure (β a)):measure_theory.measure (Π a, β a) := 
  (pi.outer_measure (λ a, (μ a).to_outer_measure)).to_measure begin
  unfold measurable_space.pi,
  simp,
  intros d,
  intros P A1,
  unfold measurable_space.comap at A1,
  simp at A1,
  cases A1 with s A1,
  cases A1 with A1 A2,
  subst P,
  apply measure_theory.outer_measure.of_function_caratheodory,
  simp,
  intros t,
  have D1:finset.univ = insert d (finset.univ.erase d),
  { rw finset.insert_erase_univ },
  rw D1,
  rw finset.prod_insert,
  rw finset.prod_insert,
  rw finset.prod_insert,
  have B1:(μ d) ((λ (p : Π (a : α), (λ (a : α), β a) a), p d) '' t∩ s) +
          (μ d) ((λ (p : Π (a : α), (λ (a : α), β a) a), p d) '' t\ s) =
          (μ d) ((λ (p : Π (a : α), (λ (a : α), β a) a), p d) '' t),
  { rw ← measure_theory.measure_eq_inter_diff', apply A1 },
   rw ← B1,
  clear B1,
  rw right_distrib,
  apply @add_le_add ennreal _;
  apply ennreal.mul_le_mul;
  try {apply measure_theory.measure_mono};
  try { simp, apply set.subset.trans,
    apply set.inter_subset_left, apply set.subset_preimage_image };
  try { apply ennreal.prod_le_prod, intros a h_a_mem,
    apply measure_theory.measure_mono, simp, apply set.subset.trans,
    apply set.inter_subset_left, apply set.subset_preimage_image },
  { simp, apply set.diff_subset_diff_left, apply set.subset_preimage_image },
  repeat {simp},
end 


def cast.pi {α:Type*} {β:α → Type*} {a a':α} (b:β a) (h:a = a'):β a' := cast begin
rw h end b  


def subst.pi {α:Type*} [decidable_eq α] {β:α → Type*} (f:Π (a:α), β a) (a':α) (b:β a'):Π (a:α), β a :=
  λ (a:α), @dite (a' = a) _ (β a) (λ h, cast.pi b h) (λ h, f a)


lemma subst.pi_eq {α:Type*} [decidable_eq α] {β:α → Type*} (f:Π (a:α), β a) (a':α) (b:β a'):
  (subst.pi f a' b) a' = b := begin
  simp [subst.pi],
  refl,
end


lemma subst.pi_ne {α:Type*} [decidable_eq α] {β:α → Type*} (f:Π (a:α), β a) (a a':α) (b:β a')
 (h:a' ≠ a):
  (subst.pi f a' b) a = f a := begin
  simp [subst.pi],
  rw dif_neg,
  apply h,
end


lemma set.project_pi {α:Type*} {β:α → Type*} {f:Π (a:α), set (β a)} (h:∀ a, (f a).nonempty) 
  {a':α}:
      ((λ (p : Π (a : α), β a), p a') '' (set.pi set.univ f)) = f a' :=
begin
  ext x,
  split;intros A1,
  simp [set.pi] at A1,
  { cases A1 with y A1,
    cases A1 with A1 A2,
    subst x,
    apply A1 },
  { simp [set.pi],
    have h2:∀ (a:α), ∃ b:β a, b ∈ (f a),
    { intros a, rw ← set.nonempty_def,
      apply h },
    rw classical.skolem at h2,
    cases h2 with g h2,
    apply exists.intro (subst.pi g a' x),
    split,
    intros q,
    cases (classical.em (a' = q)) with A3 A3,
    { subst q,
      rw subst.pi_eq, apply A1 },
    { rw subst.pi_ne,
      apply h2,
      apply A3, },
    rw subst.pi_eq },
end



lemma set.pi_empty {α:Type*} {β:α → Type*} {f:Π (a:α), set (β a)}  
  {a':α} (h2:f a' = ∅):
  (set.pi set.univ f) = ∅ :=
begin
  ext x, simp, split,
  { have h3:x a' ∉ f a',
    { simp [h2] },
    apply h3, },
end


lemma pi.outer_measure.Inf_sum {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} [M:∀ a, measurable_space (β a)] 
  (μ:Π a, measure_theory.outer_measure (β a)) {P:set (Π a, β a)}:
  pi.outer_measure μ P =
  (⨅ (f:ℕ → (Π (a:α), set (β a))) (h₁:P ⊆ ⋃ (n:ℕ), set.pi set.univ (f n)), 
  ∑' (n:ℕ), finset.univ.prod (λ (m:α), μ m (f n m))) := begin
  unfold pi.outer_measure measure_theory.outer_measure.of_function,
  rw ← measure_theory.outer_measure.measure_of_eq_coe,
  simp,
  apply le_antisymm,
  { simp,
  intros f B1,
  apply @infi_le_of_le ennreal  _ _ _ _ (λ (n:ℕ), set.pi set.univ ((f n))),
  apply @infi_le_of_le ennreal  _ _ _ _ _,
  apply ennreal.tsum_le_tsum,
  intros n,  
  cases (classical.em (∀ (a:α), (f n a).nonempty)) with B2 B2,
  { have D1:(λ (a : α), (μ a) ((λ (p : Π (a : α), β a), p a) '' (λ (n : ℕ), set.pi set.univ (f n)) n)) = (λ (m : α), (μ m) (f n m)),
    { ext1 a, simp [set.project_pi], rw set.project_pi, apply B2 },
    rw D1, apply le_refl _, },
  { rw classical.not_forall_iff_exists_not at B2,
    cases B2 with a B2, rw set.not_nonempty_iff_eq_empty at B2,
    rw @finset.prod_eq_zero _ _ _ a,
    rw @finset.prod_eq_zero _ _ _ a,
    apply le_refl _,
    apply finset.mem_univ,
    rw B2,
    apply measure_theory.outer_measure.empty,
    apply finset.mem_univ,
    simp,
    rw set.pi_empty B2,
    simp },
    apply B1 },
  { simp,
    intros f A1,
    let f':ℕ → (Π (a:α), set (β a)) := (λ n m, ((λ (p:Π (a:α), β a), p m) '' (f n))),
    begin
      apply @infi_le_of_le ennreal (ℕ → (Π (a:α), set (β a))) _ _ _ f',  
      rw infi_prop_def,
      simp [f'],
      apply le_refl _,
      apply @set.subset.trans (Π a, β a) P (set.Union f) (⋃ (n : ℕ), set.pi set.univ (f' n))  A1,
      apply set.Union_subset_Union,
      intros i,
      rw set.subset_def,
      intros x A1,
      simp,
      intros a,
      apply exists.intro x,
      simp [A1],
    end },
end


lemma set.pi_subset_pi {α:Type*} {β:α → Type*} {S:Π (a:α), set (β a)} {T:Π (a:α), set (β a)}:
    (∀ a, S a ⊆ T a) → set.pi set.univ S ⊆ set.pi set.univ T :=
begin
  rw set.subset_def,
  intros A0 x A1,
  simp,
  intros a,
  simp at A1,
  apply A0,
  apply A1,
end
 

lemma pi.outer_measure.Inf_sum2 {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} [M:∀ (a:α), measurable_space (β a)] 
  (μ:Π (a:α), measure_theory.measure (β a)) {P:set (Π (a:α), β a)}:
  pi.outer_measure (λ (a:α), (μ a).to_outer_measure) P = 

  (⨅ (f:ℕ → (Π (a:α), set (β a))) (h₁:∀ n m, measurable_set (f n m))
  (h₃:P ⊆ ⋃ (n:ℕ), set.pi set.univ (f n)), 
  ∑' (n:ℕ), finset.univ.prod (λ (m:α), μ m (f n m))) := begin
  rw pi.outer_measure.Inf_sum,
  apply le_antisymm,
  { simp,
    intros f h₁ h₃,
    apply @infi_le_trans (ℕ→ Π (a:α), set (β a)) ennreal _ f,
    rw infi_prop_def,
    apply le_refl _,
    apply h₃ },
  { simp,
    intros f h₁,
   have h4_2 := λ (n:ℕ) (m:α), measure_theory.measurable_eq (μ m) (f n m),
    have h4:∀ n, ∃ (g:Π (a:α), set (β a)), ∀ (a:α), measurable_set (g a) ∧ (μ a) (g a) = (μ a) (f n a) ∧ f n a ⊆ g a,
    { intros n, have h5_1 := h4_2 n,
      apply classical.axiom_of_choice h5_1, },
    rw classical.skolem at h4,

    cases h4 with f' h4,


    apply @infi_le_trans (ℕ→ (Π (a:α), set (β a))) ennreal _ f',
    rw infi_prop_def,
    rw infi_prop_def,
    { apply ennreal.tsum_le_tsum,
      intro n,
      apply ennreal.prod_le_prod,
      intros a h_dummy,
      rw (h4 n a).right.left, apply le_refl _, },
    apply set.subset.trans,
    apply h₁,
    apply set.Union_subset_Union,
    intro n,
    apply set.pi_subset_pi,
    intros a,
    apply (h4 n a).right.right,
    intros n m,
    apply (h4 n m).left,
    },
end


/-
  If we can make this into an equality, we're home free. 
  See https://www.math.ucdavis.edu/~hunter/measure_theory/measure_notes_ch5.pdf
  Those notes focus on measurable sets. We could theoretically do the same. However,
  it would make the rest of the analysis much more complex.
  I wonder if using an "outer measure lower integral" would make this useful. 
-/
lemma pi.outer_measure.apply_prod_le {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} [M:∀ a, measurable_space (β a)] 
  (μ:Π a, measure_theory.outer_measure (β a)) {P:(Π a, set (β a))}:
  pi.outer_measure μ (set.pi set.univ P) ≤ finset.univ.prod (λ a, μ a (P a)) :=
begin
  rw pi.outer_measure.Inf_sum,
  { apply @infi_le_of_le ennreal _ _ _ _ (λ (n:ℕ) (a:α), ite (n = 0) (P a) ∅),
    apply @infi_le_of_le ennreal _ _ _ _ _,
    rw tsum_eq_single 0,
    {simp [le_refl]},
    intros b' B1,
    simp [B1],
    rw finset.card_pos,
    rw finset.univ_nonempty_iff,
    apply N,
  apply ennreal.t2_space,
  rw set.subset_def,
  intros p B2,
  simp,
  apply exists.intro 0,
  {simp at B2,simp [B2]}},
end


lemma set.characteristic.pi {α:Type*} [F:fintype α] {β:α → Type*} {P:Π a, set (β a)}
  {x:Π a, β a}:(set.pi set.univ P).characteristic x = 
finset.univ.prod (λ a, (P a).characteristic (x a)) :=
begin
  have A1:∀ S:finset α, (set.pi (↑S) P).characteristic x = 
       S.prod (λ a, (P a).characteristic (x a)),
  { intros S,
    apply finset.induction_on S,
    { simp },
    { intros a T h_not_mem h_ind,
      rw finset.prod_insert h_not_mem,
      rw ← h_ind,
      cases classical.em ((x a) ∈ (P a)) with A1 A1,
      rw set.characteristic.of_mem A1,
      rw one_mul,
      cases classical.em (x ∈ (set.pi (↑T) P)) with A2 A2,
      { rw set.characteristic.of_mem A2,
        rw set.characteristic.of_mem,
        simp at A2, simp [A1,A2], apply A2, },
      { rw set.characteristic.of_not_mem A2,
        rw set.characteristic.of_not_mem,
        simp at A2,
        simp [A1,A2], },
      { rw set.characteristic.of_not_mem A1,
        rw zero_mul,
        rw set.characteristic.of_not_mem,
        simp [A1], } } },
  have A2:set.univ = ↑(finset.univ),
  { ext x, split; intros A1, rw  @finset.mem_coe α x, simp, simp },
  rw A2,
  apply A1,
end


lemma finset.prod_univ_diff_insert {α:Type*} [fintype α] (f:α → ennreal) (A:finset α) (a:α) (h:a∉ A):
(finset.univ \ A).prod f = f a * (finset.univ \ (insert a A)).prod f :=
begin
  have A1:finset.univ \ A = (insert a (finset.univ \ (insert a A))),
  { ext x, split;intros A1_1; simp at A1_1; simp [A1_1], apply classical.em (x = a),
    cases A1_1,
    subst x,
    apply h,
    intros contra,
    apply A1_1,
    right,
    apply contra },
  rw A1,
  rw finset.prod_insert,
  simp,
end

 
lemma pi.outer_measure.le_apply_prod {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} [M:∀ a, measurable_space (β a)] 
  (μ:Π a, measure_theory.measure (β a)) {P:(Π a, set (β a))}:(∀ (a:α), measurable_set (P a)) →
  finset.univ.prod (λ a, μ a (P a)) ≤
  pi.outer_measure (λ a, (μ a).to_outer_measure) (set.pi set.univ P) :=
begin
  intro A4,
  /- Due to an implementation detail, it is best to consider an empty set separately. -/
  cases (classical.em (∀ (a:α), (P a).nonempty)) with h_all_nonempty h_exists_empty,

  rw pi.outer_measure.Inf_sum2,
  simp,
  intros f A2 A3,
  have h2:(set.pi set.univ P).characteristic ≤ ∑' (n : ℕ), (set.pi set.univ (f n)).characteristic,
  { apply function.le_trans (set.characteristic.subset A3),
    apply set.characteristic.Union },
  have h3:∀ (x:Π (a:α), β a), finset.univ.prod (λ a, (P a).characteristic (x a))  ≤ 
          ∑' (n : ℕ), finset.univ.prod (λ a, (f n a).characteristic (x a)),
  { intros x,
    rw ← set.characteristic.pi,
    have h3a: (λ n, (finset.univ.prod (λ a, (f n a).characteristic (x a)))) =
              (λ n, (set.pi (set.univ) (f n)).characteristic x),
    { ext1 n, rw set.characteristic.pi },
    rw h3a,
    have h3b:((∑' (n : ℕ), (set.pi set.univ (f n)).characteristic) x) =
        (∑' (n : ℕ), (set.pi set.univ (f n)).characteristic x) ,
    { apply ennreal.tsum_apply }, 
    rw ← h3b,
    apply h2 },
  have h4:∀ (A:finset α), ∀ (x:Π (a:α), β a),
    (A.prod (λ a, μ a (P a))) * ((finset.univ \ A).prod (λ a, (P a).characteristic (x a))) ≤
    ∑' (n:ℕ), (A.prod (λ a, μ a (f n a))) * ((finset.univ \ A).prod (λ a, (f n a).characteristic (x a))),
  { intros A, apply finset.induction_on A,
    { intros x, simp, apply h3 },
    { intros a' s h_not_mem h_ind x,
      have h4_1:(λ (x':β a'), (P a').characteristic (x') *
      (s.prod (λ (a : α), (μ a) (P a)) *
         (finset.univ \ insert a' s).prod (λ (a : α), (P a).characteristic (x a)))) ≤
    (λ (x':β a'), ∑' (n : ℕ),
      (f n a').characteristic (x') *
        (s.prod (λ (a : α), (μ a) (f n a)) *
           (finset.univ \ insert a' s).prod (λ (a : α), (f n a).characteristic (x a)))),
      { rw has_le_fun_def, intros x',
        have h4_1_1 := h_ind (subst.pi x a' x'),
        have h4_1_2 :s.prod (λ (a : α), (μ a) (P a)) * (finset.univ \ s).prod (λ (a : α), (P a).characteristic (subst.pi x a' x' a)) =  
 (P a').characteristic (x') *
(s.prod (λ (a : α), (μ a) (P a)) *
       (finset.univ \ insert a' s).prod (λ (a : α), (P a).characteristic (x a))),
      { 
        have h4_1_2_1:
      (finset.univ \ (insert  a' s)).prod (λ (a : α), (P a).characteristic (subst.pi x a' x' a)) =
      (finset.univ \ (insert a' s)).prod (λ ⦃a' : α⦄, (P a').characteristic (x a')),
       { apply finset.prod_congr,
         refl, intros a'' h4_1_2_1_1, rw subst.pi_ne, simp at h4_1_2_1_1, intros contra, apply
         h4_1_2_1_1, left, rw contra,  },
        rw ← h4_1_2_1,
        clear h4_1_2_1,
        rw ← mul_assoc, rw mul_comm ((P a').characteristic (x')),
        rw mul_assoc,
        have h4_1_2_2:(P a').characteristic x' = (λ a, (P a).characteristic (subst.pi x a' x' a)) a',
        { simp, rw subst.pi_eq x a' x' },
        rw h4_1_2_2,
        rw finset.prod_univ_diff_insert _ _ a' h_not_mem,
         },
      rw h4_1_2 at h4_1_1,
      clear h4_1_2,
     have h4_1_3:(λ 
(n : ℕ),
      s.prod (λ (a : α), (μ a) (f n a)) *
        (finset.univ \ s).prod (λ (a : α), (f n a).characteristic (subst.pi x a' x' a))) =
(λ (n:ℕ), 
      (f n a').characteristic x' *
        (s.prod (λ (a : α), (μ a) (f n a)) *
           (finset.univ \ insert a' s).prod (λ (a : α), (f n a).characteristic (x a)))),
      { ext1 n,
        have h4_1_2_1:
      (finset.univ \ (insert  a' s)).prod (λ (a : α), (f n a).characteristic (subst.pi x a' x' a)) =
      (finset.univ \ (insert a' s)).prod (λ ⦃a' : α⦄, (f n a').characteristic (x a')),
       { apply finset.prod_congr,
         refl, intros a'' h4_1_2_1_1, rw subst.pi_ne, simp at h4_1_2_1_1, intros contra, apply
         h4_1_2_1_1, left, rw contra,  },
        rw ← h4_1_2_1,
        clear h4_1_2_1,
        rw ← mul_assoc, rw mul_comm ((f n a').characteristic (x')),
        rw mul_assoc,
        have h4_1_2_2:(f n a').characteristic x' = (λ a, (f n a).characteristic (subst.pi x a' x' a)) a',
        { simp, rw subst.pi_eq x a' x' },
        rw h4_1_2_2,
        rw finset.prod_univ_diff_insert _ _ a' h_not_mem,
        
         },
    rw h4_1_3 at h4_1_1,
    clear h4_1_3,
    apply h4_1_1,
  },
      have h4_2:measure_theory.lintegral (μ a') (λ (x':β a'), (P a').characteristic (x') *
      (s.prod (λ (a : α), (μ a) (P a)) *
         (finset.univ \ insert a' s).prod (λ (a : α), (P a).characteristic (x a)))) ≤
         measure_theory.lintegral (μ a')
    (λ (x':β a'), ∑' (n : ℕ),
      (f n a').characteristic (x') *
        (s.prod (λ (a : α), (μ a) (f n a)) *
           (finset.univ \ insert a' s).prod (λ (a : α), (f n a).characteristic (x a)))),
      { apply measure_theory.lintegral_mono, apply h4_1, },
      clear h4_1,
      have h4_3:measure_theory.lintegral (μ a') (λ (x':β a'), (P a').characteristic (x') *
      (s.prod (λ (a : α), (μ a) (P a)) *
         (finset.univ \ insert a' s).prod (λ (a : α), (P a).characteristic (x a)))) =
         (insert a' s).prod (λ (a : α), (μ a) (P a)) *
         (finset.univ \ insert a' s).prod (λ (a : α), (P a).characteristic (x a)),
      { rw measure_theory.lintegral_mul_const,
        rw measure_theory.lintegral_characteristic,
        rw ← mul_assoc,
        rw finset.prod_insert h_not_mem, apply A4, apply measurable.characteristic,
        apply A4 },
      rw h4_3 at h4_2,
      clear h4_3,
      have h4_4:(∫⁻ (x' : β a'),
      (∑' (n : ℕ),
         (f n a').characteristic x' *
           (s.prod (λ (a : α), (μ a) (f n a)) *
              (finset.univ \ insert a' s).prod (λ (a : α), (f n a).characteristic (x a)))) ∂μ a')
        = 
      (∑' (n : ℕ),
∫⁻ (x' : β a'),
(f n a').characteristic x' *
           (s.prod (λ (a : α), (μ a) (f n a)) *
              (finset.univ \ insert a' s).prod (λ (a : α), (f n a).characteristic (x a))) ∂μ a'),
      { rw measure_theory.lintegral_tsum,
        intros n, apply measurable.ennreal_mul,
        apply measurable.characteristic,
        apply A2,
        apply measurable_const },
      rw h4_4 at h4_2,
      clear h4_4,
      have h4_5:(λ (n : ℕ),
∫⁻ (x' : β a'),
(f n a').characteristic x' *
           (s.prod (λ (a : α), (μ a) (f n a)) *
              (finset.univ \ insert a' s).prod (λ (a : α), (f n a).characteristic (x a))) ∂μ a') =
(λ (n : ℕ),
           (insert a' s).prod (λ (a : α), (μ a) (f n a)) *
              (finset.univ \ insert a' s).prod (λ (a : α), (f n a).characteristic (x a))),
      { ext1 n,
        rw measure_theory.lintegral_mul_const,
        rw measure_theory.lintegral_characteristic,
        rw ← mul_assoc,
        rw finset.prod_insert h_not_mem,
        apply A2, apply measurable.characteristic, apply A2, },
   rw h4_5 at h4_2,
   clear h4_5,
   apply h4_2,
 } },

  have h7:∀ (a:α), ∃ x, x ∈ P a,
  { intros a, rw ← set.nonempty_def, apply h_all_nonempty },
  have h8 := classical.axiom_of_choice h7,
  cases h8 with g h8,
  have h6 := h4 finset.univ g,
  simp at h6,
  apply h6,
  rw classical.not_forall_iff_exists_not at h_exists_empty,
  cases h_exists_empty with a h_empty,
  rw set.not_nonempty_iff_eq_empty at h_empty,
  rw @finset.prod_eq_zero _ _ _ a,
  { simp },
  { simp },
  simp [h_empty],  
end



lemma pi.measure_apply 
{α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} [M:∀ a, measurable_space (β a)] 
  (μ:Π a, measure_theory.measure (β a)) {P:set (Π a, β a)}:measurable_set P →
  pi.measure μ P =
  pi.outer_measure (λ a, (μ a).to_outer_measure) P :=
begin
  intro h,
  simp [pi.measure],
  rw measure_theory.to_measure_apply,
  apply h,
end

lemma measurable_set.pi'' {α:Type*} [F:fintype α] {β:α → Type*} [M:∀ a, measurable_space (β a)]
  {P:Π a, set (β a)}:(∀ a, measurable_set (P a)) →
  measurable_set (set.pi set.univ P) := begin
  intros A0,
  have A1:(set.pi set.univ P) = ⋂ a, ((λ (p:Π a, β a), p a) ⁻¹' (P a)),
  { ext x, simp,  },
  rw A1,
  have A3:trunc (encodable α) := encodable.trunc_encodable_of_fintype α,
  trunc_cases A3,
  haveI:encodable α := A3,
  apply measurable_set.Inter,
  intros a',
  have A2:measurable_space.comap (λ (p:Π a, β a), p a') (M a') ≤ measurable_space.pi,
  { simp [measurable_space.pi], apply @le_supr (measurable_space (Π a, β a)) _ _ _ (a') },
  apply A2,
  simp [measurable_space.comap],
  apply exists.intro (P a'),
  simp,
  apply A0 a',
end
 

lemma pi.measure.apply_prod
{α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} [M:∀ a, measurable_space (β a)] 
  (μ:Π a, measure_theory.measure (β a)) {P:Π a, set (β a)}:(∀ a, measurable_set (P a)) →
  pi.measure μ (set.pi set.univ P) =
  finset.univ.prod (λ a, μ a (P a)) :=
begin
  intros A1,
  rw pi.measure_apply,
  apply le_antisymm,
  { apply pi.outer_measure.apply_prod_le },
  apply pi.outer_measure.le_apply_prod,
  apply A1,
  apply measurable_set.pi'' A1,
end

end pi

