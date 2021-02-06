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
import formal_ml.probability_space
import formal_ml.prod_probability_space
import formal_ml.random_variable_independent_pair
import formal_ml.random_variable_identical_IID

/- This file introduces the uniform probability space over a finite outcome type.
   This is in turn used to define a uniform distribution over permutations. -/


--Probably stay here.------------------------

noncomputable def set.cardF {α:Type*} [F:fintype α] (s:set α):nat := 
  (@set.to_finset α s (@subtype.fintype α s (classical.decidable_pred s) F)).card 


lemma set.univ_cardF_eq_fintype_card {α:Type*} [F:fintype α]:
  (@set.univ α).cardF = fintype.card α := begin
  simp [set.cardF],
  have h1:
    @finset.filter α (@set.univ α) (λ (a : α), @set.univ_decidable α a) (@finset.univ α F) =
    (@finset.univ α F),
  { ext1 a, split; intros A1; simp, },
  rw h1,
  simp [fintype.card],
end

lemma finset.disjoint_card_sum {α β:Type*} [decidable_eq α] [fintype α] [decidable_eq β]
  (f:β → finset α) (h:pairwise (disjoint on f)) (t:finset β):∀ (s:finset α),
  (⋃ (x:β) (h2:x∈ t), (@coe (finset α) (set α) _ (f x))) = ↑s → (s.card = t.sum (λ x, (f x).card)) := begin
  classical,
  apply finset.induction_on t,
  { intros s h1, simp, simp at h1,
    rw finset.ext_iff,
    intros a,
    rw set.ext_iff at h1,
    have h2 := h1 a,
    simp at h2,
    simp,
    apply h2 },
  { intros a s h3 h4 t' h5,
    rw finset.sum_insert,
    simp at h5,
    have h6:(f a) ∪ ((⋃ (x : β) (H : x ∈ s), ↑(f x)).to_finset) = t',
    { rw set.ext_iff at h5,
      rw finset.ext_iff,
      intros a',
      have h6_1 := h5 a',
      rw finset.mem_coe at h6_1,
      rw ← h6_1,
      split; intros h6_2; simp at h6_2; simp [h6_2] },
    rw ← h4 ((⋃ (x : β) (H : x ∈ s), ↑(f x)).to_finset),
    rw ← finset.card_union_eq,
    rw h6,
    rw disjoint_iff,
    simp, ext x, split; intros h1, simp at h1, cases h1 with h1 h2,
    cases h2 with i h2,
    cases h2 with h2 h7,
    have h8:i ≠ a,
    { intros contra,
       subst i, apply h3, apply h2,  },
    
    have h9 := h i a h8,
    simp [function.on_fun] at h9,
    rw disjoint_iff at h9,
    simp at h9,
    rw ← h9,
    simp [h1, h7],
    exfalso,
    apply h1,
    simp,
    apply h3,  
         },
   
end


def semiring.of_nat_hom (α:Type*) [semiring α]:nat →+* α := {
  to_fun := coe,
  map_one' := begin
    simp,
  end,
  map_mul' := begin
   intros x y,
   simp,
  end,
  map_add' := begin
    intros x y,
    simp,
  end,
  map_zero' := begin
    simp,
  end
}

lemma finset.prod_coe_nat {α β:Type*} [comm_semiring α] {s:finset β} {f:β → nat}:
  (@coe nat α _) (s.prod f) = s.prod (λ (b:β), (@coe nat α _) (f b)) := begin
  have h1:(@coe nat α _) = (semiring.of_nat_hom α).to_fun,
  { refl },
  rw h1,
  simp,
end

lemma finset.sum_coe_nat {α β:Type*} [comm_semiring α] {s:finset β} {f:β → nat}:
  (@coe nat α _) (s.sum f) = s.sum (λ (b:β), (@coe nat α _) (f b)) := begin
  have h1:(@coe nat α _) = ⇑(semiring.of_nat_hom α),
  { refl },
  rw h1,
  rw ring_hom.map_sum,
end

/- TODO: reverse direction if you get a chance. -/
lemma disjoint_to_finset_iff {α:Type*} [F:fintype α] [decidable_eq α]
  {s t:set α} [decidable_pred s] [decidable_pred t]:disjoint s t ↔ disjoint (s.to_finset) (t.to_finset) :=
begin
  rw disjoint_iff,
  rw disjoint_iff,
  rw set.ext_iff,
  rw finset.ext_iff,
  simp, split; intros h1 x; have h2 := h1 x,
  { split; intros h3, apply absurd h3.right,
    apply h2, apply h3.left,  exfalso, apply h3 },
  { intros h3 h4, have h5 := and.intro h3 h4,
    rw h2 at h5, apply h5 },
end

---DEFINITELY stay here.--------------------

noncomputable def uniform_measure (α:Type*) [F:fintype α]: 
  @measure_theory.measure α ⊤  := @measure_theory.measure.of_measurable α ⊤
  (λ (s:set α) (h:@measurable_set α ⊤ s), 
  ((s.cardF):ennreal)/((fintype.card α):ennreal)) 
begin
  simp [set.cardF],
end
begin
  classical,
  intros f h_meas h_disjoint,
  let s:finset α := (⋃ (i : ℕ), f i).to_finset,
  begin
    simp,
    have h0:s = (⋃ (i : ℕ), f i).to_finset := rfl,
    rw div_eq_mul_inv,
    have h2:(λ (i:ℕ), (((f i).cardF):ennreal) / ((@fintype.card α F):ennreal)) = 
         λ (i:ℕ), (((f i).cardF):ennreal) * ((@fintype.card α F):ennreal)⁻¹,
    { ext1 i, rw div_eq_mul_inv },
    rw h2,
    rw ennreal.tsum_mul_right,
    have h3:↑((@set.Union α ℕ f).cardF) = (∑' (i : ℕ), ↑((f i).cardF)),
    { 
       
       have h4:∀ (x:α), ∃ (i:ℕ), x∈ s → x ∈ f i,
       { intros x, cases classical.em (x ∈ s) with h4_1 h4_1,
         rw h0 at h4_1,simp at h4_1, cases h4_1 with i h4_1,
         apply exists.intro i, intros h4_2, apply h4_1,
         apply exists.intro 0, intros h4_2, apply absurd h4_2, apply h4_1,  },
       rw classical.skolem at h4,
       cases h4 with g h4,
       let t := s.image g,
       rw @tsum_eq_sum ennreal ℕ _ _ _ _ t,
       have h5:s.card = (@set.Union α ℕ f).cardF,
       { simp [set.cardF], have h5_1:(λ (x : α), ∃ (i : ℕ), x ∈ f i) = (set.Union f),
         { ext;split; intros A1; simp at A1; cases A1 with i A1; 
           simp; apply exists.intro i; apply A1, },
         rw h5_1,  },
       rw ← h5,
       rw ← finset.sum_coe_nat,
       simp only [nat.cast_inj, set.cardF],
       rw ← finset.disjoint_card_sum,
       { intros i j h_ne, simp [function.on_fun], rw ← disjoint_to_finset_iff, 
         apply h_disjoint, apply h_ne },
       { simp, ext a, split, intros h6, simp at h6, simp,
         { cases h6 with a' h6,  cases h6 with h6 h7,
           apply exists.intro (g a'), apply h7 },
         { intros h6, simp, apply exists.intro a, split, 
           { simp at h6, apply h6 },
           { apply h4, simp [s], simp at h6, apply h6 }, } },
         intros i h8,
         have h9:f i = ∅,
         { ext a, split; intros A1,
           exfalso, apply h8,
           have h9_1:a ∈ s,
           { simp [s], apply exists.intro i, apply A1 },
           have h9_2:a∈ f (g a) := h4 a h9_1,
           have h9_3:g a = i,
           { apply by_contradiction,
             intros h9_3_1,
             have h9_3_2:disjoint (f (g a)) (f i),
             { apply h_disjoint, apply h9_3_1, },
             rw disjoint_iff at h9_3_2,
             simp at h9_3_2,
             have h9_3_3:a∈ (f (g a)) ∩ (f i),
             { simp, apply and.intro h9_2 A1 },
             rw h9_3_2 at h9_3_3,
             apply h9_3_3 },
           subst i, simp [t], apply exists.intro a,
           split,
           apply exists.intro (g a),
           apply A1, refl, exfalso, apply A1 },
         rw h9,
         simp [set.cardF], refl,
     },
     rw h3,
  end
end

lemma uniform_measure_apply (α:Type*) [F:fintype α] (s:set α):
  (uniform_measure α) s = 
  ((s.cardF):ennreal)/((fintype.card α):ennreal) := begin
  apply measure_theory.measure.of_measurable_apply,
  simp,
end

noncomputable def uniform_measure_space (α:Type*) [F:fintype α]:
  measure_theory.measure_space α := @measure_theory.measure_space.mk α ⊤
  (uniform_measure α)



lemma uniform_measure_space_apply (α:Type*) [F:fintype α] (s:set α):
  @measure_theory.measure_space.volume _ (uniform_measure_space α) s = 
  ((s.cardF):ennreal)/((fintype.card α):ennreal) := begin
  have h1: (@measure_theory.measure_space.volume α (@uniform_measure_space α F)) =
           (uniform_measure α),
  { refl },
  rw h1,
  apply uniform_measure_apply,
end


lemma uniform_measure_space.to_measurable_space_eq_top (α:Type*) [F:fintype α]:
  (uniform_measure_space α).to_measurable_space = ⊤ := rfl

lemma uniform_measure_space.measurable_set'_all (α:Type*) [F:fintype α] (s:set α):
  (uniform_measure_space α).to_measurable_space.measurable_set' s := begin
  rw uniform_measure_space.to_measurable_space_eq_top,
  apply measurable_space.measurable_set_top,
end


/- DO NOT DELETE! 
   There is already proven:
   1. permutations are finite.
   2. There cardinality is the factorial.
   This tells me we are on the right track! -/
#check fintype.card_perm

lemma fintype.card_ne_zero {α:Type*} [F:fintype α] [N:nonempty α]:
  ¬(fintype.card α = 0) := begin
  apply pos_iff_ne_zero.1,
  rw fintype.card_pos_iff,
  apply N,
end



noncomputable def uniform_probability_space (α:Type*) [F:fintype α] [N:nonempty α]:
  probability_space α := @probability_space.mk α (uniform_measure_space α) 
begin
  simp,
  rw uniform_measure_space_apply,
  rw set.univ_cardF_eq_fintype_card,
  rw div_eq_mul_inv,
  apply ennreal.mul_inv_cancel,
  { simp, apply fintype.card_ne_zero },
  { simp },
end

lemma uniform_probability_space.to_measurable_space_eq_top (α:Type*) [F:fintype α] [NE:nonempty α]:
  (uniform_probability_space α).to_measurable_space = ⊤ := rfl

lemma uniform_probability_space.to_measure_space_eq (α:Type*) [F:fintype α] [NE:nonempty α]:
  (uniform_probability_space α).to_measure_space = uniform_measure_space α := rfl


lemma uniform_probability_space.measurable_set'_all (α:Type*) [F:fintype α] [nonempty α] (s:set α):
  (uniform_probability_space α).to_measurable_space.measurable_set' s := begin
  rw uniform_probability_space.to_measurable_space_eq_top,
  apply measurable_space.measurable_set_top,
end

def uniform_event {α:Type*} (s:set α) [F:fintype α] [N:nonempty α]:
  event (uniform_probability_space α) := {
  val := s,
  property := begin
    apply uniform_probability_space.measurable_set'_all,
  end
}

def uniform_probability_space.measurable_all {α β:Type*} [F:fintype α] [nonempty α] 
(M:measurable_space β) (f:α → β):@measurable α β 
  (uniform_probability_space α).to_measurable_space M f := begin
  intros S h1,
  apply uniform_probability_space.measurable_set'_all,
end

lemma uniform_probability_space_apply' (α:Type*) [F:fintype α] [nonempty α] (s:event (uniform_probability_space α)):
  Pr[s] = 
  ((s.val.cardF):nnreal)/((fintype.card α):nnreal) := begin
  rw ← ennreal.coe_eq_coe,
  rw event_prob_def,
  rw uniform_probability_space.to_measure_space_eq,
  simp,
  rw ← subtype.val_eq_coe,
  rw @uniform_measure_space_apply α F s.val,
  rw ennreal.coe_div,
  have h1:∀ (n:ℕ), (@coe nnreal ennreal _ (@coe nat nnreal _ n)) = (@coe nat ennreal _ n),
  { simp },
  rw h1,
  rw h1,
  simp,
  apply fintype.card_ne_zero, 
end

lemma uniform_probability_space_apply (α:Type*) [F:fintype α] [nonempty α] (s:set α):
  Pr[uniform_event s] = 
  ((s.cardF):nnreal)/((fintype.card α):nnreal) := begin
  apply uniform_probability_space_apply',
end

def uniform_rv {α:Type*} [F:fintype α] [N:nonempty α] (M:measurable_space α):
  (uniform_probability_space α) →ᵣ M := {
  val := id,
  property := begin
    apply uniform_probability_space.measurable_all,
  end
}  


def is_uniform_rv {Ω α:Type*} {P:probability_space Ω} [F:fintype α] {M:measurable_space α}
  (X:P →ᵣ M):Prop := ∀ (S:measurable_setB M), 
  Pr[X ∈ᵣ S] = ((S.val.cardF):nnreal)/((fintype.card α):nnreal)

@[simp]
lemma is_uniform_rv_uniform_rv {α:Type*} [F:fintype α] [N:nonempty α] (M:measurable_space α):
  is_uniform_rv (uniform_rv M) := begin
  intros S,
  let S':= uniform_event S.val,
  begin
    have h1:@uniform_rv α F N M ∈ᵣ S = S',
    { apply event.eq, simp [uniform_rv, S', uniform_event], },
    rw h1,
    rw uniform_probability_space_apply,
  end
end

def nonempty_perm {α:Type*}:nonempty (equiv.perm α) := nonempty.intro (equiv.refl α)

def uniform_perm_rv (α:Type*) [D:decidable_eq α] [F:fintype α] (M:measurable_space (equiv.perm α)):_ →ᵣ M :=
  --(@uniform_probability_space (equiv.perm α) (@fintype_perm α D F) nonempty_perm) →ᵣ M :=
  @uniform_rv (equiv.perm α) (@fintype_perm α D F) nonempty_perm M 

lemma is_uniform_rv_uniform_perm_rv {α:Type*} [F:fintype α] [N:decidable_eq α]
  (M:measurable_space (equiv.perm α)):
  @is_uniform_rv _ (equiv.perm α) _ (@fintype_perm α N F) _ (@uniform_perm_rv α N F M) := begin
  apply is_uniform_rv_uniform_rv,
end

lemma select_rv_union_helper {Ω α γ:Type*} [fintype α] [decidable_eq α] {P:probability_space Ω}
   {M:measurable_space γ} (TM:top_measurable α) 
   (X:α → P →ᵣ M) (Y:P →ᵣ (TM.to_measurable_space)) (S:set γ):
   ((λ (ω : Ω), (X (Y.val ω)).val ω) ⁻¹' S) = 
      ⋃ (a:α), ((Y.val ⁻¹' {a}) ∩ ((X a).val ⁻¹' S)) := begin
  ext1 ω,split; intros h1; simp at h1; simp [h1],
end


def select_rv {Ω α γ:Type*} [fintype α] [decidable_eq α] {P:probability_space Ω}
 {M:measurable_space γ}
 {TM:top_measurable α} (X:α → P →ᵣ M) (Y:P →ᵣ TM.to_measurable_space):
  P →ᵣ M := {
  val := (λ ω:Ω, (X (Y.val ω)).val ω),
  property := begin
    intros S h1,
    have h2:((λ (ω : Ω), (X (Y.val ω)).val ω) ⁻¹' S) = 
      ⋃ (a:α), ((Y.val ⁻¹' {a}) ∩ ((X a).val ⁻¹' S)),
    { apply select_rv_union_helper },
    rw h2,
    haveI:encodable α := fintype.encodable α,    
    apply measurable_set.Union,
    intros a,
    apply measurable_set.inter,
    apply Y.property,
    apply TM.all_measurable,
    apply (X a).property,
    apply h1,
  end
}


lemma select_rv_apply {Ω α γ:Type*} [fintype α] [decidable_eq α] {P:probability_space Ω}
   {M:measurable_space γ} {TM:top_measurable α} 
   (X:α → P →ᵣ M) (Y:P →ᵣ (TM.to_measurable_space)) (S:measurable_setB M):
   (select_rv X Y ∈ᵣ S) = (∃ᵣ (a:α), ((Y =ᵣ a) ∧ ((X a) ∈ᵣ S))) := begin
  apply event.eq,
  simp [select_rv],
  ext; split; intros h1; simp at h1; simp [h1],
end






def perm_value_rv {Ω α:Type*} [fintype α] [decidable_eq α] {P:probability_space Ω}
  {TMp:top_measurable (equiv.perm α)}
  (Y:P →ᵣ (TMp.to_measurable_space)) (a:α)
  (M:measurable_space α):
  P →ᵣ M := {
  val := (λ ω:Ω, (Y.val ω) a),
  property := begin
    classical,
    intros S A1,
    let T := {p:equiv.perm α|p a ∈ S},
    begin
      have h1:((λ (ω : Ω), (Y.val ω) a) ⁻¹' S) = ⋃ (p∈ T), ((Y.val) ⁻¹' {p}),
      { ext ω, split; intros h1_1; simp [T] at h1_1; simp [h1_1,T] },
      rw h1,
      haveI:encodable (equiv.perm α) := fintype.encodable (equiv.perm α),
      apply measurable_set.Union,
      intros p,
      apply measurable_set.Union_Prop,
      intros h2,
      apply Y.property,
      apply TMp.all_measurable,
    end
  end
}



lemma perm_value_rv_apply {Ω α:Type*} [fintype α] [decidable_eq α] {P:probability_space Ω}
  {TMp:top_measurable (equiv.perm α)}
  (Y:P →ᵣ (TMp.to_measurable_space)) (a:α)
  (M:measurable_space α) (S:measurable_setB M) 
  [D:decidable_pred (λ (p:equiv.perm α), p a ∈ S.val)]:
  (perm_value_rv Y a M) ∈ᵣ S = 
   ∃ᵣ (p:equiv.perm α) in (set.to_finset (λ (p:equiv.perm α), p a ∈ S.val)), 
    (Y =ᵣ p) := 
begin
  apply event.eq, ext ω, split; intros h1; simp [perm_value_rv] at h1; 
  simp [perm_value_rv, h1]; apply h1,
end 





--set_option pp.implicit true
lemma perm_value_rv_independent {Ω α κ:Type*} [fintype α] [decidable_eq α] {P:probability_space Ω}
  {TMp:top_measurable (equiv.perm α)}
  {Mκ:measurable_space κ}
  (Y:P →ᵣ (TMp.to_measurable_space)) (a:α) (X:P →ᵣ Mκ)
  (M:measurable_space α):
  random_variable_independent_pair X Y →
  random_variable_independent_pair X (perm_value_rv Y a M) :=
begin
  classical,
  intro h1,
  intros S T,
  rw perm_value_rv_apply,
  apply independent_event_pair_exists,
  { intros p h2,
    have h3:Y =ᵣ ↑p = Y ∈ᵣ ({p}:set (equiv.perm α)),
    { apply equal_eq_mem },
    rw h3,
    apply h1 },
  intros i h2 j h3 h_ne,
  simp [function.on_fun, disjoint_iff],
  
  { ext ω, split; intros h3, 
   { simp at h3, exfalso, apply h_ne,
     cases h3, subst i, subst j },
   { exfalso, apply h3 } },
end

def permute_rv {Ω α γ:Type*} [fintype α] [decidable_eq α] {P:probability_space Ω}
   {TM:top_measurable (equiv.perm α)}
    {M:measurable_space γ} (X:α → P →ᵣ M) (perm:P →ᵣ TM.to_measurable_space)
     (TMα:top_measurable α):
   α → P  →ᵣ M := (λ (a:α), select_rv X (perm_value_rv perm a TMα))

lemma permute_rv_identical {Ω α γ:Type*} [F:fintype α] [decidable_eq α]
  {P:probability_space Ω}
   {M:measurable_space γ} {TM:top_measurable (equiv.perm α)}
  (TMα:top_measurable α) 
  (X:α → P →ᵣ M) (perm:P →ᵣ (TM.to_measurable_space)):
  (∀ (a:α), random_variable_independent_pair perm (X a)) →
  (∀ (a a':α), random_variable_identical (X a) (X a')) →
  (∀ (a a':α), random_variable_identical (X a) ((permute_rv X perm TMα) a'))
   := begin
  intros h1 h2 a a',
  simp [permute_rv],
  intros S,
  rw select_rv_apply,
  have h3:eany_finset finset.univ (λ (a : α), perm_value_rv perm a' TMα =ᵣ a∧X a ∈ᵣ S)
           = (∃ᵣ (a : α), perm_value_rv perm a' TMα =ᵣ a∧X a ∈ᵣ S),
  {  
    apply event.eq, simp,  
  },
  rw ← h3,
  haveI:encodable α := fintype.encodable α,
  rw Pr_sum_disjoint_eq,
  have h4:(λ (b : α), Pr[perm_value_rv perm a' TMα =ᵣ b∧X b ∈ᵣ S]) =
    (λ (b : α), Pr[perm_value_rv perm a' TMα =ᵣ b] * Pr[X a ∈ᵣ S]),
  { ext b,
    have h4_1:random_variable_independent_pair (X b) perm,
    { apply random_variable_independent_pair.symm, apply (h1 b), },
    have h4_2 := perm_value_rv_independent perm a' (X b) TMα.to_measurable_space h4_1,
    have h4_3:(perm_value_rv perm a' TMα =ᵣ b) = 
              perm_value_rv perm a' TMα ∈ᵣ (measurable_setB_top {b}),
    { apply equal_eq_mem },
    rw h4_3,
    have h4_4:independent_event_pair 
                (perm_value_rv perm a' TMα ∈ᵣ (measurable_setB_top {b})) (X b ∈ᵣ S),
    { apply random_variable_independent_pair.symm,
      apply h4_2, },
    unfold independent_event_pair at h4_4,
    rw h4_4,
    --rw mul_comm,
    simp,
    left, apply h2 b a,
     },
   rw h4,
   rw ← @finset.sum_mul α nnreal finset.univ,
   rw  Pr_sum_univ_eq_one,
   simp,
   intros i j h_ne,
   rw function.on_fun,
   rw disjoint_iff,
   simp,
   ext ω, split; intros A1; simp at A1; simp [A1],
   apply h_ne,
   rw ← A1.left.left,
   rw ← A1.right.left,
   apply false.elim A1,
end

lemma random_variables_independent_proj {Ω α β γ:Type*} [fintype α] [fintype β]
  (P:probability_space Ω) (M:measurable_space γ) (X:α → P →ᵣ M) (f:β → α):
  (function.injective f) →
  (random_variable_independent X) →
  (random_variable_independent (λ (b:β), X (f b))) := begin
  classical,
  intros h1 h2,
  intros g T,
  simp,
  have h3:∀ (a:α), ∃ (S:measurable_setB M), ∀ (b:β), (f b = a) → (g b = S),
  { intros a, cases classical.em (∃ (b:β), f b = a) with h3_1 h3_1,
    { cases h3_1 with b h3_1,
      apply exists.intro (g b),
      intros b' h_b',
      rw ← h3_1 at h_b',
      have h3_2 := h1 h_b', rw h3_2 },
    { apply exists.intro measurable_setB_univ,
      intros b'  h_b',
      exfalso,
      apply h3_1,
      apply exists.intro b',
      apply h_b' }, },
  have h4 := classical.axiom_of_choice h3,
  cases h4 with g' h4,
  have h5:∀ (b:β), g b = g' (f b),
  { intros b, apply h4 (f b) b _, refl },
  have h6:(λ (b : β), Pr[X (f b) ∈ᵣ g b]) = (λ (a:α), Pr[X a ∈ᵣ g' a]) ∘ f,
  { ext1 b, simp, rw h5 },
  rw h6,
  have h7:T.prod ((λ (a:α), Pr[X a ∈ᵣ g' a]) ∘ f) = (T.image f).prod (λ (a:α), Pr[X a ∈ᵣ g' a]),
  { rw finset.prod_image, intros b h_b b' h_b' h_eq,
    apply h1, apply h_eq },
  rw h7,
  have h8: (∀ᵣ (s : β) in T,X (f s) ∈ᵣ g s) = (∀ᵣ (a:α) in (T.image f), X a ∈ᵣ g' a),
  { apply event.eq, simp, ext ω, split; intros h8_1; simp at h8_1; simp [h8_1];
    intros i h_i,
    { rw ← h5, apply h8_1 i h_i },
    { rw h5, apply h8_1 i h_i } },
  rw h8,
  apply h2,
end

lemma random_variables_IID_proj {Ω α β γ:Type*} [fintype α] [fintype β]
  (P:probability_space Ω) (M:measurable_space γ) (X:α → P →ᵣ M) (f:β → α):
  (function.injective f) →
  (random_variables_IID X) →
  (random_variables_IID (λ (b:β), X (f b))) := begin
  intros h1 h2, split,
  { apply random_variables_independent_proj, apply h1, apply h2.left },
  intros i j,
  apply h2.right,
end

lemma random_variable_independent_pair_combine_apply {Ω α γ κ:Type*} 
  [F:fintype α] 
  {P:probability_space Ω}
   {M:measurable_space γ} {Mκ:measurable_space κ}
  (X:P →ᵣ Mκ) (Y:α → P →ᵣ M) (a:α):
  random_variable_independent_pair X (pi.random_variable_combine Y) →
  random_variable_independent_pair X (Y a) := begin
  intros h1,
  intros S₁ S₂,
  have h2:(Y a ∈ᵣ S₂) = ((mf_pi (λ (a:α), M) a) ∘r (pi.random_variable_combine Y)) ∈ᵣ S₂,
  { apply event.eq, simp, split; intros h2_1; simp at h2_1; simp at h2_1, },
  rw h2,
  rw rv_compose_measurable_setB,
  apply h1,
end

lemma pairwise_disjoint_left {Ω α:Type*} 
  {P:probability_space Ω}
  {E F:α → event P}:
  (pairwise (disjoint on (λ a, (E a).val))) →
 (pairwise (disjoint on (λ a, (E a ∧ F a).val))) := begin
  intros h1,
  intros i j h_eq,
  have h2 := h1 i j h_eq,
  simp [function.on_fun],
  simp [function.on_fun] at h2,
  rw disjoint_iff,
  rw disjoint_iff at h2,
  simp,
  rw ← set.subset_empty_iff,
  apply set.subset.trans,
  apply set.inter_subset_inter,
  apply set.inter_subset_left,
  apply set.inter_subset_left,
  simp at h2,
  rw h2,
end

/- Take a given event: The arugment for this is that for any fixed permutation,
   the IID property holds. If we can show that this holds for every permutation,
   then we will be done. -/
lemma permute_rv_independent {Ω α γ:Type*} [F:fintype α] [D:decidable_eq α] [inhabited α]
  {P:probability_space Ω}
   {M:measurable_space γ} {TM:top_measurable (equiv.perm α)}
  {TMα:top_measurable α} 
  (X:α → P →ᵣ M) (perm:P →ᵣ (TM.to_measurable_space)):
  (random_variable_independent_pair perm (pi.random_variable_combine X)) →
  (random_variables_IID X) →
  (random_variable_independent (permute_rv X perm TMα)) := begin
  intros h1 h2,
  intros S T,
  simp,
  let a := inhabited.default α,
  begin
    have h4:∀ (S:measurable_setB M), ∀ (a':α), 
       Pr[X a' ∈ᵣ S] = Pr[X a ∈ᵣ S],
    { intros S a', apply h2.right a' a },
    have h_pair_ind:∀ (a':α), random_variable_independent_pair perm (X a'),
    { intros a', apply random_variable_independent_pair_combine_apply perm X a' h1 },
    have h5:∀ (S:measurable_setB M), ∀ (a':α), 
       Pr[permute_rv X perm TMα a' ∈ᵣ S] = Pr[X a ∈ᵣ S],
    { intros S a', symmetry, 
      have h5_1 := permute_rv_identical TMα X perm h_pair_ind _ a a',
      apply h5_1,
      apply h2.right },
    rw @finset.prod_congr α nnreal _ T _   (λ (b:α), Pr[X a ∈ᵣ S b]),
    have h7:(∀ᵣ (s : α) in T, permute_rv X perm TMα s ∈ᵣ S s) = 
      eany_finset (finset.univ) (λ (p:equiv.perm α), (perm =ᵣ p) ∧ 
          (∀ᵣ (s : α) in (T.image p),X s ∈ᵣ S (p.inv_fun s))),
    { apply event.eq, ext ω, split; intros h7_1; 
      simp [equiv_cancel_left, permute_rv, select_rv, perm_value_rv] at h7_1; 
      simp [equiv_cancel_left, permute_rv, select_rv, perm_value_rv, h7_1]; intros i h_i,
      { rw equiv_cancel_left, apply h7_1 i h_i },
      { have h7_2 := h7_1  i h_i, rw equiv_cancel_left at h7_2, apply h7_2 } },
    rw h7,
    --haveI:fintype (equiv.perm α) := infer_instance,
    haveI E:encodable (equiv.perm α) := fintype.encodable (equiv.perm α),
    rw @Pr_sum_disjoint_eq Ω (equiv.perm α) P,
    have h8:(λ (b : equiv.perm α), Pr[perm =ᵣ ↑b∧∀ᵣ (s : α) in (T.image b),X s ∈ᵣ S (b.inv_fun s)]) =
       (λ (b : equiv.perm α), T.prod (λ a', Pr[X a ∈ᵣ S a']) * Pr[perm =ᵣ ↑b]),
    { ext1 b,
      have h8_1:independent_event_pair (perm =ᵣ b) (∀ᵣ (s : α) in (T.image b),X s ∈ᵣ S (b.inv_fun s)),
      { apply random_variable_independent_pair_apply h1,
        apply equal_eq_mem_exists,
        apply joint_random_variable_mem_exists X (T.image b) (S ∘ (b.inv_fun)),
         },
      unfold independent_event_pair at h8_1,
      rw h8_1,
      rw mul_comm,
      have h8_2:random_variable_independent X :=h2.left,
      have h8_3:independent_events (λ (s : α),X s ∈ᵣ S (b.inv_fun s)),
      { apply h8_2 },
      rw ← h8_3 (T.image b), rw finset.prod_image, simp,
      left,
      apply finset.prod_congr, refl, intros x h_x, rw equiv_cancel_left, apply h4,
      intros i h_i j h_j h_eq, simp at h_eq, apply h_eq },
    rw h8,
    rw finset.sum_distrib_left,
    have h9:finset.univ.sum (λ (a : equiv.perm α), Pr[perm =ᵣ ↑a]) = 1,
    { rw Pr_sum_univ_eq_one },
    rw h9,
    simp,
    { apply pairwise_disjoint_left, apply event_eq_disjoint },
    refl,
    { intros x h_x, rw h5 },
  end
end

lemma permute_rv_IID' {Ω α γ:Type*} [fintype α] [decidable_eq α] [I:inhabited α]
  {P:probability_space Ω}
   {M:measurable_space γ} {TM:top_measurable (equiv.perm α)}
  {TMα:top_measurable α} 
  (X:α → P →ᵣ M) (perm:P →ᵣ (TM.to_measurable_space)):
  (random_variables_IID X) →
  (random_variable_independent_pair perm (pi.random_variable_combine X)) →
  (random_variables_IID (permute_rv X perm TMα)) := begin
  intros h1 h2,
  split,
  apply permute_rv_independent,
  apply h2,
  apply h1,
  have h4:∀ (a a'), random_variable_identical (X a) (permute_rv X perm TMα a'),
  { apply permute_rv_identical,
    intros a'',
    apply random_variable_independent_pair_combine_apply,
    apply h2, 
    apply h1.right },
  intros i j,
  apply random_variable_identical.trans,
  apply random_variable_identical.symm,
  apply h4 (inhabited.default α) i,
  apply h4,
end

lemma permute_rv_IID {Ω α γ:Type*} [fintype α] [decidable_eq α] {P:probability_space Ω}
   {M:measurable_space γ} {TM:top_measurable (equiv.perm α)}
  {TMα:top_measurable α} 
  (X:α → P →ᵣ M) (perm:P →ᵣ (TM.to_measurable_space)):
  (random_variables_IID X) →
  (random_variable_independent_pair perm (pi.random_variable_combine X)) →
  (random_variables_IID (permute_rv X perm TMα)) := begin
  classical,
  cases classical.em (nonempty α) with h1 h1,
  { haveI:inhabited α := classical.inhabited_of_nonempty h1,
    apply permute_rv_IID' },
  intros h2 h3, apply random_variables_IID_empty,
  apply h1,
end



/--
   This is a core result, that a partition of an IID random variable results in two independent
   random variables.
   It is not as trivial as it appears, as one must handle events that expose correlations 
   within each set. Again, the monotone class theorem is useful.

   Note: functions do not have to be injective, nor does β₁ or β₂ have to be nonempty.
   However, this can be used to prove the case when they
   are not, as you can create an injective function as an intermediate step,
   and case-based analysis can handle the cases where β₁ or β₂ are empty. -/
lemma random_variables_independent_disjoint_proj {Ω α β₁ β₂ γ:Type*} [fintype α] [fintype β₁] [fintype β₂] [nonempty β₁] [nonempty β₂]
  (P:probability_space Ω) (M:measurable_space γ) (X:α → P →ᵣ M) (f₁:β₁ → α) (f₂:β₂ → α):
  (function.injective f₁) →
  (function.injective f₂) →
  (disjoint (set.range f₁) (set.range f₂)) →
  (random_variable_independent X) →
  (random_variable_independent_pair (pi.random_variable_combine (λ (b:β₁), X (f₁ b))) (pi.random_variable_combine (λ (b:β₂), X (f₂ b)))) := begin
  intros h1 h2 h_disjoint_range h3,
  haveI:encodable β₁ := fintype.encodable β₁,
  haveI:encodable β₂ := fintype.encodable β₂,
  apply random_variable_independent_pair_on_semialgebra' pi_base,
  apply pi_base_is_semialgebra,
  apply pi_base_is_semialgebra,
  apply pi_base_eq_measurable_space_pi,
  apply pi_base_eq_measurable_space_pi,
  intros T₁ T₂ h_T₁ h_T₂,
  unfold independent_event_pair,
  have h_T₁_def := pi_base_eq T₁ h_T₁,
  have h_T₂_def := pi_base_eq T₂ h_T₂,
  cases h_T₁_def with g₁ h_T₁_def,
  cases h_T₂_def with g₂ h_T₂_def,
  subst T₁,
  subst T₂,
  classical,
  let U₁:finset α := (finset.image f₁ (@finset.univ β₁ _)),
  let U₂:finset α := (finset.image f₂ (@finset.univ β₂ _)),
  begin
    have h_mem_U₁:∀ (a:α), a ∈ U₁ ↔ a ∈ (set.range f₁),
    { simp [U₁], },
    have h_mem_U₂:∀ (a:α), a ∈ U₂ ↔ a ∈ (set.range f₂),
    { simp [U₂], },
    have h_b₁_ne_b₂:∀ (b₁:β₁) (b₂:β₂), f₁ b₁ ≠ f₂ b₂,
    { intros b₁ b₂ h_contra,
      rw disjoint_iff at h_disjoint_range,
      simp at h_disjoint_range,
      rw ← set.subset_empty_iff at h_disjoint_range,
      rw set.subset_def at h_disjoint_range,
      apply h_disjoint_range (f₁ b₁),
      rw set.mem_inter_iff,
      split,
      simp,
      rw h_contra,
      simp },
    
    have h_disjoint:disjoint U₁ U₂,
    { rw disjoint_iff, simp, ext a, split; intros h_sub1,
      { exfalso,
        rw finset.mem_inter at h_sub1,
        rw h_mem_U₁ at h_sub1,
        rw h_mem_U₂ at h_sub1,
        rw ← set.mem_inter_iff at h_sub1,
        rw disjoint_iff at h_disjoint_range,
        simp at h_disjoint_range,
        rw ← set.subset_empty_iff at h_disjoint_range,
        rw set.subset_def at h_disjoint_range,
        --have h_disjoint_range_contra := h_disjoint_range a h_sub1,
        apply h_disjoint_range,
        apply h_sub1 },
      { exfalso, apply h_sub1 } },
    have h_inv:∀ (a:α), ∃ (S:measurable_setB M), 
      (∀ (b:β₁), f₁ b = a → S = g₁ b) ∧ (∀ (b:β₂), f₂ b = a → S = g₂ b),
    { intros a,
      cases classical.em (∃ (b:β₁), f₁ b = a) with h_in_U₁ h_notin_U₁,
      { cases h_in_U₁ with b₁ h_b₁,
        subst a,
        apply exists.intro (g₁ b₁),
        split,
        { intros b₁' h_b₁', simp [h1] at h_b₁', subst b₁' },
        { intros b₂' h_b₂', exfalso, apply h_b₁_ne_b₂ b₁ b₂', rw h_b₂' } },
      -- If a is not in U₁, then we consider when it is in U₂.
      cases classical.em (∃ (b₂:β₂), f₂ b₂ = a) with h_in_U₂ h_notin_U₂,
      { cases h_in_U₂ with b₂ h_b₂,
        subst a,
        apply exists.intro (g₂ b₂),
        split,
        { intros b₁' h_b₁', exfalso, apply h_b₁_ne_b₂ b₁' b₂, rw h_b₁' },
        { intros b₂' h_b₂', simp [h2] at h_b₂', subst b₂' } },
      -- If a is not in U₁ or U₂, then just use the universal set.
      { apply exists.intro (∅:measurable_setB M), 
         split,
         { intros b₁ h_b₁, exfalso, apply h_notin_U₁,
           apply exists.intro b₁, apply h_b₁ },
         { intros b₂ h_b₂, exfalso, apply h_notin_U₂,
           apply exists.intro b₂, apply h_b₂ } } },
    rw classical.skolem at h_inv,
    cases h_inv with g_inv h_inv,
    have h_inv₁:pi.random_variable_combine (λ (b : β₁), X (f₁ b)) ∈ᵣ
          set.pi_measurable (set.univ) g₁ = (∀ᵣ a in U₁, X a ∈ᵣ g_inv a),
    { apply event.eq, ext1 ω, split; intros h_sub1;
      simp [pi.random_variable_combine, set.pi_measurable,
            pi.measurable_fun] at h_sub1;
      simp [pi.random_variable_combine, set.pi_measurable,
            pi.measurable_fun, h_sub1];
      intros b₁, 
      { rw (h_inv (f₁ b₁)).left b₁ _, apply h_sub1, refl },
      { rw ← (h_inv (f₁ b₁)).left b₁ _, apply h_sub1, refl } },
    rw h_inv₁,
    have h_inv₂:pi.random_variable_combine (λ (b : β₂), X (f₂ b)) ∈ᵣ
          set.pi_measurable (set.univ) g₂ = (∀ᵣ a in U₂, X a ∈ᵣ g_inv a),
    { apply event.eq, ext1 ω, split; intros h_sub1;
      simp [pi.random_variable_combine, set.pi_measurable,
            pi.measurable_fun] at h_sub1;
      simp [pi.random_variable_combine, set.pi_measurable,
            pi.measurable_fun, h_sub1];
      intros b₂, 
      { rw (h_inv (f₂ b₂)).right b₂ _, apply h_sub1, refl },
      { rw ← (h_inv (f₂ b₂)).right b₂ _, apply h_sub1, refl }, },
    rw h_inv₂,
    have h_union:((∀ᵣ (a : α) in U₁,X a ∈ᵣ g_inv a)∧(∀ᵣ (a : α) in U₂,X a ∈ᵣ g_inv a))
      = (∀ᵣ (a : α) in (U₁∪ U₂),X a ∈ᵣ g_inv a),
    { apply event.eq, ext1 ω, split; intros h_sub1; simp at h_sub1; simp [h_sub1],
      -- Simplification solves one direction.
      intros a h_sub2, cases h_sub2 with h_in_U₁ h_in_U₂,
      { cases h_in_U₁ with b₁ h_b₁, subst a, apply h_sub1.left },
      { cases h_in_U₂ with b₂ h_b₂, subst a, apply h_sub1.right } },
    rw h_union,
    rw ← h3 g_inv U₁,
    rw ← h3 g_inv U₂,
    rw ← h3 g_inv (U₁ ∪ U₂),
    rw finset.prod_union,
    apply h_disjoint,
  end
end

