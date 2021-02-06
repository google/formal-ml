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
import formal_ml.sum
import formal_ml.lattice
import formal_ml.measurable_space
import formal_ml.classical
import data.equiv.list
import formal_ml.probability_space

/-! This file gives various ways to produce independent events. -/


--- Find a different place for these lemmas ----------
lemma disjoint_exists_and {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (x y:finset α):set.pairwise_on (↑(x∪ y)) (disjoint on (λ s, (E s).val)) →
  ((∃ᵣ a in x, E a) ∧ (∃ᵣ a in y, E a)) = (∃ᵣ a in (x ∩ y), E a) :=
begin
  classical,
  intros h_disj,
  apply event.eq,
  ext1 ω, split; intros h1; simp at h1; simp, 
  { cases h1 with h1 h2,
    cases h1 with a h1,
    cases h2 with a' h2,
    have h3:a = a',
    { apply by_contradiction, intros h_contra, 
      have h3_1:= h_disj a _ a' _ h_contra,
      rw [function.on_fun, disjoint_iff, subtype.val_eq_coe, set.inf_eq_inter, set.bot_eq_empty,
          ← set.subset_compl_iff_disjoint,
          set.subset_def] at h3_1,
      apply h3_1 ω h1.right h2.right, 
      simp [h1],
      simp [h2] },
    subst a', apply exists.intro a,
    simp [h1, h2] },
  { cases h1 with a h1,
    split; apply exists.intro a; simp [h1] },
end


lemma disjoint_exists_diff {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (x y:finset α):set.pairwise_on (↑(x∪ y)) (disjoint on (λ s, (E s).val)) →
  ((∃ᵣ a in x, E a) \ (∃ᵣ a in y, E a)) = (∃ᵣ a in (x \ y), E a) :=
begin
  classical,
  intros h_disj,
  apply event.eq,
  ext1 ω, split; intros h1; simp at h1; simp,
  { cases h1 with h1 h2,
    cases h1 with i h1,
    apply exists.intro i,
    split, split,
    { apply h1.left },
    { intros contra, apply h2 i contra,
      apply h1.right },
    apply h1.right },
  { cases h1 with i h1, 
    split, 
    { apply exists.intro i, simp [h1] },
    { intros a' h_a'_in_y h_contra,
      have h2:a' = i,
      { apply by_contradiction,
        intros h_contra2,
        have h2_disj := h_disj a' _ i _ h_contra2, 
        rw [function.on_fun, set.disjoint_left] at h2_disj, simp at h2_disj,
        apply h2_disj h_contra,
        apply h1.right,
        simp,
        right,
        apply h_a'_in_y,
        simp,
        left,
        apply h1.left.left },
      subst a',
      apply h1.left.right,
      apply h_a'_in_y }  },  
end


lemma exists_or {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (x y:finset α):
  ((∃ᵣ a in x, E a) ∨ (∃ᵣ a in y, E a)) = (∃ᵣ a in (x ∪ y), E a) :=
begin
  classical,
  apply event.eq,
  ext1 ω, split; intros h1; simp at h1; simp, 
  { cases h1 with h1 h1;
    { cases h1 with a h1,
      apply exists.intro a, simp [h1] } },
  { cases h1 with a h1,
    cases h1 with h1 h2,
    cases h1 with h1 h1,
    { left, apply exists.intro a, simp [h1,h2] },
    { right, apply exists.intro a, simp [h1,h2] } },
end

lemma forall_and {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (x y:finset α):
  ((∀ᵣ a in x, E a) ∧ (∀ᵣ a in y, E a)) = (∀ᵣ a in (x ∪ y), E a) :=
begin
  classical,
  apply event.eq,
  ext1 ω, split; intros h1; simp at h1; simp [h1], 
  { cases h1 with h1 h2,
    intros a h3,
    cases h3 with h3 h3,
    { apply h1 a h3 },
    { apply h2 a h3 } },
  { split; intros a h2; apply h1;
    { simp [h2] } },
end

-----------------------------------------


lemma independent_event_pair_exists {Ω α:Type*} {P:probability_space Ω}
 {S:finset α} {E:event P} {F:α → event P} [decidable_eq (event P)]:
  (∀ (s∈ S), independent_event_pair E (F s)) →
  (set.pairwise_on (↑S) (disjoint on (λ a, (F a).val))) →
  independent_event_pair E (∃ᵣ a in S, F a) := begin
  classical,
  intros h1 h2,
  simp [independent_event_pair],
  --rw eany_in_finset_def,
  rw Pr_sum_disjoint_eq',
  
  rw ← finset.sum_distrib_left,
  rw ← distrib_exists_and,
  rw Pr_sum_disjoint_eq',
  apply finset.sum_congr,
  { refl },
  { intros x h_x, have h4 := h1 x h_x, simp [independent_event_pair] at h4,
    apply h4 },
  { intros i h_i j h_j h_ne, simp only [function.on_fun], rw disjoint_iff, 
    simp, rw ← set.subset_empty_iff, apply set.subset.trans,
    apply set.inter_subset_inter,
    apply set.inter_subset_right,
    apply set.inter_subset_right, 
    have h5 := h2 i _ j _ h_ne, simp only [function.on_fun] at h5, rw disjoint_iff at h5,
    simp at h5, rw h5, apply h_i, apply h_j },
  apply h2,
end

lemma independent_events_induction {Ω:Type*} {α:Type*} {P:probability_space Ω}
  {E:α → event P}:(∀ (a:α) (S:finset α), (a ∉ S) → 
   independent_event_pair (E a) (∀ᵣ a' in S, E a')) →
  (independent_events E) :=
begin
  classical,
  intros h1 T,
  apply finset.induction_on T,
  { simp },
  { intros a s h2 h3,
    rw finset.prod_insert,
    rw eall_finset_insert,
    have h4 := h1 a s h2,
    unfold independent_event_pair at h4,
    rw h4,
    rw ← h3,
    apply h2 },
end


@[simp]
lemma event_univ_and {Ω:Type*} {P:probability_space Ω} {A:event P}:
(event_univ ∧ A) = A := begin
  apply event.eq, simp,
end


lemma Pr_and_or_not_and {Ω:Type*} {P:probability_space Ω}  {A B:event P}:
Pr[(A ∧ B)] + Pr[(¬ₑ A) ∧ B] = Pr[B] := begin
  have h1:((A ∧ B) ∨ ((¬ₑ A)) ∧ B) = B,
  { apply event.eq, ext ω, split; intros h1; simp at h1; simp [h1],
    cases h1 with h1 h1; simp [h1], apply (classical.em  (ω ∈ ↑(A))), },
  rw ← Pr_disjoint_eor,  
  rw h1,
  rw disjoint_iff,
  ext1 ω, split; intros h2; simp at h2; simp [h2],
  apply h2.right.left h2.left.left,
  apply false.elim h2,
end

lemma Pr_not_and_eq {Ω:Type*} {P:probability_space Ω}  {A B:event P}:
  Pr[(¬ₑ A)∧ B] = Pr[B] - Pr[A ∧ B] :=
begin
  rw ← @Pr_and_or_not_and _ _ A B,
  rw add_comm,
  rw nnreal.add_sub_cancel,
end


lemma nnreal.sub_mul_eq {a b c:nnreal}:(a - b) * c = (a * c) - (b * c) :=
begin
  cases (le_total a b) with h h,
  { have h2:(a * c) ≤ (b * c),
    { apply mul_le_mul', apply h, apply le_refl _ },
    rw nnreal.sub_eq_zero h, 
    rw nnreal.sub_eq_zero h2,
    simp },
  have h2:(b * c) ≤ (a * c),
  { apply mul_le_mul', apply h, apply le_refl _ },    
  rw ←  nnreal.coe_eq,
  rw nnreal.coe_mul,
  rw nnreal.coe_sub h,
  rw nnreal.coe_sub h2,
  rw nnreal.coe_mul,
  rw nnreal.coe_mul,
  linarith,
end

lemma independent_events_rel {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (f:α → event P)
(h_ind:independent_events f) (T_not:finset α) (T_same:finset α) (h_disj:disjoint T_not T_same):
Pr[(∀ᵣ a in T_not, ¬ₑ (f a)) ∧ (∀ᵣ a in T_same, (f a))]
  = (T_not.prod (λ a, Pr[¬ₑ (f a)])) * (T_same.prod (λ a, Pr[f a])) :=
begin
  revert T_same,
  apply finset.induction_on T_not,
  { intros T_same h_disj, simp, rw h_ind, },
  { intros a s h_a_notin_s h_ind T_same T_disj, 
    rw has_eall_in_insert, rw eand_assoc,
    rw Pr_not_and_eq,
    rw h_ind T_same _,
    have h1:∀ (A B C:event P), (A ∧ (B ∧ C)) = (B ∧ (A ∧ C)),
    { intros A B C, apply event.eq, ext1 ω; split; intros h1; simp at h1; simp [h1] },
    rw ←  eand_assoc,
    rw eand_comm (f a),
    rw eand_assoc,
    rw ← has_eall_in_insert,
    rw h_ind (insert a T_same) _,
    rw finset.prod_insert,
    rw finset.prod_insert,
    rw ← Pr_one_minus_eq_not,
    rw nnreal.sub_mul_eq,
    rw nnreal.sub_mul_eq,
    rw ← mul_assoc,
    rw mul_comm _ (Pr[f a]),
    simp,
    { apply h_a_notin_s },
    { rw finset.disjoint_left at T_disj,
      apply T_disj,
      simp },
    { rw finset.disjoint_left, 
      intros a' h_a'_in_s, 
      rw finset.disjoint_left at T_disj,
      intros contra,
      simp at contra,
      cases contra with contra contra, 
      { subst a', apply h_a_notin_s h_a'_in_s },
      { apply @T_disj a', simp [h_a'_in_s], apply contra,  } },
    { rw finset.disjoint_left, intros a' h_a'_in_s,
      rw finset.disjoint_left at T_disj,
      apply T_disj,
      simp [h_a'_in_s] } }, 
end


/-- This represents a function of a finite number of events in a tabular way. -/
def function_of_events {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α) (F:event P):Prop := ∃ (T:finset (finset α)), T ⊆ S.powerset ∧ 
  (∃ᵣ s in T,  (∀ᵣ a in s, E a) ∧ (∀ᵣ a in (S \ s), ¬ₑ(E a))) = F 

lemma function_of_events_event {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α) (a:α) (h_a:a ∈ S):function_of_events E S (E a) := begin
  classical,
  apply exists.intro (S.powerset.filter (λ s, a ∈ s)),
  split, 
  { simp }, 
  apply event.eq,
  ext1 ω, split; intros h1; simp [h1]; simp at h1,
  { cases h1 with s h1,
    cases h1 with h1 h2, cases h2 with h2 h3,
    apply h2 a h1.right, },
  { apply exists.intro (S.filter (λ a', ω ∈ E a')),
    simp [h_a, h1],split,
    { apply h1 },
    split,
    { intros i h4 h5, apply h5 },
    { intros i h4 h5, apply h5 h4 } },
end



lemma disjoint_union {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α):set.pairwise_on ↑(S.powerset) (λ s t, disjoint 
  ((∀ᵣ a in s, E a) ∧ (∀ᵣ a in (S \ s), ¬ₑ(E a))).val 
  ((∀ᵣ a in t, E a) ∧ (∀ᵣ a in (S \ t), ¬ₑ(E a))).val) := begin
  classical,
  intros i h_i j h_j h_ne,
  have h_ne_exists:∃ a, ((a ∈ i) ∧ (a ∉ j)) ∨ ((a∉ i) ∧ (a ∈ j)),
  { rw ← not_forall_not, intros contra, apply h_ne,
    ext a, have contra_a := contra a,
    split; intros h_1;
    apply by_contradiction; intros h_2;
    apply contra_a;
    simp [contra_a, h_1, h_2] },
  have h_i_subset_S:i ⊆ S,
  { rw [finset.mem_coe, finset.mem_powerset] at h_i, apply h_i },
  have h_j_subset_S:j ⊆ S,
  { rw [finset.mem_coe, finset.mem_powerset] at h_j, apply h_j },
  rw disjoint_iff,
  simp,
  rw ← set.subset_compl_iff_disjoint,
  rw set.subset_def,
  intros ω h_ω,
  simp at h_ω,
  simp,
  intros h_j,
  cases h_ne_exists with a h_ne_exists,
  cases h_ne_exists with h_a_in_i h_a_in_j,
  { have h_ω_2 := h_ω.left a h_a_in_i.left,
    apply exists.intro a,
    simp [h_ω_2, h_a_in_i],
    apply h_i_subset_S,
    apply h_a_in_i.left  },
  { exfalso, apply h_ω.right a _ h_a_in_j.left,
    apply h_j, apply h_a_in_j.right,
    apply h_j_subset_S,
    apply h_a_in_j.right },
end


lemma disjoint_union_sub {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α) (F:finset (finset α)) (h_sub:F⊆ S.powerset):set.pairwise_on ↑(F) (λ s t, disjoint 
  ((∀ᵣ a in s, E a) ∧ (∀ᵣ a in (S \ s), ¬ₑ(E a))).val 
  ((∀ᵣ a in t, E a) ∧ (∀ᵣ a in (S \ t), ¬ₑ(E a))).val) := begin
  apply @set.pairwise_on.mono (finset α) (↑S.powerset) ↑F
    (λ (s t : finset α),
       disjoint ((∀ᵣ (a : α) in s,E a)∧∀ᵣ (a : α) in S \ s,¬ₑ E a).val
         ((∀ᵣ (a : α) in t,E a)∧∀ᵣ (a : α) in S \ t,¬ₑ E a).val)
  _ _,
  { simp [h_sub] },
  apply disjoint_union,
end

#print instances has_sdiff


lemma function_of_events_diff {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α) (F G:event P) (h_F:function_of_events E S F)
  (h_G:function_of_events E S G):function_of_events E S (F \ G) := begin
  cases h_F with F_T h_F,
  cases h_G with G_T h_G,
  apply exists.intro (F_T \ G_T),
  split,
  { apply finset.subset.trans, apply finset.sdiff_subset, apply h_F.left },
  rw ← disjoint_exists_diff,
  rw h_F.right,
  rw h_G.right,
  apply disjoint_union_sub,
  apply finset.union_subset,
  apply h_F.left,
  apply h_G.left,
end

@[simp]
lemma function_of_events_univ {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α): (function_of_events E S event_univ) := begin
  classical,
  apply exists.intro (S.powerset),
  split,
  apply finset.subset.refl,
  apply event.eq,
  ext1 ω, split; intros h1; simp at h1, simp,
  apply exists.intro (S.filter (λ a, ω ∈ (E a))),
  split,
  simp,
  split,
  { intros i h_i,
    simp at h_i,
    apply h_i.right },
  { intros i h_1 h_2 h_3, apply h_2,
    simp,
    apply and.intro h_1,
    apply h_3 },
end

lemma function_of_events_compl {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α) (F:event P) (h_F:function_of_events E S F):function_of_events E S (Fᶜ) := begin
  have h1:event_univ \ F = Fᶜ,
  { apply event.eq, ext1 ω, split; intros h1; simp at h1; simp [h1], },
  rw ← h1,
  apply function_of_events_diff,
  simp,
  apply h_F,
end

lemma function_of_events_and {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α) (F G:event P) (h_F:function_of_events E S F)
  (h_G:function_of_events E S G):function_of_events E S (F ∧ G) := begin
  have h1:(F ∧ G) = F \ Gᶜ,
  { apply event.eq, ext1 ω, split; intros h1; simp at h1; simp [h1], },
  rw h1,
  apply function_of_events_diff,
  apply h_F,
  apply function_of_events_compl,
  apply h_G,
end

lemma function_of_events_or {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α) (F G:event P) (h_F:function_of_events E S F)
  (h_G:function_of_events E S G):function_of_events E S (F ∨ G) := begin
  cases h_F with F_T h_F,
  cases h_G with G_T h_G,
  apply exists.intro (F_T ∪ G_T),
  split,
  { apply finset.union_subset; simp [h_F, h_G], },
  rw ← exists_or,
  rw h_F.right,
  rw h_G.right,
end


lemma function_of_events_not {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α) (F:event P) (h_F:function_of_events E S F):function_of_events E S (¬ₑ F) := begin
  have h1:(¬ₑ F) = Fᶜ,
  { apply event.eq, simp },
  rw h1,
  apply function_of_events_compl,
  apply h_F,
end

lemma function_of_events_empty {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α):function_of_events E S ∅ := begin
  have h1:(¬ₑ event_univ) = (∅:event P),
  { apply event.eq, simp },
  rw ← h1,
  apply function_of_events_compl,
  apply function_of_events_univ,
end

lemma function_of_events_forall {α β Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (S:finset α) (T:finset β) (F:β → event P) (h_F:∀ b∈ T, function_of_events E S (F b))
  :function_of_events E S (∀ᵣ b in T, F b) := begin
  classical,
  revert h_F,
  apply finset.induction_on T,
  { intros, simp },
  { intros b T' h_b_notin_T' h2 h3, rw has_eall_in_insert,
    apply function_of_events_and, { apply h3, simp },
    { apply h2, intros b h_b, 
      apply h3, simp [h_b] } },
end


lemma function_of_events_ind {α Ω:Type*} {P:probability_space Ω} [decidable_eq α] (E:α → event P)
  (h_ind:independent_events E) (S T:finset α) (F G:event P) (h_disj: disjoint S T) 
  (h_F:function_of_events E S F) (h_G:function_of_events E T G):
  independent_event_pair F G :=
begin
  classical,
  have h_disj_diff:∀ (s t:finset α), disjoint (s \ t) t,
  { intros s t, rw finset.disjoint_left,
    intros a h_a, simp at h_a, apply h_a.right },
  
  have h_disj_subset:∀ (s t:finset α), (s ⊆ S) → (t ⊆ T) → (disjoint s t),
  { intros s t h_s h_t,
    rw finset.disjoint_left,
    rw finset.disjoint_left at h_disj,
    intros a h_a h_a',
    apply h_disj,
    apply h_s h_a,
    apply h_t h_a' },
  cases h_G with T_G h_G,
  have h_subset_T:∀ t ∈ T_G, t ⊆ T,
  { intros t h_t, 
    apply finset.mem_powerset.1 (h_G.left h_t) },
  cases h_F with T_F h_F,
  have h_subset_S:∀ s ∈ T_F, s ⊆ S,
  { intros s h_s, 
    apply finset.mem_powerset.1 (h_F.left h_s) },
  rw ← h_G.right,
  apply independent_event_pair_exists,
  intros s h_s,
  rw ← h_F.right,
  apply independent_event_pair.symm,
  apply independent_event_pair_exists,
  intros t h_t,
  apply independent_event_pair.symm,
  rw eand_comm,
  rw eand_comm (∀ᵣ (a : α) in s,E a),
  unfold independent_event_pair,
  have h1:∀ (H1 H2 H3 H4:event P), ((H1 ∧ H2) ∧ (H3 ∧ H4)) = ((H1 ∧ H3) ∧ (H2 ∧ H4)),
  { intros H1 H2 H3 H4, 
    apply event.eq, ext1 ω, split; intros h1_1; simp at h1_1; simp [h1_1] },
  rw h1,
  rw forall_and,
  rw forall_and,
  rw independent_events_rel,
  rw independent_events_rel,
  rw independent_events_rel,
  rw finset.prod_union,
  rw finset.prod_union,
  have h2:∀ (a b c d:nnreal), a * b * (c * d) = a * c * (b * d),
  { intros a b c d, rw ← nnreal.coe_eq, repeat { rw nnreal.coe_mul },
    linarith },
  rw h2,
  { apply h_disj_subset,
    apply h_subset_S _ h_t,
    apply h_subset_T _ h_s },
  { apply h_disj_subset,
    simp,
    simp },
  apply h_ind,
  { rw finset.disjoint_left,
    intros a h_a, simp at h_a, apply h_a.right },
  apply h_ind,
  { rw finset.disjoint_left,
    intros a h_a, simp at h_a, apply h_a.right },
  apply h_ind,
  { rw finset.disjoint_left,
    intros a h_a h_a',  simp at h_a', simp [h_a'] at h_a,
    cases h_a with h_a h_a; cases h_a' with h_a' h_a',
    { apply h_a.right h_a' },
    { rw finset.disjoint_left at h_disj,
     apply h_disj h_a.left,
     apply h_subset_T s h_s h_a' },
    { rw finset.disjoint_right at h_disj,
      apply h_disj h_a.left,
      apply h_subset_S t h_t h_a' },
    { apply h_a.right h_a' } },
  { apply disjoint_union_sub, apply h_F.left },
  { apply disjoint_union_sub, apply h_G.left },
end




