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

/-!
  This file focuses on more esoteric proofs that random variables are identical
  and independent. These are based upon the monotone class theorem.

  Semi-algebras are the basic object. A sigma algebra or algebra is a semi-algebra.
  For example, the set of (closed, open, half-open) intervals on the real line form a 
  semi-algebra. The simplest sets in a product of a measurable space form a semi-algebra.
  
  If you close a semi-algebra under finite disjoint union, it becomes an algebra.

  An algebra is defined as containing the universal set and being closed under set 
  difference. However, it is also closed under finite union, intersection, complement,
  and it contains the empty set.

  The monotone class of a set is the closure under monotone intersection and monotone
  union. The monotone class of an algebra is a sigma algebra (the monotone class theorem).

  This file contains the definition of a monotone class, a semi-algebra, and an algebra.
  (set.monotone_class, set.is_semialgebra, and set.is_algebra). It also contains
  the definition of closure under finite disjoint union.


  This is most useful for proving independent and identical random variables, when
  considered as an aggregate random variable, are identical.

  The core is the monotone class theorem, measurable_space.generate_from_monotone_class.
-/


/-- A monotone class: an extension of a set of sets to be closed under
   monotone intersection and union.
   When a monotone class extends an algebra (not a sigma algebra, just a regular algebra),
   it is equivalent to the
   measurable space generated from the algebra.

   First, we introduce the properties of algebras. Then, we show that the
   result of a monotone class of an algebra is an algebra. Finally, we
   show the monotone class of an algebra is a sigma algebra (i.e., a
   measurable space).
   See measurable_space.generate_from_monotone_class
 -/
inductive set.monotone_class {α:Type*} (s : set (set α)) : set α → Prop
| basic : ∀ u, u∈ s → set.monotone_class u 
| inter : ∀ f : ℕ → set α, (∀ n, set.monotone_class (f n)) → 
                           (∀ (i:ℕ), f i.succ ⊆ f i) →  
                           set.monotone_class (set.Inter f)
| union : ∀ f : ℕ → set α, (∀ n, set.monotone_class (f n)) →
                           monotone f →
                            set.monotone_class (set.Union f)

--namespace measure_theory

structure set.is_algebra {α:Type*} (s:set (set α)) :=
  (univ : set.univ ∈ s)
  (diff : ∀ a b, a ∈ s →  b ∈ s → (a \ b) ∈ s)


lemma set.is_algebra.compl {α:Type*} {s:set (set α)} (A:s.is_algebra):
  (∀ a, a∈ s → aᶜ ∈ s) := begin
  intros a h_a,
  have h3:aᶜ = set.univ \ a,
  { ext ω, split; intros h3_1; simp at h3_1; simp [h3_1] },
  rw h3,
  apply A.diff,
  apply A.univ,
  apply h_a
end 

lemma set.is_algebra.empty {α:Type*} {s:set (set α)} (A:s.is_algebra):
  (∅ ∈ s) := begin
  rw ← set.compl_univ,
  apply A.compl,
  apply A.univ,
end



lemma set.is_algebra.inter {α:Type*} {s:set (set α)} (A:s.is_algebra):
  (∀ a b, a∈ s → b∈ s→ a∩ b ∈ s) := begin
  intros a b h_a h_b,
  have h3:a ∩ b = a \ bᶜ,
  { ext ω, split; intros h3_1; simp at h3_1; simp [h3_1] },
  rw h3,
  apply A.diff,
  apply h_a,
  apply A.compl,
  apply h_b,
end


lemma set.is_algebra.union {α:Type*} {s : set (set α)} (A:s.is_algebra):
  (∀ a b, a∈ s → b ∈ s → a ∪ b ∈ s) := begin
  intros a b h_a h_b,
  have h3:a ∪ b = (aᶜ ∩ bᶜ)ᶜ,
  { rw set.union_eq_compl_compl_inter_compl },
  rw h3,
  apply A.compl,
  apply A.inter,
  apply A.compl,
  apply h_a,
  apply A.compl,
  apply h_b,
end


lemma set.Union_succ {α:Type*} (j_n:ℕ) (f:ℕ → set α):
  (⋃ (i : ℕ) (h : i ≤ j_n.succ), f i) = (f j_n.succ) ∪ (⋃ (i : ℕ) (h : i ≤ j_n), f i) := 
begin
  ext a, split; intros h1; simp at h1; simp [h1],
  cases h1 with i h1,
  cases decidable.em (i = j_n.succ) with h2 h2,
  { subst i, simp [h1] },
  { right, apply exists.intro i,
    split,
    apply nat.le_of_lt_succ,
    rw lt_iff_le_and_ne, split,
    apply h1.left,
    apply h2, apply h1.right },
  cases h1 with h1 h1,
  { apply exists.intro j_n.succ, 
    split, apply le_refl _,
    apply h1 },
  { cases h1 with i h1,
    apply exists.intro i,
    split,
    apply le_trans h1.left (le_of_lt (nat.lt_succ_self j_n)),
    apply h1.right },
end

lemma set.is_algebra.finite_union {α:Type*} {s : set (set α)} (A:s.is_algebra):
  (∀ (f:ℕ → (set α)), (∀ i, f i ∈ s) → (∀ j, (⋃ (i:ℕ) (h:i ≤ j), f i) ∈ s)) := begin
  intros f h3 j,
  induction j,
  { have h4:(⋃ (i : ℕ) (h : i ≤ 0), f i) = f 0,
   { ext a; split; intros h4_1, simp at h4_1, apply h4_1,
     simp, apply h4_1 }, rw h4, apply h3 },
  { rw set.Union_succ,
    apply A.union,
    apply h3,
    apply j_ih },
end



lemma set.monotone_class.compl {α:Type*} {s : set (set α)} : 
  (∀ a ∈ s, aᶜ ∈ s) →
  (∀ (a:set α), s.monotone_class a → s.monotone_class aᶜ) := begin
  intros h1 a h2,
  induction h2 with a' h_a' f h_rec h_mono h_ind f h_rec h_mono h_ind,
  { apply set.monotone_class.basic,
    apply h1, apply h_a' },
  { rw set.compl_Inter,
    apply set.monotone_class.union,
    { intros n, apply h_ind },
    { apply @monotone_of_monotone_nat (set α) _ (λ (i : ℕ), (f i)ᶜ),
      intros n, simp, rw set.compl_subset_compl, apply h_mono } },
  { rw set.compl_Union,
    apply set.monotone_class.inter,
    { intros n, apply h_ind },
    { intros n, rw set.compl_subset_compl, apply h_mono, apply nat.le_of_lt,
      apply nat.lt_succ_self } },
end

lemma set.diff_Inter_eq_Union_diff {α:Type*} (a':set α) (f_b:ℕ → set α):
  a' \ (set.Inter f_b) = set.Union (λ i, a' \ (f_b i)) :=
begin
  ext ω, split; intros h5_1; simp at h5_1; simp [h5_1],
end

lemma set.Inter_diff_distrib {α:Type*} (a':set α) (f_b:ℕ → set α):
  (set.Inter f_b) \ a' = set.Inter (λ i, (f_b i) \ a') :=
begin
  ext ω, split; intros h5_1; simp at h5_1; simp [h5_1],
  apply (h5_1 0).right,
end

lemma set.diff_Union_eq_Inter_diff {α:Type*} (a':set α) (f_b:ℕ → set α):
  a' \ (set.Union f_b) = set.Inter (λ i, a' \ (f_b i)) :=
begin
  ext ω, split; intros h5_1; simp at h5_1; simp [h5_1],
  apply (h5_1 0).left,
end

lemma set.Union_diff_distrib {α:Type*} (a':set α) (f_b:ℕ → set α):
  (set.Union f_b) \ a' = set.Union (λ i, (f_b i) \ a') :=
begin
  ext ω, split; intros h5_1; simp at h5_1; simp [h5_1],
end

/- Effectively proves the monotone class of an algebra is an algebra. -/
lemma set.monotone_class.diff {α:Type*} {s : set (set α)} : 
  (∀ a b, a∈ s → b ∈ s → a \ b ∈ s) →
  (∀ (a b:set α), s.monotone_class a → s.monotone_class b →
                  s.monotone_class (a \ b)) := begin
  intros h2 a b h3, revert b,
  induction h3 with a' h_a' f_a h_rec_a h_mono_a h_ind_a f_a h_rec_a 
  h_mono_a h_ind_a, 
  intros b h4,
  
  induction h4 with b' h_b' f_b h_rec_b h_mono_b h_ind_b f_b h_rec_b 
  h_mono_b h_ind_b,
  { apply set.monotone_class.basic, apply h2, apply h_a', apply h_b' },
  { have h5:a' \ (set.Inter f_b) = set.Union (λ i, a' \ (f_b i)),
    { rw set.diff_Inter_eq_Union_diff },
    rw h5, apply set.monotone_class.union,
    { apply h_ind_b },
    { apply @monotone_of_monotone_nat (set α) _ (λ (i : ℕ), a' \ f_b i),
      intros n, simp, apply set.diff_subset_diff_right,
      apply h_mono_b } },
  { rw set.diff_Union_eq_Inter_diff,
    apply set.monotone_class.inter,
    { apply h_ind_b },
    { intros n,
      apply set.diff_subset_diff_right,
      apply h_mono_b,
      apply le_of_lt,
      apply nat.lt_succ_self } },
  { intros b h4,
    rw set.Inter_diff_distrib,
    apply set.monotone_class.inter,
    intros n,
    apply h_ind_a,
    apply h4,
    intros i,
    apply set.diff_subset_diff_left,
    apply h_mono_a },
  { intros b h4,
    rw set.Union_diff_distrib,
    apply set.monotone_class.union,
    { intros n, apply h_ind_a, apply h4 },
    intros i j h_le, simp, apply set.diff_subset_diff_left,
    apply h_mono_a, apply h_le },
end

lemma set.monotone_class.univ {α:Type*} {s : set (set α)} : 
  (set.univ ∈ s) →
  (s.monotone_class set.univ) := begin
  intros h1,
  apply set.monotone_class.basic,
  apply h1
end

lemma set.is_algebra.monotone_class {α:Type*} {s : set (set α)} (A:s.is_algebra):
  set.is_algebra s.monotone_class := {
  univ := @set.monotone_class.univ α s (A.univ),
  diff := @set.monotone_class.diff α s (A.diff),
}

lemma set.monotone_class.pair_inter {α:Type*} {s : set (set α)} (A:s.is_algebra): 
  (∀ (a b:set α), s.monotone_class a → s.monotone_class b →
                  s.monotone_class (a ∩ b)) := begin
  have AM := A.monotone_class,
  apply AM.inter,
end

lemma measurable_space.generate_measurable.inter {α:Type*} (s : set (set α)):
 ∀ f : ℕ → set α, (∀ n, measurable_space.generate_measurable s (f n)) → 
  measurable_space.generate_measurable s (⋂ i, f i) :=
begin
  intros f h1,
  rw set.Inter_eq_comp_Union_comp,
  apply measurable_space.generate_measurable.compl,
  apply measurable_space.generate_measurable.union,
  intros n,
  apply measurable_space.generate_measurable.compl,
  apply h1,
end

/- The monotone class theorem (for sets) -/
lemma measurable_space.generate_from_monotone_class {α:Type*} (s : set (set α)) (A:s.is_algebra):
  (s.monotone_class = measurable_space.generate_measurable s) :=
begin
  have h3:∀ a ∈ s, aᶜ ∈ s,
  { apply  A.compl  },
  have h4:∅ ∈ s,
  { apply A.empty },
  have AM := A.monotone_class,
 
  ext a, split; intros h,
  { induction h with a' h_a' h_f h_rec h_mono h_ih,
    { apply measurable_space.generate_measurable.basic, apply h_a' },
    { apply measurable_space.generate_measurable.inter,
      intros n, apply h_ih }, 
    { apply measurable_space.generate_measurable.union,
      intros n, apply h_ih } },
  { induction h with a' h_a' a' h_a' h_ind f h_rec h_ind h_X4 h_X5,
    { apply set.monotone_class.basic, apply h_a' },
    { apply set.monotone_class.basic, apply h4 },
    { apply set.monotone_class.compl h3,
      apply h_ind },
    { let g:ℕ → set α := λ j, ⋃ (i:ℕ) (h:i ≤ j), (f i),
      begin
        have h7:set.Union f = set.Union g,
        { simp [g], ext a, split; intros h7_1;
          simp at h7_1; cases h7_1 with i h7_1;
          simp, existsi [i, i], simp [h7_1], 
          cases h7_1 with j h7_1, existsi [j], simp [h7_1],  },
        rw h7,
        apply set.monotone_class.union,
        intros n,
        simp [g],
        apply AM.finite_union f,
        {apply h_ind },
        apply @monotone_of_monotone_nat (set α) _ g,
        intros n, simp [g],
        rw set.Union_succ,
        apply set.subset_union_right,
      end   },  },
end

def set.disjoint_union_closure {α:Type*} (S:set (set α)):set (set α) :=
  {s|∃ (m:ℕ) (f:fin m → set α), (∀ i, f i ∈ S) ∧ (pairwise (disjoint on f)) ∧ (s=(⋃ i, f i)) }

lemma set.mem_disjoint_union_closure_iff {α:Type*} (S:set (set α)) (s:set α):
  s ∈ S.disjoint_union_closure ↔ 
  (∃ (m:ℕ) (f:fin m → set α), (∀ i, f i ∈ S) ∧ (pairwise (disjoint on f)) ∧ (s=(⋃ i, f i))) := begin
  unfold set.disjoint_union_closure,
  simp,
end

lemma set.disjoint_union_closure_intro {α β:Type*} [fintype β] (S:set (set α)) (f:β → set α):
  (∀ b, f b ∈ S) →
  (pairwise (disjoint on f)) →
  (set.Union f) ∈ S.disjoint_union_closure := begin
  classical,
  intros h1 h2,
  simp [set.disjoint_union_closure],
  have h3:=fintype.exists_equiv_fin β,
  cases h3 with n h3,
  apply exists.intro n,
  let g := classical.choice h3,
  let h:fin n → set α := f ∘ g.inv_fun,
  begin
    apply exists.intro h,
    split,
    { intros i, simp [h,g,h1] },
    split,
    { intros i j h_ne,
      simp [function.on_fun, h],
      have h_ne2:g.symm i ≠ g.symm j,
      { simp, apply h_ne },
      have h_disj := h2 (g.symm i) (g.symm j) h_ne2,
      apply h_disj,
       },
    { ext ω, split; intros h4; simp at h4; cases h4 with i h4; simp [h4],
      { apply exists.intro (g i), simp [h, h4] },
      { apply exists.intro (g.symm i), apply h4  } },
  end 
end

lemma set.disjoint_union_closure_self {α:Type*} (S:set (set α)) (s:set α):
  (s ∈ S) →
  (s∈ S.disjoint_union_closure) := begin
  let f:unit → (set α) := (λ _, s),
  begin
    intros h0,
    have h1:set.Union f = s,
    { simp [f], ext a, split; intros h1_1,
      simp at h1_1, apply h1_1,
      simp, apply h1_1 },
    rw ← h1,
    apply set.disjoint_union_closure_intro,
    intros n, simp [f, h0],
    intros i j h_ne,
    exfalso,
    apply h_ne,
    simp,
  end
end


structure set.is_semialgebra {α:Type*} (s:set (set α)) :=
  (univ : set.univ ∈ s)
  (empty : ∅ ∈ s)
  (inter : ∀ (a b:set α), a ∈ s → b ∈ s → a ∩ b ∈ s) 
  (compl : ∀ (b:set α), b ∈ s → bᶜ ∈ s.disjoint_union_closure)


lemma set.disjoint_union_closure_inter {α:Type*} (S:set (set α)):
  (∀ (s t:set α), s ∈ S → t ∈ S → s ∩ t ∈ S) →
  (∀ (s t:set α), s ∈ S.disjoint_union_closure →
   t ∈ S.disjoint_union_closure → (s∩ t) ∈ S.disjoint_union_closure) := begin
  intros h1 s t h2 h3,
  simp [set.disjoint_union_closure] at h2,
  simp [set.disjoint_union_closure] at h3,
  cases h2 with m_s h2,
  cases h2 with f_s h2,
  cases h3 with m_t h3,
  cases h3 with f_t h3,
  cases h2 with h_in_s h2,
  cases h2 with h_pairwise_s h_def_s,
  subst s,
  cases h3 with h_in_t h3,
  cases h3 with h_pairwise_t h_def_t,
  subst t,
  let f:(fin m_s × fin m_t) → set α := (λ p, f_s p.fst ∩ f_t p.snd),
  begin
    have h4:set.Union f_s ∩ set.Union f_t  = set.Union f,
    { ext ω, split; intros h4_1; simp [f] at h4_1; cases h4_1 with h4_1 h4_2;
      cases h4_1 with i_s h4_1; cases h4_2 with i_t h4_2;
      simp [f]; split,
      { apply exists.intro i_s, apply h4_1 },
      { apply exists.intro i_t, apply h4_2 },
      { apply exists.intro i_s, apply h4_1 },
      { apply exists.intro i_t, apply h4_2 },      
       },
   rw h4,
   apply set.disjoint_union_closure_intro,
   { intros p, simp [f], apply h1, apply h_in_s, apply h_in_t },
   { intros i j h_ne, simp [function.on_fun, f],
     rw disjoint_iff, simp, rw ← set.subset_empty_iff,
     have h_ne_alt:i.fst ≠ j.fst ∨ i.snd ≠ j.snd,
     { cases i, cases j, simp, cases classical.em (i_fst = j_fst) with h1 h1,
       { subst j_fst, right, intros contra, subst j_snd, apply h_ne, simp },
       simp [h1] },
     cases h_ne_alt with h_ne_fst h_ne_snd,
     { apply set.subset.trans, apply set.inter_subset_inter,
       apply set.inter_subset_left,
       apply set.inter_subset_left,
       have h_disj_s := h_pairwise_s i.fst j.fst h_ne_fst,
       simp [function.on_fun] at h_disj_s, rw disjoint_iff at h_disj_s, simp at h_disj_s,
       rw set.subset_empty_iff,
       apply h_disj_s },
     { apply set.subset.trans, apply set.inter_subset_inter,
       apply set.inter_subset_right,
       apply set.inter_subset_right,
       have h_disj_t := h_pairwise_t i.snd j.snd h_ne_snd,
       simp [function.on_fun] at h_disj_t, rw disjoint_iff at h_disj_t, simp at h_disj_t,
       rw set.subset_empty_iff,
       apply h_disj_t },
     }, 
  end
end

lemma set.disjoint_union_closure_univ {α:Type*} (S:set (set α)):
  (∀ s ∈ S, sᶜ ∈ S.disjoint_union_closure) →  
  (∅ ∈ S) →
   (set.univ ∈ S.disjoint_union_closure) := begin
  intros h1 h2,
  rw ← set.compl_empty,
  apply h1,
  apply h2,
end

lemma set.disjoint_union_closure_finite_Inter_finset {α β:Type*} (S:set (set α))
  {f:β → set α} (T:finset β):
  (∀ (s t:set α), s ∈ S → t ∈ S → s ∩ t ∈ S) →
  (∀ s ∈ S, sᶜ ∈ S.disjoint_union_closure) →  
  (∅ ∈ S) →
  (∀ (b:β), (f b) ∈ S.disjoint_union_closure) →
   ((⋂ i ∈ T, f i) ∈ S.disjoint_union_closure) := begin
  classical,
  intros h1 h2 h3 h4,
  have h5 := set.disjoint_union_closure_univ S h2 h3,
  apply finset.induction_on T,
  { simp, apply h5 },
  { intros a s h_a_notin_s h_ind,
    simp, apply set.disjoint_union_closure_inter S h1,
    apply h4, apply h_ind },
end

lemma set.disjoint_union_closure_finite_Inter {α β:Type*} [fintype β] (S:set (set α))
  {f:β → set α}:
  (∀ (s t:set α), s ∈ S → t ∈ S → s ∩ t ∈ S) →
  (∀ s ∈ S, sᶜ ∈ S.disjoint_union_closure) →  
  (∅ ∈ S) →
  (∀ (b:β), (f b) ∈ S.disjoint_union_closure) →
   ((⋂ i, f i) ∈ S.disjoint_union_closure) := begin
  intros h1 h2 h3 h4,
  have h5:(⋂ i, f i) = (⋂ i ∈ finset.univ, f i),
  { ext a, split; intros h5_1; simp at h5_1; simp [h5_1],
    intros i, apply h5_1, apply finset.mem_univ },
  rw h5,
  apply @set.disjoint_union_closure_finite_Inter_finset α β S f finset.univ
    h1 h2 h3 h4,
end

lemma set.disjoint_union_closure_compl {α:Type*}  (S:set (set α)):
  (∀ (s t:set α), s ∈ S → t ∈ S → s ∩ t ∈ S) →
  (∀ s ∈ S, sᶜ ∈ S.disjoint_union_closure) →  
  (∅ ∈ S) →
  (∀ s ∈ S.disjoint_union_closure, sᶜ ∈ S.disjoint_union_closure) := begin
  intros h1 h2 h3 s h4,
  rw set.mem_disjoint_union_closure_iff at h4,
  cases h4 with m h4,
  cases h4 with f h4,
  cases h4 with h4 h5,
  cases h5 with h5 h6,
  subst s,
  rw set.compl_Union,
  apply set.disjoint_union_closure_finite_Inter S h1 h2 h3,
  intros b, apply h2, apply h4,
  apply fin.fintype,
end

lemma set.disjoint_union_closure_diff {α:Type*}  (S:set (set α)):
  (∀ (s t:set α), s ∈ S → t ∈ S → s ∩ t ∈ S) →
  (∀ s ∈ S, sᶜ ∈ S.disjoint_union_closure) →  
  (∅ ∈ S) →
  (∀ s t, s ∈ S.disjoint_union_closure → t ∈ S.disjoint_union_closure → 
   (s \ t) ∈ S.disjoint_union_closure) := begin
  intros h1 h2 h3 s t h_s h_t,
  rw set.diff_eq,
  apply set.disjoint_union_closure_inter S h1,
  apply h_s,
  apply set.disjoint_union_closure_compl S h1 h2 h3,
  apply h_t, 
end

/- A key connection. The closure of a semi-algebra is an algebra. -/
lemma set.is_semialgebra.disjoint_union_closure {α:Type*} {S:set (set α)} (A:S.is_semialgebra):
  S.disjoint_union_closure.is_algebra := {
  univ := set.disjoint_union_closure_univ S (A.compl) (A.empty),
  diff := set.disjoint_union_closure_diff S (A.inter) (A.compl) (A.empty),
}

lemma measurable_space.disjoint_union_encodable {α β:Type*} (S:set (set α)) 
  [E:encodable β] (f:β → (set α)):
  (∀ (b:β), f b ∈ S) →
  (pairwise (disjoint on f)) →
  (∅ ∈ S) → 
  (∃ (g:ℕ → (set α)), (set.Union f = set.Union g) ∧ (pairwise (disjoint on g)) 
   ∧ (∀ i, g i ∈ S)) := begin
  intros h1 h2 h3,
  let g:ℕ → set α := λ (n:ℕ), (option.map f (encodable.decode2 β n)).get_or_else ∅,
  begin
    apply exists.intro g,
    split,
    ext1 ω, split; intros h4; simp [g] at h4; simp [h4, g]; cases h4 with i h4,
    { apply exists.intro (encodable.encode i),
      rw encodable.encodek2,
      simp [h4] },
    destruct (encodable.decode2 β i),
    { intros h5,
      rw h5 at h4,
      simp [option.map, option.get_or_else] at h4,
      exfalso, apply h4 },
    { intros b h6, rw h6 at h4,
      simp [option.map, option.get_or_else] at h4,
      apply exists.intro b,
      apply h4 },
    split,
    { intros i j h_ne,
      simp [function.on_fun, g],
      rw disjoint_iff,
      destruct (encodable.decode2 β i),
      { intros h7, simp [h7, option.map, option.get_or_else] },
      intros i_val h_i,
      simp [h_i, option.map, option.get_or_else],
      destruct (encodable.decode2 β j),
      { intros h8, simp [h8, option.map, option.get_or_else] },
      intros j_val h_j,
      simp [h_j, option.map, option.get_or_else],
      have h9: i_val ≠ j_val,
      { intros contra, apply h_ne,
        have h_partial:=@encodable.decode2_is_partial_inv β E,
        simp [function.is_partial_inv] at h_partial,
        subst j_val,
        rw h_partial at h_i,
        rw h_partial at h_j,
        rw ← h_i,
        rw ← h_j },
      have h10 := h2 i_val j_val h9,
      simp [function.on_fun, disjoint_iff] at h10,
      apply h10 },
    intros i,
    simp [g],
    cases (encodable.decode2 β i),
    repeat {simp [option.map, option.get_or_else, h3, h1]},
  end
end 


lemma measurable_space.closure_union_Union {α:Type*} (S:set (set α)) (f:ℕ → (set α)):
  (∀ i, f i ∈ S.disjoint_union_closure) →
  (pairwise (disjoint on f)) →
  (∅ ∈ S) →  
  (∃ (g:ℕ → (set α)), (set.Union f = set.Union g) ∧ (pairwise (disjoint on g))
    ∧ (∀ i, g i ∈ S)) := begin
  intros h1 h0,
  have h2 := (λ i, (set.mem_disjoint_union_closure_iff S (f i)).1 (h1 i)),
  rw classical.skolem at h2,
  cases h2 with m h2,
  have h3 := classical.axiom_of_choice h2,
  cases h3 with f' h3,
  let f'':(Σ (i:ℕ), fin (m i)) → set α := λ p, f' (p.fst) (p.snd),
  begin
    have h4:set.Union f'' = set.Union f,
    { ext, split; intros h4_1; simp [f''] at h4_1; simp [f'']; cases h4_1 with i h4_1;
      apply exists.intro i; have h4_2 := (h3 i).right.right,
      { cases h4_1 with b h4_1,
        rw h4_2, simp, apply exists.intro b,
        apply h4_1 },
      { rw h4_2 at h4_1,
        simp at h4_1,
        cases h4_1 with b h4_2,
        apply exists.intro b,
        apply h4_2 },
        },
    rw ← h4,
    have h6:∀ i, ∀ (j:fin (m i)), f'' (sigma.mk i j) ⊆ f i,
    { intros i j, simp [f''], rw (h3 i).right.right,  simp,
      have h6_1:f' (sigma.mk i j).fst j = f' i j := rfl,
      rw h6_1, apply set.subset_Union },
    apply measurable_space.disjoint_union_encodable,
    { intros b, have h5 := (h3 b.fst).left b.snd, 
      apply h5 },
    intros i j h_ne,
    cases i, cases j,
    simp at h_ne,
    simp [function.on_fun],
    rw disjoint_iff,
    simp [f''],
    cases classical.em (i_fst = j_fst) with h5 h5,
    { have h_ne_snd := h_ne h5,
      subst j_fst,
      have h_ne_snd2:i_snd ≠ j_snd,
      { intros contra, apply h_ne_snd, rw contra },
      have h_disj := (h3 i_fst).right.left i_snd j_snd h_ne_snd2, 
      simp [function.on_fun] at h_disj, rw disjoint_iff at h_disj,  simp at h_disj,
      apply h_disj },
    { rw ← set.subset_empty_iff,
      apply set.subset.trans,
      apply set.inter_subset_inter,
      apply h6, apply h6,
      have h7 := h0 i_fst j_fst h5,
      simp [function.on_fun] at h7,
      rw disjoint_iff at h7, simp at h7, simp [h7] },
  end
end

lemma set.disjoint_union_closure_Inter {α:Type*} (S:set (set α)) 
  (f:ℕ → (set α)) (j:ℕ):
  (∀ s t∈ S, s ∩ t ∈ S) →
  (∀ s ∈ S, sᶜ ∈ S.disjoint_union_closure) →  
  (∅ ∈ S) →
  (∀ i, f i ∈ S.disjoint_union_closure) →
  ((⋂ (i_1 : ℕ) (H : i_1 < j), f i_1) ∈ S.disjoint_union_closure) := begin
  intros h1 h2 h3 h4,
  induction j,
  { simp, rw ← set.compl_empty, apply h2, apply h3 },
  { have h5:(⋂ (i_1 : ℕ) (H : i_1 < j_n.succ), f i_1) = 
    (f j_n) ∩ (⋂ (i_1 : ℕ) (H : i_1 < j_n), f i_1),
    { ext a, split; intros h5_1; simp at h5_1; simp,
      split,
      apply h5_1,
      apply nat.lt_succ_self,
      intros i h5_2, 
      apply h5_1,
      apply lt_trans h5_2,
      apply nat.lt_succ_self,
      intros i h5_2,
      cases classical.em (i = j_n) with h5_3 h5_3,
      subst i,
      apply h5_1.left,
      apply h5_1.right,
      rw lt_iff_le_and_ne,
      split,
      rw ← nat.lt_succ_iff,
      apply h5_2,
      apply h5_3 },
    rw h5,
    apply set.disjoint_union_closure_inter,
    apply h1,
    apply h4,
    apply j_ih },
end

lemma measurable_space.union_to_disjoint {α:Type*} (S:set (set α)) (f:ℕ → (set α)):
  (∀ s t∈ S, s ∩ t ∈ S) →
  (∀ s ∈ S, sᶜ ∈ S.disjoint_union_closure) →  
  (∅ ∈ S) →
  (∀ i, f i ∈ S) →
  (∃ (g:ℕ → (set α)), (set.Union f = set.Union g) ∧ (pairwise (disjoint on g))
    ∧ (∀ i, g i ∈ S)) := begin
  intros h1 h2 h3 h4,
  have h5:∃ f':ℕ → set α, (set.Union f = set.Union f') ∧ (∀ i, f' i ∈ S.disjoint_union_closure) ∧
  (pairwise (disjoint on f')),
  { apply exists.intro (set.disjointed f),
    split,
    rw set.Union_disjointed,
    rw and.comm,
    split,
    apply set.disjoint_disjointed,
    intros i,
    simp [set.disjointed],
    apply set.disjoint_union_closure_inter,
    apply h1,
    apply set.disjoint_union_closure_self,
    apply h4, 
    apply set.disjoint_union_closure_Inter,
    apply h1, apply h2, 
    apply h3,
    intros i,
    apply h2,
    apply h4 },
  cases h5 with f' h5,
  rw h5.left,
  apply measurable_space.closure_union_Union S f' h5.right.left h5.right.right,
  apply h3,
end

