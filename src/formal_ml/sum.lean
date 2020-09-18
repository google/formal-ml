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
import order.filter.basic
import topology.bases
import data.real.nnreal
import topology.instances.real
import topology.instances.nnreal
import topology.instances.ennreal

import topology.algebra.infinite_sum
import formal_ml.set
import formal_ml.finset
import formal_ml.nat
import formal_ml.ennreal
import formal_ml.nnreal
import data.finset
import order.complete_lattice
import formal_ml.filter_util
import formal_ml.real

/-
  A high-level point:
  On closer inspection of infinite-sum.lean, several of these theorems are covered.
-/
open finset
-- See cfilter
/-
  There are some useful functions already in the library:
  finset.sum_subset
-/



lemma le_add_of_nonneg {β:Type*} [ordered_add_comm_monoid β] (a b:β):
  0 ≤ b → a ≤ a + b :=
begin
  intros A1,
  have B1:a + 0 ≤ a + b,
  {
    apply @add_le_add,
    apply le_refl a,
    apply A1,
  },
  rw add_zero at B1,
  apply B1,
end


lemma le_add_nonnegative {β:Type*} [canonically_ordered_add_monoid β] (a b:β):
  a ≤ a + b :=
begin
  apply le_add_of_nonneg,
  apply zero_le,
end


--The core of this is finset.sum_const. However, there are not many lemmas that I found
--around add_monoid.smul.
lemma finset_sum_const {α:Type*} {S:finset α} {f:α → ennreal} {c:ennreal}:(∀ k, f k =c) →
  S.sum f = S.card * c :=
begin
  intros A1,
  have A2:f = λ k, c,
  {
    ext,
    rw A1,
  },
  rw A2,
  rw (@finset.sum_const α ennreal S _ c),
  rw ennreal_add_monoid_smul_def,
end


--This is a combination of finset.sum_congr and finset.sum_const_zero.
lemma finite_sum_zero_eq_zero {α β:Type*} [add_comm_monoid α] [decidable_eq β] (f:β → α) (S:finset β):
  (∀ s∈ S, f s = 0) →
  S.sum f = 0 :=
begin
  intro A1,
  let g:β → α := λ a:β, (0:α),
  begin
    have B1:S = S := rfl,
    have B2:(∀ x∈ S, f x = g x),
    {
      intros x B2A,
      rw A1 x B2A, 
    },
    
    rw finset.sum_congr B1 B2,
    apply finset.sum_const_zero,
  end
end


lemma finset_sum_le2 {α β:Type*} [decidable_eq α]
    [ordered_add_comm_monoid β] {S:finset α} {f g:α → β}:
  (∀ s∈ S, f s ≤ g s) →  S.sum f ≤ S.sum g :=
begin
  apply finset.induction_on S,
  {
    intros A1,
    simp,
  },
  {
    intros a S2 A1 A2 A3,
    rw finset.sum_insert,
    rw finset.sum_insert,
    apply add_le_add,
    apply A3,
    simp,
    apply A2,
    {
      intros a2 A4,
      apply A3,
      simp,
      right,
      exact A4,
    },
    exact A1,
    exact A1,
  }
end


--Drop, and use finset_sum_le2
lemma finset_sum_le {α:Type*} [decidable_eq α] {S:finset α} {f g:α → nnreal}:
  (∀ s∈ S, f s ≤ g s) →  S.sum f ≤ S.sum g :=
begin
  apply finset_sum_le2,
end


lemma finset_sum_le3 {α β:Type*}  [decidable_eq α] [ordered_add_comm_monoid β] {f g:α → β} {S:finset α}:
  f ≤ g →
  S.sum f ≤ S.sum g :=
begin
  intro A1,
  apply finset_sum_le2,
  intros n A2,
  apply A1,
end


lemma finset.sum_nonnegative_of_nonnegative {α β:Type*} [decidable_eq α] [ordered_add_comm_monoid β] {S:finset α}
  {f:α → β}:(0 ≤ f) → 0 ≤ S.sum f :=
begin
  intros A1,
  have A2:S.sum (0:α → β) = (0:β),
  {
    apply finite_sum_zero_eq_zero,
    intros a A2A,
    refl,
  },
  rw ← A2,
  apply finset_sum_le3,
  apply A1,
end

lemma finset.sum_monotone_of_nonnegative {α β:Type*} [decidable_eq α] [ordered_add_comm_monoid β] {S T:finset α}
  {f:α → β}:0 ≤ f → S ⊆ T → S.sum f ≤ T.sum f  :=
begin
  intros A1 A2,
  rw ← finset.sum_sdiff A2,
  rw add_comm,
  apply le_add_of_nonneg,
  apply finset.sum_nonnegative_of_nonnegative,
  apply A1,
end



lemma finset.sum_monotone {α β:Type*} [decidable_eq α] [canonically_ordered_add_monoid β] {S T:finset α}
  {f:α → β}:S ⊆ T → S.sum f ≤ T.sum f  :=
begin
  intros A2,
  rw ← finset.sum_sdiff A2,
  rw add_comm,
  apply le_add_nonnegative,
end


lemma finset.element_le_sum {α β:Type*} [D:decidable_eq α] [canonically_ordered_add_monoid β] {S:finset α} {a:α}
  {f:α → β}:(a ∈ S) → f a ≤ S.sum f  :=
begin
  intros A2,
  rw ← @finset.sum_singleton α β a f,
  apply finset.sum_monotone,
  simp,
  apply A2,
end


lemma finset.sum_monotone' {α β:Type*} [D:decidable_eq α] [canonically_ordered_add_monoid β] 
  {f:α → β}:monotone (λ S:finset α, S.sum f) :=
begin
  intros S T B1,
  apply finset.sum_monotone B1,
end

lemma ennreal.sum_monotone {α:Type*} [decidable_eq α] {S T:finset α}
  {f:α → ennreal}:S ⊆ T → S.sum f ≤ T.sum f  :=
begin
  intro A1,
  apply finset.sum_monotone A1,
end


--This should be removed, and finset.sum_nonnegative_of_nonnegative should be used directly.
lemma nn_sum_nonneg {α:Type*} [decidable_eq α] (f:α → real) (S:finset α):
  (∀ n, f n ≥ 0) → (0≤ (S.sum f) ) :=
begin
  intro A1,
  apply finset.sum_nonnegative_of_nonnegative,
  rw le_func_def2,
  intros n,
  apply A1,
end


--This should be removed, and finset.sum_monotone_of_nonnegative should be used directly.
lemma nn_sum_monotonic {α:Type*} [decidable_eq α] (f:α → real) (S T:finset α):
  (∀ n, f n ≥ 0) → (S⊆ T)→ ((S.sum f) ≤ (T.sum f)) :=
begin
  intro A1,
  apply finset.sum_monotone_of_nonnegative,
  rw le_func_def2,
  intros n,
  apply A1,
end


lemma sum_monotonic_of_nnreal {α:Type*} [D:decidable_eq α] (f:α → nnreal) (S T:finset α):
  (S⊆ T)→ ((S.sum f) ≤ (T.sum f)) :=
begin
  apply finset.sum_monotone,
end


lemma sum_monotone_of_nonneg {α:Type*} [D:decidable_eq α] {f:α → ℝ}:
  0 ≤ f → monotone (λ s:finset α, s.sum f) :=
begin
  intros A1 a b A2,
  simp,
  apply @nn_sum_monotonic α D f a b,
  apply A1,
  apply A2,
end

lemma sum_monotone_of_nnreal {α:Type*} [D:decidable_eq α] {f:α → nnreal}:
  monotone (λ s:finset α, s.sum f) :=
begin
  apply finset.sum_monotone',
end

/-
  This concept of sum is similar to absolutely convergent,
  as opposed to convergent. To eliminate the difference, we
  just insist the function is positive.

  TODO: revisit in the context of later theories.
-/
lemma has_classical_limit_real (f:ℕ → real) (v:real):
  (∀ n, f n ≥ 0) →
  (∀ e>0, ∃ m,∀ m', m < m' →
  ((v - e <(finset.sum (finset.range m') f)) ∧
    (finset.sum (finset.range m') f) < v  + e)
   ) →
  has_sum f v
  :=
begin
  intros,
  unfold has_sum,
  apply filter_tendsto_intro,
  intros,
  unfold set.preimage,
  -- lemma mem_nhds_elim_real_bound (b:set real) (x:real): b∈ nhds x →
  -- (∃ r>0, (set.Ioo (x-r) (x+r)) ⊆ b)
  have A1:(∃ r>0, (set.Ioo (v-r) (v+r)) ⊆ b),
  {
    apply mem_nhds_elim_real_bound,
    exact H,
  },
  cases A1,
  cases A1_h,
  apply filter_contains_preimage_superset,
  {
    apply A1_h_h,
  },
  have A2:(∃ (m : ℕ), ∀ (m' : ℕ), m < m' →

        v - A1_w < finset.sum (range m') f ∧
        finset.sum (range m') f < v + A1_w
        ),
  {
    apply a_1,
    apply A1_h_w,
  },
  cases A2,

  apply filter_at_top_intro3,
  show finset ℕ,
  {
    exact finset.range (nat.succ A2_w),
  },
  {
    intros,
    unfold set.Ioo,
    simp,
    split,
    {
      have D1:(range (nat.succ A2_w)).sum  f ≤ d.sum f,
      {
         apply nn_sum_monotonic,
         apply a,
         apply H_1,
      },
      have D2:v - A1_w < finset.sum (range (nat.succ A2_w)) f  ∧
             finset.sum (range (nat.succ A2_w)) f < v + A1_w,
      {
         apply A2_h,
          apply nat.lt_succ_self,
      },
      cases D2,
      apply lt_of_lt_of_le,
      {
        apply D2_left,
      },
      {
        apply D1,
      },
    },
    {
      have B1:∃ n, (d⊆ finset.range n),
      {
        apply finset_range_bound,
      },
      cases B1,
      cases (nat.decidable_le B1_w A2_w),
      {
        have B2:A2_w<B1_w,
        {
          have B3:A2_w<B1_w ∨ A2_w ≥ B1_w,
          {
            apply nat.lt_or_ge,
          },
          cases B3,
          {
            apply B3,
          },
          {
            exfalso,
            apply h,
            apply B3,
          }
        },
        have B4:d.sum f ≤ (range B1_w).sum  f,
        {
          apply nn_sum_monotonic,
          {
            apply a,
          },
          {
            apply B1_h,
          }
        },
        --rw ← finite_sum_real_finset at B4,
        have B5:v - A1_w < (finset.sum (range B1_w) f) ∧ finset.sum (range B1_w) f < v + A1_w,
        {
          apply A2_h,
          apply B2,
        },
        cases B5,
        apply lt_of_le_of_lt,
        {
          apply B4,
        },
        {
          apply B5_right,
        }
      },
      {
        have C1:range B1_w ⊆ range (nat.succ A2_w),
        {
          apply finset_range_monotonic,
          apply le_trans,
          apply h,
          apply nat.le_of_lt,
          apply nat.lt_succ_self,
        },
        have C2:v - A1_w < finset.sum (range (nat.succ A2_w)) f ∧
               finset.sum (range (nat.succ A2_w)) f < v + A1_w,
        {
          apply A2_h,
          apply nat.lt_succ_self,
        },
        cases C2,
        have C3:d⊆ range (nat.succ A2_w),
        {
          apply finset.subset.trans,
          apply B1_h,
          apply C1,
        },
        have C4:d.sum f ≤  (range (nat.succ A2_w)).sum f,
        {
          apply nn_sum_monotonic,
          apply a,
          apply C3,
        },
        apply lt_of_le_of_lt,
        {
          apply C4,
        },
        {
          apply C2_right,
        }
      }
    }
  }

end


lemma finite_sum_real_eq_finite_sum2 (f:ℕ → nnreal) (n:ℕ):
  (finset.sum (range n)  (λ (a : ℕ), ((f a):real))) = 
  ((@finset.sum ℕ nnreal _ (range n) f):real) :=
begin
  rw nnreal.coe_sum,
end


lemma has_classical_limit_nnreal (f:ℕ → nnreal) (v:nnreal):
  (∀ e>0, ∃ m,∀ m', m < m' →  v < (finset.sum (range m') f) + e)  →
  (∀ m', (finset.sum (range m') f) ≤ v) →
  has_sum f v
  :=
begin
  intros,

  apply (@nnreal.has_sum_coe _ f v).mp,
  apply has_classical_limit_real,
  {
    intros,
    simp,
  },
  {
    intros,
    have A1:0 < e,
    {
      apply H,
    },
    have A2:max e 0 = e,
    {
      apply max_eq_left,
      apply le_of_lt,
      apply A1,
    },
    rw ← A2 at A1,
    have A2B:(nnreal.of_real e) > 0,
    {
      unfold nnreal.of_real,
      apply A1,
    },
    have A3:(∃ (m : ℕ), ∀ (m' : ℕ), m < m' → v < (finset.sum (range m') f) + (nnreal.of_real e)),
    {
      apply a,
      apply A2B,
    },
    cases A3,
    apply exists.intro A3_w,
    intros,
    have A4:v < finset.sum (range m') f  + nnreal.of_real e,
    {
      apply A3_h,
      apply a_2,
    },
    split,
    {
      rw finite_sum_real_eq_finite_sum2,
      apply (@sub_lt_iff_lt_add real _ (↑v) ↑(finset.sum (range m') (λ (a : ℕ), f a)) e).mpr,
      simp,
      rw real.decidable_linear_ordered_comm_ring.add_comm,
      have A5: (v:ℝ) < (((@finset.sum ℕ nnreal _ (range m') f) + nnreal.of_real e):ℝ),
      {
        apply A4,
      },
      have A6:((nnreal.of_real e):ℝ) = e,
      {
        unfold nnreal.of_real,
        simp,
        exact A2,
      },
      rw A6 at A5,
      rw add_comm,
      apply A5,
    },
    {
      rw finite_sum_real_eq_finite_sum2,
      have A7:finset.sum (range m') f ≤ v,
      {
        apply a_1,
      },
      simp,
      have A8:((@finset.sum ℕ nnreal _ (range m') f):ℝ) ≤ (v:ℝ),
      {
        apply A7,
      },
      apply lt_of_le_of_lt,
      {
        apply A8,
      },
      rw add_comm,
      apply (@sub_lt_iff_lt_add real _ (↑v) e (↑v)).mp,
      simp,
      apply H,
    }
  }
end


--Not quite the classical way of thinking about a limit, but
--more practical for nonnegative sums. 
lemma has_classical_limit_nnreal' (f:ℕ → nnreal) (v:nnreal):
  (∀ e>0, ∃ m,  v < (finset.sum (range m) f) + e)  →
  (∀ m', (finset.sum (range m') f) ≤ v) →
  has_sum f v
  :=
begin
  intros A1 A2,
  apply has_classical_limit_nnreal f v _ A2,
  intros e B1,
  have B2 := A1 e B1,
  cases B2 with m B2,
  apply exists.intro m,
  intro m',
  intro B3,
  have B4:(range m).sum f ≤ (range m').sum f,
  {
    apply sum_monotonic_of_nnreal,
    simp,
    apply le_of_lt B3,
  },
  have B5:(range m).sum f + e ≤ (range m').sum f + e,
  {
    simp,
    apply B4,
  },
  apply lt_of_lt_of_le B2 B5,
end



--Definitely this is in the mathlib libtary under a different name.
lemma disjoint_partition_sum_eq {α β:Type*} [decidable_eq α] [add_comm_monoid β]
  (f:α  → β) (S T:finset α):
  (T ≥ S) →
   S.sum f +  (T\S).sum f = T.sum f :=
begin
  intros,
  have A1:disjoint S (T\ S),
  {
    apply (@disjoint.symm (finset α) _ (T \ S) S),
    apply finset.sdiff_disjoint,
  },
  have A2:S.sum f +  (T\S).sum f = (S ∪ T \ S).sum  f,
  {
    apply (sum_disjoint_add f S (T \ S)),
    apply A1,
  },
  rw finset.union_sdiff_of_subset at A2,
  {
    exact A2,
  },
  {
    apply a,
  }
end



--This is a special case of finset.sum_subset



--TODO: remove, and use summable.has_sum.
lemma has_sum_tsum {α β: Type*} [add_comm_monoid α] [topological_space α]
  {f:β → α}:summable f → has_sum f (tsum f) :=
begin
  intro A1,
  apply summable.has_sum A1,
end



--TODO: remove, and use has_sum_sum_of_ne_finset_zero.
--This is certainly a lemma in infinite_sum.
lemma has_finite_sum (α β:Type*) [topological_space α] [add_comm_monoid α] [decidable_eq β] (f:β → α) (S:finset β):
  (∀ s∉ S, f s = 0) → (has_sum f (S.sum f)) :=
begin
  intros,
  apply has_sum_sum_of_ne_finset_zero,
  apply a,
end


lemma finite_sum_eq3 (α β:Type*) [topological_space α] [t2_space α] [add_comm_monoid α]
  [decidable_eq β] (f:β → α) (S:finset β):
  (∀ s∉ S, f s = 0) → (tsum f) =  (S.sum f) :=
begin
  intros,
  have A1:has_sum f (S.sum f),
  {
    apply has_finite_sum,
    apply a,
  },
  have A2:summable f,
  {
    apply has_sum.summable,
    apply A1,
  },
  apply has_sum.tsum_eq,
  apply A1,
end


--TODO: replace with finset.sum_congr
lemma finset_sum_subst2 {α β:Type*} [decidable_eq α] [add_comm_monoid β] {S:finset α} {f g:α → β}:
  (∀ s∈ S, f s = g s) →  S.sum f = S.sum g :=
begin
  intros A1,
  apply finset.sum_congr,
  refl,
  apply A1,
end



lemma finset_sum_subst {α:Type*} [decidable_eq α] {S:finset α} {f g:α → nnreal}:
  (∀ s∈ S, f s = g s) →  S.sum f = S.sum g :=
begin
  apply finset_sum_subst2,
end



/-
add_monoid.smul (card S) k = ↑(card S) * k
-/
lemma finset_sum_le_const {α:Type*} [D:decidable_eq α] {S:finset α} {f:α → nnreal} {k:nnreal}:
  (∀ s∈ S, f s ≤ k) →  S.sum f ≤ S.card  * k :=
begin
  have A1:S.sum (λ s, k) = S.card * k,
  {
    rw finset.sum_const,
    apply nnreal_add_monoid_smul_def,
  },
  intro A2,
  rw ← A1,
  apply finset_sum_le,
  intros s A4,
  apply A2,
  apply A4,
end

/-
canonically_ordered_comm_semiring.mul_eq_zero_iff :
  ∀ {α : Type u_1} [c : canonically_ordered_comm_semiring α] (a b : α), a * b = 0 ↔ a = 0 ∨ b = 0
-/
lemma finset_sum_eq_zero_iff {α:Type*} [decidable_eq α] {S:finset α} {f:α → nnreal}:
  S.sum f = 0 ↔ ∀ s∈ S, f s = 0 :=
begin
  split,
  {
    apply finset.induction_on S,
    {
      intros A1 s A2,
      exfalso,
      apply A2,
    },
    {
      intros,
      rw finset.sum_insert at a_3,
      rw nnreal_add_eq_zero_iff (f a) (finset.sum s f) at a_3,
      cases a_3 with A3 A4,
      simp at H,
      cases H,
      {
        subst s_1,
        exact A3,
      },
      {
        apply a_2,
        exact A4,
        exact H,
      },
      apply a_1,
    }
  },
  {
    intros A1,
    have A2:∀ s:α, s ∈ S→ f s = (λ k:α, 0) s,
    {
      simp,
      exact A1,
    },
    rw finset_sum_subst A2,
    simp,
  }
end

lemma finset_sum_neg  {α:Type*} {f:α → ℝ} {S:finset α}:
  (S).sum (-f) = -((S).sum f) :=
begin
  apply finset.sum_neg_distrib,
end

lemma finset_sum_mul_const {α:Type*} {f:α → ℝ} {S:finset α} {k:ℝ}:
    S.sum (λ n, k * (f n)) = k * S.sum f :=
begin
  apply finset.sum_hom,
end


----- Working on the relationship between the supremum and the sum of a nonnegative function--------

/-
  A lot of times, it helps to think about a sum over nonnegative values. In particular,
  if 0 ≤ f ≤ g, then if g is summable, then f is summable. For example, this allows us to write:

  0 ≤ pos_only g ≤ abs g
  0 ≤ -neg_only g ≤ abs g

  This seemingly innocuous result is tricky, but there is a simple way to achieve it. In
  particular, we can show that if the image of finset.sum.

  Some of the lemmas below might hold for a conditionally complete linear order.
-/

/-
  A more explicit interpretation of summation over the reals.
 -/
lemma has_sum_real {α:Type*} {f:α → ℝ} [decidable_eq α] {x:ℝ}:
  (∀ ε>0, ∃ S:finset α, ∀ T⊇S, abs (T.sum f - x) < ε) ↔
  (has_sum f x) :=
begin
  split;intro A1,
  {
    unfold has_sum,
    apply filter_tendsto_intro,
    intros b A2,
    have A3:= mem_nhds_elim_real_bound b x A2,
    cases A3 with ε A4,
    cases A4 with A5 A6,
    have A7 := A1 ε A5,
    cases A7 with S A8,
    apply filter_at_top_intro3 S,
    intros T A9,
    have A10 := A8 T A9,
    apply A6,
    rw ← abs_lt_iff_in_Ioo,
    simp,
    apply A10,
  },
  {
    intros ε A2,
    unfold has_sum at A1,
    have A3:set.Ioo (x - ε) (x + ε) ∈ nhds x := Ioo_nbhd A2,
    have A4 := filter_tendsto_elim A1 A3,
    have A5 := mem_filter_at_top_elim A4,
    cases A5 with S A6,
    apply exists.intro S,
    intros T A7,
    rw set.subset_def at A6,
    have A8 := A6 T A7,
    have A9:T.sum f ∈ set.Ioo (x - ε) (x + ε) := A8,
    rw abs_lt_iff_in_Ioo,
    apply A9,
  }
end


lemma real_le_of_forall_lt {x y:ℝ}:(∀ ε > 0, x < y + ε) → x ≤ y :=
begin
  intro A1,
  apply le_of_not_gt,
  intro A2,
  have A3:0 < x-y := sub_pos_of_lt A2,
  have A4:= A1 (x-y) A3,
  simp at A4,
  apply lt_irrefl x A4,
end

lemma has_sum_real_nonnegh {α:Type*} {f:α → ℝ} [decidable_eq α] {x:ℝ}:
  (0 ≤ f) →
  (((∀ ε>0, ∃ S:finset α, x - ε  < S.sum f) ∧ (∀ T:finset α, T.sum f ≤ x)) ↔
  (∀ ε>0, ∃ S:finset α, ∀ T⊇S, abs (T.sum f - x) < ε)) :=
begin
  intro A1,
  split;intros A2,
  {
    cases A2 with A3 A4,
    intros ε A5,
    have A6 := A3 ε A5,
    cases A6 with S A7,
    apply exists.intro S,
    intros T A8,
    rw abs_lt2,
    split,
    {
      apply lt_of_lt_of_le,
      apply A7,
      apply sum_monotone_of_nonneg A1 A8,
    },
    {
      apply lt_of_le_of_lt,
      apply A4,
      simp,
      apply A5,
    }
  },
  {
    split,
    {
      intros ε A5,
      have A6 := A2 ε A5,
      cases A6 with S A7,
      apply exists.intro S,
      have A8:S ⊆ S := finset.subset.refl S,
      have A9:= A7 S A8,
      rw abs_lt2 at A9,
      apply A9.left,
    },
    {
      intro T,
      apply real_le_of_forall_lt,
      intros ε A3,
      have A4 := A2 ε A3,
      cases A4 with S A5,
      have A6:S ⊆ S ∪ T := finset.subset_union_left S T,
      have A7:T ⊆ S ∪ T := finset.subset_union_right S T,
      have A8 := A5 (S ∪ T) A6,
      rw abs_lt2 at A8,
      cases A8 with A9 A10,
      apply lt_of_le_of_lt,
      apply sum_monotone_of_nonneg A1 A7,
      apply A10,
    }
  }
end

lemma has_sum_real_nonneg {α:Type*} {f:α → ℝ} [decidable_eq α] {x:ℝ}:
  (0 ≤ f) →
  (((∀ ε>0, ∃ S:finset α, x - ε  < S.sum f) ∧ (∀ T:finset α, T.sum f ≤ x)) ↔
  (has_sum f x)) :=
begin
  intro A1,
  apply iff.trans,
  rw has_sum_real_nonnegh A1,
  apply has_sum_real,
end


lemma mem_upper_bounds_of_has_sum {α:Type*} {f:α → ℝ} [decidable_eq α] {x:ℝ}:
  0 ≤ f →
  has_sum f x →
  x∈ upper_bounds (set.range (λ s:finset α, s.sum f)) :=
begin
  intros A1 A2,
  rw ← has_sum_real_nonneg at A2,
  cases A2 with A3 A4,
  unfold upper_bounds,
  simp,
  intros a S A5,
  subst a,
  apply A4,
  apply A1
end

lemma lower_not_upper_bound_of_has_sum {α:Type*} {f:α → ℝ} [decidable_eq α] {x y:ℝ}:
  0 ≤ f →
  has_sum f x →
  y < x →
  (∃ z∈ (set.range (λ s:finset α, s.sum f)), y < z) :=
begin
  intros A1 A2 A3,
  rw ← has_sum_real_nonneg A1 at A2,
  cases A2 with A4 A5,
  have A6:0 < x-y := sub_pos_of_lt A3,
  have A7:= A4 (x-y) A6,
  cases A7 with S A8,
  apply exists.intro (S.sum f),
  split,
  {
    simp,
  },
  {
    rw sub_inv at A8,
    apply A8
  }
end




lemma le_upper_bound_intro {s : set ℝ} {b c: ℝ}:
   (∀ (w : ℝ), w < b → (∃ (a : ℝ) (H : a ∈ s), w < a)) →
   (c∈ upper_bounds s) →
   (b ≤ c) :=
begin
  intros A1 A2,
  apply le_of_not_lt,
  intro A3,
  have A4 := A1 c A3,
  cases A4 with z A5,
  cases A5 with A6 A7,
  unfold upper_bounds at A2,
  simp at A2,
  have A8:= A2 A6,
  apply not_le_of_lt A7,
  apply A8,
end



lemma least_upper_bounds_of_has_sum {α:Type*} {f:α → ℝ} [decidable_eq α] {x y:ℝ}:
  0 ≤ f →
  has_sum f x →
  y∈ upper_bounds (set.range (λ s:finset α, s.sum f)) →
  (x ≤ y):=
begin
  intros A1 A2 A3,
  apply @le_upper_bound_intro (set.range (λ s:finset α, s.sum f)),
  {
    intros w A4,
    apply lower_not_upper_bound_of_has_sum;assumption,
  },
  {
    apply A3,
  },
end

lemma set_range_inhabited_domain {α:Type*} {β:Type*} {f:α → β}
  [A1:inhabited α]:(set.range f).nonempty :=
begin
  unfold set.range,
  apply exists.intro (f A1.default),
  simp,
end


lemma set_range_finset_nonempty {α β:Type*} [add_comm_monoid β] {f:α → β}: 
  (set.range (λ (s : finset α), s.sum f)).nonempty :=
begin
  apply set_range_inhabited_domain,
end

lemma bdd_above_def {α:Type*} [preorder α] {s:set α}:
  bdd_above s = (upper_bounds s).nonempty := rfl

lemma bdd_above_of_has_sum {α:Type*} {f:α → ℝ} [decidable_eq α] {x:ℝ}:
  0 ≤ f →
  has_sum f x →
  bdd_above (set.range (λ s:finset α, s.sum f)) :=
begin
  intros A1 A2,
  rw bdd_above_def,
  apply exists.intro x,
  apply mem_upper_bounds_of_has_sum A1 A2,
end


lemma supr_of_has_sum {α:Type*} {f:α → ℝ} [decidable_eq α] {x:ℝ}:
  0 ≤ f →
  has_sum f x →
  x = ⨆ (s : finset α), s.sum f :=
begin
  intros A1 A2,
  unfold supr,
  symmetry,
  apply cSup_intro,
  {
    apply set_range_finset_nonempty,
  },
  {
    intros x2 A3,
    have A4:=mem_upper_bounds_of_has_sum A1 A2,
    unfold upper_bounds at A4,
    simp at A4,
    simp at A3,
    cases A3 with y A5,
    subst x2,
    have A6:y.sum f = y.sum f := rfl,
    have A6 := A4 y A6,
    apply A6,
  },
  {
    intros w A7,
    apply lower_not_upper_bound_of_has_sum;assumption,
  }
end

lemma tsum_eq_supr_of_summable {α:Type*} {f:α → ℝ} [decidable_eq α] {x:ℝ}:
  0 ≤ f →
  summable f →
  tsum f = ⨆ (s : finset α), s.sum f :=
begin
  intros A1 A2,
  have A3:=summable.has_sum A2,
  apply supr_of_has_sum A1 A3,
end

lemma tsum_in_upper_bounds_of_summable {α:Type*} {f:α → ℝ} [decidable_eq α]:
  0 ≤ f →
  summable f →
  (tsum f)∈ upper_bounds (set.range (λ s:finset α, s.sum f)) :=
begin
  intros A1 A2,
  have A3 := summable.has_sum A2,
  apply mem_upper_bounds_of_has_sum A1 A3,
end


lemma has_sum_of_bdd_above {α:Type*} {f:α → ℝ} [decidable_eq α] {x:ℝ}:
  0 ≤ f →
  bdd_above (set.range (λ s:finset α, s.sum f)) →
  (x = ⨆ (s : finset α), s.sum f) →
  has_sum f x  :=
begin
  intros A1 AX A2,
  unfold supr at A2,
  unfold has_sum,
  apply filter_tendsto_intro,
  intros S A3,
  have A4 := mem_nhds_elim_real A3,
  cases A4 with a A5,
  cases A5 with b A6,
  cases A6 with A7 A8,
  cases A8 with A9 A10,
  cases A10 with A11 A12,
  rw A2 at A11,
  have A13:(set.range (λ (s : finset α), s.sum f)).nonempty,
  {
    apply set_range_finset_nonempty,
  },
  have A14:= exists_lt_of_lt_cSup A13 A11,
  cases A14 with d A15,
  cases A15 with A16 A17,
  simp at A16,
  cases A16 with T A18,
  subst d,

  apply filter_at_top_intro3 T,
  intros V A19,
  apply A9,
  simp,
  split,
  {
    apply lt_of_lt_of_le A17,
    apply sum_monotone_of_nonneg A1 A19,
  },
  {
    have A20:V.sum f ≤ x,
    {
      rw A2,
      apply le_cSup,
      apply AX,
      simp,
    },
    apply lt_of_le_of_lt,
    apply A20,
    apply A12,
  }
end

lemma has_sum_of_supr2 {α:Type*} {f:α → ℝ} [decidable_eq α]:
  0 ≤ f →
  bdd_above (set.range (λ s:finset α, s.sum f)) →
  has_sum f (⨆ (s : finset α), s.sum f)  :=
begin
  intros A1 A2,
  apply has_sum_of_bdd_above A1 A2,
  refl,
end

lemma summable_of_bdd_above {α:Type*} {f:α → ℝ} [decidable_eq α]:
  0 ≤ f →
  bdd_above (set.range (λ s:finset α, s.sum f)) →
  summable f  :=
begin
  intros A1 A2,
  unfold summable,
  apply exists.intro (⨆ (s : finset α), s.sum f),
  apply has_sum_of_supr2 A1 A2,
end


lemma bdd_above_of_le_of_bdd_above {α:Type*}  [D:decidable_eq α] {f g:α → ℝ}:
  f ≤ g →
  bdd_above (set.range (λ (s : finset α), s.sum g)) →
  bdd_above (set.range (λ (s : finset α), s.sum f)) :=
begin
  intros A1 A2,
  rw bdd_above_def at A2,
  cases A2 with x A3,
  unfold upper_bounds at A3,
  simp at A3,
  rw bdd_above_def,
  apply exists.intro x,
  unfold upper_bounds,
  simp,
  intros x2 S A4,
  subst x2,
  have A5:S.sum g = S.sum g := rfl,
  have A6 := A3 S A5,
  have A7:S.sum f ≤ S.sum g,
  {
    apply finset_sum_le2,
    intros a A7A,
    apply A1,
  },
  apply le_trans A7 A6,
end

lemma has_sum_of_le_of_le_of_has_sum {α:Type*} {f g:α → ℝ} [D:decidable_eq α]:
  0 ≤ f →
  f ≤ g →
  summable g →
  summable f :=
begin
  intros A1 A2 A3,
  have A4:0 ≤ g,
  {
    apply le_trans A1 A2,
  },
  apply summable_of_bdd_above A1,

  cases A3 with x A5,
  --have A6 := supr_of_has_sum A4 A5,
  have A7 := bdd_above_of_has_sum A4 A5,
  --have A11 := A7,
  apply bdd_above_of_le_of_bdd_above A2 A7,
end



-- is_bdd



lemma le_func_def {α:Type*} {f g:α → ℝ}:(f ≤ g) ↔ (∀ n:α, f n ≤ g n) :=
begin
  refl,
end


lemma le_func_refl {α:Type*} {f:α → ℝ}:f ≤ f :=
begin
  rw le_func_def,
  intro n,
  refl,
end


lemma le_func_trans {α:Type*} {f g h:α → ℝ}:f ≤ g → g ≤ h → f ≤ h :=
begin
  rw le_func_def,
  rw le_func_def,
  rw le_func_def,
  intros A1 A2,
  intro n,
  apply le_trans (A1 n) (A2 n),
end

lemma nonpos_iff_neg_nonneg_func {α:Type*} {f:α → ℝ}:(f ≤ 0) ↔ (0 ≤ -f) :=
begin
  rw le_func_def,
  rw le_func_def,
  split;intros A1 n,
  {
    apply neg_nonneg_of_nonpos,
    apply A1,
  },
  {
    apply nonpos_of_neg_nonneg,
    apply A1,
  }
end

noncomputable def pos_only (x:ℝ):ℝ := if (0 ≤ x) then x else 0

noncomputable def neg_only (x:ℝ):ℝ := if (x ≤ 0) then x else 0


def restrict_real  (P:ℝ → Prop) (D:decidable_pred P) (x:ℝ):ℝ :=
   if (P x) then x else 0


lemma pos_only_add_neg_only_eq {α:Type*} {f:α → ℝ}:(pos_only ∘ f) + (neg_only ∘ f) = f :=
begin
  ext x,
  simp,
  unfold pos_only neg_only,
  have A1:0 <f x ∨ 0 =f x ∨ f x < 0 := lt_trichotomy 0 (f x),
  cases A1,
  {
    rw if_pos,
    rw if_neg,
  
    rw add_zero,
    apply not_le_of_lt A1,
    apply le_of_lt A1,
  },
  cases A1,
  {
    rw if_pos,
    rw if_pos,
    rw ← A1,
    rw zero_add,
    rw ← A1,
    rw ← A1,
  },
  {
    rw if_neg,
    rw if_pos,
    rw zero_add,
    apply le_of_lt A1,
    apply not_le_of_lt A1,
  }
end

lemma pos_only_sub_neg_only_eq_abs {α:Type*} {f:α → ℝ}:(pos_only ∘ f) - (neg_only ∘ f) = abs ∘ f :=
begin
  ext x,
  have A1:((pos_only ∘ f) - (neg_only ∘ f) ) x = ((pos_only (f x)) - (neg_only (f x))) := rfl,
  have A2:((abs ∘ f) x) = (abs (f x)) := rfl,
  rw A1,
  rw A2,
  unfold pos_only neg_only,

  have A3:0 <f x ∨ 0 =f x ∨ f x < 0 := lt_trichotomy 0 (f x),
  cases A3,
  {
    rw if_pos,
    rw if_neg,
    simp,
    rw abs_of_pos,
    apply A3,
    apply not_le_of_lt A3,
    apply le_of_lt A3,
  },
  cases A3,
  {
    rw if_pos,
    rw if_pos,
    rw ← A3,
    rw sub_zero,
    simp,
    rw ← A3,
    rw ← A3,
  },
  {
    rw if_neg,
    rw if_pos,
    simp,
    rw abs_of_neg,
    apply A3,
    apply le_of_lt A3,
    apply not_le_of_lt A3,
  }
end


lemma le_of_add_nonneg_le {α:Type*} {f g h:α → ℝ}:f + g ≤ h → 0 ≤ g → f ≤ h :=
begin
  rw le_func_def,
  rw le_func_def,
  rw le_func_def,
  intros A1 A2 n,
  have A3 := A1 n,
  have A4 := A2 n,
  simp at A3,
  have A5:f n + 0 ≤  f n + g n,
  {
    apply add_le_add_left A4,
  },
  rw add_zero at A5,
  apply le_trans,
  apply A5,
  apply A3,
end

lemma le_of_add_nonneg_eq {α:Type*} {f g h:α → ℝ}:f + g = h → 0 ≤ g → f ≤ h :=
begin
  intros A1 A2,
  have A3:f + g ≤ h,
  {
    rw A1,
    apply le_func_refl,
  },
  apply le_of_add_nonneg_le A3 A2,
end

lemma pos_only_nonneg {α:Type*} {f:α → ℝ}:0≤ (pos_only ∘ f) :=
begin
  rw le_func_def,
  intro n,
  simp,
  unfold pos_only,
  have A1:(0 ≤ f n) ∨ ¬(0 ≤ f n) := le_or_not_le,
  cases A1,
  {
    rw if_pos,
    apply A1,
    apply A1,
  },
  {
    rw if_neg,
    apply A1,
  }
end



lemma neg_neg_only_nonneg {α:Type*} {f:α → ℝ}:0≤ -(neg_only ∘ f) :=
begin
  rw le_func_def,
  intro n,
  simp,
  unfold neg_only,
  have A1:(f n ≤ 0) ∨ ¬(f n ≤ 0) := le_or_not_le,
  cases A1,
  {
    rw if_pos,
    apply A1,
    apply A1,
  },
  {
    rw if_neg,
    apply A1,
  }
end

lemma neg_only_nonpos {α:Type*} {f:α → ℝ}:(neg_only ∘ f) ≤ 0 :=
begin
  rw nonpos_iff_neg_nonneg_func,
  apply neg_neg_only_nonneg,
end



lemma pos_only_le_abs {α:Type*} {f:α → ℝ}: (pos_only ∘ f ≤ abs ∘ f) :=
begin
  have A1:=@pos_only_sub_neg_only_eq_abs α f,
  apply le_of_add_nonneg_eq A1,
  apply neg_neg_only_nonneg,
end

lemma neg_neg_only_le_abs {α:Type*} {f:α → ℝ}: (-neg_only ∘ f ≤ abs ∘ f) :=
begin
  have A1:=@pos_only_sub_neg_only_eq_abs α f,
  rw sub_eq_add_neg at A1,
  rw add_comm at A1,
  apply le_of_add_nonneg_eq A1,
  apply pos_only_nonneg,
end


lemma pos_only_neg_eq_neg_only {α:Type*} {f:α → ℝ}: (pos_only ∘ (-f)) = -(neg_only ∘ f) :=
begin
  ext x,
  simp,
  unfold pos_only neg_only,
  have A3:0 <f x ∨ 0 =f x ∨ f x < 0 := lt_trichotomy 0 (f x),
  cases A3,
  {
    rw if_neg,
    rw if_neg,
    {
      simp,
    },
    {
      intro A4,
      apply not_le_of_lt A3,
      apply A4,
    },
    {
      intro A4,
      apply not_le_of_lt A3,
      apply nonpos_of_neg_nonneg,
      apply A4,
    }
  },
  cases A3,
  {
    rw if_pos,
    rw if_pos,
    rw ← A3,
    simp,
    rw ← A3,
  },
  {
    rw if_pos,
    rw if_pos,
    apply le_of_lt A3,
    apply neg_nonneg_of_nonpos,
    apply le_of_lt A3,
  }
end


lemma neg_only_le {α:Type*} {f:α → ℝ}: (neg_only ∘ f ≤ f) :=
begin
  have A1:=@pos_only_add_neg_only_eq α f,
  --simp at A1,
  rw add_comm at A1,
  apply le_of_add_nonneg_eq A1,
  apply pos_only_nonneg,
end


/-
  Okay, so far I have:
  pos_only f ∧  neg_only f → f
  pos_only f ∧  neg_only f → abs f
  Now, with the new result, I get:
  abs f → pos_only f
  abs f → -neg_only f → neg_only f

  What remains is either:
  f → pos_only f
  f → neg_only f
  f → abs f

  The solution is that if summable f,
-/

lemma neg_neg_func {α:Type*} {f:α → ℝ}:-(-f)=f :=
begin
  simp,
end




lemma finset_sum_lower_bound {α:Type*} [decidable_eq α] {f:α → ℝ} {S:finset α}:
  S.sum (neg_only ∘ f) ≤ S.sum (f) :=
begin
  apply finset_sum_le2,
  intros s A1,
  apply neg_only_le,
end

lemma finset_sum_diff {α:Type*} [decidable_eq α] {f:α → ℝ} {S T:finset α}:
  T.sum f = (T ∪ S).sum f - (S \ T).sum f :=
begin
  have A1:T ∪ S = T ∪ (S\ T),
  {
    simp,
  },
  have A2:disjoint T (S \ T),
  {
    apply finset_disjoint_symm,
    apply finset.sdiff_disjoint,
  },
  have A3:(T ∪ S).sum f = T.sum f + (S \ T).sum f,
  {
    rw A1,
    symmetry,
    apply sum_disjoint_add,
    apply A2,
  },
  have A4:(T ∪ S).sum f - (S \ T).sum f= T.sum f + (S \ T).sum f - (S \ T).sum f,
  {
    rw A3,
  },
  symmetry,
  simp at A4,
  apply A4,
end

lemma finset_sum_neg_monotone_neg {α:Type*} [decidable_eq α] {f:α → ℝ} {S T:finset α}:
  f ≤ 0 →
  T ⊆ S →
  S.sum f ≤ T.sum (f) :=
begin
  intros A1 A2,
  apply le_of_neg_le_neg,
  rw ← finset_sum_neg,
  rw ← finset_sum_neg,
  apply sum_monotone_of_nonneg,
  {
    rw ← nonpos_iff_neg_nonneg_func,
    apply A1,
  },
  {
    apply A2,
  }
end


lemma finset_sum_diff_lower_bound {α:Type*} [decidable_eq α] {f:α → ℝ} {S T:finset α}:
  S.sum (neg_only ∘ f) ≤ (S \ T).sum (f) :=
begin
  have A1:S.sum (neg_only ∘ f) ≤ (S \ T).sum (neg_only ∘ f),
  {
    apply finset_sum_neg_monotone_neg,
    apply neg_only_nonpos,
    apply finset.sdiff_subset,
  },
  have A2:(S \ T).sum (neg_only ∘ f) ≤ (S \ T).sum f,
  {
    apply finset_sum_lower_bound,
  },
  apply le_trans A1 A2,

end


lemma bdd_above_of_summable_f {α:Type*} [decidable_eq α] {f:α → ℝ}:
  summable f → bdd_above  (set.range (λ (s : finset α), s.sum f)) :=
begin
  intro A1,
  unfold summable at A1,
  cases A1 with x A2,
  unfold has_sum at A2,
  have A5:(0:ℝ) < (1:ℝ) := zero_lt_one,
  have A6:set.Ioo (x - 1) (x + 1) ∈ nhds x := Ioo_nbhd A5,
  have A7:=filter_tendsto_elim A2 A6,
  simp at A7,
  cases A7 with S A8,
  let z:=x + 1 - (S.sum (neg_only ∘ f)),
  begin
    have B1:z=x + 1 - (S.sum (neg_only ∘ f)) := rfl,
    rw bdd_above_def,
    unfold upper_bounds,
    apply exists.intro z,
    simp,
    intros x2 T B2,
    subst x2,
    have B3:T.sum f = (T ∪ S).sum f - (S \ T).sum f := finset_sum_diff,
    rw B3,
    have B4:(T ∪ S).sum f - (S \ T).sum f ≤ (T ∪ S).sum f - S.sum (neg_only ∘ f),
    {
      apply sub_le_sub_left,
      apply finset_sum_diff_lower_bound,
    },
    apply le_trans B4 ,
    have B5:= (A8 (T ∪ S) (subset_union_right T S)).right,
    rw B1,
    simp,
    
    apply le_of_lt B5,
  end
end

lemma finset_sum_pos_only_eq_sum {α:Type*} [decidable_eq α] {f:α → ℝ} {S:finset α}:
  ∃ {T:finset α}, T⊆ S ∧ T.sum f = S.sum (pos_only ∘ f) :=
begin
  apply finset.induction_on S,
  {
    apply exists.intro ∅,
    split,
    {
      simp,
    },
    {
      simp,
      refl,
    }
  },
  {
    intros a V A1 A2,
    cases A2 with T A3,
    cases A3 with A4 A5,
    have A6: (0 ≤ f a) ∨ ¬ (0 ≤ f a) := le_or_not_le,
    cases A6,
    {
      apply exists.intro (insert a T),
      split,
      {
        rw finset.subset_iff,
        intros x A7,
        simp at A7,
        simp,
        cases A7,
        {
          left,
          apply A7,
        },
        {
          right,
          apply A4,
          apply A7,
        }
      },
      {
        rw sum_insert_add,
        rw sum_insert_add,
        rw ← A5,
        simp,
        unfold pos_only,
        rw if_pos,
        apply A6,
        {
          intro A8,
          apply A1,
          apply A8,
        },
        {
          intro A9,
          apply A1,
          rw finset.subset_iff at A4,
          apply A4,
          apply A9,
        }
      }
    },
    {
      apply exists.intro T,
      split,
      {
        rw finset.subset_iff,
        intros x A10,
        simp,
        right,
        apply A4,
        apply A10,
      },
      {
        rw sum_insert_add,
        rw ← A5,
        simp,
        have A11:pos_only (f a) = 0,
        {
          unfold pos_only,
          apply if_neg,
          apply A6,

        },
        rw A11,
        simp,
        apply A1,
      }
    }
  }
end


lemma summable_pos_only_of_summable {α:Type*} [decidable_eq α] {f:α → ℝ}:
  summable f → summable (pos_only ∘ f) :=
begin
  intro A1,
  apply summable_of_bdd_above,
  apply pos_only_nonneg,
  have A2:=bdd_above_of_summable_f A1,
  rw bdd_above_def,
  unfold upper_bounds,
  rw bdd_above_def at A2,
  unfold upper_bounds at A2,
  cases A2 with x A3,
  apply exists.intro x,
  simp,
  intros x2 S A4,
  subst x2,
  have A5 := @finset_sum_pos_only_eq_sum α _ f S,
  cases A5 with T A6,
  cases A6 with A7 A8,
  rw ← A8,
  simp at A3,
  have A9:T.sum f = T.sum f := rfl,
  have A10 := A3 T A9,
  apply A10,
end

lemma summable_neg_only_of_summable {α:Type*} [decidable_eq α] {f:α → ℝ}:
  summable f → summable (neg_only ∘ f) :=
begin
  intro A1,
  have A2:-(-(neg_only ∘ f)) = neg_only ∘ f := neg_neg_func,
  rw ← A2,
  apply summable.neg,
  rw ← pos_only_neg_eq_neg_only,
  apply summable_pos_only_of_summable,
  apply summable.neg,
  apply A1,
end

lemma summable_iff_pos_only_summable_neg_only_summable {α:Type*} [decidable_eq α] {f:α → ℝ}:
  summable f ↔ (summable (pos_only ∘ f) ∧ summable (neg_only ∘ f))  :=
begin
  split;intro A1,
  {
    split,
    apply summable_pos_only_of_summable A1,
    apply summable_neg_only_of_summable A1,
  },
  {
    rw ← @pos_only_add_neg_only_eq α f,
    apply summable.add,
    apply A1.left,
    apply A1.right,
  }
end

lemma summable_iff_abs_summable {α:Type*} [decidable_eq α] {f:α → ℝ}:
    summable f ↔ summable (abs ∘ f) :=
begin
  apply iff.trans,
  apply summable_iff_pos_only_summable_neg_only_summable,
  split;intro A1,
  {
    rw ← pos_only_sub_neg_only_eq_abs,
    apply summable.sub,
    apply A1.left,
    apply A1.right,
  },
  {
    split,
    {
      apply has_sum_of_le_of_le_of_has_sum,
      {
        apply pos_only_nonneg,
      },
      {
        apply pos_only_le_abs,
      },
      {
        apply A1,
      }
    },
    {
      have A2:(-(-neg_only ∘ f))=neg_only ∘ f := neg_neg_func,
      rw ← A2,
      apply summable.neg,
      apply has_sum_of_le_of_le_of_has_sum,
      {
        apply neg_neg_only_nonneg,
      },
      {
        apply neg_neg_only_le_abs,
      },
      {
        apply A1,
      }
    }
  }
end

lemma summable_intro {α β:Type*} [add_comm_monoid β] [topological_space β] {f:α → β} {x:β}:
  has_sum f x → summable f :=
begin
  intro A1,
  unfold summable,
  apply exists.intro x,
  apply A1,
end

lemma has_sum_nnreal_bounds {α:Type*} {f:α → nnreal} [D:decidable_eq α] {x:nnreal}:(x≠ 0) → (has_sum f x) → (∀ S:finset α, S.sum f ≤ x) :=
begin
  intros A1 A2,
  intro S,
  unfold has_sum at A2,
  apply le_of_not_lt,
  intro A3,
  let r := (finset.sum S f) - x,
  --let B := {C:finset α|S ≤ C},
  begin
    have A5:set.Iio (finset.sum S f) ∈ nhds x,
    {
      apply set_Iio_in_nhds_of_lt A1 A3,
    },
    --have A4:set.Ioo (x - r) (x + r) ∈ filter.at_top,
    --unfold filter.tendsto at A2,
    --unfold filter.map at A2,
    --apply filter_at_top_intro,
    have A6:= filter_tendsto_elim A2 A5,
    have A7 := filter_at_top_elim  A6,
    cases A7 with B A7,
    rw set.subset_def at A7,
    have A8:(B∪ S) ∈ {b : finset α | B ≤ b},
    {
      simp,
      apply finset.subset_union_left,
    },
    have A9 := A7 (B ∪ S) A8,
    simp at A9,
    have A10 := not_le_of_lt A9,
    apply A10,
    apply sum_monotone_of_nnreal,
    simp,
    apply finset.subset_union_right,
  end  
end

lemma has_sum_nnreal_ne_zero {α:Type*} {f:α → nnreal} [decidable_eq α] {x:nnreal}:(x≠ 0) →
  ((∀ ε>0, ∃ S:finset α, 
   ∀ T⊇S,  (T.sum f ≤ x) ∧  x - ε < T.sum f  )↔
  (has_sum f x)) :=
begin
  intro AX,
  split;intro A1,
  {
    unfold has_sum,
    apply filter_tendsto_intro,
    intros b A2,
    have A3:= mem_nhds_elim_nnreal_bound b x AX A2,
    cases A3 with ε A4,
    cases A4 with A5 A6,
    have A7 := A1 ε A5,
    cases A7 with S A8,
    apply filter_at_top_intro3 S,
    intros T A9,
    have A10 := A8 T A9,
    apply A6,
    simp,
    split,
    {
      apply A10.right,
    },
    {
     apply lt_of_le_of_lt,
     apply A10.left,
     apply lt_add_of_pos_right,
     apply A5,
    },
  },
  {
    intros ε A2,
    have A10 := has_sum_nnreal_bounds AX A1,
    unfold has_sum at A1,
    have A3:set.Ioo (x - ε) (x + ε) ∈ nhds x,
    {
      apply set_Ioo_in_nhds_of_ne_zero AX A2,
    },
    have A4 := filter_tendsto_elim A1 A3,
    have A5 := mem_filter_at_top_elim A4,
    cases A5 with S A6,
    apply exists.intro S,
    intros T A7,
    rw set.subset_def at A6,
    have A8 := A6 T A7,
    have A9:T.sum f ∈ set.Ioo (x - ε) (x + ε) := A8,
    split,
    {
      apply A10 T,
    },
    {
      simp at A9,
      apply A9.left,
    },
  }
end

/-

lemma summable_bounded_nnreal {β:Type*} (f:β → nnreal):
 (∀ S:finset β,  S.sum f = 0) →
 has_sum f 0 :=
begin
  apply has_sum_zero,
end -/






lemma nnreal.minus_half_eq_half {ε:nnreal}:ε - ε/2 = ε/2 :=
begin
  have A1:(ε/2 + ε/2) - ε/2 = ε - ε/2,
  {
    rw nnreal.add_halves,
  },
  rw ← A1,
  rw nnreal.add_sub_cancel,
end


lemma all_finset_sum_eq_zero_iff_eq_zero {β:Type*} [D:decidable_eq β] (f:β → nnreal):
 (∀ S:finset β,  S.sum f = 0) ↔ f = 0 :=
begin
  split;intros A1,
  {
    ext b,
    have A2 := A1 {b},
    simp at A2,
    rw A2,
    simp,  
  },
  {
    intros S,
    apply finite_sum_zero_eq_zero,
    intros b A2,
    rw A1,
    simp,
  },
end


lemma has_sum_of_bounded_nnreal {β:Type*} [D:decidable_eq β] (f:β → nnreal) (v:nnreal):
 (∀ S:finset β,  S.sum f ≤ v) →
 (∀ ε>0, ∃ S:finset β,  v - ε ≤ S.sum f)  →
 has_sum f v :=
begin
  intros A1 A2,
  have A3:v = 0 ∨ v ≠ 0 := @eq_or_ne nnreal _ v 0,
  cases A3,
  {
    subst v,
    have A4:f = 0,
    {
      rw ← all_finset_sum_eq_zero_iff_eq_zero,
      intro S,
      apply le_bot_iff.mp,
      apply A1 S,
    },
    subst f,
    apply has_sum_zero,
  },
  {
    have A10:0 < v,
    {
      apply bot_lt_iff_ne_bot.mpr A3,
    },
    rw ←  has_sum_nnreal_ne_zero A3,
    intros ε A4,
    let k:nnreal := (min ε v)/2,
    begin
      have A8:k = ((min ε v)/2) := rfl,
      have A11:0 < min ε v,
      {
        rw lt_min_iff,
        split,
        apply A4,
        apply A10,
      },
      have A7:0 < k,
      {
        rw A8,                
        apply nnreal.half_pos,
        apply A11,
      },
      have A12:k < min ε v,
      {
        apply nnreal.half_lt_self,
        apply bot_lt_iff_ne_bot.mp A11,      
      },
      have A6 := A2 k A7,
      cases A6 with S A6,
      apply exists.intro S,
      intro T,
      intro A5,
      split,
      {
        apply A1,
      },
      {
        apply lt_of_lt_of_le,
        have A9:v - ε < v - k,
        {
          apply nnreal_sub_lt_sub_of_lt,
          {
            apply lt_of_lt_of_le,
            apply A12,
            apply min_le_left,
          },
          {
            apply lt_of_lt_of_le,
            apply A12,
            apply min_le_right,            
          },
        },
        apply A9,
        apply le_trans,
        apply A6,
        apply sum_monotone_of_nnreal,
        --simp,
        apply A5,
      },
    end,
    apply D,
  },
end















lemma nnreal.le_Sup {S:set nnreal}:(∃ (x : nnreal), ∀ (y : nnreal), y ∈ S → y ≤ x) → 
   ∀ {x : nnreal}, x ∈ S → x ≤ Sup S :=
begin
  intro A1,
  intros x A2,
  rw ← nnreal.coe_le_coe,
  rw nnreal.coe_Sup,
  apply real.le_Sup,
  cases A1 with z A1,
  apply exists.intro (coe z),
  intros y A3,
  cases A3 with y2 A3,
  cases A3 with A3 A4,
  subst y,
  rw nnreal.coe_le_coe,
  apply A1 y2 A3,
  simp,
  apply A2,
end


lemma nnreal.le_Sup_of_bdd_above {S:set nnreal}:
  bdd_above S →
  (∀ x∈ S, (x ≤ Sup S)) :=
begin
  intros A1 y A2,
  apply nnreal.le_Sup,
  rw bdd_above_def at A1,
  unfold set.nonempty upper_bounds at A1,
  cases A1 with x A1,
  apply exists.intro x,
  apply A1,
  apply A2,
end


lemma nnreal.le_supr_of_bdd_above {α:Type*} {f:α → nnreal}:
  bdd_above (set.range f) →
  (∀ x:α, (f x ≤ ⨆ (s : α), f s)) :=
begin
  intro A1,
  unfold supr,
  intro a,
  simp,
  apply nnreal.le_Sup_of_bdd_above A1,
  simp,
end

lemma nnreal.x_eq_zero_of_supr_finset_sum_eq_zero {S:set nnreal}:
   (bdd_above S) →
   (Sup S = 0) →
   (∀ x:nnreal, x∈ S → x = 0):=
begin
  intros A1 A2 x A3,
  have A4:x≤ 0,
  {
    rw ← A2,
    apply nnreal.le_Sup_of_bdd_above,
    apply A1,
    apply A3,
  },
  apply le_bot_iff.mp A4,
end

lemma zero_of_supr_finset_sum_eq_zero {α:Type*} [D:decidable_eq α] {f:α → nnreal}:
  (bdd_above (set.range (λ s:finset α, s.sum f))) →
 ((⨆ (s :finset α), finset.sum s f) = 0) → 
 (f = 0) := 
begin
  intros A1 A2,
  have A3:(∀ (s :finset α), finset.sum s f= 0),
  {
    intros S,
    --apply le_bot_iff.mp,
    apply nnreal.x_eq_zero_of_supr_finset_sum_eq_zero A1,
    unfold supr at A2,
    apply A2,
    simp,
  },
  rw @all_finset_sum_eq_zero_iff_eq_zero α D f at A3, 
  apply A3
end























noncomputable def nnreal.conditionally_complete_lattice:conditionally_complete_lattice nnreal := conditionally_complete_linear_order_bot.to_conditionally_complete_lattice nnreal

noncomputable instance nnreal.conditionally_complete_linear_order:conditionally_complete_linear_order nnreal := {
  .. nnreal.conditionally_complete_lattice,
  .. nnreal.decidable_linear_order
}



lemma nnreal.has_sum_of_bdd_above {α:Type*} {f:α → nnreal} [decidable_eq α] {x:nnreal}:
  bdd_above (set.range (λ s:finset α, s.sum f)) →
  (x = ⨆ (s : finset α), s.sum f) →
  has_sum f x  :=
begin
  intros AX A2,
  apply has_sum_of_bounded_nnreal,
  {
    intro S,
    rw A2,
    apply @nnreal.le_supr_of_bdd_above (finset α) (λ s:finset α, s.sum f) AX,
  },
  {
    have A3:(x = 0) ∨ (x ≠ 0) := eq_or_ne,
    cases A3,
    {
      subst x,
      intro ε,
      intro A4,
      apply exists.intro ∅,
      rw A3,
      have A4:0 - ε ≤ 0,
      {
        apply nnreal.sub_le_self,
      },
      apply le_trans A4,
      apply bot_le,
      have A3A:f = 0,
      {
        apply zero_of_supr_finset_sum_eq_zero,
        apply AX,
        apply A3,
      },
      apply finset.has_emptyc,
    },
    {
      intros ε A1,
      have A4:x - ε < x,
      {
        apply nnreal.sub_lt_self,
        apply bot_lt_iff_ne_bot.mpr,
        apply A3,
        apply A1,
      },
      --apply nnreal.
      let T := (set.range (λ (s : finset α), finset.sum s f)),
      begin 
        have A5:T = (set.range (λ (s : finset α), finset.sum s f)) := rfl,
        have A6:Sup T = x,
        {
          rw A2,
          refl,
        },
        have A7:∃b∈ T, x-ε< b,
        {
          apply @exists_lt_of_lt_cSup nnreal _ T,
          rw A5,
          apply @set_range_finset_nonempty α nnreal _ f,
          rw A6,
          apply A4,
        },
        cases A7 with b A7,
        cases A7 with A7 A8,
        rw A5 at A7,
        simp at A7,
        cases A7 with S A7,
        subst b,
        apply exists.intro S,
        apply le_of_lt A8,
      end
    },
  },
end

lemma nnreal.has_sum_of_supr {α:Type*} {f:α → nnreal} [decidable_eq α]:
  bdd_above (set.range (λ s:finset α, s.sum f)) →
  has_sum f (⨆ (s : finset α), s.sum f)  :=
begin
  intros A1 A2,
  have A3:(⨆ (s : finset α), s.sum f) = (⨆ (s : finset α), s.sum f),
  {
    refl,
  },
  apply nnreal.has_sum_of_bdd_above A1 A3,
end

lemma summable_bounded_nnreal {β:Type*} [decidable_eq β] (f:β → nnreal) (v:nnreal):
 (∀ S:finset β,  S.sum f ≤ v) →
 summable f :=
begin
  intro A1,
  apply has_sum.summable, 
  apply nnreal.has_sum_of_supr,
    rw bdd_above_def,
    unfold upper_bounds,
    apply @set.nonempty_of_mem _ _ v,
    simp,
    intros a S A3,
    subst a,
    apply A1,  
end

