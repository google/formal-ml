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
import measure_theory.set_integral
import measure_theory.borel_space
import data.set.countable
import formal_ml.nnreal
import formal_ml.sum
import formal_ml.core
import formal_ml.measurable_space
import formal_ml.semiring
import formal_ml.real_measurable_space
import formal_ml.set
import formal_ml.filter_util
import topology.instances.ennreal
import formal_ml.int
import formal_ml.with_density_compose_eq_multiply
import formal_ml.classical
import formal_ml.restrict

/-
  This does not prove the classic Hahn decomposition theorem for signed measures.
  Instead, it proves a similar theorem for unsigned measures. To understand various
  operations on unsigned measures (like the supremum of two measures, the infimum of
  two measures, or the "difference" of two measures), it is important to be able
  to consider two non-negative measures and partition the space into a set where
  the first measure is less than or equal to the second, and a set where the second
  is less than or equal to the first. So, given measures μ and ν, we want a measurable
  set S such that:

  μ.restrict S ≤ ν.restrict S and  ν.restrict Sᶜ ≤ μ.restrict Sᶜ.

  This means that for any set T ⊆ S, μ T ≤ ν T, and for any U ⊆ Sᶜ, ν U ≤ μ U.

  By partitioning the space like so, we can separately consider supremum, infimum,
  and difference in each half, and combine them back together. This in turn
  helps to prove the Lebesgue-Radon-Nikodym theorem.

  Note that {S|is_measurable S ∧ μ.restrict S ≤ ν.restrict S} is a ring of sets.

 -/

lemma nonnegative_fn {α β:Type*} [canonically_ordered_add_monoid β] {f:α → β}:0 ≤ f :=
begin
  intro x,
  simp,
end

lemma nnreal.add_lt_of_lt_sub {a b c:nnreal}:a < b - c → a + c < b :=
begin
  cases (decidable.em (c ≤ b)) with B1 B1,
  {
    repeat {rw ← nnreal.coe_lt_coe <|> rw nnreal.coe_add},
    rw nnreal.coe_sub B1,
    intro B2,
    linarith,
  },
  {
    intros A1,
    rw nnreal.sub_eq_zero at A1,
    exfalso,
    simp at A1,
    apply A1,
    apply le_of_not_le B1,
  },
end

lemma nnreal.lt_sub_of_add_lt {a b c:nnreal}:a + c < b → a < b - c :=
begin
  intro A1,
  have B1:c ≤ b,
  {
    have B1A := le_of_lt A1,
    have B1B:a + c ≤ a + b,
    {
      have B1BA:b ≤ a + b,
      {
        rw add_comm,
        apply le_add_nonnegative _ _,
      },
      apply le_trans B1A B1BA,
    },
    simp at B1B,
    apply B1B,
  },
  revert A1,
  repeat {rw ← nnreal.coe_lt_coe <|> rw nnreal.coe_add},
  rw nnreal.coe_sub B1,
  intros,
  linarith,
end

lemma nnreal.le_sub_add {a b c:nnreal}:b ≤ c → c ≤ a → 
a ≤ a - b + c := 
begin
  repeat {rw ← nnreal.coe_le_coe},
  repeat {rw nnreal.coe_add},
  intros A1 A2,
  repeat {rw nnreal.coe_sub},
  linarith,
  apply le_trans A1 A2,
end



lemma nnreal.lt_of_add_le_of_le_of_sub_lt {a b c d e:nnreal}:
    a + b ≤ c → d ≤ b → c - e < a → d < e := 
begin
  rw ← nnreal.coe_le_coe,
  rw ← nnreal.coe_le_coe,
  rw ← nnreal.coe_lt_coe,
  rw ← nnreal.coe_lt_coe,
  rw nnreal.coe_add,
  cases (le_or_lt e c) with B1 B1,
  {
    rw nnreal.coe_sub B1,
    rw ← nnreal.coe_le_coe at B1,
    intros,linarith,
  },
  {   
    rw nnreal.sub_eq_zero (le_of_lt B1),
    rw ← nnreal.coe_lt_coe at B1,
    rw nnreal.coe_zero,
    intros,linarith,
  },
end

lemma nnreal.inv_as_fraction {c:nnreal}:(1)/(c) = (c)⁻¹ := 
begin
  rw nnreal.div_def,
  rw one_mul,
end


lemma nnreal.lt_of_add_lt_of_pos {a b c:nnreal}:
      b + c ≤ a →
      0 < b →
      c < a :=
begin
  rw ← nnreal.coe_le_coe,
  rw ← nnreal.coe_lt_coe,
  rw ← nnreal.coe_lt_coe,
  rw nnreal.coe_add,
  rw nnreal.coe_zero,
  intros,
  linarith,
end


lemma nnreal.mul_le_mul_of_le_left {a b c:nnreal}:
  a ≤ b → c * a ≤ c * b :=
begin
  intro A1,
  apply ordered_comm_monoid.mul_le_mul_left,
  apply A1,
end

lemma with_top.not_none_lt {α:Type*} [preorder α] (a:with_top α):
  ¬(@has_lt.lt (with_top α) _  (none:with_top α) a):=
begin
  intro A1,
  rw lt_iff_le_not_le at A1,
  cases A1 with A1 A2,
  apply A2,
  apply with_top.le_none,
end

lemma with_top.not_none_le_some {α:Type*} [partial_order α] (a:α):
  ¬(@has_le.le (with_top α) _ (none) (some a)):=
begin
  intro A1,
  have B1:(some a) ≠ (none:with_top α),
  {
    simp,
  },
  have B3:(@has_le.le (with_top α) _ (some a) (none)) := with_top.le_none,
  have B4 := @le_antisymm (with_top α) _ (some a) (none) B3 A1,
  apply B1,
  apply B4
end


-- TODO: everything used below here.
lemma ennreal.inv_as_fraction {c:ennreal}:(1)/(c) = (c)⁻¹ := 
begin
  rw ennreal.div_def,
  rw one_mul,
end

lemma ennreal.add_lt_of_lt_sub {a b c:ennreal}:a < b - c → a + c < b :=
begin
  --intros AX A1,
  cases a;cases b;cases c;try {simp},
  {
    rw ← ennreal.coe_add,
    apply with_top.some_lt_none,
  },
  {
    repeat {rw ← ennreal.coe_sub 
            <|> rw ennreal.coe_lt_coe
            <|> rw ← ennreal.coe_add},
    apply nnreal.add_lt_of_lt_sub,
  },
end


lemma ennreal.lt_sub_of_add_lt {a b c:ennreal}: a + c < b → a < b - c :=
begin
  --intros AX A1,
  cases a;cases b;cases c;try {simp},
  {
    repeat {rw ← ennreal.coe_sub 
            <|> rw ennreal.coe_lt_coe
            <|> rw ← ennreal.coe_add},
    apply nnreal.lt_sub_of_add_lt,
  },
end


lemma ennreal.eq_zero_or_zero_lt {x:ennreal}:¬(x=0) → (0 < x) :=
begin
  intro A1,
  have A2:= @lt_trichotomy ennreal _ x 0,
  cases A2,
  {
    exfalso,
    apply @ennreal.not_lt_zero x,
    apply A2,
  },
  cases A2,
  {
    exfalso,
    apply A1,
    apply A2,
  },
  {
    apply A2,
  },
end

--TODO: everything used below here.

lemma ennreal.sub_eq_of_add_of_not_top_of_le {a b c:ennreal}:a = b + c →
  c ≠ ⊤ →
  c ≤ a → a - c = b :=
begin
  intros A1 A4 A2,
  cases c,
  {
    exfalso,
    simp at A4,
    apply A4,
  },
  cases a,
  {
    simp,
    cases b,
    {
      refl,
    },
    exfalso,
    simp at A1,
    rw ← ennreal.coe_add at A1,
    apply ennreal.top_ne_coe A1,
  },
  cases b,
  {
    simp at A1,
    exfalso,
    apply A1,
  },
  {
    repeat {rw ennreal.some_eq_coe},
    rw ← ennreal.coe_sub,
    rw ennreal.coe_eq_coe,
    repeat {rw ennreal.some_eq_coe at A1},
    rw ← ennreal.coe_add at A1,
    rw ennreal.coe_eq_coe at A1,
    repeat {rw ennreal.some_eq_coe at A2},
    rw ennreal.coe_le_coe at A2,
    apply nnreal.sub_eq_of_add_of_le A1 A2,
  },
end

lemma ennreal.eq_add_of_sub_eq {a b c:ennreal}:b ≤ a →
  a - b = c → a = b + c :=
begin
  intros A1 A2,
  cases a;cases b,
  {
    simp,
  },
  {
    cases c,
    {
      simp,
    },
    exfalso,
    simp at A2,
    apply A2,
  },
  {
    exfalso,
    apply with_top.not_none_le_some _ A1,
  },
  simp at A2,
  rw ← ennreal.coe_sub at A2,
  cases c,
  {
    exfalso,
    simp at A2,
    apply A2,
  },
  {
    simp,
    rw ← ennreal.coe_add,
    rw ennreal.coe_eq_coe,
    simp at A2,
    simp at A1,
    apply nnreal.eq_add_of_sub_eq A1 A2,
  },
end


lemma ennreal.sub_lt_sub_of_lt_of_le {a b c d:ennreal}:a < b →
  c ≤ d →
  d ≤ a →
  a - d < b - c :=
begin
  intros A1 A2 A3,
  have B1:(⊤:ennreal) = none := rfl,
  have B2:∀ n:nnreal,  (some n) = n,
  {
    intro n,
    refl,
  },
  cases a,
  {
    exfalso,
    apply @with_top.not_none_lt nnreal _ b A1,
  },
  cases d,
  {
    exfalso,
    apply @with_top.not_none_le_some nnreal _ a A3,
  },
  cases c,
  {
    exfalso,
    apply @with_top.not_none_le_some nnreal _ d A2,
  },
  cases b,
  {
    simp,
    rw ← ennreal.coe_sub,
    rw B1,
    rw ← B2,
    apply with_top.some_lt_none,
  },
  repeat {rw B2},
  repeat {rw ← ennreal.coe_sub},
  rw ennreal.coe_lt_coe,
  apply nnreal.sub_lt_sub_of_lt_of_le,
  repeat {rw B2 at A1},
  rw ennreal.coe_lt_coe at A1,
  apply A1,
  
  repeat {rw B2 at A2},
  rw ennreal.coe_le_coe at A2,
  apply A2,

  repeat {rw B2 at A3},
  rw ennreal.coe_le_coe at A3,
  apply A3,
end


lemma ennreal.le_sub_add {a b c:ennreal}:b ≤ c → c ≤ a → 
a ≤ a - b + c := 
begin
  cases a;cases b;cases c;try {simp},
  rw ← ennreal.coe_sub,
  rw ← ennreal.coe_add,
  rw ennreal.coe_le_coe,
  apply nnreal.le_sub_add,
end


lemma ennreal.add_sub_cancel {a b:ennreal}:b < ⊤ → a + b - b = a :=
begin
  cases a;cases b;try {simp},
end


lemma ennreal.exists_coe {x:ennreal}:x < ⊤ → ∃ v:nnreal, x = v :=
begin
  cases x;try {simp},
end



lemma ennreal.lt_of_add_le_of_le_of_sub_lt {a b c d e:ennreal}:c < ⊤ →
    a + b ≤ c → d ≤ b → c - e < a → d < e := 
begin
  cases c,simp,
  cases a;cases b;cases d;cases e;try {simp},
  rw ← ennreal.coe_add,
  rw ← ennreal.coe_sub,
  rw ennreal.coe_le_coe,
  rw ennreal.coe_lt_coe,
  apply nnreal.lt_of_add_le_of_le_of_sub_lt,
end


lemma ennreal.coe_sub_lt_self {a:nnreal} {b:ennreal}:
     0 < a  → 0 < b →
     (a:ennreal) - b < (a:ennreal) :=
begin
  cases b;simp,
  intros A1 A2,
  rw ← ennreal.coe_sub,
  rw ennreal.coe_lt_coe,
  apply nnreal.sub_lt_self A1 A2,
end 

lemma ennreal.lt_of_lt_top_of_add_lt_of_pos {a b c:ennreal}:a < ⊤ →
      b + c ≤ a →
      0 < b →
      c < a :=
begin
  cases a;simp;
  cases b;cases c;simp,
  rw ← ennreal.coe_add,
  rw ennreal.coe_le_coe,
  apply nnreal.lt_of_add_lt_of_pos,
end


/-
  enneral could be a linear_ordered_comm_group_with_zero,
  and therefore a ordered_comm_monoid.
  HOWEVER, I am not sure how to integrate this.
  I am going to just prove the basic results from the class.
  NOTE that this is strictly more general than
  ennreal.mul_le_mul_left.
-/
lemma ennreal.mul_le_mul_of_le_left {a b c:ennreal}:
  a ≤ b → c * a ≤ c * b :=
begin
  cases a;cases b;cases c;simp;
  try {
    cases (classical.em (c=0)) with B1 B1,
    {
      subst c,
      simp,
    },
    {
      have B2:(c:ennreal) * ⊤ = ⊤,
      {
        rw ennreal.mul_top,
        rw if_neg,
        intro B2A,
        apply B1,
        simp at B2A,
        apply B2A,
      },
      rw B2,
      {apply le_refl _ <|> simp},
    },
  },
  {
    cases (classical.em (b=0)) with B1 B1,
    {
      subst b,
      simp,
    },
    {
      have B2:⊤ * (b:ennreal) = ⊤,
      {
        rw ennreal.top_mul,
        rw if_neg,
        intro B2A,
        apply B1,
        simp at B2A,
        apply B2A,
      },
      rw B2,
      simp,
    },
  },
  rw ← ennreal.coe_mul,
  rw ← ennreal.coe_mul,
  rw ennreal.coe_le_coe,
  apply nnreal.mul_le_mul_of_le_left,
end


lemma ennreal.inverse_le_of_le {a b:ennreal}:
  a ≤ b →
  b⁻¹ ≤ a⁻¹ :=
begin
  intros A2,
  cases (classical.em (a = 0)) with A1 A1,
  {
    subst a,
    simp,
  },

  cases b,
  {
    simp,
  },
  cases (classical.em (b = 0)) with C1 C1,
  {
    subst b,
    simp at A2,
    exfalso,
    apply A1,
    apply A2,
  },
  simp,
  simp at A2,
  have B1: (a⁻¹ * b⁻¹) * a ≤  (a⁻¹ * b⁻¹) * b,
  {
    apply ennreal.mul_le_mul_of_le_left A2,
  },
  rw mul_comm a⁻¹  b⁻¹ at B1,
  rw mul_assoc at B1,
  rw ennreal.inv_mul_cancel at B1,
  rw mul_comm (b:ennreal)⁻¹  a⁻¹ at B1,
  rw mul_assoc at B1,
  rw mul_one at B1,
  rw ennreal.inv_mul_cancel at B1,
  rw mul_one at B1,
  apply A2,
  {
    simp [C1],
  },
  {
    simp,
  },
  {
    apply A1,
  },
  {
    rw ← lt_top_iff_ne_top,
    apply lt_of_le_of_lt A2,
    simp,  
  },
end


lemma ennreal.nat_coe_add {a b:ℕ}:(a:ennreal) + (b:ennreal) = 
    ((@has_add.add nat _ a  b):ennreal) :=
begin
  simp,
end

lemma ennreal.nat_coe_le_coe {a b:ℕ}:(a:ennreal) ≤ (b:ennreal) ↔ (a ≤ b) :=
begin
  have B1:(a:ennreal) = ((a:nnreal):ennreal),
  {
    simp,
  }, 
  have B2:(b:ennreal) = ((b:nnreal):ennreal),
  {
    simp,
  }, 
  rw B1,
  rw B2,
  rw ennreal.coe_le_coe,
  split;intros A1,
  {
    simp at A1,
    apply A1,
  },
  {
    simp,
    apply A1,
  },
end

lemma ennreal.tsum {α:Type*} {f:α → ennreal}:tsum f = supr (λ s:finset α,s.sum f) :=
begin
  rw ← summable.has_sum_iff ennreal.summable,
  apply @ennreal.has_sum α f,
end

lemma ennreal.tsum_le {f:ℕ → ennreal} {x:ennreal}:(∀ n:ℕ,
(finset.range n).sum f ≤ x) ↔
(tsum f ≤ x) :=
begin
  rw ennreal.tsum,

  split;intros A1,
  {
    apply @supr_le ennreal (finset ℕ) _ (λ s:finset ℕ,s.sum f),
    intro s,
    have B1:=finset_range_bound s,
    cases B1 with n B1,
    apply le_trans _ (A1 n),
    simp,
    apply @finset.sum_le_sum_of_subset ℕ ennreal s (finset.range n) f _ B1,
  },
  {
    intro n,
    apply le_trans _ A1,
    apply @le_supr ennreal (finset ℕ) _ (λ s, s.sum f),
  },
end


lemma ennreal.finset_sum_le_tsum {f:ℕ → ennreal} {n:ℕ}:
(finset.range n).sum f ≤ tsum f :=
begin
  rw ennreal.tsum,
  apply @le_supr ennreal (finset ℕ) _ (λ s, s.sum f),
end 


lemma ennreal.lim_finset_sum_eq_tsum {f:ℕ → ennreal}:
(⨆  n, (finset.range n).sum f)  = tsum f :=
begin
  apply le_antisymm,
  apply @supr_le ennreal _ _,
  intro n,
  apply ennreal.finset_sum_le_tsum,
  rw ← ennreal.tsum_le,
  intro n,
  apply @le_supr ennreal _ _,
end

lemma ennreal.Sup_eq_supr {S:set ennreal}:S.nonempty →
   (∃ f:ℕ → ennreal, 
      (∀ n, f n ∈ S) ∧
      (supr f = Sup S)) :=
begin
  intro A1,
  cases (classical.em (Sup S = ⊤)) with A2 A2, 
  {
    -- If Sup S = ⊤, then we have a sequence that is larger than every natural.
    have B1:∀ n:ℕ, ∃ s:ennreal,  (s∈ S) ∧ (n:ennreal) ≤ s,
    {
      intro n,
      rw Sup_eq_top at A2,
      have B1A:=A2 n _,
      cases B1A with s B1A,
      cases B1A with B1A B1B,
      apply exists.intro s,
      apply and.intro B1A (@le_of_lt ennreal _ _ _ B1B),
      have B1C:(n:ennreal) = ((n:nnreal):ennreal),
      {
        simp,
      },
      rw B1C,
      apply ennreal.coe_lt_top,
    },
    have B2:=classical.some_func B1,
    cases B2 with f B2,
    apply exists.intro f,
    simp at B2,
    split,
    {
      intro n,
      apply (B2 n).left,
    },
    {
      rw A2,
      rw ← top_le_iff,
      rw ← ennreal.supr_coe_nat,
      apply @supr_le_supr ennreal ℕ _,
      intro n,
      apply (B2 n).right,
    },
  },
  {
    have C1:∀ n:ℕ, ∃ s:ennreal, (s∈S) ∧ (Sup S - (1/(n.succ:ennreal)) ≤ s),
    {
      intro n,
      have C1A:=@ennreal.Sup_elim S (1/(n.succ:nnreal)) _ A1 A2,
      cases C1A with s C1A,
      cases C1A with C1A C1B,
      apply exists.intro s,
      apply and.intro C1A _,
      rw ennreal.coe_div at C1B,
      simp at C1B,
      simp,
      apply C1B,
      simp,
      simp,
      apply zero_lt_one,  
    },
    have C2:=classical.some_func C1,
    cases C2 with f C2,
    apply exists.intro f,
    split,
    {
      intro n,
      apply (C2 n).left,
    },
    apply le_antisymm,
    {
      apply @supr_le ennreal _ _,
      intro i,
      have C3 := C2 i,
      apply @le_Sup ennreal _ _,
      apply C3.left,
    },
    apply @ennreal.le_of_forall_epsilon_le,
    intros ε C4 C5,
    have C6 := nnreal.exists_unit_frac_lt_pos C4,
    cases C6 with n C6,
    have C7 := C2 n,  
    have C8:Sup S ≤ f n + ε,
    {
      have C8A:1/ ((nat.succ n):ennreal) ≤ (ε:ennreal),
      {
        simp,
        rw ← ennreal.coe_one,
        have C8A1:(n:ennreal) = ((n:nnreal):ennreal),
        {
          simp,
        },
        rw C8A1,
        rw ← ennreal.coe_add,
        rw ← ennreal.coe_div,
        rw ennreal.coe_le_coe,
        apply le_of_lt,
        apply C6,
        simp,
      },
      have C8B:Sup S - (ε:ennreal) ≤
               Sup S - 1/ ((nat.succ n):ennreal),
      {
        apply ennreal.sub_le_sub,
        apply le_refl (Sup S),
        apply C8A,    
      },
      have C8C:Sup S - (ε:ennreal) ≤ f n,
      {
        apply le_trans C8B C7.right,
      },
      rw add_comm,
      rw ← ennreal.sub_le_iff_le_add',
      apply C8C,   
    },
    apply le_trans C8,
    have C9 := le_supr f n,
    apply add_le_add_right C9,
  },
end


def Sup_so_far {α:Type*} [semilattice_sup_bot α] (f:ℕ → α) (n:ℕ):α :=
  (finset.range (n.succ)).sup f


lemma Sup_so_far_def {α:Type*} [semilattice_sup_bot α] {f:ℕ → α} 
    {n:ℕ}:
    Sup_so_far f n = (finset.range (n.succ)).sup f := rfl


lemma le_Sup_so_far {α:Type*} [semilattice_sup_bot α] (f:ℕ → α):
   f ≤ (Sup_so_far f) := 
begin
  rw le_func_def2,
  intro n,
  rw Sup_so_far_def,
  apply finset.le_sup,
  simp,
end

lemma finset.sup_closed_nonempty {α β:Type*} [decidable_eq α] 
   [semilattice_sup_bot β]
   (S:finset α) 
   (f:α → β) (T:set β):
   (S ≠ ∅) →
   (∀ a∈ S, f a ∈ T) →
   (∀ a∈ T, ∀ b∈ T, a⊔b ∈ T) →
   (S.sup f ∈ T) :=
begin
  intros A2 A4 A3,
  revert A2,
  revert A4,
  apply finset.induction_on S,
  {
    intros B1,
    simp,
  },
  {
    intros a S C1 C2 C3,
    simp,
    cases classical.em (S = ∅) with C5 C5,
    {
      subst S,
      simp,
      apply C3,
      simp,
    },
    apply A3,
    {
      apply C3,
      simp,  
    },
    {
      apply C2,
      intro a2,
      intro C4,
      apply C3,
      simp,
      apply or.inr C4,  
      apply C5,
    },
  },
end

lemma Sup_so_far_of_closed {α:Type*} [semilattice_sup_bot α] (f:ℕ → α) (S:set α):
   (∀ n:ℕ, f n ∈ S) →
   (∀ a∈ S, ∀ b∈ S, a⊔b ∈ S) →
   (∀ n:ℕ, (Sup_so_far f n ∈ S)) :=
begin
  intros A1 A2 n,
  rw Sup_so_far_def,
  apply finset.sup_closed_nonempty,
  {
    rw finset.range_eq_Ico,
    intro B1,
    rw finset.Ico.eq_empty_iff at B1,
    simp at B1,
    apply nat.succ_ne_zero n B1,
  },
  {
    intros n2 C1,
    apply A1,
  },
  {
    apply A2,
  },
end


lemma monotone_Sup_so_far {α:Type*} [semilattice_sup_bot α] (f:ℕ → α):
   monotone (Sup_so_far f) := 
begin
  intros a b A1,
  rw Sup_so_far_def,
  rw Sup_so_far_def,
  apply finset.sup_mono,
  simp,
  apply nat.succ_le_succ A1,
end



------------------------------------------------

--No such (sane) set exists, certainly not if μ and ν are finite.
--Note that we don't make the system inconsistent
--by constructing a definition that is possibly unsatisfiable.
--The general idea that we want to prove is that if μ X < ν X,
--then there must be some pure set X'⊆ X, where for all subsets
-- X''⊆ X', μ X'' ≤ ν X'', and μ X' < ν X'. A hahn crazy set
--is a counterexample to this theorem.
def hahn_crazy_set {α:Type*} [M:measurable_space α] 
  (μ ν:measure_theory.measure α) (X:set α):Prop :=
    (μ X < ν X) ∧ 
    is_measurable X ∧ 
    (∀ X':set α,  (X' ⊆ X) → is_measurable X' → 
    (μ.restrict X' ≤ ν.restrict X')→ (ν X' ≤ μ X') )

lemma hahn_crazy_set_def' {α:Type*} [M:measurable_space α] 
  (μ ν:measure_theory.measure α) (X:set α):hahn_crazy_set μ ν X =
    ((μ X < ν X) ∧ 
    is_measurable X ∧ 
    (∀ X':set α,  (X' ⊆ X) → is_measurable X' → 
    (μ.restrict X' ≤ ν.restrict X')→ (ν X' ≤ μ X') )) := rfl



--The contradiction proofs chip away at this set. This
--theorem shows that when you chip a piece off a crazy set,
--a crazy set remains.
lemma hahn_crazy_set_subset {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α)
  (X:set α) (X':set α):
  hahn_crazy_set μ ν X → 
  X' ⊆ X →
  is_measurable X' →
  ν X' ≤ μ X' →
  hahn_crazy_set μ ν (X\X') :=
begin
  intros A1 A2 A3 A5,
  rw hahn_crazy_set_def' at A1,
  have A4:μ X' < ⊤,
  {
    have A4A:μ X' ≤ μ X,
    {
      apply measure_theory.measure_mono A2,
    },
    apply lt_of_le_of_lt A4A,
    apply lt_of_lt_of_le A1.left,
    apply @le_top ennreal _,
  },
  rw hahn_crazy_set_def',
  split,
  {
    rw measure_theory.measure_diff A2 A1.right.left A3 A4, 
    rw measure_theory.measure_diff A2 A1.right.left A3
       (lt_of_le_of_lt A5 A4),
    -- ⊢ ⇑μ X - ⇑μ X' < ⇑ν X - ⇑ν X'
    apply ennreal.sub_lt_sub_of_lt_of_le,
    { -- ⊢ ⇑μ X < ⇑ν X
      apply A1.left,
    },
    { -- ⊢ ⇑ν X' ≤ ⇑μ X'
      apply A5,
    },
    { -- ⊢ ⇑μ X' ≤ ⇑μ X
      apply (measure_theory.measure_mono A2),
    },
  },
  apply and.intro (is_measurable.diff A1.right.left A3),    
  intros X'' C1 C2,
  apply A1.right.right,
  apply @set.subset.trans α X'' (X \ X') X C1,
  apply set.diff_subset,
  apply C2,
end


--In a hahn_crazy_set μ ν X, you will find sets X'⊆ X where ν X' < μ X',
--even though μ X < ν X. So, by creating X - X', you get an even crazier
--set. In hahn_crazy_diff_big below, we show how we can select an element
--that is big ENOUGH.
def hahn_crazy_diff_set {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α)
  (X:set α):set (set α) := { X':set α|X' ⊆ X ∧ is_measurable X' ∧ 
                      μ X' < ν X'}

lemma hahn_crazy_diff_set_def {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α):hahn_crazy_diff_set μ ν X = 
  { X':set α|X' ⊆ X ∧ is_measurable X' ∧ μ X' < ν X'} := rfl



lemma not_restrict_le_elim {α:Type*} [M:measurable_space α]
  {μ ν:measure_theory.measure α} {X:set α}: 
  is_measurable X →
  ¬(μ.restrict X ≤ ν.restrict X) →
  (∃ X':set α, X'⊆ X ∧ is_measurable X' ∧ ν X' < μ X') :=
begin
  intros A1 A2,
  rw ← @decidable.not_forall_not _ _ (@classical.prop_decidable _),
  intro A3,
  apply A2,
  rw measure_theory.measure.le_iff,
  intros s A4,
  repeat {rw measure_theory.measure.restrict_apply},
  have A5 := A3 (s ∩ X),
  simp at A5,
  apply A5,
  repeat {simp [A4,A1]},
end

lemma hahn_crazy_diff_set_nonempty' {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α): 
  hahn_crazy_set ν μ X →
  (hahn_crazy_diff_set μ ν X).nonempty :=
begin
  intros A1,
  rw hahn_crazy_set_def' at A1,
  cases A1 with A1 A2,
  cases A2 with A2 A3,
  rw set.nonempty_def,
  have A4:¬ (ν.restrict X ≤ μ.restrict X),
  { intro A4A, rw lt_iff_not_ge at A1,
    apply A1, apply A3 X (set.subset.refl X) A2 A4A},
  have A5 := not_restrict_le_elim A2 A4,
  cases A5 with X' A5,
  apply exists.intro X',
  rw hahn_crazy_diff_set_def,
  simp only [set.mem_set_of_eq],
  apply A5,
end

--Too trivial, used once.
lemma pred_eq_set {α:Type*} {S:set α} {a:α}:
    (S a) = (a∈ S) := rfl

lemma nat.find_spec_set {S : set ℕ} [_inst_1 : decidable_pred S] (H : ∃ (n : ℕ), S n):(nat.find H) ∈ S :=
begin
  rw ← pred_eq_set,
  apply nat.find_spec,
end

lemma nat.Inf_of_nonempty {S:set ℕ}:S.nonempty → Inf S ∈ S :=
begin
  intro A1,
  have A2:=set.nonempty_def.mp A1,
  rw nat.Inf_def A2,
  have A3:decidable_pred S := classical_set ℕ S,
  apply nat.find_spec_set,
end

lemma nat.exists_le_Inf_map 
  {α:Type*} {f:α → ℕ} {S:set α}:S.nonempty → ∃ s∈ S,
  ∀ a∈ S, f s ≤ f a :=
begin
  intro A1,
  let n := Inf (f '' S),
  begin
    have A2:(f '' S).nonempty,
    {
      apply set.nonempty_image_iff.mpr A1,
    },
    have A3 := nat.Inf_of_nonempty A2,
    simp at A3,
    cases A3 with a A3,
    apply exists.intro a,
    apply exists.intro A3.left,
    intros b B1,
    rw A3.right,
    apply nat.Inf_le,
    simp,
    apply exists.intro b,
    apply and.intro B1,
    refl,
  end
end

lemma nat.le_Inf  {S:set ℕ} {a:ℕ}:S.nonempty → (∀ s∈ S,
  a ≤ s) → a ≤ Inf S := 
begin
  intros A1 A2,
  apply A2,
  apply nat.Inf_of_nonempty A1,
end

lemma nat.exists_eq_Inf_map {α:Type*} {f:α → ℕ} {S:set α}:S.nonempty → 
    ∃ s∈ S, f s = Inf (f '' S) :=
begin
  intros A1,
  have B1:(f '' S).nonempty,
  {
    apply set.nonempty_image_iff.mpr A1,
  },

  have B2 := nat.Inf_of_nonempty B1,
  simp at B2,
  cases B2 with a B2,
  cases B2 with B2 B3,
  apply exists.intro a,
  apply exists.intro B2,
  apply B3,
end

/--Notice that this function chooses the minimum n that is greater than or equal to the inverse.
Put another way, this chooses the maximum 1/n that is less than or equal to the value.-/
noncomputable def floor_simple_fraction (x:ennreal):ℕ  := Inf {n:ℕ|(n:ennreal) ≥ x⁻¹}

/--This is a way of selecting a "big" input of a function when it is hard to select a maximum
input. Because we are mapping the extended non-negative reals onto the naturals with a
monotonically decreasing function, and for any nonempty set of natural numbers there is
a minimum, we get a set of "big" inputs to the function, and we apply classical.some, we 
get one of these values.
 
This is good for showing progress: if we whittle away something, and get smaller and
smaller results, we eventually grab every nonzero result remaining.-/
lemma hahn_infi_ennreal {α:Type*} {f:α→ ennreal} (S:set α):S.nonempty → 
  ∃ a∈ S, 
  (floor_simple_fraction ∘ f) a = Inf ((floor_simple_fraction ∘ f) '' S) :=
begin
  intro A1,
  apply nat.exists_eq_Inf_map,
  apply A1,
end 

/-- When we start with some hahn_crazy_set μ ν X, we know μ X < ν X. We want to
grab a big chunk X' where ν X' < μ X'. This can only go on for so long.
-/
def hahn_crazy_diff_big {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):set α :=
  classical.some
  (@hahn_infi_ennreal (set α) (λ X':set α, μ X' - ν X')
  (hahn_crazy_diff_set ν μ X) (hahn_crazy_diff_set_nonempty' ν μ X H))



lemma hahn_crazy_diff_big_def {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):hahn_crazy_diff_big μ ν X H =
  classical.some
  (@hahn_infi_ennreal (set α) (λ X':set α, μ X' - ν X')
  (hahn_crazy_diff_set ν μ X) (hahn_crazy_diff_set_nonempty' ν μ X H)) := rfl


lemma hahn_crazy_diff_big_spec {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):
 (hahn_crazy_diff_big μ ν X H) ∈ 
  (hahn_crazy_diff_set ν μ X) ∧
  (floor_simple_fraction ∘ (λ X':set α, μ X' - ν X')) (hahn_crazy_diff_big μ ν X H)
  = Inf  ((floor_simple_fraction ∘ (λ X':set α, μ X' - ν X'))''(hahn_crazy_diff_set ν μ X)) :=
begin
  let f :=  (λ X':set α, μ X' - ν X'),
  let S := (hahn_crazy_diff_set ν μ X),
  let P := (λ (a:set α), 
       (∃ (H:a∈ hahn_crazy_diff_set  ν μ X),
      (floor_simple_fraction ∘ f)
       a =
      Inf ((floor_simple_fraction ∘ f) '' S))),
  begin
  have A1: f = (λ X':set α, μ X' - ν X') := rfl,
  have A2: S = (hahn_crazy_diff_set ν μ X) := rfl,
  have A3: P = (λ (a:set α), 
       (∃ (H:a∈ hahn_crazy_diff_set  ν μ X),
      (floor_simple_fraction ∘ f)
       a =
      Inf ((floor_simple_fraction ∘ f) '' S))) := rfl,
  have B1:(λ (a:set α), 
       (∃ (H:a∈ hahn_crazy_diff_set  ν μ X),
      (floor_simple_fraction ∘ f)
       a =
      Inf ((floor_simple_fraction ∘ f) '' S))) 
       (hahn_crazy_diff_big μ ν X H),
  {  
    rw hahn_crazy_diff_big_def,

    have B1A:∃ y:set α, P y,
    {
      rw A3,
      apply hahn_infi_ennreal,
      apply hahn_crazy_diff_set_nonempty',
      apply H,
    },
    apply @classical.some_spec (set α) P B1A,
  },
  cases B1 with B1 B2,
  split,
  apply B1,
  apply B2
  end
end




lemma hahn_crazy_diff_big_Inf {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):
  (floor_simple_fraction ∘ (λ X':set α, μ X' - ν X')) (hahn_crazy_diff_big μ ν X H)
  = Inf  ((floor_simple_fraction ∘ (λ X':set α, μ X' - ν X'))''(hahn_crazy_diff_set ν μ X)) :=
begin
  have A1 := hahn_crazy_diff_big_spec μ ν X H,
  apply A1.right,
end

lemma hahn_crazy_diff_big_mem {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):
  (hahn_crazy_diff_big μ ν X H) ∈ (hahn_crazy_diff_set ν μ X) := 
begin
  have A1 := hahn_crazy_diff_big_spec μ ν X H,
  apply A1.left,
end


lemma lt_of_hahn_crazy_diff_big {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):
  ν (hahn_crazy_diff_big μ ν X H) < μ (hahn_crazy_diff_big μ ν X H) := 
begin
  have A1 := hahn_crazy_diff_big_mem μ ν X H,
  rw hahn_crazy_diff_set_def at A1,
  simp at A1,
  apply A1.right.right,
end


lemma hahn_crazy_set_of_hahn_crazy_diff_big {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):
  (hahn_crazy_set μ ν (X \ (hahn_crazy_diff_big μ ν X H))) :=
begin
  have B1:=hahn_crazy_diff_big_mem μ ν X H,
  rw hahn_crazy_diff_set_def at B1,
  simp at B1,
  apply hahn_crazy_set_subset,
  {
    apply H,
  },
  {
    -- ⊢ hahn_crazy_diff_big μ ν X H ⊆ X
    apply B1.left,
  },
  {
    apply B1.right.left,
  },
  {
    apply le_of_lt B1.right.right,
  },
end

def next_hahn_crazy_set {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:subtype (hahn_crazy_set μ ν)):
  subtype (hahn_crazy_set μ ν) := subtype.mk 
      (X.1 \ (hahn_crazy_diff_big μ ν X.1 X.2))
      (hahn_crazy_set_of_hahn_crazy_diff_big μ ν X.1 X.2)

lemma next_hahn_crazy_set_val {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (S:set α) (H:hahn_crazy_set μ ν S):
  ((next_hahn_crazy_set μ ν (subtype.mk S H)):set α) =
      (S \ (hahn_crazy_diff_big μ ν S H)) := rfl

lemma set.diff_diff_eq_of_subset {α:Type*} (S T:set α):S ⊆ T →
  T \ (T \ S) = S :=
begin
  intro A1,
  ext a,split;intros B1,
  {
    rw set.mem_diff at B1,
    cases B1 with B1 B2,
    rw set.mem_diff at B2,
    simp at B2,
    apply B2 B1,
  },
  {
    simp,
    rw set.subset_def at A1,
    apply and.intro (A1 a B1), 
    intro C1,
    apply B1,
  },
end

lemma next_hahn_crazy_set_diff {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (S:set α) (H:hahn_crazy_set μ ν S):
  S \ (next_hahn_crazy_set μ ν (subtype.mk S H)) =
      (hahn_crazy_diff_big μ ν S H) := 
begin
  rw next_hahn_crazy_set_val,
  apply set.diff_diff_eq_of_subset (hahn_crazy_diff_big μ ν S H) S,
  have B1:=hahn_crazy_diff_big_mem μ ν S H,
  rw hahn_crazy_diff_set_def at B1,
  cases B1 with B1 B2,
  apply B1,
end

/-- Given a crazy set, we can repeatedly cut away big elements of
hahn_crazy_diff_sets.-/
def nth_hahn_crazy_set {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:subtype (hahn_crazy_set μ ν)):
  ℕ → subtype (hahn_crazy_set μ ν)
  | 0 := X
  | (nat.succ n) := next_hahn_crazy_set μ ν (nth_hahn_crazy_set n)

lemma neg_monotone_of_succ_le {α:Type*} [partial_order α] {f:ℕ → α}:
  (∀ n:ℕ, f (n.succ) ≤ f n) →
  (∀ i j, i ≤ j → f j ≤ f i) :=
begin
  intros A1,
  intros i j,
  induction j,
  {
    intro B1,
    simp at B1,
    subst i,
  },
  {
    intro C1,
    cases C1 with C1 C1,
    apply le_refl _,
    have C2 := j_ih C1,
    apply le_trans (A1 j_n) C2,
  },
end

lemma directed_superset_of_monotone {α:Type*} {f:ℕ → set α}:
  (∀ n:ℕ,  f n.succ ⊆ f n) → directed superset f :=
begin
  intros A1,
  unfold directed superset,
  intros x y,
  apply exists.intro (max x y),
  split,
  {
    rw ← set.le_eq_subset,
    apply @neg_monotone_of_succ_le (set α) _ f  A1,
    apply le_max_left,
  },
  {
    rw ← set.le_eq_subset,
    apply @neg_monotone_of_succ_le (set α) _ f  A1,
    apply le_max_right,
  },
end

lemma measure_Inter_eq_infi_nat' {α:Type*} [measurable_space α]
  {μ:measure_theory.measure α} {f:ℕ → set α}:
  (∀ n:ℕ,  f n.succ ⊆ f n) →
  (∀ n, is_measurable (f n)) →
  (μ (f 0) < ⊤) → 
  μ (⋂ n, f n) =  ⨅ n, μ (f n)  :=
begin
  intros A1 A2 A3,
  apply measure_theory.measure_Inter_eq_infi,
  apply A2,
  {
    apply directed_superset_of_monotone A1,
  },
  apply exists.intro 0,
  apply A3,
end

lemma measure_monotone_finite {α:Type*} [measurable_space α]
  {μ:measure_theory.measure α} {f:ℕ → set α}:
  (∀ n:ℕ,  f n.succ ⊆ f n) →
  (∀ n, is_measurable (f n)) →
  (μ (f 0) < ⊤) →
  (∀ n, μ (f n) < ⊤) :=
begin
  intros A1 A2 A3,
  intro n,
  induction n,
  {
    apply A3,
  },
  {
    have B1:μ (f (n_n.succ)) ≤ μ (f (n_n)),
    {
      apply measure_theory.measure_mono,
      apply A1,
    },
    apply lt_of_le_of_lt B1,
    apply n_ih,
  },
end



--∀ᶠ
--All of the variants of has_classical_limit follow easily from this.
lemma has_classical_limit_nonneg {β:Type*} [ordered_add_comm_monoid β] [topological_space β]
  [order_topology β]
  [t2_space β] (f:ℕ → β) (v:β):(0≤ f) →
  (∀ z<v, ∃ m,  z < (finset.sum (finset.range m) f))  →
  (∀ m', (finset.sum (finset.range m') f) ≤ v) →
  has_sum f v
  :=
begin
  intros A1 A2 A3,
  unfold has_sum,
  rw tendsto_order,
  split,
  {
    intros x B1,
    rw filter.eventually_iff,
    simp,
    have B2 := A2 x B1,
    cases B2 with m B2,
    apply exists.intro (finset.range m),
    intros T B3,
    apply lt_of_lt_of_le B2,
    apply finset.sum_monotone_of_nonnegative A1 B3,
  },
  {
    intros b C1,
    rw filter.eventually_iff,
    simp,
    apply exists.intro finset.empty,
    intros T C2,
    apply lt_of_le_of_lt _ C1,
    have C3:∃ m, T ⊆ (finset.range m) := finset_range_bound T,
    cases C3 with m C3,
    apply le_trans _ (A3 m),
    apply finset.sum_monotone_of_nonnegative A1 C3,
  },
end




--Not quite the classical way of thinking about a limit, but
--more practical for nonnegative sums.
--See has_classical_limit_nnreal' 
lemma has_classical_limit_ennreal (f:ℕ → ennreal) (v:ennreal):
  (∀ z<v, ∃ m,  z < (finset.sum (finset.range m) f))  →
  (∀ m', (finset.sum (finset.range m') f) ≤ v) →
  has_sum f v
  :=
begin
  intros A1 A2,
  apply has_classical_limit_nonneg,
  {
    apply @nonnegative_fn ℕ ennreal _,
  },
  {
    apply A1,
  },
  {
    apply A2,
  },
end




lemma ennreal_telescope_helper2 {f:ℕ → ennreal} {m:ℕ}:
  (∀ n:ℕ,  f n.succ ≤ f n) →
  (f 0) - (f m) = (finset.range m).sum (λ n, (f n) - (f n.succ)) :=
begin
  intros A1,
  induction m,
  {
    simp,
  },
  {
    rw finset.range_succ,
    simp,
    rw ← m_ih,
    rw add_comm,
    symmetry,
    apply ennreal.sub_add_sub,
    apply A1,
    apply neg_monotone_of_succ_le A1,
    simp,
  },
end




lemma Inf_lt {α:Type*} [complete_linear_order α]
   {S:set α} {z:α}:S.nonempty →
  Inf S < z → ∃ s∈ S, s < z :=
begin
  intros A1 A2,
  apply classical.exists_of_not_forall_not,
  intro A3,
  have A4:z ≤ Inf S,
  {
    apply @le_Inf α _ _,
    intros b A4A,
    have A4B := A3 b,
    rw not_exists_iff_forall_not at A4B,
    have A4C := A4B A4A,
    apply le_of_not_lt A4C,
  },
  apply not_lt_of_le A4,
  apply A2,
end 



lemma infi_lt {α β:Type*} [nonempty α] [complete_linear_order β] 
  {f:α → β} {z:β}:
  infi f < z → ∃ a, f a < z :=
begin
  intro A1,
  have B1:(set.range f).nonempty,
  {
    apply set.range_nonempty,
  },
  have B2:(Inf (set.range f)) < z,
  {
    unfold infi at A1,
    apply A1,
  },
  have B3:=Inf_lt B1 B2,
  cases B3 with x B3,
  cases B3 with B3 B4,
  cases B3 with a B3,
  apply exists.intro a,
  subst x,
  apply B4,
end 


lemma ennreal_infi_diff {f:ℕ → ennreal} {z:ennreal}:z < f 0 - infi f →
  ∃ n, z < f 0 - f n := 
begin
  intros A1,
  have B1:infi f ≤ f 0 := @infi_le ennreal _ _ f 0,
  have B2:= ennreal.add_lt_of_lt_sub A1,
  rw add_comm at B2,
  have B3 := ennreal.lt_sub_of_add_lt B2,
  have B4 := infi_lt B3,
  cases B4 with n B4,
  apply exists.intro n,
  apply ennreal.lt_sub_of_add_lt,
  rw add_comm,
  apply ennreal.add_lt_of_lt_sub,
  apply B4,
end


lemma ennreal_telescope_helper {f:ℕ → ennreal}:
  (∀ n:ℕ,  f n.succ ≤ f n) →
  (f 0) - (infi f) = (∑' n, (f n) - (f n.succ)) :=
begin
  intro A1,
  symmetry,
  rw ← summable.has_sum_iff (ennreal.summable),
  apply has_classical_limit_ennreal,
  {
    intros z B1,
    have B2 := ennreal_infi_diff B1,
    cases B2 with n B2,
    apply exists.intro n,
    rw ← ennreal_telescope_helper2 A1,
    apply B2,
  },
  {
    intro m,
    rw ← ennreal_telescope_helper2 A1,
    simp,
    apply ennreal.le_sub_add,
    apply @infi_le ennreal ℕ _,
    apply neg_monotone_of_succ_le A1,
    simp,
  },
end

lemma ennreal_telescope {f:ℕ → ennreal}:
  (∀ n:ℕ,  f n.succ ≤ f n) →
  (f 0) = (∑' n, (f n) - (f n.succ)) + (infi f) :=
begin
  intros A1,
  have B1 := ennreal_telescope_helper A1,
  rw add_comm,
  apply ennreal.eq_add_of_sub_eq _ B1,   
  apply @infi_le ennreal _ _,
end


lemma measure_Inter_telescope {α:Type*} [measurable_space α]
  {μ:measure_theory.measure α} {f:ℕ → set α}:
  (∀ n:ℕ,  f n.succ ⊆ f n) →
  (∀ n, is_measurable (f n)) →
  (μ (f 0) < ⊤) →
  μ (f 0) = (∑' n, μ (f n \ (f (n.succ)))) + μ (⋂ n, f n) := 
begin
  intros A1 A2 A3,
  rw measure_Inter_eq_infi_nat' A1 A2 A3,
  have B1:(λ n, μ (f n \ (f (n.succ))))=(λ n, μ (f n) - μ (f (n.succ))),
  {
    apply funext,
    intro n,
    have B1A:μ (f n \ f (n.succ))=μ (f n \ (f (n.succ))) := rfl,
    rw B1A,
    rw measure_theory.measure_diff,
    apply A1,
    apply A2,
    apply A2,
    apply measure_monotone_finite A1 A2 A3,
  },
  rw B1,
  apply @ennreal_telescope (μ ∘ f),
  intro n,
  apply measure_theory.measure_mono,
  apply A1,
end


lemma measure_Inter_telescope' {α:Type*} [measurable_space α]
  {μ:measure_theory.measure α} {f:ℕ → set α}:
  (∀ n:ℕ,  f n.succ ⊆ f n) →
  (∀ n, is_measurable (f n)) →
  (μ (f 0) < ⊤) →
  μ (⋂ n, f n) =
  μ (f 0) - (∑' n, μ (f n \ (f (n.succ)))) := 
begin
  intros A1 A2 A3,
  have B1 := measure_Inter_telescope A1 A2 A3,
  rw B1,
  rw add_comm,
  simp,
  rw ennreal.add_sub_cancel,
  rw B1 at A3,
  apply lt_of_le_of_lt _ A3,
  apply @le_add_nonnegative ennreal _ _ _,
end


lemma lt_Sup {α:Type*} [complete_linear_order α]
   {S:set α} {z:α}:S.nonempty →
  z < Sup S  → ∃ s∈ S,  z < s :=
begin
  intros A1 A2,
  apply classical.exists_of_not_forall_not,
  intro A3,
  have A4:Sup S ≤ z,
  {
    apply @Sup_le α _ _,
    intros b A4A,
    have A4B := A3 b,
    rw not_exists_iff_forall_not at A4B,
    have A4C := A4B A4A,
    apply le_of_not_lt A4C,
  },
  apply not_lt_of_le A4,
  apply A2,
end 



lemma lt_supr {α β:Type*} [nonempty α] [complete_linear_order β] 
  {f:α → β} {z:β}:
  z < supr f → ∃ a, z < f a :=
begin
  intro A1,
  have B1:(set.range f).nonempty,
  {
    apply set.range_nonempty,
  },
  have B2:z < (Sup (set.range f)),
  {
    unfold supr at A1,
    apply A1,
  },
  have B3:= lt_Sup B1 B2,
  cases B3 with x B3,
  cases B3 with B3 B4,
  cases B3 with a B3,
  apply exists.intro a,
  subst x,
  apply B4,
end 


--This is true WITHOUT the non-negative part. So long as the sum is 
--well-defined, this should be true.
--Revisit later (and search mathlib).
lemma ennreal.tendsto_zero_of_finite_sum (f:ℕ → ennreal):tsum f < ⊤ →
  filter.tendsto f filter.at_top (nhds 0) :=
begin
  intro A1,
  rw tendsto_order,
  split,
  {
    intros a B1,
    exfalso,
    simp at B1,
    apply B1,
  },
  {
    intros x C1,
    rw filter.eventually_iff,
    simp,
    have C2:=ennreal.exists_coe A1,
    cases C2 with v C2,
    have C5:(⨆  n, (finset.range n).sum f)  = (v:ennreal),
    {
      rw ennreal.lim_finset_sum_eq_tsum,
      apply C2,
    },
    cases (lt_or_le x (v:ennreal)) with C4 C4,
    { -- C4 : a < ↑v
      have D1:(v:ennreal) - x < (⨆ (n : ℕ), (finset.range n).sum f),
      {
        rw C5,
        simp,
        apply ennreal.coe_sub_lt_self,
        have D1A:0 < (v:ennreal),
        {
          apply lt_trans C1 C4,
        },
        simp at D1A,
        apply D1A,
        apply C1,
      },
      have D2 := lt_supr D1,
      cases D2 with b D2,
      apply exists.intro b,
      intros c D3,
      have D4:(finset.range (c.succ)).sum f ≤ (v:ennreal),
      {
        rw ← C5,
        apply @le_supr ennreal ℕ _,
      },
      have D5:0 ≤ b,
      {
        simp,
      },
      have D6:b ≤ c.succ,
      {
        apply le_trans D3,
        apply nat.le_succ,
      },
      rw ← finset.Ico.zero_bot at D4,
      have D7:disjoint (finset.Ico 0 b) (finset.Ico b c.succ),
      {
        apply finset.Ico.disjoint_consecutive,
      },
      rw ← finset.Ico.union_consecutive D5 D6 at D4,
      rw finset.sum_union D7 at D4,
      rw finset.Ico.zero_bot at D4,
      -- b' + c'' ≤ v
      -- c' ≤ c''
      -- v - x < b' 
      -- ⊢ c' < x
      -- Working here.
      have D8:f c ≤ (finset.Ico b c.succ).sum f,
      {
        apply @finset.element_le_sum ℕ ennreal _ _,
        {
          simp [D3,lt_succ], 
        }, 
      },
      have D9:(v:ennreal) < ⊤,
      {
        simp,
      },
      apply ennreal.lt_of_add_le_of_le_of_sub_lt D9 D4 D8 D2,      
    },

    cases (@eq_or_ne nnreal _ v 0) with C6 C6,
    {
      subst v,
      apply exists.intro 0,
      intros n E1,
      simp at C5,
      have E2:(finset.range (n.succ)).sum f ≤ 0,
      {
        rw ← C5,
        apply @le_supr ennreal ℕ _,
      },
      simp at C1,
      apply lt_of_le_of_lt _ C1,
      apply le_trans _ E2,  
      apply @finset.element_le_sum ℕ ennreal _ _ _ n f,
      {
        simp,
      },
    },
    {
      have F1:0 < v,
      {
        rw lt_iff_le_and_ne,
        split,
        simp,
        symmetry,
        apply C6,
      },
      have F2:0 < (⨆ (n : ℕ), (finset.range n).sum f),
      {
        rw C5,
        simp,
        apply F1,
      },
      have F3 := lt_supr F2,
      cases F3 with a F3,
      apply exists.intro a,
      intros b F4,
      apply lt_of_lt_of_le _ C4,
      have F5:(finset.range (b.succ)).sum f ≤ (v:ennreal),
      {
        rw ← C5,
        apply @le_supr ennreal ℕ _,
      },
      have F6:0 ≤ a,
      {
        simp,
      },
      have F7:a ≤ b.succ,
      {
        apply le_trans F4,
        apply nat.le_succ,
      },
      rw ← finset.Ico.zero_bot at F5,
      have F8:disjoint (finset.Ico 0 a) (finset.Ico a b.succ),
      {
        apply finset.Ico.disjoint_consecutive,
      },
      rw ← finset.Ico.union_consecutive F6 F7 at F5,
      rw finset.sum_union F8 at F5,
      rw finset.Ico.zero_bot at F5,
      have F9:f b ≤ (finset.Ico a b.succ).sum f,
      {
        apply @finset.element_le_sum ℕ ennreal _ _,
        {
          simp [F4,lt_succ], 
        }, 
      },
      have F10:(v:ennreal) < ⊤,
      {
        simp,
      },
      have F11: (finset.range a).sum (λ (x : ℕ), f x) + f b ≤ ↑v,
      {
        apply le_trans _ F5,
        apply add_le_add_left F9,
      },
      apply ennreal.lt_of_lt_top_of_add_lt_of_pos F10 F11 F3,      
    },
  },
end

lemma filter.tendsto_const {α β:Type*} [topological_space β]
    {v:β} {F:filter α}:
    filter.tendsto (λ n:α, v) F (nhds v) :=
begin
  apply filter.tendsto.mono_right (filter.tendsto_const_pure) (pure_le_nhds v),
end


/-- If a function is bracketed by two functions that converge to the same value,
then it too converges to that value. -/
lemma filter.tendsto_le {α β:Type*} [topological_space β]
    [partial_order β] [order_topology β] {F:filter α} 
    {f g h:α  → β} {v:β}:
    f ≤ g →
    g ≤ h →
    filter.tendsto f F (nhds v) →
    filter.tendsto h F (nhds v) →
    filter.tendsto g F (nhds v) :=
begin
  intros A1 A2 A3 A4,
  rw tendsto_order,
  split,
  {
    intros x B1,
    rw filter.eventually_iff,
    rw tendsto_order at A3,
    have B2 := A3.left x B1,
    rw filter.eventually_iff at B2,
    have B4: {x_1 : α | x < f x_1}⊆ {x_1 : α | x < g x_1},
    {
      rw set.subset_def,
      intros a B4A,
      simp at B4A,
      simp,
      apply lt_of_lt_of_le B4A (A1 a),
    },
    apply filter.sets_of_superset F B2 B4,
  },
  {
    intros x B1,
    rw filter.eventually_iff,
    rw tendsto_order at A4,
    have B2 := A4.right x B1,
    rw filter.eventually_iff at B2,
    have B4: {x_1 : α | h x_1 < x}⊆ {x_1 : α | g x_1 < x},
    {
      rw set.subset_def,
      intros a B4A,
      simp at B4A,
      simp,
      apply lt_of_le_of_lt (A2 a) B4A,
    },
    apply filter.sets_of_superset F B2 B4,
  },
end


--Extend to nonnegative type (well, nnreal).
lemma ennreal.tendsto_le {α:Type*} {F:filter α} {g h:α  → ennreal}:
    g ≤ h →
    filter.tendsto h F (nhds 0) →
    filter.tendsto g F (nhds 0) :=
begin
  intros A1 A2,
  let f:α → ennreal := (λ a:α, 0),
  begin
    have B1:f = (λ a:α, 0) := rfl,
    have B2:f ≤ g,
    {
      rw B1,
      intros a,
      simp,
    },
    have B3:filter.tendsto f F (nhds 0),
    {
      apply filter.tendsto_const,
    },
    apply filter.tendsto_le B2 A1 B3 A2,
  end
end

lemma set.preimage_subset_preimage_of_subset {α β:Type*} {S T:set α} {f:β  → α}:
  (S⊆ T)→ set.preimage f S ⊆  set.preimage f T :=
begin
--{x:β |f x ∈ S} ⊆ {x:β |f x ∈ T} :=
  intro A1,
  have B1:set.preimage f S = {x:β |f x ∈ S} := rfl,
  have B2:set.preimage f T = {x:β |f x ∈ T} := rfl,
  rw B1,
  rw B2,
  apply set.preimage_mono,
  apply A1,
end

--∀ᶠ (b : ℕ) in filter.at_top, f b < x
lemma tendsto_top {α β:Type*} [NE:nonempty β] [SL:semilattice_sup β] {g:α → β} {F:filter α}:filter.tendsto g F filter.at_top ↔ (∀ b:β,  ∀ᶠ (c:α) in F, b ≤ g c) :=
begin
  split;intros A1,
  {
    rw filter.tendsto_iff_eventually at A1,
    intro b,apply A1,
    rw filter.eventually_iff,
    simp,
    apply exists.intro b,
    intros b_1,
    simp,
  },
  {
    rw filter.tendsto_def,
    intros S C1,
    rw filter.mem_at_top_sets at C1,
    cases C1 with a C1,
    have C2 := A1 a,
    rw filter.eventually_iff at C2,
    apply filter.mem_sets_of_superset C2,
    apply set.preimage_subset_preimage_of_subset,
    rw set.subset_def,
    intros b C3,
    apply C1,
    apply C3,
  },
end

lemma eventually_at_top_iff {α:Type*} [nonempty α] [semilattice_sup α] {P:α → Prop}:
  (∀ᶠ (c:α) in filter.at_top,  P c) ↔ ∃ (a : α), ∀ (b : α), b ≥ a → b ∈ {x : α | P x}:=
begin
  rw filter.eventually_iff,
  split;intros A1,
  {
    rw filter.mem_at_top_sets at A1,
    ---cases A1 with a A1,
    apply A1,
  },
  {
    rw filter.mem_at_top_sets,
    apply A1,
  },
end


lemma floor_simple_fraction_def (x:ennreal):floor_simple_fraction x = Inf {n:ℕ|(n:ennreal) ≥ x⁻¹} := rfl



lemma floor_simple_fraction_bound (b:ℕ) (x:ennreal):0 < x →
x < (1/(b:ennreal)) →
b ≤ floor_simple_fraction x := 
begin
  intros A1 A2,
  cases b,
  {
    simp,
  },
  rw floor_simple_fraction_def,
  
  apply @nat.le_Inf,
  {
    simp,
    cases x,
    {
      simp,
    },
    simp,
    simp at A1,
    have A3 := nnreal.exists_unit_frac_lt_pos A1,
    cases A3 with a A3,
    have A4 := le_of_lt A3,
    rw nnreal.inv_as_fraction at A4,
    have A6 := nnreal.inverse_le_of_le _ A4,
    rw nnreal.inv_inv at A6,
    rw set.nonempty_def,
    apply exists.intro a.succ,
    simp,
    rw ← ennreal.coe_inv,
    have A7:((a + 1:nnreal):ennreal) = (a:ennreal) + 1,
    {
      simp,
    },
    rw ← A7,
    rw ennreal.coe_le_coe,
    apply A6,
    {
      intro B1,
      subst x,
      simp at A1,
      apply A1,
    },
    {
      rw nnreal.inv_pos,
      rw add_comm,
      have B2:(0:nnreal) < (1:nnreal) := zero_lt_one,
      apply lt_of_lt_of_le B2,
      apply le_add_nonnegative _ _,
    },
  },
  {
    intros c C1,
    simp at C1,
    simp at A2,
    have C2:(1:ennreal)/(c:ennreal) ≤ x,
    {
      rw ennreal.inv_as_fraction,
      rw ← @ennreal.inv_inv x,
      apply ennreal.inverse_le_of_le,
      have C2A:x < ⊤,
      {
        apply lt_trans A2,
        rw ennreal.inv_as_fraction,
        simp,
        rw add_comm,
        
        apply @lt_of_lt_of_le ennreal _ 0 1 _
              (ennreal.zero_lt_one),
        apply le_add_nonnegative 1 (b:ennreal),
      },
      rw lt_top_iff_ne_top at C2A,
      rw ← ennreal.inv_pos at C2A,
      apply C1,
    },
    have C3 := lt_of_le_of_lt C2 A2,
    have C4 := le_of_lt C3,
    rw ennreal.inv_as_fraction at C4,
    rw ennreal.inv_as_fraction at C4,
    have C5 := ennreal.inverse_le_of_le C4,
    rw ennreal.inv_inv at C5,
    rw ennreal.inv_inv at C5,
    have C6:((1:nat):ennreal) = (1:ennreal),
    {
      simp,
    },
    rw ← C6 at C5,    
    rw ennreal.nat_coe_add at C5,
    rw ennreal.nat_coe_le_coe at C5,
    apply C5,
  },
end

/-- If positive g approaches zero, then (floor_simple_fraction ∘ g )approaches infinity. -/
lemma floor_simple_fraction_limit_top {g:ℕ  → ennreal}:
    (∀ n, 0 < g n) →
    filter.tendsto g filter.at_top (nhds 0) →
    filter.tendsto (floor_simple_fraction∘ g) filter.at_top filter.at_top :=
begin
  intros AX A1,
  rw tendsto_order at A1,
  cases A1 with A1 A2,
  clear A1,
  rw tendsto_top,
  intro b,
  rw eventually_at_top_iff,
  have B1:((1:ennreal)/(b.succ:ennreal)) > 0,
  {
    simp,
    have B1A:(b:ennreal) = ((b:nnreal):ennreal),
    {
      simp,
    },
    rw B1A,
    have B1B:(1:ennreal) = ((1:nnreal):ennreal),
    {
      simp,
    },
    rw B1B,
    rw ← ennreal.coe_add,
    apply ennreal.coe_ne_top,
  },
  have B2 := A2 ((1:ennreal)/(b.succ:ennreal)) B1,
  rw eventually_at_top_iff at B2,
  cases B2 with a B2,
  apply exists.intro a,
  intros c B3,
  have B4 := B2 c B3,
  simp,
  simp at B4,
  have B5:b ≤ b.succ,
  {
    apply nat.le_succ,
  },
  apply le_trans B5,
  apply floor_simple_fraction_bound,
  apply AX,
  apply B4
end

/-
  This is the crux of the hahn decomposition theorem, the key of a proof by induction by
  contradiction. We assume that there is a set X where μ X < ν X and v X < ⊤, and there 
  does not exista a subset X' ⊆ X where μ X' < ν X', where for all X''⊆ X', μ X'' ≤ ν X''.

  The proof follows the contradiction part in An Epsilon of Room. If such a hahn crazy set
  existed, then we could find a set Y ⊆ X where ν Y < μ Y. And if we subtracted this set
  off, we would be back where we started with X-Y being a set where μ (X - Y) < ν (X - Y) 
  and no subset X' ⊆ X - Y where μ X' < ν X' and μ.restrict X' ≤ ν.restrict X'. 

  What if we want to grab a set Y which maximizes μ Y - ν Y?
  Unfortunately, we find this as hard as the entire Hahn decomposition
  problem itself. But we don't need to find the biggest one, just one 
  that is big enough. What follows is one of the most unusual mathematical 
  tricks I have seen. We basically chunk the reals into (1,∞],(1/2,1],(1/3,1/2],
  et cetera. Instead of grabbing the absolute largest element, we grab an
  element in the first populated range. Thus, if we do this an infinite number
  of times, either the values we get sum to infinity (which they can't),
  or each range gets eventually depopulated. Thus, after this point, any remaining
  set must have μ Y - ν Y=0, a contradiction.
 -/
lemma hahn_crazy_set_not_finite {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α):
  (hahn_crazy_set μ ν X) →
  ¬(measure_theory.finite_measure ν) :=
begin
  intros A1 A2,
  let h:ℕ → set α :=
      (λ n, (nth_hahn_crazy_set μ ν (subtype.mk X A1) n).val),
  let d:ℕ → (set α) :=
      λ n, h n \ h (n.succ),
  let Z:=⋂ n, (h n),
  begin
    have B1:h =λ n, (nth_hahn_crazy_set μ ν (subtype.mk X A1) n).val := rfl,
    have B2:d = λ n, h (n) \ h (n.succ) := rfl,
    have B3:Z = ⋂ n, (h n) := rfl,
    have B4:(h 0) = X,
    {
      rw B1,
      refl,
    },
    have B5:∀ n:ℕ, nth_hahn_crazy_set μ ν (subtype.mk X A1) (nat.succ n)
           = next_hahn_crazy_set μ ν (nth_hahn_crazy_set μ ν (subtype.mk X A1) (n)),
    {
      intro n,
      refl,
    },
    have B6:∀ n:ℕ, h (n.succ) = next_hahn_crazy_set μ ν (nth_hahn_crazy_set μ ν (subtype.mk X A1) (n)),
    {
      intro n,
      rw B1,
      refl,
    },
    have J0:∀ n:ℕ, (hahn_crazy_set μ ν (h n)),
    {
      intros n,
      rw B1,
      apply (nth_hahn_crazy_set μ ν (subtype.mk X A1) n).property,
    },
    have J0B:∀ n:ℕ, h (n.succ) = next_hahn_crazy_set μ ν  
             (subtype.mk (h n) (J0 n)),
    {
      intro n,
      rw B6,
      refl,
    },
    have J1:∀ n:ℕ, h (n.succ) ⊆ h n,
    {
      intro n,
      rw J0B,
      unfold next_hahn_crazy_set,
      apply set.diff_subset,
    },
    have J2:∀ n:ℕ, is_measurable (h n),
    {
      intro n,
      have J2A := J0 n,
      rw hahn_crazy_set_def' at J2A,
      apply J2A.right.left,  
    },
    have C1A:ν  (h 0) < ⊤,
    {
      rw B4,
      apply @measure_theory.measure_lt_top α M ν A2 X,
    },
    have J4:μ (h 0) < ν (h 0),
    {
       rw B4,
       rw hahn_crazy_set_def' at A1,
       apply A1.left,
    },
    have C1:ν Z = ν (h 0) - (∑' n, ν (d n)),
    {
      rw B3,
      rw B2,
      simp,
      apply @measure_Inter_telescope' α M ν h J1 J2 C1A,
    },
      have C2A:μ  (h 0) < ⊤,
      {
        apply lt_trans J4 C1A,
      },

    have C2:μ Z = μ (h 0) - (∑' n, μ (d n)),
    {
      rw B3,
      rw B2,
      apply @measure_Inter_telescope' α M μ h J1 J2 C2A,
    },
    have C3C:(∑' (n : ℕ), μ (d n)) ≤ μ (h 0),
    {  
      rw measure_Inter_telescope J1 J2 C2A,
      have C3B1:(∑' (n : ℕ), μ (d n)) =
                (∑' (n : ℕ), μ (h n \ h n.succ)) := rfl,
      rw ← C3B1,
      apply le_add_nonnegative _ _,
    },
    have C3X:(∑' (n : ℕ), ν (d n)) ≤ ν (h 0),
    {  
      rw measure_Inter_telescope J1 J2 C1A,
      have C3B1:(∑' (n : ℕ), ν (d n)) =
                (∑' (n : ℕ), ν (h n \ h n.succ)) := rfl,
      rw ← C3B1,
      apply le_add_nonnegative _ _,
    },

    have C3:μ Z < ν Z,
    {
      rw C1,
      rw C2,
      apply ennreal.sub_lt_sub_of_lt_of_le,
      {
        rw B4,
        rw hahn_crazy_set_def' at A1,
        apply A1.left,
      },
      {
        apply tsum_le_tsum _ ennreal.summable ennreal.summable,
        intro n,
        rw B2,
        simp,
        rw J0B,
        rw next_hahn_crazy_set_diff,
        have C3A1:= hahn_crazy_diff_big_mem μ ν (h n) (J0 n),
        rw hahn_crazy_diff_set_def at C3A1,
        apply le_of_lt (C3A1.right.right),
      },
      {
        apply C3C,
      },
    },
    have D1:is_measurable Z,
    {
      apply is_measurable.Inter,
      apply J2,
    },
    have D3:Z ⊆ X,
    {
      rw B3,
      rw ← B4,
      simp,
      apply set.Inter_subset,
    },
    have D2:hahn_crazy_set μ ν Z,
    {
      rw hahn_crazy_set_def',
      apply and.intro C3,
      apply and.intro D1,
      intros X' D2A D2B,
      rw hahn_crazy_set_def' at A1,
      apply A1.right.right,
      apply set.subset.trans D2A D3,
      apply D2B,
    },
    have D3:filter.tendsto 
      (λ n:ℕ, μ (d n)) filter.at_top (nhds 0),
    {
      --There is a sequence of positive numbers with a finite sum.
      --Thus, their limit must be zero.
      apply ennreal.tendsto_zero_of_finite_sum,
      apply lt_of_le_of_lt C3C C2A,
    },
    have D3B:filter.tendsto 
      (λ n:ℕ, ν (d n)) filter.at_top (nhds 0),
    {
      --This is definitely true, but I am not sure if I need it,
      --or D3 above is what is needed. I need to walk through the
      --rest of this proof.
      apply ennreal.tendsto_zero_of_finite_sum,
      apply lt_of_le_of_lt C3X C1A,
    },
    have D4:filter.tendsto 
      (λ n:ℕ, Inf ((floor_simple_fraction ∘ (λ X':set α, μ X' - ν X'))
       ''(hahn_crazy_diff_set ν μ (h n))))  filter.at_top filter.at_top,
    {
      --I reversed this: I need to figure out if I can make the rest of the proof work.
      --Now, I need to reverse it back.
      have D4A:(λ n:ℕ, Inf ((floor_simple_fraction ∘ (λ X':set α, μ X' - ν X'))
       ''(hahn_crazy_diff_set ν μ (h n)))) = 
         (λ n:ℕ, (floor_simple_fraction ∘ (λ X':set α,  μ X' - ν X'))
                (hahn_crazy_diff_big μ ν (h n) (J0 n))),
      {
        -- J0 n:hahn_crazy_set μ ν (h n)
        apply funext,
        intro n,
        symmetry,
        apply @hahn_crazy_diff_big_Inf α _ μ ν (h n) (J0 n),
        
      },
      have D4B:∀ n, (hahn_crazy_diff_big μ ν (h n) (J0 n)) = d n,
      {
        intro n,
        rw B2,
        simp,
        rw ← next_hahn_crazy_set_diff,
        rw J0B,
      },
      have D4C:(λ n:ℕ, Inf ((floor_simple_fraction ∘ (λ X':set α, μ X' - ν X'))
       ''(hahn_crazy_diff_set ν μ (h n)))) = 
         (λ n:ℕ, (floor_simple_fraction ∘ (λ X':set α,  μ X' - ν X'))
                (d n)),
      {
        rw D4A,
        apply funext,
        intro n,
        rw D4B n,
      },
      have D4E: (λ n:ℕ, (λ X':set α,  μ X' - ν X')
                (d n)) ≤ (λ n:ℕ, μ (d n)),
      {
        intro n,
        simp,
        apply le_add_nonnegative _ _,
      },
  
      have D4G:∀ n, ν (d n) < μ (d n),
      {
        intro n,
        rw ← D4B,
        apply @lt_of_hahn_crazy_diff_big α _ μ ν (h n),
      },
      have D4F:filter.tendsto (λ n:ℕ,  (λ X':set α,  μ X' - ν X')
                (d n)) filter.at_top (nhds (0:ennreal)),
      {
        apply ennreal.tendsto_le D4E D3,  
      },
      rw D4C,
      apply floor_simple_fraction_limit_top,
      {
        intro n,
        simp,
        rw ← D4B,
        apply @lt_of_hahn_crazy_diff_big α _ μ ν (h n),
      },
      apply D4F,
    },
    have E1:(hahn_crazy_diff_set ν μ Z).nonempty,
    {
      apply hahn_crazy_diff_set_nonempty' ν μ Z D2,
    },
    have E2:∃ S, S∈(hahn_crazy_diff_set ν μ Z),
    {
      apply set.nonempty_def.mp E1,
    },
    cases E2 with S E2,
    rw hahn_crazy_diff_set_def at E2,
    simp at E2,
    let n := floor_simple_fraction (μ S - ν S),
    begin
      have G1:n = floor_simple_fraction (μ S - ν S) := rfl,
      have H1: {m:ℕ| n.succ ≤ m} ∈ filter.at_top,
      {
        apply filter.mem_at_top,
      },
      have H2 := filter_tendsto_elim D4 H1,
      simp at H2,
      cases H2 with n2 H2,
      have H3 := H2 n2 (le_refl n2),
      have H4:Inf ((λ (a : set α), floor_simple_fraction (μ a - ν a)) '' hahn_crazy_diff_set ν μ (h n2))
              ≤ n,
      {
        apply nat.Inf_le,
        simp,
        apply exists.intro S,
        split,
        {
          rw hahn_crazy_diff_set_def,
          simp,
          split,
          {
             apply @set.subset.trans α S Z (h n2) E2.left,
             rw B3,
             apply set.Inter_subset,
           },
           apply (E2.right),
         },
         rw G1,
      },
      have H5 := le_trans H3 H4,
      apply not_lt_of_le H5,
      apply nat.lt.base,
    end
  end
end



lemma finite_set_not_hahn_crazy_set {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α)
  [F:measure_theory.finite_measure ν]: 
  ¬ (hahn_crazy_set μ ν X)  :=
begin
 intros A2,
 apply hahn_crazy_set_not_finite μ ν X A2 F, 
end

/-- This theorem is a weak variant of hahn_unsigned_inequality_decomp.
However, it probably has uses in its own right, beyond that of
its parent theorem.
 -/
lemma hahn_unsigned_inequality_decomp_junior' {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) {X:set α} [A1:measure_theory.finite_measure ν]:
    (is_measurable X) →
    (μ X < ν X) → 
    (∃ X':set α, 
      X' ⊆ X ∧
      μ X' < ν X' ∧
      is_measurable X' ∧
      μ.restrict X' ≤ ν.restrict X') :=
begin
  intros A2 A3,
  have B1:= @finite_set_not_hahn_crazy_set _ _ μ ν X A1,
  rw hahn_crazy_set_def' at B1,
  simp at B1,
  have B2 := B1 A3 A2,
  cases B2 with X' B2,
  apply exists.intro X',
  simp [B2],
end


--TODO: Unify with Sup_apply_eq_supr_apply_of_closed'
lemma Sup_apply_eq_supr_apply_of_closed'' {α:Type*}
  [complete_lattice α] {S:set α} (g:α → ennreal):
  (∀ (a∈ S) (b∈ S), a ≤ b → g a ≤ g b) →
  (∀ f:ℕ → α, set.range f ⊆ S → monotone f → (supr f)∈ S) →
  (S.nonempty) →
  (∀ a ∈ S, ∀ b ∈ S, a ⊔ b ∈ S)→
  (∃ f:ℕ → α,
            (∀ n, f n ∈ S) ∧ 
            (monotone f) ∧
            g (supr f) = Sup (g '' S)) :=
begin
  intros A1 AX A2 A3,
  have B1:(g '' S).nonempty,
  {
    apply set.nonempty_image_iff.mpr A2,
  },
  have B1X := ennreal.Sup_eq_supr B1,
  cases B1X with f' B1X,
  have B2:∃ f'':ℕ → α, ∀ n:ℕ, 
          (f'' n)∈ S ∧ g (f'' n) = f' n, 
  {
    apply @classical.some_func ℕ α (λ (n:ℕ) (a:α), 
        a∈ S ∧ g a = f' n),
    intro n,
    have B2A:=(B1X.left) n,
    simp at B2A,
    cases B2A with a B2A,
    apply exists.intro a,
    simp,
    apply B2A,
  },
  cases B2 with f'' B2,
  have C1:∀ (n : ℕ), Sup_so_far f'' n ∈ S,
  {
    apply Sup_so_far_of_closed,
    intro n,
    apply (B2 n).left,
    apply A3,  
  },
  apply exists.intro (Sup_so_far f''),
  split,
  {
    apply C1,
  },
  split,
  {
    apply monotone_Sup_so_far,
  },
  {
    --rw ← AX,
      have D1:(supr (Sup_so_far f''))∈ S,
      {
        apply AX,
        {
          rw set.subset_def,
          intros x D1A,
          --apply C1,
          simp at D1A,
          cases D1A with y D1A,
          subst x,
          apply C1,
        },
        apply monotone_Sup_so_far,
      },
    apply le_antisymm,
    {
      apply @le_Sup ennreal _ _,
      simp,
      apply exists.intro (supr (Sup_so_far f'')),
      apply and.intro D1,
      refl,   
    },
    {
      rw ← B1X.right,
      apply @supr_le ennreal _ _,
      intro i,
      rw ← (B2 i).right,
      apply A1,
      apply (B2 i).left,
      apply D1,
      have D2:f'' i ≤ (Sup_so_far f'') i,
      {
        apply le_Sup_so_far,
      },
      apply le_trans D2,
      apply @le_supr _ ℕ _ (Sup_so_far f'') i,
   },
  },
end

--Replacing hahn_unsigned_inequality_decomp' (and hahn_unsigned_inequality_decomp).
lemma hahn_unsigned_inequality_decomp' {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) [A1:measure_theory.finite_measure ν]: 
    (∃ X:set α, is_measurable X ∧  μ.restrict X ≤ ν.restrict X ∧ ν.restrict (Xᶜ) ≤ μ.restrict (Xᶜ)) :=
begin
  /-
    What we want is the argmax of f on S: this is our candidate for X.
    However, we must first establish that such an argmax exists.
     
    First, we construct an  M that is our candidate for X.
    It is the supremum of 
   -/
  let S:set (set α) := {X:set α|is_measurable X ∧  μ.restrict X ≤ ν.restrict X},
  let f:set α → ennreal := (λ T:set α, (ν T) - (μ T)),
  -- M is unused.
  let M:ennreal := Sup (f '' S),
  begin
    -- S is a ring of sets (closed under countable union).
    have A2:S = {X:set α|is_measurable X ∧  μ.restrict X ≤ ν.restrict X} := rfl,
    have A3:f = (λ T:set α, (ν T) - (μ T)) := rfl,
    have A5:∀ X, is_measurable X → μ.restrict X ≤ ν.restrict X → μ X < ⊤,
    {
      intros X A5A A5B,
      apply lt_of_le_of_lt (measure_theory.measure.le_of_restrict_le_restrict_self _ _ A5A A5B),
      apply measure_theory.measure_lt_top,
    },
    have A6:∀ T, f T = ν T - μ T,
    {
      intro T,
      refl,
    },
    have B1:∀ (a∈ S) (b∈ S), a ≤ b → f a ≤ f b,
    {
      intros T1 B1A T2 B1B B1C,
      rw A2 at B1A,
      simp at B1A,      
      rw A2 at B1B,
      simp at B1B,
      repeat {rw A6},
      have B1F:μ.restrict (T2 \ T1) ≤ ν.restrict (T2 \ T1),
      {
        apply restrict_le_restrict_of_restrict_le_restrict_of_subset B1B.right,
        apply set.diff_subset,
        repeat {simp [B1A.left,B1B.left]},
      },
      have E1:is_measurable (T2 \ T1),
      {
        simp [B1A.left,B1B.left],
      },
      have B1G:T2 = T1 ∪ (T2 \ T1),
      { 
        rw set.union_diff_cancel,
        apply B1C,
      },
      rw B1G,
      rw restrict_le_restrict_add,
      apply @le_add_of_nonneg_right ennreal _,
      simp only [zero_le],
      {
        apply A5 T1 B1A.left B1A.right,
      },
      {
        apply A5 (T2 \ T1) E1 B1F,
      },
      apply B1A.left,
      apply E1,
      apply B1A.right,
      apply B1F, 
      apply set.disjoint_diff,
    },
    
    have B2B:(∀ h:ℕ → set α, set.range h ⊆ S → monotone h → (supr h)∈ S),
    {
      intros h B2C B2D,
      have B2BG:∀ n, is_measurable (h n) ∧  μ.restrict (h n) ≤ ν.restrict (h n),
      {
        intro n,
        apply B2C,
        simp,
      }, 
      rw A2,
      rw supr_eq_Union,
      simp only [set.mem_set_of_eq],
      split,
      apply is_measurable.Union,
      intros b,
      --simp at B2C,
      have B2BA:h b ∈ S,
      {apply B2C, simp},
      rw A2 at B2BA,
      simp at B2BA,
      apply B2BA.left,
      apply restrict_le_restrict_m_Union,
      apply B2D,
      intro n,
      have B2E := B2BG n,
      --simp at B2E, 
      apply (B2BG n).left,
      intro n,
      apply (B2BG n).right,
    },
    have B3B:∅ ∈ S,
    {
      simp [le_refl _],
    },
    have B3:S.nonempty,
    {
      apply set.nonempty_of_mem B3B,
    },
    have B4:(∀ (a ∈ S) (b ∈ S), a ⊔ b ∈ S),
    {
      rw A2,
      simp,
      intros a B4A B4B b B4D B4E,
      have B4C:a ⊔ b = a ∪ b := rfl,
      split,
      {simp [B4A,B4D]},
      apply restrict_le_restrict_union B4B B4E,
      repeat {assumption},
    },
    have C1:=@Sup_apply_eq_supr_apply_of_closed'' (set α) _ S f B1 B2B B3 B4,
    cases C1 with g C1,
    apply exists.intro (supr g),
    have E1:∀ n, is_measurable (g n) ∧ μ.restrict (g n) ≤ ν.restrict (g n),
    {
      intro n,
      apply (C1.left n),
    },
    have E2:=λ n, (E1 n).left,
    have E3 := λ n, (E1 n).right,
    have E4:is_measurable (supr g),
    {
      rw supr_eq_Union,
      apply is_measurable.Union,
      apply E2,
    },
    have C2:μ.restrict (supr g) ≤ ν.restrict (supr g),
    {
      rw supr_eq_Union,
      apply restrict_le_restrict_m_Union,
      apply C1.right.left,
      apply E2,
      apply E3,
    },
    apply and.intro E4,
    apply and.intro C2,
    -- ⊢ ν.restrict (supr g)ᶜ ≤ μ.restrict (supr g)ᶜ
    {
      --intros X' D1 D2,
      apply restrict_le_restrict_of_le_subset,
      apply is_measurable.compl E4,
      intros X' D1 D2, 
      apply le_of_not_lt _,
      intro D3,
      have D4:= hahn_unsigned_inequality_decomp_junior' μ ν D2 D3,
      cases D4 with X'' D4,
      have D5:f (X'' ∪ supr g) ≤  f (supr g),
      {
        rw C1.right.right,
        apply @le_Sup ennreal _ _,
        simp,
        apply exists.intro (X'' ∪ supr g),
        simp only [D4, E4, true_and, is_measurable.union, and_true, eq_self_iff_true],
        --squeeze_simp [D4,D2,E4],
        apply restrict_le_restrict_union,
        repeat {simp [D4,C2,E4]},
      },
      repeat {rw A6 at D5},
      rw restrict_le_restrict_add at D5,
      repeat {rw ← A6 at D5},
      rw add_comm at D5,
      apply @ennreal.not_add_le_of_lt_of_lt_top (f (supr g)) (f X'') _ _ _,
      {
        rw A6,
        simp,
        apply D4.right.left,
      },
      {
        rw A6,
        have D6:ν (supr g) < ⊤,
        {
          apply measure_theory.measure_lt_top,
        },
        apply lt_of_le_of_lt _ D6,
        simp,
        apply ennreal.le_add,
        apply le_refl _,
      },
      apply D5,
      apply A5 X'' D4.right.right.left,
      apply D4.right.right.right,
      apply A5 (supr g) E4 C2,
      apply D4.right.right.left,
      repeat {simp [D4,E4,C2]},
      {
        apply @set.disjoint_of_subset_left _ _ _ ((supr g)ᶜ),
        apply set.subset.trans D4.left D1,
        apply set.disjoint.symm,
        apply set.disjoint_compl_right,
      },
    },
  end
end

