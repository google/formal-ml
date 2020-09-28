
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
import formal_ml.integral
import formal_ml.int
import formal_ml.with_density_compose_eq_multiply
import formal_ml.classical

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
 -/


lemma nonnegative_fn {α β:Type*} [canonically_ordered_add_monoid β] {f:α → β}:0 ≤ f :=
begin
  intro x,
  simp,
end

lemma real.add_lt_of_lt_sub {a b c:real}:a < b - c → a + c < b :=
begin
  intro A1,
  have B1:a + c < (b - c) + c,
  {
    apply add_lt_add_right,
    apply A1,
  },
  simp at B1,
  apply B1,
end


lemma real.lt_sub_of_add_lt {a b c:real}:a + c < b → a < b - c :=
begin
  intro A1,
  have B1:a + c + (-c) < b + (-c),
  {
    apply add_lt_add_right,
    apply A1,
  },
  simp at B1,
  apply B1,
end


lemma real.le_sub_add {a b c:real}:b ≤ c → 
a ≤ a - b + c := 
begin
  intros A1,
  have B1:a - b + b ≤ a - b + c,
  {
    apply add_le_add_left,
    apply A1,
  },
  simp at B1,
  apply B1,
end

lemma real.lt_of_le_of_add_le_of_le_of_sub_lt {a b c d e:real}:
    a + b ≤ c → d ≤ b → c - e < a → d < e := 
begin
  intros A1 A2 A3,
  have B1:c < a + e,
  {
    have B1A:(c - e) + e < a + e,
    {
      apply add_lt_add_right,
      apply A3,
    },
    simp at B1A,
    apply B1A,
  },
  have B2:a + b < a + e,
  {
    apply lt_of_le_of_lt A1 B1,
  },
  simp at B2,
  apply lt_of_le_of_lt A2 B2,
end


lemma real.lt_of_lt_of_le_of_add_le_of_le_of_sub_lt {a b c d e:real}:
    c < e → a + b ≤ c → d ≤ b → 0 < a → d < e := 
begin
  intros A1 A2 A3 A4,
  apply lt_of_le_of_lt _ A1,
  apply le_trans A3,
  clear A1 A3,
  have B1:0 + c < a + c,
  {
    simp,
    apply A4,
  },
  rw zero_add at B1,
  have B2 := lt_of_le_of_lt A2 B1,
  simp at B2,
  apply le_of_lt B2, 
end

lemma real.lt_of_add_lt_of_pos {a b c:real}:
      b + c ≤ a →
      0 < b →
      c < a :=
begin
  intros A1 A2,
  have A3:0 + c < b + c,
  {
    apply add_lt_add_right A2,
  }, 
  rw zero_add at A3,
  apply lt_of_lt_of_le A3,
  apply A1,
end


lemma nnreal.add_lt_of_lt_sub {a b c:nnreal}:a < b - c → a + c < b :=
begin
  cases (classical.em (c ≤ b)) with B1 B1,
  {
    repeat {rw ← nnreal.coe_lt_coe <|> rw nnreal.coe_add},
    rw nnreal.coe_sub B1,
    apply real.add_lt_of_lt_sub,    
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
  apply real.lt_sub_of_add_lt,
end


lemma nnreal.le_sub_add {a b c:nnreal}:b ≤ c → c ≤ a → 
a ≤ a - b + c := 
begin
  repeat {rw ← nnreal.coe_le_coe},
  repeat {rw nnreal.coe_add},
  intros A1 A2,
  repeat {rw nnreal.coe_sub},
  apply real.le_sub_add A1,
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
    apply real.lt_of_le_of_add_le_of_le_of_sub_lt,
  },
  {   
    rw nnreal.sub_eq_zero (le_of_lt B1),
    rw ← nnreal.coe_lt_coe at B1,
    apply real.lt_of_lt_of_le_of_add_le_of_le_of_sub_lt B1,
  },
end


lemma nnreal.epsilon_half_lt_epsilon {ε:nnreal}: 0 < ε → (ε / 2) < ε :=
begin
  rw ← nnreal.coe_lt_coe,
  rw ← nnreal.coe_lt_coe,
  --rw ← nnreal.coe_two,
  rw nnreal.coe_div,
  apply epsilon_half_lt_epsilon,
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
  --intros A1 A2,
  rw ← nnreal.coe_le_coe,
  rw ← nnreal.coe_lt_coe,
  rw ← nnreal.coe_lt_coe,
  rw nnreal.coe_add,
  apply real.lt_of_add_lt_of_pos,
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

lemma not_top_eq_some {x:ennreal}:x≠ ⊤ → (∃ (y:nnreal), (y:ennreal) = x) :=
begin
  intro A1,
  cases x,
  {
    exfalso,
    simp at A1,
    apply A1,
  },
  apply exists.intro x,
  refl
end

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


lemma ennreal.epsilon_half_lt_epsilon {ε:ennreal}: ε < ⊤ → 0 < ε → (ε / 2) < ε :=
begin
  cases ε;simp,
  --rw ennreal.coe_div,
  have B1:((2:nnreal):ennreal) = 2 := rfl,
  rw ← B1,
  rw ← ennreal.coe_div,
  rw ennreal.coe_lt_coe,
  apply nnreal.epsilon_half_lt_epsilon,
  intro C1,
  have C2:(0:nnreal) < (2:nnreal),
  {
    apply zero_lt_two,
  },
  rw C1 at C2,
  simp at C2,
  apply C2,
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


lemma measures_equal {Ω:Type*} {M:measurable_space Ω}
    (μ ν:measure_theory.measure Ω) [measure_theory.finite_measure ν]:
  (μ ≤ ν) →
  (μ set.univ = ν set.univ) →
  (μ = ν) :=
begin
  intros A3 A4,
  apply measure_theory.measure.ext,
  intros S A5,
  have B3:is_measurable (Sᶜ),
  {
    apply is_measurable.compl,
    apply A5,
  },
  apply le_antisymm,
  {
    apply A3,
    apply A5,
  },
  {
    apply @le_of_not_lt ennreal _,
    intro A6,
    have A7:μ (Sᶜ) ≤ ν (Sᶜ),
    {
      apply A3,
      apply B3,
    },
    have B1:S ∪ (Sᶜ) = set.univ ,
    {
      simp,
    },
    have B2:disjoint S (Sᶜ),
    {
      unfold disjoint,
      simp,
    },
    have A8:μ set.univ = μ S + μ (Sᶜ),
    {
      rw ← B1,
      apply measure_theory.measure_union,
      apply B2,
      apply A5,
      apply B3,
    },
    have A9:ν set.univ = ν S + ν (Sᶜ),
    {
      rw ← B1,
      apply measure_theory.measure_union,
      apply B2,
      apply A5,
      apply B3,
    },
    have A10:μ set.univ < ν set.univ,
    {
      rw A8,
      rw A9,
      apply ennreal.add_lt_add_of_lt_of_le_of_lt_top,
      {
        apply measure_theory.measure_lt_top,
      },
      {
        apply A7,
      },
      {
        apply A6,
      },
    },
    rw A4 at A10,
    apply lt_irrefl _ A10,
  },
end


lemma measurable_supr_of_measurable {Ω:Type*} [M:measurable_space Ω]
    {h:ℕ → Ω → ennreal}:
    (∀ n:ℕ, measurable (h n)) →
    (measurable (supr h)) :=
begin
  intros A1,
  apply is_ennreal_measurable_intro_Ioi,
  intro x,
  have A3:((supr h) ⁻¹' {y : ennreal | x < y}) =⋃ (n:ℕ), (h n) ⁻¹' {y:ennreal | x < y},
  {
    simp,
    ext ω,
      have A3B:supr h ω = supr (λ n, h n ω),
      {
        apply supr_apply,
      },
    split;
    intros A3A;simp;simp at A3A,
    {
      rw A3B at A3A,
      rw @lt_supr_iff ennreal _ at A3A,
      apply A3A,
    },
    {
      cases A3A with i A3A,
      apply lt_of_lt_of_le A3A,
      rw A3B,
      apply @le_supr ennreal ℕ _,
    },
  },    
  rw A3,
  apply is_measurable.Union,
  intro b,
  apply A1 b,
  apply is_ennreal_is_measurable_intro_Ioi,
end 




lemma monotone_set_indicator {Ω β:Type*} [has_zero β] [preorder β] {S:set Ω}:
    monotone ((set.indicator S):(Ω → β) → (Ω → β)) :=
begin
  unfold monotone,
  intros f g A1,
  rw le_func_def2,
  intro ω,
  cases (classical.em (ω ∈ S)) with A2 A2,
  {
    rw set.indicator_of_mem A2,
    rw set.indicator_of_mem A2,
    apply A1,
  },
  {
    rw set.indicator_of_not_mem A2,
    rw set.indicator_of_not_mem A2,
  },
end


lemma supr_with_density_apply_eq_with_density_supr_apply {Ω:Type*} [measurable_space Ω] {μ:measure_theory.measure Ω}
    {h:ℕ → Ω → ennreal} {S:set Ω}:
    is_measurable S →
    (∀ n:ℕ, measurable (h n)) →
    (monotone h) →
    supr (λ n:ℕ, μ.with_density (h n) S) = μ.with_density (supr h) S :=
begin
  intros A1 A2 A3,
  have A4:(λ n, μ.with_density (h n) S) = (λ n, μ.integral (set.indicator S (h n))),
  {
    apply funext,
    intro n,
    rw measure_theory.with_density_apply2,
    --apply A2 n,
    apply A1,
  },
  rw A4,
  clear A4,
  rw measure_theory.with_density_apply2,
  rw supr_indicator,
  rw measure_theory.integral_supr,
  {
    intro n,
    apply measurable_set_indicator,
    apply A1,
    apply A2 n,
  },
  {
    have B1:(λ (n:ℕ), set.indicator S (h n)) = (set.indicator S) ∘ h := rfl,
    rw B1,
    apply @monotone.comp ℕ (Ω → ennreal) (Ω → ennreal) _ _ _,
    apply @monotone_set_indicator Ω ennreal _ _,
    apply A3,
  },
  {
    apply A1,
  },
end 


lemma with_density_supr_apply_le {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}
    {h:ℕ → Ω → ennreal} {S:set Ω}:
    is_measurable S →
    (∀ n:ℕ, measurable (h n)) →
    (monotone h) →
    (∀ n:ℕ, μ.with_density (h n) ≤  ν) →
    μ.with_density (supr h) S ≤ ν S :=
begin
  intros A1 A2 A3 A4,
  rw ← supr_with_density_apply_eq_with_density_supr_apply A1 A2 A3,
  apply @supr_le ennreal ℕ _,
  intro n,
  apply A4,
  apply A1,
end


-- So, although there is a LOT below, this is the easiest third of the
-- Radon-Nikodym derivative: namely, that if we have a monotone sequence
-- of functions, the sequence will be less than or equal to ν.
lemma with_density_supr_le {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}
    {h:ℕ → Ω → ennreal}:
    (∀ n:ℕ, measurable (h n)) →
    (monotone h) →
    (∀ n:ℕ, μ.with_density (h n) ≤  ν) →
    μ.with_density (supr h) ≤ ν :=
begin
  intros A1 A2 A3,
  intros S A4,
  apply with_density_supr_apply_le A4 A1 A2 A3,
end


lemma measure_of_monotone' {Ω:Type*} [measurable_space Ω] {S:set Ω}
    :is_measurable S →
    monotone (λ μ:measure_theory.measure Ω, μ S) :=
begin
  intros A0 μ ν A1,
  simp,
  rw measure.apply,
  rw measure.apply,
  apply A1,
  apply A0,
end



-- Compare with ennreal.has_sub.
-- I think that this is the equivalent of (a - b)⁺, if 
-- a and b were signed measures.
-- Specifically, note that if you have α = {1,2}, and
-- a {1} = 2, a {2} = 0, and 
-- b {2} = 2, b {1} = 0, then 
-- (a - b) {1, 2} = 2. However, if a ≤ b, and
--  a set.univ ≠ ⊤, then (a - b) + b = a.
-- Also, a - b ≤ a.
noncomputable instance measure_theory.measure.has_sub {α:Type*}
  [measurable_space α]:has_sub (measure_theory.measure α) := ⟨λa b, Inf {d | a ≤ d + b}⟩


lemma measure_theory.measure.sub_def {α:Type*}
  [measurable_space α] {a b:measure_theory.measure α}:
  (a - b) = Inf {d | a ≤ d + b} := rfl


def sub_pred {α:Type*} (f:ℕ → set α):ℕ → set α
  | (nat.succ n) := f n.succ \ f n
  | 0 := f 0 


lemma sub_pred_subset {α:Type*} (f:ℕ → set α) {n:ℕ}:
  sub_pred f n ⊆ f n :=
begin
  cases n,
  {
    unfold sub_pred,
  },
  {
    unfold sub_pred,
    apply set.diff_subset,
  },
end

lemma sub_pred_subset' {α:Type*} (f:ℕ → set α) {n:ℕ} {x:α}:
  x∈ sub_pred f n → x ∈ f n :=
begin
  intro A1,
  have A2:sub_pred f n ⊆ f n := @sub_pred_subset α f n, 
  rw set.subset_def at A2,
  apply A2 _ A1,
end


def prefix_union {α:Type*} (f:ℕ → set α) (n:ℕ):=
  (⋃ (m∈ finset.range n.succ), f m )


lemma prefix_union_def {α:Type*} (f:ℕ → set α) (n:ℕ):
  (⋃ (m∈ finset.range n.succ), f m )= prefix_union f n := rfl


lemma prefix_union_zero {α:Type*} (f:ℕ → set α):
  (prefix_union f 0) = f 0 :=
begin
  rw ← prefix_union_def,
  apply set.ext,
  intros a,
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

lemma prefix_union_succ {α:Type*} (f:ℕ → set α) (n:ℕ):
  (prefix_union f n.succ) = (prefix_union f n) ∪ f n.succ :=
begin
  rw ← prefix_union_def,
  rw ← prefix_union_def,
  ext,
  split;intros A1;simp;simp at A1,
  {
    cases A1 with m A1,
    cases (classical.em (m = nat.succ n)) with A2 A2,
    {
      subst m,
      right,
      apply A1.right,
    },
    {
      left,
      apply exists.intro m,
      split,
      apply lt_of_le_of_ne,
      apply lt_succ_imp_le m (nat.succ n) A1.left,  
      apply A2,
      apply A1.right,
    },
  },
  {
    cases A1 with A1 A1,
    {
      cases A1 with m A1,
      apply exists.intro m,
      split,
      apply lt_trans A1.left,
      apply nat.lt.base,
      apply A1.right,
    },
    {
      apply exists.intro (nat.succ n),
      split,
      apply nat.lt.base,
      apply A1,
    },
  },
end


lemma prefix_union_def2 {α:Type*} (f:ℕ → set α) (n:ℕ):
  (⨆  (m:ℕ) (H:m ≤ n), f m)=prefix_union f n :=
begin
  unfold prefix_union,
  ext,split;intros A1;simp at A1;simp,
  {
    cases A1 with m A1,
    apply exists.intro m,
    split,
    apply nat.lt_succ_of_le A1.left,
    apply A1.right,
  },
  {
    cases A1 with m A1,
    apply exists.intro m,
    split,
    apply lt_succ_imp_le m n A1.left,
    apply A1.right, 
  },
end


lemma prefix_union_contains {α:Type*} (f:ℕ → set α) {m n:ℕ}:
    m ≤ n → 
    f m ⊆ prefix_union f n :=
begin
  intro A1,
  rw ← prefix_union_def2,
  rw set.subset_def,
  intros ω A2,
  simp,
  apply exists.intro m,
  apply and.intro A1 A2,
end


lemma prefix_union_contains' {α:Type*} (f:ℕ → set α) {m n:ℕ} {x:α}:
    m ≤ n → 
    x∈ f m → x ∈ prefix_union f n :=
begin
  intros A1 A2,
  have A3 := prefix_union_contains f A1,
  rw set.subset_def at A3,
  apply A3 x A2,
end


lemma prefix_union_sub_pred {α:Type*} (f:ℕ → set α):
    prefix_union (sub_pred f) = prefix_union f :=
begin
  apply funext,
  intro n,
  induction n,
  {
    repeat {rw prefix_union_zero},
    unfold sub_pred,
  },
  {
    rw prefix_union_succ,
    rw prefix_union_succ f,
    rw n_ih,
    ext;split;intros A1;simp;simp at A1;cases A1 with A1 A1;
    try {
      apply or.inl A1,
    },
    {
      right,
      apply sub_pred_subset',
      apply A1,
    },
    {
      cases (classical.em (x ∈ f n_n)) with A2 A2,
      {
        left,
        apply prefix_union_contains' f _ A2,
        apply le_refl,
      },
      {
        right,
        unfold sub_pred,
        simp,
        apply and.intro A1 A2,
      },
    },
  },
end


lemma Union_sub_pred {α:Type*} {f:ℕ → set α}:
  set.Union (sub_pred f) = set.Union f :=
begin
  apply set.ext,
  intro a,
  split;intros A1;simp at A1;simp;cases A1 with n A1,
  {
    apply exists.intro n,
    apply sub_pred_subset',
    apply A1,
  },
  {
    have A2:a ∈ prefix_union f n,
    {
      apply prefix_union_contains' f (le_refl n) A1,
    },
    rw ← prefix_union_sub_pred at A2,
    rw ← prefix_union_def at A2,
    simp at A2,
    cases A2 with n A2,
    apply exists.intro n,
    apply A2.right,
  },
end


lemma mem_sub_pred_succ {α:Type*} {n:ℕ} {x:α} {f:ℕ → set α}:
    x ∉ f n → (x ∈ f (nat.succ n)) →
    x ∈ sub_pred f (nat.succ n) :=
begin
  intros A1 A2,
  unfold sub_pred,
  apply and.intro A2 A1,
end

lemma not_mem_of_sub_pred_succ {α:Type*} {n:ℕ} {x:α} {f:ℕ → set α}:
    x ∈ sub_pred f (nat.succ n) → x ∉ f n  :=
begin
  intros A1,
  unfold sub_pred at A1,
  simp at A1,
  apply A1.right,
end


lemma sub_pred_pairwise_disjoint_helper {α:Type*} {f:ℕ → set α} {m n:ℕ}:
  (monotone f) →
  m < n →
  disjoint (sub_pred f m) (sub_pred f n) :=
begin
  intros A1 A2,
  rw set.disjoint_right,
  intros x A4 A3,
  cases n,
  {
    apply nat.not_lt_zero m A2,
  },
  have A5 := lt_succ_imp_le m n A2,
  have A6:f m ⊆ f n,
  {
    apply A1 A5,
  },
  have A7:sub_pred f m ⊆ f m,
  {
    apply sub_pred_subset,
  },
  have A8:x ∈ f n,
  {
     have A8:=set.subset.trans A7 A6,
     rw set.subset_def at A8,
     apply A8 x A3,
  },
  apply not_mem_of_sub_pred_succ A4 A8,
end


lemma sub_pred_pairwise_disjoint {α:Type*} {f:ℕ → set α}:
  (monotone f) →
  pairwise (disjoint on (sub_pred f)) :=
begin
  intro A1,
  intros m n A2,
  have A3:disjoint (sub_pred f m) (sub_pred f n),
  {
    have A3A:=lt_trichotomy m n,
    cases A3A with A3A A3A,
    {
      apply sub_pred_pairwise_disjoint_helper A1 A3A,
    },
    cases A3A with A3A A3A,
    {
      exfalso,
      apply A2,
      apply A3A,
    },
    {
      apply set.disjoint.symm,
      apply sub_pred_pairwise_disjoint_helper A1 A3A,      
    },
  },
  apply A3,
end


lemma measure_finset_sum {α:Type*}
    [measurable_space α] {μ:measure_theory.measure α}
    {f:ℕ → set α} {n:ℕ}:(∀ n, is_measurable (f n)) →
    (pairwise (disjoint on f)) →
    (finset.range n).sum (λ m, μ (f m)) = 
    μ (⋃  (m∈ finset.range n), f m) :=
begin
  intros A1 A2,
  rw measure_theory.measure_bUnion_finset,
  {
    intros m B1 n B2 B3,
    apply A2,
    apply B3,
  },
  {
    intros m C1,
    apply A1,
  },
end


lemma union_range_sub_pred {α:Type*} {f:ℕ → set α} {n:ℕ}:
 (⋃ (m : ℕ) (H : m ∈ finset.range n), sub_pred f m) =
     (⋃ (m : ℕ) (H : m ∈ finset.range n), f m) :=
begin
  cases n,
  {
    simp,
  },
  {
    rw prefix_union_def,
    rw prefix_union_def,
    rw prefix_union_sub_pred,
  },
end


lemma is_measurable_sub_pred {α:Type*} [measurable_space α] 
  {f:ℕ → set α} {n:ℕ}:
  (∀ m, is_measurable (f m)) → is_measurable (sub_pred f n) :=
begin
  intro A1,
  cases n,
  {
    unfold sub_pred,
    apply A1,
  },
  {
    unfold sub_pred,
    apply is_measurable.diff,
    repeat {apply A1},
  },
end



lemma union_finset_range_monotone {α:Type*} {f:ℕ → set α} {n:ℕ}:
    monotone f →
    (⋃ m ∈ finset.range (n.succ), f m) = f n :=
begin
  intro A1,
  ext,split;intros A2,
  {
    simp at A2,
    cases A2 with m A2,
    have A3 := lt_succ_imp_le m n A2.left,
    have A4 := A1 A3,
    have A5:(f m ⊆ f n)= (f m ≤ f n ):= rfl,
    rw ← A5 at A4,
    rw set.subset_def at A4,
    apply A4,
    apply A2.right,
  },
  {
    simp,
    apply exists.intro n,
    split,
    apply nat.lt.base,
    apply A2,
  },
end


def le_on_subsets {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) (X:set α):Prop :=
    is_measurable X ∧ 
    (∀ X':set α, X'⊆ X → is_measurable X' → μ X' ≤ ν X') 


lemma le_on_subsets_def {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) (X:set α):
    le_on_subsets μ ν X =
    (is_measurable X ∧ 
    (∀ X':set α, X'⊆ X → is_measurable X' → μ X' ≤ ν X')) := rfl


lemma le_on_subsets_is_measurable {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X:set α}:
    le_on_subsets μ ν X →
    (is_measurable X) :=
begin
  intros A1,
  rw le_on_subsets_def at A1,
  apply A1.left,
end


lemma le_on_subsets_self {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X:set α}:
    le_on_subsets μ ν X →
    μ X ≤ ν X :=
begin
  intro A1,
  rw le_on_subsets_def at A1,
  apply A1.right X (le_refl X) A1.left,
end


lemma le_on_subsets_empty {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):
    le_on_subsets μ ν ∅ := 
begin
  rw le_on_subsets_def,
  split,
  {
    apply is_measurable.empty,
  },
  {
    intros X' A1 A2,
    have A3 := empty_of_subset_empty X' A1,
    subst X',
    simp,
  },
end

lemma le_on_subsets_union {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X Y:set α}:
    le_on_subsets μ ν X →
    le_on_subsets μ ν Y →
    le_on_subsets μ ν (X ∪ Y) :=
begin
  repeat {rw le_on_subsets_def},
  intros A1 A2,
  split,
  {
     apply is_measurable.union A1.left A2.left,
  },
  {
     intros X' A3 A4,
     rw @measure_theory.measure_eq_inter_diff _ _ μ _ X A4 A1.left,
     rw @measure_theory.measure_eq_inter_diff _ _ ν _ X A4 A1.left,
     have A5:X' ∩ X ⊆ X := set.inter_subset_right X' X,
     have A6:X' \ X ⊆ Y,
     {
       rw set.subset_def,
       intros a A6A,
       rw set.subset_def at A3,
       simp at A6A,
       have A6B := A3 a A6A.left,
       simp at A6B,
       cases A6B,
       {
         exfalso,
         apply A6A.right,
         apply A6B,
       },
       {
         apply A6B,
       },
     },
     
     have A7:is_measurable (X' ∩ X) := is_measurable.inter A4 A1.left,
     have A8:is_measurable (X' \ X) := is_measurable.diff A4 A1.left,
     have A9:=A1.right (X' ∩ X) A5 A7,
     have A10:=A2.right (X' \ X) A6 A8,
     apply @add_le_add ennreal _ _ _ _ _ A9 A10,
  },
end


lemma le_on_subsets_subset {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) (X Y:set α):
    le_on_subsets μ ν X →
    Y ⊆ X →
    is_measurable Y →
    le_on_subsets μ ν Y :=
begin
  repeat {rw le_on_subsets_def},
  intros A1 A2 A3,
  split,
  apply A3,
  intros X' A4 A5,
  apply A1.right X' (set.subset.trans A4 A2) A5,
end


lemma le_on_subsets_diff {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X Y:set α}:
    le_on_subsets μ ν X →
    le_on_subsets μ ν Y →
    le_on_subsets μ ν (X \ Y) :=
begin
  intros A1 A2,
  apply le_on_subsets_subset μ ν X (X \ Y) A1,
  {
    apply set.diff_subset,
  },
  {
    apply is_measurable.diff 
       (le_on_subsets_is_measurable A1)
       (le_on_subsets_is_measurable A2),
  },
end


lemma le_on_subsets_m_Union {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) {f:ℕ → set α}:
    monotone f →
    (∀ n:ℕ, le_on_subsets μ ν (f n)) → 
    (le_on_subsets μ ν (set.Union f)) :=
begin
  intros A1 A2,
  have A3:∀ n, le_on_subsets μ ν ((sub_pred f) n),
  {
    intros n,
    cases n,
    {
      unfold sub_pred,
      apply A2,
    },
    {
      unfold sub_pred,
      apply le_on_subsets_diff,
      apply A2,
      apply A2,
    },
  },
  rw ← Union_sub_pred,
  
  rw le_on_subsets_def,
  split,
  {
    apply is_measurable.Union,
    intro n,
    apply le_on_subsets_is_measurable (A3 n),
  },
  {
    intros X' A4 A5,
    have D1:pairwise (disjoint on λ (i : ℕ), X' ∩ sub_pred f i),
    {
      intros m n C1,
      have C2:disjoint (X' ∩ sub_pred f m) (X' ∩ sub_pred f n),
      {
        rw set.inter_comm,
        apply set.disjoint_inter_left,
        apply set.disjoint_inter_right,
        apply sub_pred_pairwise_disjoint A1,
        apply C1,
      },
   
      apply C2,
    },
    have D2:∀ n, is_measurable (X' ∩ (sub_pred f n)),
    {
      intro n,
      apply is_measurable.inter A5 (le_on_subsets_is_measurable (A3 n)),
    },
    
    have A6:X' = ⋃ n, X' ∩ (sub_pred f n),
    {
      ext,split;intros A4A,
      {
        simp,
        apply and.intro A4A,
        rw set.subset_def at A4,
        have A4B := A4 x A4A,
        simp at A4B,
        apply A4B,
      },
      {
        simp at A4A,
        apply A4A.left,
      },
    },
    rw A6,
    repeat {rw measure_theory.measure_Union},
    apply @tsum_le_tsum ennreal ℕ _ _ _,
    {
      intro b,
      have B1 := A3 b,
      rw le_on_subsets_def at B1,
      apply B1.right,
      apply set.inter_subset_right,
      apply is_measurable.inter A5 B1.left,
    },
    repeat {
      apply ennreal.summable,
    },
    apply D1,
    apply D2,
    apply D1,
    apply D2,
  },
end


lemma le_measurable_add {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) {X Y:set α}:
    μ X < ⊤ →
    μ Y < ⊤ →
    is_measurable X →
    is_measurable Y →
    μ X ≤ ν X →
    μ Y ≤ ν Y →
    disjoint X Y →
    ν (X ∪ Y) - μ (X ∪ Y) = (ν X - μ X) +  (ν Y - μ Y) :=
begin
  intros A1 A2 A3 A4 A5 A6 A7,
  rw measure_theory.measure_union A7 A3 A4,
  rw measure_theory.measure_union A7 A3 A4,
  rw ennreal.add_sub_add_eq_sub_add_sub A1 A2 A5 A6,
end


lemma le_on_subsets_add {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) {X Y:set α}:
    μ X < ⊤ →
    μ Y < ⊤ →
    le_on_subsets μ ν X → le_on_subsets μ ν Y →
    disjoint X Y →
    ν (X ∪ Y) - μ (X ∪ Y) = (ν X - μ X) +  (ν Y - μ Y) :=
begin
  intros A1 A2 A5 A6 A7,
  have A3 := le_on_subsets_is_measurable A5,
  have A4 := le_on_subsets_is_measurable A6,
  apply le_measurable_add μ ν A1 A2 A3 A4 
      (le_on_subsets_self A5) (le_on_subsets_self A6) A7,
end


--This is a function that is equivalent to the above if
--ν ≤ μ and ν is finite (ν set.univ ≠ ⊤).
--This definition is "wrong", in the sense that the
--definition below is closer to subtraction.
--This definition falls apart unless ν ≤ μ.
noncomputable def measure_sub_fn {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α):Π (s:set α),is_measurable s → ennreal := 
  λ (S:set α) (H:is_measurable S), (μ S - ν S)


--A better variant of measure_sub_fn.
--This definition is valid even if ¬(ν ≤ μ).
noncomputable def measure_sub_fn' {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α):Π (s:set α),is_measurable s → ennreal := 
  λ (S:set α) (H:is_measurable S), 
  ⨆ (S' ⊆ S) (H2:le_on_subsets ν μ S'), (μ S' - ν S')


lemma measure_sub_fn_def {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α):
  measure_sub_fn μ ν = λ (S:set α) (H:is_measurable S), (μ S - ν S) := rfl


lemma measure_sub_fn_def' {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α):measure_sub_fn' μ ν = 
  λ (S:set α) (H:is_measurable S), 
  ⨆ (S' ⊆ S) (H2:le_on_subsets ν μ S'), (μ S' - ν S') := rfl


lemma measure_sub_fn_apply {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (s:set α) (H:is_measurable s):
  measure_sub_fn μ ν s H = (μ s - ν s) := rfl

lemma measure_sub_fn_apply' {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (s:set α) (H:is_measurable s):
  measure_sub_fn' μ ν s H = 
  ⨆ (S' ⊆ s) (H2:le_on_subsets ν μ S'), (μ S' - ν S')  := rfl


lemma measure_sub_fn_apply_empty {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α): 
  (measure_sub_fn μ ν) ∅ is_measurable.empty = 0 :=
begin
  rw measure_sub_fn_apply,
  rw measure_theory.measure_empty,
  rw measure_theory.measure_empty,
  rw ennreal.sub_zero,
end


lemma measure_sub_fn_apply_empty' {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α): 
  (measure_sub_fn' μ ν) ∅ is_measurable.empty = 0 :=
begin
  rw measure_sub_fn_apply',
  apply le_antisymm,
  {
    apply @supr_le ennreal _ _,
    intro S',
    apply @supr_le ennreal _ _,
    intro A1,
    apply @supr_le ennreal _ _,
    intros A2,
    have A3:= empty_of_subset_empty S' A1,
    subst S',
    simp,
  },
  {
    simp,
  },
end


lemma sub_eq_supr_le {x y:ennreal}:
  x - y = (⨆ (H:y ≤ x), x) - (⨆ (H:y ≤ x), y) :=
begin
  cases classical.em (y ≤ x) with A1 A1,
  {
    repeat {rw supr_prop_def A1},
  },
  {
    repeat {rw supr_prop_false A1},
    simp,
    apply le_of_not_le A1,
  },
end 



/-
  This only works if the sum of g is finite.
  The consequence of this is that f minus g
  is only well-defined if either f or g.
 -/
lemma ennreal.tsum_sub {f:ℕ → ennreal} {g:ℕ → ennreal}:
(∑' i, g i) ≠ ⊤ → (g ≤ f) → (∑' i, (f i - g i)) = (∑' i, f i) - (∑' i, g i) :=
begin
  intros A1 B2,
  let h:ℕ → ennreal := (λ i, f i - g i),
  begin
    have B1:h = (λ i, f i - g i) := rfl,
    have A2:(∑' i, (h i) + (g i))=(∑' i, h i) + (∑' i, g i),
    {
      apply tsum_add,
      apply ennreal.summable,
      apply ennreal.summable,
    },
    have A3:g ≤ (h + g),
    {
      rw B1,
      rw le_func_def2,
      intro n,
      simp,
      rw ennreal.sub_add_cancel_of_le,
      apply B2,
      apply B2,
    },
    have A4:(∑' i, g i) ≤ (∑' i, (h i) + (g i)),
    {
      apply @tsum_le_tsum ennreal ℕ _ _ _,
      {
        intro n,
        apply A3,
      },
      apply ennreal.summable,
      apply ennreal.summable,
    },
    have A5:(∑' i, (h i) + (g i))-(∑' i, g i)=(∑' i, h i),
    {
      apply ennreal.sub_eq_of_add_of_not_top_of_le A2 A1 A4,
    },
    have A6:(λ i, (h i) + (g i)) = f,
    {
      apply funext,
      intro n,
      rw B1,
      simp,
      rw ennreal.sub_add_cancel_of_le,
      apply B2,
    }, 
    rw A6 at A5,
    rw B1 at A5,
    symmetry,
    apply A5,
  end
end


lemma measure_sub_fn_m_Union {α:Type*} [M:measurable_space α] 
    (μ ν:measure_theory.measure α) (H:ν ≤ μ) 
    [H2:measure_theory.finite_measure ν]:
(∀ (g : ℕ → set α) (h : ∀ (i : ℕ), is_measurable (g i)), 
  pairwise (disjoint on g) → 
 ((measure_sub_fn μ ν) (⋃ (i : ℕ), g i) (M.is_measurable_Union g h)) = 
  ∑' (i : ℕ), (measure_sub_fn μ ν) (g i) (h i)) :=
begin
  intros g A1 A2,
  have A5:(λ i, ν (g i)) = (λ i, ν.to_outer_measure.measure_of (g i)) := rfl,
  have A6:(λ i, μ (g i)) = (λ i, μ.to_outer_measure.measure_of (g i)) := rfl,

  rw measure_sub_fn_apply,
  have A3:(λ n:ℕ, (measure_sub_fn μ ν (g n) (A1 n)))
      =(λ n:ℕ, (μ (g n)) - (ν (g n))),
  {
    apply funext,
    intro n,
    rw measure_sub_fn_apply,
  },
  rw A3,
  clear A3,
  have A4:(∑' (n:ℕ), (μ (g n))-(ν (g n))) = 
(∑' (n:ℕ), (μ (g n)))-
(∑' (n:ℕ), (ν (g n))),
  {
    apply ennreal.tsum_sub,
    {
      rw A5,
      rw ← ν.m_Union A1 A2,
      apply measure_theory.measure_ne_top,
    },
    {
      rw le_func_def2,
      intro i,
      apply H,
      apply A1,
    },
  },
  rw A4,
  repeat {rw measure.apply},
  rw ν.m_Union A1 A2,
  rw μ.m_Union A1 A2,
  rw ← A5,
  rw ← A6,
end


--TODO:Remove if possible. The theorems from the Hahn decomposition cover this.
noncomputable def measure_sub {α:Type*} [M:measurable_space α] 
    {μ ν:measure_theory.measure α} (H:ν ≤ μ) 
    [H2:measure_theory.finite_measure ν]:measure_theory.measure α := @measure_theory.measure.of_measurable α M (measure_sub_fn μ ν)  (measure_sub_fn_apply_empty μ ν) (measure_sub_fn_m_Union μ ν H)



lemma measure_sub_def {α:Type*} [M:measurable_space α] 
    {μ ν:measure_theory.measure α} (H:ν ≤ μ) [H2:measure_theory.finite_measure ν]
  :measure_sub H = @measure_theory.measure.of_measurable α M (measure_sub_fn μ ν)  (measure_sub_fn_apply_empty μ ν) (measure_sub_fn_m_Union μ ν H) := rfl

lemma measure_sub_apply {α:Type*} [M:measurable_space α] 
    {μ ν:measure_theory.measure α} (H:ν ≤ μ) 
    [H2:measure_theory.finite_measure ν] {S:set α} (H3:is_measurable S):
    measure_sub H S = μ S - ν S :=
begin
  rw measure_sub_def,
  rw measure_theory.measure.of_measurable_apply,
  rw measure_sub_fn_apply,
  apply H3,
end





lemma measure_theory.measure.le_of_add_le_add_left {α:Type*} 
  [M:measurable_space α]
  {μ ν₁ ν₂:measure_theory.measure α} [measure_theory.finite_measure μ]: 
  μ + ν₁ ≤ μ + ν₂ → ν₁ ≤ ν₂ :=
begin
  intros A2,
  rw measure_theory.measure.le_iff,
  intros S B1,
  rw measure_theory.measure.le_iff at A2,
  have A3 := A2 S B1,
  simp at A3,
  apply ennreal.le_of_add_le_add_left _ A3,
  apply measure_theory.measure_lt_top,
end


lemma measure_theory.measure.le_of_add_le_add_right 
    {α:Type*} [M:measurable_space α] 
    {μ₁ ν μ₂:measure_theory.measure α} [measure_theory.finite_measure ν]:
   (μ₁ + ν ≤ μ₂ + ν) → (μ₁ ≤ μ₂) :=
begin
  intros A2,
  rw add_comm μ₁ ν at A2,
  rw add_comm μ₂ ν at A2,
  apply measure_theory.measure.le_of_add_le_add_left A2,
end



def measure_theory.measure.is_support {α:Type*} [measurable_space α]
    (μ:measure_theory.measure α) (S:set α):Prop := is_measurable S ∧ μ (Sᶜ) = 0


noncomputable def scale_measure_fn {α:Type*}
    [measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α) 
    (S:set α) (H:is_measurable S):ennreal := x * μ S


noncomputable def scale_measure {α:Type*}
    [M:measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α):(measure_theory.measure α) :=
    measure_theory.measure.of_measurable
    (λ (s:set α) (H:is_measurable s), x * (μ s))
begin
  simp,
end
begin
  intros f A1 A2,
  simp,
  rw measure.apply,  
  rw μ.m_Union A1 A2,
  have A3:(λ i, μ.to_outer_measure.measure_of (f i)) =
          λ i, μ (f i) := rfl,
  rw  A3,
  rw ennreal.tsum_mul_left,
end


lemma scale_measure_apply {α:Type*}
    [M:measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α)
    (s:set α) (H:is_measurable s):
    scale_measure x μ s =
    (λ (s:set α) (H:is_measurable s), x * (μ s)) s H :=
begin
  apply measure_theory.measure.of_measurable_apply,
  apply H,
end

lemma scale_measure_apply2 {α:Type*}
    [M:measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α)
    (s:set α) (H:is_measurable s):
    scale_measure x μ s = x * (μ s) :=
begin
  rw scale_measure_apply,
  apply H,
end


noncomputable instance has_scalar_ennreal_measure {α:Type*}
    [measurable_space α]:
    has_scalar (ennreal) (measure_theory.measure α) := {
  smul := λ x y, scale_measure x y, 
}


lemma ennreal_smul_measure_def {α:Type*}
    [measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α):
    (x  • μ) = (scale_measure x μ)  := rfl


lemma ennreal_smul_measure_apply {α:Type*}
    [measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α)
    (s:set α) (H:is_measurable s):
    (x  • μ) s = x * (μ s) :=
begin
  rw ennreal_smul_measure_def,
  rw scale_measure_apply2,
  apply H,
end
    

lemma ennreal_measure_zero_smul {α:Type*}
    [measurable_space α] (μ:measure_theory.measure α):
    (0:ennreal) • μ = 0 :=
begin
  apply measure_theory.measure.ext,
  intros s A1,
  rw ennreal_smul_measure_apply,
  simp,
  apply A1,  
end


noncomputable instance mul_action_ennreal_measure
    {α:Type*}
    [M:measurable_space α]:
    mul_action (ennreal) (measure_theory.measure α)
     := {
  mul_smul := 
  begin
    intros x y μ,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply,
    rw ennreal_smul_measure_apply,
    rw ennreal_smul_measure_apply,   
    rw mul_assoc,
    repeat {apply A1},
  end,
  one_smul :=
  begin
    intro μ,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply,
    rw one_mul,
    apply A1,
  end,
}


noncomputable instance distrib_mul_action_ennreal_measure
    {α:Type*}
    [M:measurable_space α]:
    distrib_mul_action (ennreal) (measure_theory.measure α)
     := {
  smul_zero :=
  begin
    intro r,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply,
    apply mul_zero,
    apply A1,
  end,
  smul_add :=
  begin
    intros r μ ν,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply _ _ _ A1,
    have A2:(μ + ν) s = (μ s) + (ν s)
        := rfl,
    rw A2,
    have A3:((r • μ) + (r • ν)) s = ((r • μ) s) + ((r • ν) s)
        := rfl,
    rw A3,
    repeat {rw scale_measure_apply2 _ _ _ A1},
    rw left_distrib,
    rw ennreal_smul_measure_apply _ _ _ A1,
    rw ennreal_smul_measure_apply _ _ _ A1,
  end,
}


noncomputable instance ennreal_measure_semimodule {α:Type*}
    [M:measurable_space α]:
    semimodule (ennreal) (measure_theory.measure α) := {
  zero_smul :=
  begin
    intro μ,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply _ _ _ A1,
    apply zero_mul,
  end,
  add_smul := 
  begin
    intros r t μ,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply _ _ _ A1,
    rw measure_theory.measure.add_apply,    
repeat {rw scale_measure_apply2 _ _ _ A1},
    rw right_distrib,
    rw ennreal_smul_measure_apply _ _ _ A1,
    rw ennreal_smul_measure_apply _ _ _ A1,
  end,
}


lemma ennreal.zero_if_lt_pos {x:ennreal}:
  (∀ y >0, x ≤ y) → x = 0 := 
begin
  intro A1,
  have A2:(0:ennreal)=⊥ := rfl,
  rw A2,
  rw ← le_bot_iff,
  rw ← A2,
  apply ennreal.le_of_forall_epsilon_le,
  intros ε A3 A4,
  rw zero_add,
  apply A1,
  have A5:(0:ennreal)=(0:nnreal) := rfl,
  rw A5,
  simp,
  apply A3,  
end


lemma outer_measure_measure_of_le {Ω:Type*} {μ ν:measure_theory.outer_measure Ω}:
    μ ≤ ν ↔
    (μ.measure_of) ≤
    (ν.measure_of) :=
begin
  refl,
end


lemma to_outer_measure_measure_of_le {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}:
    μ ≤ ν ↔
    (μ.to_outer_measure.measure_of) ≤
    (ν.to_outer_measure.measure_of) :=
begin
  split;intro A1,
  {
    rw ← measure_theory.measure.to_outer_measure_le at A1,
    rw le_func_def2,
    intro ω,
    apply A1,
  },
  {
    intros S A2,
    apply A1,
  },
end



lemma monotone_to_outer_measure {Ω:Type*} [measurable_space Ω]:
    monotone (λ μ:measure_theory.measure Ω, μ.to_outer_measure) :=
begin
  intros μ ν A1,
  simp,
  rw ← measure_theory.measure.to_outer_measure_le at A1,
  apply A1,
end


lemma monotone_to_outer_measure_measure_of {Ω:Type*} [measurable_space Ω]:
    monotone (λ μ:measure_theory.measure Ω, μ.to_outer_measure.measure_of) :=
begin
  intros μ ν A1,
  simp,
  rw ← measure_theory.measure.to_outer_measure_le at A1,
  apply A1,
end


lemma measure_apply_le_measure_apply {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω} {S:set Ω}:
    μ ≤ ν →
    (μ S) ≤ (ν S) :=
begin
  intro A1,
  rw to_outer_measure_measure_of_le at A1,
  apply A1,
end


noncomputable def measure_theory.outer_measure.of_function' {Ω:Type*} 
    (f:set Ω → ennreal):
    measure_theory.outer_measure Ω := measure_theory.outer_measure.of_function 
    (set.indicator ({(∅:set Ω)}ᶜ) f)
begin
  rw set.indicator_of_not_mem,
  simp,
end


lemma outer_measure_measure_of_def {Ω:Type*} {μ:measure_theory.outer_measure Ω}
  {S:set Ω}:μ S  = μ.measure_of S := rfl


lemma measure_theory.outer_measure.of_function_def 
  {α : Type*} (m : set α → ennreal) (m_empty : m ∅ = 0) :
  (measure_theory.outer_measure.of_function m m_empty).measure_of
    = λs, ⨅{f : ℕ → set α} (h : s ⊆ ⋃i, f i), ∑'i, m (f i)  := rfl


lemma measure_theory.outer_measure.of_function_le_of_function_of_le {Ω:Type*} 
    {f g:set Ω → ennreal} {Hf:f ∅ = 0} {Hg:g ∅ = 0}:
    f ≤ g → 
    (measure_theory.outer_measure.of_function f Hf ≤
     measure_theory.outer_measure.of_function g Hg) :=
begin
  intro A1,
  rw measure_theory.outer_measure.le_of_function,
  intro S,
  have A2 := @measure_theory.outer_measure.of_function_le _ f Hf S,
  apply le_trans A2,
  apply A1,
end


lemma measure_theory.outer_measure.monotone_of_function' {Ω:Type*}:
    monotone (@measure_theory.outer_measure.of_function' Ω) :=
begin
  unfold monotone measure_theory.outer_measure.of_function',
  intros f g A1,
  apply measure_theory.outer_measure.of_function_le_of_function_of_le,
  have A2 := @monotone_set_indicator (set Ω) ennreal _ _ ({∅}ᶜ),
  apply A2,
  apply A1,
end


lemma measure_theory.outer_measure.of_function'_le {Ω:Type*} 
    {f:set Ω → ennreal} {S:set Ω}: 
    (measure_theory.outer_measure.of_function' f S ≤ f S) :=
begin
  have A2 := @measure_theory.outer_measure.of_function_le _ 
            (@set.indicator (set Ω) ennreal _  ({(∅:set Ω)}ᶜ) f) _ S,
  apply le_trans A2,
  clear A2,
  cases classical.em (S = ∅)  with A3 A3,
  {
    subst S,
    rw set.indicator_of_not_mem,
    {
      simp,
    },
    {
      simp,
    },
  },
  {
    rw set.indicator_of_mem,
    apply le_refl (f S),
    simp [A3],
  },
end


lemma galois_connection_measure_of_of_function' {Ω:Type*}:
  galois_connection 
      (λ μ:measure_theory.outer_measure Ω, μ.measure_of) 
      (λ f:set Ω → ennreal, measure_theory.outer_measure.of_function' f)  :=
begin
  unfold galois_connection,
  intros μ f,
  unfold measure_theory.outer_measure.of_function',
  rw measure_theory.outer_measure.le_of_function,

  split;intros A1,
  {
    intro S,
    cases (classical.em (S = ∅)) with B1 B1,
    {
      subst S,
      rw outer_measure_measure_of_def,
      rw measure_theory.outer_measure.empty,
      simp,
    },
    {
      rw set.indicator_of_mem,
      apply A1,
      simp [B1],
    },
  },
  {
    rw le_func_def2,
    intro S,
    cases (classical.em (S = ∅)) with C1 C1,
    {
      subst S,  
      rw measure_theory.outer_measure.empty,
      simp,
    },
    {
      have C2:= A1 S,
      rw set.indicator_of_mem at C2,
      apply C2,
      simp [C1],
    },
  },
end


lemma of_function_replace {Ω:Type*} {f g:set Ω → ennreal} {Hf:f ∅ = 0} {Hg:g ∅ = 0}:
    (f = g) →
    measure_theory.outer_measure.of_function f Hf =
    measure_theory.outer_measure.of_function g Hg :=
begin
  intro A1,
  apply measure_theory.outer_measure.ext,
  intro S,
  repeat {rw outer_measure_measure_of_def},
  repeat {rw measure_theory.outer_measure.of_function_def},
  rw A1,
end

lemma of_function_invariant {Ω:Type*} {μ:measure_theory.outer_measure Ω}:
    measure_theory.outer_measure.of_function (μ.measure_of) (μ.empty) = μ :=
begin
  apply le_antisymm,
  {
    rw outer_measure_measure_of_le,
    rw le_func_def2,
    intro S,
    apply measure_theory.outer_measure.of_function_le,
    apply μ.empty,
  },
  {
    rw measure_theory.outer_measure.le_of_function,
    intro S,
    apply le_refl (μ.measure_of S),
  },
end 


noncomputable def galois_insertion_measure_of_of_function' {Ω:Type*}:
  @galois_insertion (order_dual (set Ω → ennreal)) (order_dual (measure_theory.outer_measure Ω)) _ _
      (λ f:set Ω → ennreal, measure_theory.outer_measure.of_function' f)
      (λ μ:measure_theory.outer_measure Ω, μ.measure_of) 
  := 
begin
  apply galois_insertion.monotone_intro,
  {
    intros μ ν B1,
    simp,
    apply B1,
  },
  {
    intros f g C1,
    apply measure_theory.outer_measure.monotone_of_function',
    apply C1,
  },
  {
    intro f,
    apply measure_theory.outer_measure.of_function'_le,
  },
  {
    intro μ,
    unfold measure_theory.outer_measure.of_function',
    have D1:(set.indicator ({∅}ᶜ) μ.measure_of)=μ.measure_of,
    {
      apply funext,
      intro S,
      cases (classical.em (S = ∅)) with D1A D1A,
      {
        subst S,
        rw set.indicator_of_not_mem,
        rw measure_theory.outer_measure.empty,
        simp,  
      },
      {
        rw set.indicator_of_mem,
        simp [D1A],  
      },
    },
    rw of_function_replace D1,
    clear D1,
    apply of_function_invariant,  
  },
end


def strictly_monotone {α β:Type*} [preorder α] [preorder β] (f:α → β):Prop :=
  ∀ a b:α, a < b → f a < f b


lemma monotone_of_strictly_monotone {α β:Type*} [partial_order α] [partial_order β] {f:α → β}:strictly_monotone f → monotone f :=
begin
  intros A1,
  intros b1 b2 A3,
  cases (classical.em (b1 = b2)) with A4 A4,
  {
    subst b2,
  },
  {
    apply le_of_lt,
    apply A1,   
    apply lt_of_le_of_ne A3 A4,
  },
end 


/-
  This represents that for all a, a', the converse of a the monotone property holds.
 -/
def monotone_converse {α β:Type*} [partial_order α] [partial_order β] (f:α → β):Prop :=
    ∀ a a':α, f a ≤ f a' → a ≤ a'


lemma Sup_eq_Sup_of_monotone_converse {α β:Type*} [complete_lattice α] [complete_lattice β] {f:α → β} {s:set α} (a:α):monotone f →
    monotone_converse f →
    (Sup (f '' s) = f a) →
    (Sup (f '' s) = f (Sup s)) :=
begin
  intros A1 A2 A3,
  apply le_antisymm,
  {
    apply Sup_le_Sup_of_monotone A1,
  },
  {
    rw A3,
    apply A1,
    apply Sup_le,
    intros b A4,
    apply A2,
    rw ← A3,
    apply le_Sup,
    apply exists.intro b,
    apply and.intro A4 rfl,
  },
end


lemma supr_eq_supr_of_monotone_converse {α β γ:Type*} [complete_lattice α] [complete_lattice β] {f:α → β} {g:γ → α} (a:α):monotone f →
    monotone_converse f →
    (supr (f ∘ g) = f a) →
    (supr (f ∘ g) = f (supr g)) :=
begin
  intros A1 A2 A3,
  apply le_antisymm,
  {
    apply supr_le_supr_of_monotone A1,
  },
  {
    rw A3,
    apply A1,
    apply Sup_le,
    intros b A4,
    apply A2,
    rw ← A3,
    cases A4 with y A4,
    subst b,
    apply le_supr (f ∘ g),
  },
end

lemma infi_eq_infi_of_monotone_converse {α β γ:Type*} [complete_lattice α] [complete_lattice β] {f:α → β} {g:γ → α} (a:α):monotone f →
    monotone_converse f →
    (infi (f ∘ g) = f a) →
    (infi (f ∘ g) = f (infi g)) :=
begin
  intros A1 A2 A3,
  apply le_antisymm,
  {
    rw A3,
    apply A1,
    apply le_infi,
    intros b,
    apply A2,
    rw ← A3,
    apply infi_le,
  },
  {
    apply infi_le_infi_of_monotone A1,
  },
end

lemma Inf_eq_Inf_of_monotone_converse {α β:Type*} [complete_lattice α] [complete_lattice β] {f:α → β} {s:set α} (a:α):monotone f →
    monotone_converse f →
    (Inf (f '' s) = f a) →
    (Inf (f '' s) = f (Inf s)) :=
begin
  intros A1 A2 A3,
  apply le_antisymm,
  {
    rw A3,
    apply A1,
    apply le_Inf,
    intros b A4,
    apply A2,
    rw ← A3,
    apply Inf_le,
    simp,
    apply exists.intro b,
    split,
    apply A4,
    refl,
  },
  {
    apply Inf_le_Inf_of_monotone A1,
  },
end


lemma monotone_converse_to_outer_measure_measure_of {Ω:Type*} [measurable_space Ω]:
    monotone_converse (λ μ:measure_theory.measure Ω, μ.to_outer_measure.measure_of) :=
begin
  intros μ ν A1,
  intros s A2,
  apply A1,
end


--TODO: write infi_eq_infi_to_outer_measure_measure_of,
-- or better, Inf_eq_Inf_to_outer_measure_measure_of...
lemma supr_eq_supr_to_outer_measure_measure_of {α γ:Type*}
   [measurable_space α]  {g:γ → measure_theory.measure α} 
   (μ:measure_theory.measure α):
    (supr ((λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) ∘ g) =
     (λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) μ) →
    (supr ((λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) ∘ g) =
    (λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) (supr g)) :=
begin
  intros A1,
  apply supr_eq_supr_of_monotone_converse μ,
  apply monotone_to_outer_measure_measure_of,
  apply monotone_converse_to_outer_measure_measure_of,
  apply A1,
end


-- This would be better if it required only for all measurable sets.
lemma supr_eq_supr_of_apply {α γ:Type*}
   [measurable_space α]  {g:γ → measure_theory.measure α} 
   {μ:measure_theory.measure α}:
    (∀ (s:set α), 
    (supr ((λ ν:measure_theory.measure α, ν s) ∘ g) = μ s)) →
    (supr ((λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) ∘ g) =
    (λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) (supr g)) :=
begin
  intros A1,
  apply supr_eq_supr_to_outer_measure_measure_of μ,
  apply funext,
  intro s,
  rw supr_apply,
  simp,
  apply A1,
end


lemma dual_galois_insertion.l_infi_u' {α : Type*} {β : Type*} {l : α → β} {u : β → α}
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β]: 
   @galois_insertion (order_dual α) (order_dual β) _ _ l u → ∀ {ι : Type*} (f : ι → β), l (⨅ (i : ι), u (f i)) = ⨅ (i : ι), f i :=
begin
  intros A1 γ f,
  have A2 := @galois_insertion.l_supr_u (order_dual α) (order_dual β) l u _ _ A1 γ f,
  apply A2,
end

lemma dual_galois_insertion.l_supr_u' {α : Type*} {β : Type*} {l : α → β} {u : β → α}
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β]: 
   @galois_insertion (order_dual α) (order_dual β) _ _ l u → ∀ {ι : Type*} (f : ι → β), l (⨆  (i : ι), u (f i)) = ⨆  (i : ι), f i :=
begin
  intros A1 γ f,
  have A2 := @galois_insertion.l_infi_u (order_dual α) (order_dual β) l u _ _ A1 γ f,
  apply A2,
end


lemma galois_insertion.le_iff_u_le_u {α : Type*} {β : Type*} {l : α → β} {u : β → α}
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β] {b b':β}: 
   @galois_insertion α β _ _ l u → 
   ((b ≤ b') ↔ (u b ≤ u b')) :=
begin
  intro A1,
  split;intros A2,
  {
    apply A1.gc.monotone_u A2,
  },
  {
    rw ← A1.gc at A2,
    rw A1.l_u_eq at A2,
    apply A2,
  },
end

lemma galois_insertion.Sup_u_eq_u_Sup {α : Type*} {β : Type*} {l : α → β} {u : β → α}
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β]: 
   @galois_insertion α β _ _ l u → 
   ∀ (S:set β), (∃ b:β, u b = Sup (u '' S)) →  u (Sup S)  = Sup (u '' S) :=
begin
  intros A1 S A2,
  cases A2 with b A2,
  apply le_antisymm,
  {
    rw ← A2,
    have A3 := A1.gc.monotone_u,
    apply A3,
    apply Sup_le,
    intros b' A4,
    rw A1.le_iff_u_le_u,
    rw A2,
    apply le_Sup,
    simp,
    apply exists.intro b',
    apply and.intro A4 _,
    refl,
  },
  {
    apply Sup_le,
    intros a A3,
    rw ← A1.gc,
    apply le_Sup,
    simp at A3,
    cases A3 with  b' A3,
    cases A3 with A3 A4,
    subst a,
    rw A1.l_u_eq,
    apply A3,
  },
end

lemma dual_galois_connection.u_Sup {α β : Type*}
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β] 
   {l : α → β} {u : β → α}:
   @galois_connection (order_dual α) (order_dual β) _ _ l u →
   ∀ (s : set β), u (Sup s) = (⨆a∈s, u a) :=
begin
  intros A1 s,
  apply A1.u_Inf,
end

lemma dual_galois_connection.u_supr {α β : Type*} {ι: Sort*} 
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β] 
   {l : α → β} {u : β → α}:
   @galois_connection (order_dual α) (order_dual β) _ _ l u →
   ∀  (γ:Type*) (f : γ → β), u (supr f) = (⨆a, u (f a)) :=
begin
  intros A1 γ f,
  apply A1.u_infi,
end

-- A local function for mapping the supremum as a function back to a measure.
-- It is sufficient that such a measure exists.
noncomputable def supr_as_fun {α:Type*} [measurable_space α] 
    (f:ℕ → (measure_theory.measure α)):Π (s:set α), (is_measurable s) → ennreal :=
  (λ s H,(⨆ n:ℕ, f n s)) 


lemma supr_as_fun_apply {α:Type*} [measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (s:set α) (H:is_measurable s):
   supr_as_fun f s H = (⨆ n:ℕ, f n s) := rfl


lemma supr_as_fun_empty {α:Type*} [measurable_space α] 
    {f:ℕ → (measure_theory.measure α)}:
  (supr_as_fun f) ∅ is_measurable.empty = 0 := 
begin
  unfold supr_as_fun,
  have A1:(λ n:ℕ, f n ∅ ) = 0,
  {
    apply funext,
    intro n,
    apply measure_theory.measure_empty,
  },
  rw A1,
  apply @supr_const ennreal ℕ _ _ 0,
end


lemma supr_sum_le_sum_supr {g:ℕ → ℕ → ennreal}:
  (⨆ m:ℕ, ∑' n, g m n) ≤
  (∑' m, ⨆ n:ℕ,  g n m) := 
begin
    apply @supr_le ennreal ℕ _,
    intro i,
    apply @tsum_le_tsum ennreal ℕ _ _,
    intro b,
    apply @le_supr ennreal ℕ _,
    repeat {apply ennreal.summable},
end






lemma tsum_single  {α : Type*} {β : Type*} [_inst_1 : add_comm_monoid α] [_inst_2 : topological_space α] [t2_space α] {f : β → α} (b : β): (∀ (b' : β), b' ≠ b → f b' = 0) → tsum f = (f b) :=
begin
  intro A1,
  have A2:=has_sum_single b A1,
  have A3:summable f := has_sum.summable A2, 
  rw ← summable.has_sum_iff A3,
  apply A2,
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


lemma supr_sum_eq_sum_supr {g:ℕ → ℕ → ennreal}:
  monotone g →
  (⨆ m:ℕ, ∑' n, g m n) = 
  (∑' m, ⨆ n:ℕ,  g n m) := 
begin
  intro A1,
  apply le_antisymm,
  {
    apply supr_sum_le_sum_supr,
  },
  {
    rw ← @ennreal.tsum_le (λ m, ⨆ n:ℕ,  g n m) (⨆ m:ℕ, ∑' n, g m n),
    intros n2,
    have A2:(λ m, (finset.range n2).sum (g m)) ≤ (λ m, ∑' n, g m n),
    {
      rw le_func_def2,
      intro m,
      simp,
      apply ennreal.finset_sum_le_tsum,
    },
    have A3:(⨆  m, (finset.range n2).sum (g m)) ≤ (⨆ m, ∑' n, g m n),
    {
      apply supr_le_supr A2,
    },
    apply le_trans _ A3,
    rw @ennreal.finset_sum_supr_nat ℕ ℕ _ (finset.range n2) (λ m n, g n m), 
    simp,
    intro i,
    apply @le_supr ennreal ℕ _,
    intros a,
    simp,
    intros x y A4,
    simp,
    apply A1,
    apply A4,
  },
end

lemma supr_as_fun_m_Union {α:Type*} [M:measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (H:monotone f):
(∀ {g : ℕ → set α} (h : ∀ (i : ℕ), is_measurable (g i)), 
  pairwise (disjoint on g) → 
 ((supr_as_fun f) (⋃ (i : ℕ), g i) (M.is_measurable_Union g h)) = 
  ∑' (i : ℕ), (supr_as_fun f) (g i) (h i)) :=
begin
  intros g h A1,
  rw supr_as_fun_apply,
  have A2:(λ i, supr_as_fun f (g i) (h i)) = (λ i, (⨆ n:ℕ, f n (g i) )),
  {
    apply funext,
    intro i,
    rw supr_as_fun_apply,
  },
  rw A2,
  clear A2,
  have A3:(λ (n : ℕ), (f n) (⋃ (i : ℕ), g i))= (λ (n : ℕ),∑' i,  (f n) (g i)),
  {
    apply funext,
    intro n,
    apply (f n).m_Union h A1,
  },
  rw A3,
  clear A3,
  apply supr_sum_eq_sum_supr,
  intros x y A4,
  simp,
  intro n,
  apply H,
  apply A4,
  apply h,
end

noncomputable def supr_as_measure {α:Type*} [M:measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (H:monotone f):measure_theory.measure α :=
  measure_theory.measure.of_measurable (supr_as_fun f) (@supr_as_fun_empty α M f)
  (@supr_as_fun_m_Union α M f H)


lemma supr_as_measure_def {α:Type*} [M:measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (H:monotone f):(supr_as_measure f H) =
  measure_theory.measure.of_measurable (supr_as_fun f) (@supr_as_fun_empty α M f)
  (@supr_as_fun_m_Union α M f H) := rfl


lemma supr_as_measure_apply {α:Type*} [M:measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (H2:monotone f) (s:set α) (H:is_measurable s):
  (supr_as_measure f H2) s = (λ s,(⨆ n:ℕ, f n s))  s := 
begin
  rw supr_as_measure_def,
  rw measure_theory.measure.of_measurable_apply s H,
  rw supr_as_fun_apply f s,
end


lemma measure_theory.measure.Union_nat {α : Type*} [M : measurable_space α] 
    {μ:measure_theory.measure α} {f:ℕ → set α}:μ (⋃ i, f i) ≤ ∑' i, μ (f i) :=
begin
  rw measure.apply,
  have A1:(λ i, μ (f i))=(λ i, μ.to_outer_measure.measure_of (f i)) := rfl,
  rw A1,
  apply measure_theory.outer_measure.Union_nat,
end


lemma infi_eq_infi {α β:Type*} [has_Inf β] {f:α → β} {g:α → β}:
    (∀ a:α, f a =  g a) →
    (⨅ a:α, f a) = ⨅ a:α, g a :=
begin
  intro A1,
  have A2:f = g,
  {
    ext,
    apply A1,
  },
  rw A2,
end  

lemma supr_eq_supr {α β:Type*} [has_Sup β] {f:α → β} {g:α → β}:
    (∀ a:α, f a =  g a) →
    (⨆ a:α, f a) = ⨆ a:α, g a :=
begin
  intro A1,
  have A2:f = g,
  {
    ext,
    apply A1,
  },
  rw A2,
end 


lemma infi_commute_helper {α β:Sort} {γ:Type*} [complete_lattice γ] {f:α → β → γ}:
    (⨅ a:α,⨅ b:β, f a b) ≤ ⨅ b:β, ⨅ a:α, f a b :=  
begin
    apply le_infi,
    intro b,
    apply le_infi,
    intro a,
    have A1:(⨅ (a : α) (b : β), f a b)≤(⨅ (b : β), f a b),
    {
      apply infi_le,
    },
    apply le_trans A1,
    apply infi_le,
end  


lemma infi_commute {α β:Sort} {γ:Type*} [complete_lattice γ] {f:α → β → γ}:
    (⨅ a:α,⨅ b:β, f a b) = ⨅ b:β, ⨅ a:α, f a b :=  
begin
  apply le_antisymm,
  {
    apply infi_commute_helper,
  },
  {
    apply infi_commute_helper,
  },
end  


lemma measure_theory.measure.to_outer_measure_def {α : Type*} [M : measurable_space α] 
    {μ:measure_theory.measure α} {s:set α}:
   μ s = ⨅ (s':set α) (H:is_measurable s') (H2:s⊆ s'), μ s' :=
begin
  rw measure_theory.measure_eq_infi,
  apply infi_eq_infi,
  intro s',
  rw infi_commute,
end


lemma measure_theory.measure.of_measurable_apply3 {α : Type*} [M : measurable_space α] 
    {m : Π (s : set α), is_measurable s → ennreal} {m0 : m ∅ is_measurable.empty = 0} 
    {mU : ∀ (f : ℕ → set α) (h : ∀ (i : ℕ), is_measurable (f i)), pairwise (disjoint on f) → (m
    (⋃ (i : ℕ), f i) (M.is_measurable_Union f h)) = ∑' (i : ℕ), m (f i) (h i)} 
  (s : set α): 
   (measure_theory.measure.of_measurable m m0 mU) s = 
    ⨅ (s':set α) (H:is_measurable s') (H2:s⊆ s'), m s' H :=
begin
  rw measure_theory.measure.to_outer_measure_def,
  have A1:(λ s':set α, ⨅  (H : is_measurable s') (H2 : s ⊆ s'), (measure_theory.measure.of_measurable m m0 mU) s') =
    (λ s':set α,  ⨅ (H : is_measurable s') (H2 : s ⊆ s'), m s' H),
  {
    apply funext,
    intro s',
    have A1A:(λ (H : is_measurable s'), ⨅ (H2 : s ⊆ s'), 
             (measure_theory.measure.of_measurable m m0 mU) s') =
             λ (H : is_measurable s'), ⨅  (H2 : s ⊆ s'), m s' H,
    {
      apply funext,
      intro A1A1,
      have A1A2:(λ (H2 : s ⊆ s'), (measure_theory.measure.of_measurable m m0 mU) s') =
                 λ  (H2 : s ⊆ s'), m s' A1A1,
      {
        apply funext,
        intro A1A2A,
        apply @measure_theory.measure.of_measurable_apply α M m m0 mU,
      },
      rw A1A2,
    },
    rw A1A,
  },
  rw A1,
end


lemma supr_as_measure_apply2 {α:Type*} [M:measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (H2:monotone f) (s:set α):
  (supr_as_measure f H2) s = ⨅ (s':set α) (H:is_measurable s') (H2:s⊆ s'),  (⨆ n:ℕ, f n s') := 
begin
  rw supr_as_measure_def,
  rw measure_theory.measure.of_measurable_apply3,
  have A1:(λ (s' : set α), ⨅ (H : is_measurable s') (H2 : s ⊆ s'), supr_as_fun f s' H) =
    λ (s' : set α), ⨅ (H : is_measurable s') (H2 : s ⊆ s'), ⨆ (n : ℕ), (f n) s',
  {
    apply funext,
    intro s',
    have A1A:(λ (H : is_measurable s'), ⨅ (H2 : s ⊆ s'), supr_as_fun f s' H) =
              λ (H : is_measurable s'), ⨅ (H2 : s ⊆ s'), ⨆ (n : ℕ), (f n) s',
    {
      apply funext,
      intro H,
      have A1A1:(λ (H2 : s ⊆ s'), supr_as_fun f s' H) =
              λ  (H2 : s ⊆ s'), ⨆ (n : ℕ), (f n) s',
      {
        apply funext,
        intro H2,
        rw supr_as_fun_apply,
      },
      rw A1A1,
    },
    rw A1A,
  },
  rw A1,
end


lemma supr_eq_supr_to_outer_measure_measure_of_of_monotone {α:Type*}
   [M:measurable_space α]  {g:ℕ → measure_theory.measure α}
   :monotone g → 
    (supr ((λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) ∘ g) =
    (λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) (supr g)) :=
begin
  intro A1,
  apply @supr_eq_supr_to_outer_measure_measure_of α ℕ M g (@supr_as_measure α M g A1),
  simp,
  apply funext,
  intro s,
  rw supr_as_measure_apply2,
  apply le_antisymm,
  {
    apply @le_infi ennreal (set α) _,
    intro s',
    apply @le_infi ennreal _ _,
    intro H,
    apply @le_infi ennreal _ _,
    intro H2,
    rw supr_apply,
    apply @supr_le_supr ennreal ℕ _,
    intro n,
    apply measure_theory.measure_mono,
    apply H2,
  },
  {
    rw supr_apply,    
    have C1:(λ (i : ℕ), (g i) s)
            = λ i, ⨅ (s':set α) (H:is_measurable s') (H2:s⊆ s'), (g i) s' ,
    {
      apply funext,
      intro i,
      apply measure_theory.measure.to_outer_measure_def,
    },
    rw C1,
    clear C1,
    apply ennreal.infi_le,
    intros ε C2 C3,

    have C4:∃ (f:ℕ → (set α)), (∀ i:ℕ, 
        (is_measurable (f i)) ∧
        (s ⊆ (f i)) ∧
         ((g i (f i)) ≤ 
      ( ⨅ (s' : set α) (H : is_measurable s') (H2 : s ⊆ s'), (g i) s') + (ε:ennreal))), 
    {
      have C4A:(∀ i:ℕ, ∃  s'':set α,
        (is_measurable (s'')) ∧
        (s ⊆ (s'')) ∧
         ((g i (s'')) ≤ 
      ( ⨅ (s' : set α) (H : is_measurable s') (H2 : s ⊆ s'), (g i) s') + (ε:ennreal))), 
      {
        intro i,
        rw @lt_top_iff_ne_top ennreal _ _ at C3,
        have C4B:=@ne_top_of_supr_ne_top ℕ _ i C3,
        have C4C:(⨅ (s' : set α) (H : is_measurable s') (H2 : s ⊆ s'), (g i) s')≠ ⊤ ,
        {
          apply C4B,
        },
        
        have C4E := lt_top_iff_ne_top.mpr C4C,
        have C4D := ennreal.infi_elim C2 C4E,
        cases C4D with s'' C4D,
        apply exists.intro s'',
        simp at C4D,
        have C4F: (⨅ (s' : set α) (H : is_measurable s') (H2 : s ⊆ s'), (g i) s') + ↑ε < ⊤,
        {
          rw with_top.add_lt_top,
          split,
          apply C4E,
          simp,
        },
        have C4G := lt_of_le_of_lt C4D C4F,
        have C4H := of_infi_lt_top C4G,
        rw infi_prop_def at C4G,
        have C4I := of_infi_lt_top C4G,
        rw infi_prop_def at C4G,        
        split,
        {
          apply C4H,
        },
        split,
        {
          apply C4I,
        },
        rw infi_prop_def at C4D,
        rw infi_prop_def at C4D,
        apply C4D,
        apply C4I,
        apply C4H,
        apply C4I,
        apply C4H,
      },
      apply @classical.some_func ℕ (set α) _ C4A,
    },
    cases C4 with f C4,
    apply exists.intro (set.Inter f),
    rw infi_prop_def,
    rw infi_prop_def,
    rw ennreal.supr_add,
    apply @supr_le_supr ennreal ℕ _ (λ n, (g n) (set.Inter f)),
    {
      intro i,   
      have D1:(λ (n : ℕ), (g n) (set.Inter f)) i ≤ (g i) (f i),
      {
        simp,
        apply measure_theory.measure_mono,
        apply @set.Inter_subset α ℕ f,
      },
      apply le_trans D1 (C4 i).right.right,  
    },
    {
      apply set.subset_Inter,
      intro i,
      apply (C4 i).right.left,      
    },
    {
      apply is_measurable.Inter,
      intro i,
      apply (C4 i).left,      
    },
  },
end


lemma supr_eq_supr_to_outer_measure_measure_of_of_monotone' {α:Type*}
   [M:measurable_space α]  {g:ℕ → measure_theory.measure α}
   :monotone g → 
    (supr ((λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) ∘ g) =
    (supr g).to_outer_measure.measure_of) :=
begin
  apply supr_eq_supr_to_outer_measure_measure_of_of_monotone,
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



lemma finset.sup_closed {α β:Type*} [decidable_eq α] 
   [semilattice_sup_bot β]
   (S:finset α) 
   (f:α → β) (T:set β):
   (⊥ ∈ T) →
   (∀ a∈ S, f a ∈ T) →
   (∀ a∈ T, ∀ b∈ T, a⊔b ∈ T) →
   (S.sup f ∈ T) :=
begin
  intros A1 A2 A3,
  revert A2,
  apply finset.induction_on S,
  {
    intros B1,
    simp,
    apply A1,
  },
  {
    intros a S C1 C2 C3,
    simp,
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
    },
  },
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


/- For supr_measure_eq_measure_supr, this is a more
   useful rewrite, as (finset.range (nat.succ n)).sum f = f n -/ 
lemma ennreal.lim_finset_sum_succ_eq_tsum {f:ℕ → ennreal}:
(⨆  n, (finset.range (nat.succ n)).sum f)  = tsum f :=
begin
  apply le_antisymm,
  {
    apply @supr_le ennreal _ _,
    intro n,
    apply ennreal.finset_sum_le_tsum,
  },
  {
    rw ← ennreal.tsum_le,
    intro n,
    cases n,
    {
      simp,
    },
    {
      apply @le_supr ennreal _ _,
    },
  }
end


/-
  This is useful to prove Hahn decomposition.
  No wait, it's not.
 -/
lemma supr_measure_eq_measure_supr {α:Type*}
    [M:measurable_space α] {μ:measure_theory.measure α}
    {f:ℕ → set α}:(∀ n, is_measurable (f n)) →
    monotone f →
    supr (λ n, μ (f n)) = μ (supr f) :=
begin
  intros A1 A2,
  rw supr_eq_Union,
  rw ← Union_sub_pred,
  rw measure.apply,
  rw measure_theory.measure.m_Union,
  rw ← ennreal.lim_finset_sum_succ_eq_tsum,
  have A3:(λ (i : ℕ), μ.to_outer_measure.measure_of (sub_pred f i))
          = (λ (i : ℕ), μ (sub_pred f i)),
  {
    apply funext,
    intro i,
    rw measure.apply,
  },
  rw A3,
  have A5:(λ (n : ℕ), finset.sum (finset.range n.succ)
          (λ (i : ℕ), μ (sub_pred f i)))=
          (λ n, μ (f n) ),
  {
    apply funext,
    intro n,
    rw @measure_finset_sum α M μ (sub_pred f) _,
    rw union_range_sub_pred,
    rw union_finset_range_monotone,
    apply A2,
    intro m,
    apply is_measurable_sub_pred A1,
    apply sub_pred_pairwise_disjoint,
    apply A2,
  },
  rw A5,
  intro m,
  apply is_measurable_sub_pred A1,
  apply sub_pred_pairwise_disjoint,
  apply A2,
end


/-
  This theorem is immediately useful to prove the
  existence of the Radon-Nikodym derivative, if 
  α = measure_theory.measure Ω, and g = (λ μ, μ T)
  (see Sup_apply_eq_supr_apply_of_closed). 
  However, if α = set Ω, and g = μ, then this
  can be used to prove the Hahn decomposition variant.
  The critical proof is that supr (μ T) =
  μ (supr T).
 -/
lemma Sup_apply_eq_supr_apply_of_closed' {α:Type*}
  [complete_lattice α] {S:set α} (g:α → ennreal):
  (∀ (a∈ S) (b∈ S), a ≤ b → g a ≤ g b) →
  (∀ f:ℕ → α, (set.range f ⊆ S) → 
               monotone f → supr (g ∘ f) = g (supr f)) →
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
    rw ← AX,
    apply le_antisymm,
    {
      apply @supr_le ennreal _ _,
      intro n,
      apply @le_Sup ennreal _ _,
      simp,
      apply exists.intro (Sup_so_far f'' n),
      apply and.intro (C1 n),
      refl,   
    },
    {
      rw ← B1X.right,
      apply @supr_le_supr ennreal _ _,
      intros n,
      rw ← (B2 n).right,
      simp,
      apply A1,
      apply (B2 n).left,
      apply C1 n,
      apply le_Sup_so_far,
    },
    {
      rw set.subset_def,
      intros x C2,
      simp at C2,
      cases C2 with n C2,
      rw ← C2,
      apply C1,
    },
    apply monotone_Sup_so_far,
  },
end



/- This lemma presents a pattern that is repeated
   many times, both for Hahn decomposition and for
   the Lebesgue-Radon-Nikodym theorem. -/
lemma Sup_apply_has_max {α:Type*}
  [complete_lattice α] {S:set α} (g:α → ennreal):
  (∀ (a∈ S) (b∈ S), a ≤ b → g a ≤ g b) →
  (∀ f:ℕ → α, (set.range f ⊆ S) → 
               monotone f → supr (g ∘ f) = g (supr f)) →
  (∀ f:ℕ → α, (set.range f ⊆ S) → 
               monotone f → supr f ∈ S) → 
  (S).nonempty →
  (∀ a ∈ S, ∀ b ∈ S, a ⊔ b ∈ S)→
  (∃ a∈ S, g a = Sup (g '' S)) :=
begin
  intros A1 A2 A3 A4 A5,
  have B1 := Sup_apply_eq_supr_apply_of_closed' g A1 A2 A4 A5,
  cases B1 with f B1,
  apply exists.intro (supr f),
  have C1:set.range f ⊆ S,
  {
    rw set.range_subset_iff,
    apply B1.left,
  },
  have C2 := A3 f C1 B1.right.left,
  apply exists.intro C2,
  apply B1.right.right,
end


lemma Sup_apply_eq_supr_apply_of_closed {α:Type*}
   [M:measurable_space α]  {S:set (measure_theory.measure α)}
   {T:set α}:
  (S.nonempty) →
  (is_measurable T) →
  (∀ μ ∈ S, ∀ ν ∈ S, μ ⊔ ν ∈ S)→
  (∃ f:ℕ → (measure_theory.measure α),
            (∀ n, f n ∈ S) ∧ 
            (monotone f) ∧
            (supr f T = Sup ((λ μ:measure_theory.measure α, μ T) '' S))) :=
begin
  intros A1 A2 A3,
  apply @Sup_apply_eq_supr_apply_of_closed' (measure_theory.measure α) _ S (λ μ:measure_theory.measure α, μ T),
  {
     intros x B1 y B2 B3,
     apply monotone_to_outer_measure_measure_of,
     apply B3,
  },
  {
    intros f CX C1,
    simp,
    have C2:= supr_eq_supr_to_outer_measure_measure_of_of_monotone' C1,
    rw measure.apply,
    rw ← C2,
    rw supr_apply,
    refl,
  },
  {
    apply A1,
  },
  {
    apply A3,
  },
end


/- Note that for outer measures, the supremum commutes with measure_of, in a way. -/
lemma of_function'_supr_measure_of_eq_supr {Ω γ:Type*}
    {h:γ → (measure_theory.outer_measure Ω)}:
      (λ f:set Ω → ennreal, measure_theory.outer_measure.of_function' f)
      (⨆ (i:γ), 
      (λ μ:measure_theory.outer_measure Ω, μ.measure_of) (h i))
      = supr h 
  := 
begin
  apply dual_galois_insertion.l_supr_u',
  apply @galois_insertion_measure_of_of_function' Ω,
end


lemma monotone_integral {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.measure Ω} {f g:Ω → ennreal}:f ≤ g → 
    (μ.integral f)≤μ.integral g :=
begin
  intro A1,
  apply measure_theory.lintegral_mono,
  apply A1,
end

lemma monotone_integral' {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.measure Ω} {f g:Ω → ennreal}:monotone (μ.integral) :=
begin
  apply monotone_integral,
end


-- TODO(martinz): remove measurability requirement?
lemma monotone_with_density {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.measure Ω}
    {f:ℕ → (Ω → ennreal)}:
    monotone f →
    (∀ n, measurable (f n)) → 
    monotone ((μ.with_density) ∘ f) :=
begin
  intros B1 B2 a b A1,
  intros S A2,
  rw measure_theory.with_density_apply2,
  rw measure_theory.with_density_apply2,
  apply monotone_integral,
  apply @monotone_set_indicator Ω ennreal _ _,
  apply B1,
  apply A1,
  --apply B2,
  apply A2,
  --apply B2,
  apply A2,
end


-- Update: I am using this now in R-N theorem.
-- It's not clear to me anymore that this is necessary.
-- However, I am fairly certain it is true.
-- What is missing is proving that (λ i, with_density (h i)) itself is a
-- monotone. It is also probably useful.
lemma supr_with_density_eq_with_density_supr {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.measure Ω}
    {h:ℕ → Ω → ennreal}:
    (∀ n:ℕ, measurable (h n)) →
    (monotone h) →
    supr (λ n:ℕ, μ.with_density (h n)) = μ.with_density (supr h) :=
begin
  intros A1 A2,
  apply measure_theory.measure.ext,
  intros S A3,
  rw ← @supr_with_density_apply_eq_with_density_supr_apply Ω M μ h S A3 A1 A2,
  rw measure.apply,
  rw ← @supr_eq_supr_to_outer_measure_measure_of_of_monotone' Ω M (λ n, μ.with_density (h n)),
  rw supr_apply,
  apply @supr_eq_supr ℕ ennreal _,
  intro n,
  refl,
  apply monotone_with_density,
  apply A2,
  apply A1,
end 




-- The nature of this proof suggests the lemma already exists.
lemma measure_theory.measure.sup_le {Ω:Type*} {N:measurable_space Ω} (μ₁ μ₂ ν:measure_theory.measure Ω):μ₁ ≤ ν → μ₂ ≤ ν → μ₁ ⊔ μ₂ ≤ ν :=
begin
  intros A1 A2,
  simp,
  apply and.intro A1 A2,
end


lemma sup_fun_def {Ω:Type*} {f g:Ω → ennreal}:
    (f ⊔ g) = λ ω:Ω, f ω ⊔ g ω :=
begin
  refl
end

--TODO:remove, trivial?
lemma ennreal.sup_apply {Ω:Type*} {f g:Ω → ennreal} {x:Ω}:
    (f ⊔ g) x = f x ⊔ g x :=
begin
  apply sup_apply,
end


--Extensible to a (complete?) linear order.
lemma ennreal.lt_sup_iff {a b c:ennreal}:
  c < a ⊔ b ↔ c < a ∨ c < b :=
begin
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


lemma measurable_sup {Ω:Type*} {M:measurable_space Ω} 
  {f g:Ω → ennreal}:measurable f → measurable g → 
    measurable (f ⊔ g) :=
begin
  intros A1 A2,
  /- Proof sketch:
     x is measurable iff if ∀ a, x⁻¹ (a,⊤] is measurable.
     (f ⊔ g)⁻¹ (a,⊤] =f⁻¹ (a,⊤]∪g⁻¹ (a,⊤].
     Since the union of two measurable functions is measurable,
     we are done.
   -/ 
  apply is_ennreal_measurable_intro_Ioi,
  intro a,
  have A3:(f ⊔ g) ⁻¹' {y : ennreal | a < y}=
      f ⁻¹' {y : ennreal | a < y}∪
      g ⁻¹' {y : ennreal | a < y},
  {
    simp,
    ext,
    split;intros A3A;simp at A3A;simp;apply A3A,
  },
  rw A3,
  apply is_measurable.union,
  {
    apply A1,
    apply is_ennreal_is_measurable_intro_Ioi,
  },
  {
    apply A2,
    apply is_ennreal_is_measurable_intro_Ioi,
  },
end



--Could remove, but let's leave it here for now.
lemma ennreal.is_measurable_le {Ω:Type*} {M:measurable_space Ω}
  {x y:Ω → ennreal}:measurable x → measurable y →
  is_measurable {ω:Ω|x ω ≤ y ω} :=
begin
  intros A1 A2,
  apply is_measurable_le A1 A2,
end



lemma with_density_le_with_density {Ω:Type*} {M:measurable_space Ω}
  {μ:measure_theory.measure Ω} {x y:Ω → ennreal} 
  {S:set Ω}:
  is_measurable S →
  (∀ ω ∈ S, x ω ≤ y ω) →  
  μ.with_density x S ≤ μ.with_density y S :=
begin
  intros A3 A4,
  rw measure_theory.with_density_apply2 μ x S A3,
  rw measure_theory.with_density_apply2 μ y S A3,
  apply integral.monotone,
  rw le_func_def2,
  intros ω,
  cases (classical.em (ω ∈ S)) with A5 A5,
  {
    rw set.indicator_of_mem A5,
    rw set.indicator_of_mem A5,
    apply A4 _ A5,
  },
  {
    rw set.indicator_of_not_mem A5,
    rw set.indicator_of_not_mem A5,
    apply le_refl _,
  },
end


--TODO(martinz): Remove measurability?
lemma with_density_sup_of_le {Ω:Type*} {M:measurable_space Ω}
  {μ:measure_theory.measure Ω} {x y:Ω → ennreal} 
  {S:set Ω}:measurable x → measurable y →
  is_measurable S →
  (∀ ω ∈ S, x ω ≤ y ω) →  
  μ.with_density (x⊔y) S = μ.with_density y S :=
begin
  intros A1 A2 A3 A4,
  rw measure_theory.with_density_apply2 μ (x ⊔ y) S A3,
  rw measure_theory.with_density_apply2 μ y S A3,
  have A5:set.indicator S (x ⊔ y) = set.indicator S y,
  {
    apply funext,
    intro ω,
    cases (classical.em (ω∈ S)) with A5A A5A,
    {
      rw set.indicator_of_mem A5A,
      rw set.indicator_of_mem A5A,
      rw sup_apply,
      simp,
      apply max_eq_right (A4 _ A5A),
      --simp,
    },
    {
      rw set.indicator_of_not_mem A5A,
      rw set.indicator_of_not_mem A5A,
    },
  },
  rw A5,
end


lemma measure_theory.measure.sup_le_apply {Ω:Type*}
  {M:measurable_space Ω}
  {μ ν m:measure_theory.measure Ω}
  {S:set Ω}:is_measurable S →
  (μ ≤ m) →
  (ν ≤ m) → 
  (μ ⊔ ν) S ≤ m S :=
begin
  intros A1 A2 A3,
  have A4:μ ⊔ ν ≤ m := 
      @sup_le (measure_theory.measure Ω) _ μ ν m A2 A3,
  apply A4,
  apply A1,
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
    (∀ X':set α,  (X' ⊆ X) → (μ X' < ν X')  →  
    ¬ (le_on_subsets μ ν X'))


lemma hahn_crazy_set_def {α:Type*} [M:measurable_space α] 
  (μ ν:measure_theory.measure α) (X:set α):
  hahn_crazy_set μ ν X =
    ((μ X < ν X) ∧ 
    is_measurable X ∧ 
    (∀ X':set α,  (X' ⊆ X) → (μ X' < ν X')  →  
    ¬ (le_on_subsets μ ν X'))) := rfl



lemma measure_theory.measure_diff' {α:Type*}
    [measurable_space α] {μ:measure_theory.measure α}
    {s₁ s₂:set α}:s₂ ⊆ s₁ →  is_measurable s₁ →
    is_measurable s₂ → μ s₂ < ⊤ →
    μ (s₁ \ s₂) = μ s₁ - μ s₂ :=
begin
  apply measure_theory.measure_diff,
end





--The contradiction proofs chip away at this set. This
--theorem shows that when you chip a piece off a crazy set,
--a crazy set remains.
lemma hahn_crazy_set_subset {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α)
  (X:set α) (X':set α):
  hahn_crazy_set μ ν X → 
  X' ⊆ X →
  is_measurable X' →
  --μ X' < ⊤ →
  ν X' ≤ μ X' →
  hahn_crazy_set μ ν (X\X') :=
begin
  intros A1 A2 A3 A5,
  rw hahn_crazy_set_def at A1,
  have A4:μ X' < ⊤,
  {
    have A4A:μ X' ≤ μ X,
    {
      apply measure_theory.measure_mono A2,
    },
    apply lt_of_le_of_lt A4A,
    apply lt_of_lt_of_le A1.left,
    apply @le_top ennreal _,
    --A1.left,
  },
  have B1:is_measurable (X \ X'),
  {
    apply is_measurable.diff A1.right.left A3,
  },
  have B2:μ (X \ X') < ν (X \ X'),
  {
    rw measure_theory.measure_diff' A2 A1.right.left A3 A4, 
    rw measure_theory.measure_diff' A2 A1.right.left A3
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
  rw hahn_crazy_set_def,
  apply and.intro B2,
  apply and.intro B1,
  intros X'' C1 C2,
  apply A1.right.right,
  apply @set.subset.trans α X'' (X \ X') X C1,
  apply set.diff_subset,
  apply C2,
end

lemma hahn_crazy_set_self {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α)
  (X:set α):hahn_crazy_set μ ν X →
  ¬le_on_subsets μ ν X :=
begin
  intros A1,
  rw hahn_crazy_set_def at A1,
  apply A1.right.right X (set.subset.refl _) A1.left,
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



lemma hahn_crazy_diff_set_nonempty {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α):is_measurable X → 
  ¬le_on_subsets ν μ X →
  (hahn_crazy_diff_set μ ν X).nonempty :=
begin
  intros A1 A2,
  rw ← set.ne_empty_iff_nonempty,
  intro A3,
  apply A2,
  rw le_on_subsets_def,
  apply and.intro A1,
  intros X' B1 B2,
  rw hahn_crazy_diff_set_def at A3,
  apply @le_of_not_lt ennreal _,
  intro C1,
  rw set.eq_empty_iff_forall_not_mem at A3,
  have C2 := A3 X',
  simp at C2,
  have C3 := C2 B1 B2,
  apply not_lt_of_le C3 C1,
end


lemma hahn_crazy_diff_set_nonempty' {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α): 
  hahn_crazy_set ν μ X →
  (hahn_crazy_diff_set μ ν X).nonempty :=
begin
  intros A1,
  apply hahn_crazy_diff_set_nonempty,
  have A2 := (hahn_crazy_set_def ν μ X).mp A1,
  apply A2.right.left,
  apply hahn_crazy_set_self,
  apply A1,
end


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



--Notice that this function chooses the minimum n that is greater than or equal to the inverse.
--Put another way, this chooses the maximum 1/n that is less than or equal to the value.
noncomputable def floor_simple_fraction (x:ennreal):ℕ  := Inf {n:ℕ|(n:ennreal) ≥ x⁻¹}


--This is a way of selecting a "big" input of a function when it is hard to select a maximum
--input. Because we are mapping the extended non-negative reals onto the naturals with a
--monotonically decreasing function, and for any nonempty set of natural numbers there is
--a minimum, we get a set of "big" inputs to the function, and we apply classical.some, we 
--get one of these values.
-- 
--This is good for showing progress: if we whittle away something, and get smaller and
--smaller results, we eventually grab every nonzero result remaining.
lemma hahn_infi_ennreal {α:Type*} {f:α→ ennreal} (S:set α):S.nonempty → 
  ∃ a∈ S, 
  (floor_simple_fraction ∘ f) a = Inf ((floor_simple_fraction ∘ f) '' S) :=
begin
  intro A1,
  apply nat.exists_eq_Inf_map,
  apply A1,
end 


/-
  When we start with some hahn_crazy_set μ ν X, we know μ X < ν X. We want to
  grab a big chunk X' where ν X' < μ X'. This can only go on for so long.

  NOTE: there WAS a sign mistake here, where I flipped μ and ν in the difference.
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
      apply hahn_crazy_diff_set_nonempty,
      {
        rw hahn_crazy_set_def at H,
        apply H.right.left,
      },
      {
        apply hahn_crazy_set_self,
        apply H,
      },
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

--open subtype


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


/-
begin
  refl
end-/
   


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
      --have E3:
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
      --have F3 := lt_supr F2,
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
      --apply ennreal.lt_of_add_le_of_le_of_sub_lt D9 D4 D8 D2,      
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
        --apply add_le_add_of_le,
      },
      apply ennreal.lt_of_lt_top_of_add_lt_of_pos F10 F11 F3,      
    },
  },
end





lemma filter.tendsto_const {α β:Type*} [topological_space β]
    {v:β} {F:filter α}:
    filter.tendsto (λ n:α, v) F (nhds v) :=
begin
  unfold filter.tendsto,
  unfold filter.map,
  unfold nhds,
  simp,
  intros S B1 B2,
  have C1:(λ n:α, v) ⁻¹' S = set.univ,
  {
    ext;split;intro C1A,
    simp,
    simp,
    apply B1,  
  },
  rw C1,
  apply filter.univ_sets,
end



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
 
lemma tendsto_top' {α β:Type*} [NE:nonempty β] [SL:semilattice_sup β] {g:α → β} {F:filter α}:filter.tendsto g F filter.at_top ↔ (∀ b:β, g⁻¹' {c|b≤ c} ∈ F) :=
begin
  rw tendsto_top,
  split;intros A1;intros b;have B1 := A1 b,
  {
    rw filter.eventually_iff at B1,
    apply B1,
  },
  {
    rw filter.eventually_iff,
    apply B1,
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
  and no subset X' ⊆ X - Y where μ X' < ν X' and le_on_subsets μ ν X'. 

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
      rw hahn_crazy_set_def at J2A,
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
       rw hahn_crazy_set_def at A1,
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
        rw hahn_crazy_set_def at A1,
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
      rw hahn_crazy_set_def,
      apply and.intro C3,
      apply and.intro D1,
      intros X' D2A D2B,
      rw hahn_crazy_set_def at A1,
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

/-
  This theorem is a weak variant of hahn_unsigned_inequality_decomp.
  However, it probably has uses in its own right, beyond that of
  its parent theorem.
 -/
lemma hahn_unsigned_inequality_decomp_junior {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) {X:set α} [A1:measure_theory.finite_measure ν]:
    (is_measurable X) →
    (μ X < ν X) → 
    (∃ X':set α, 
      X' ⊆ X ∧
      μ X' < ν X' ∧
      le_on_subsets μ ν X') :=
begin
  intros A2 A3,
  have B1:= @finite_set_not_hahn_crazy_set _ _ μ ν X A1,
  rw hahn_crazy_set_def at B1,
  simp at B1,
  apply B1 A3 A2, 
end


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


lemma hahn_unsigned_inequality_decomp {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) [A1:measure_theory.finite_measure ν]: 
    (∃ X:set α,  le_on_subsets μ ν X ∧ le_on_subsets ν μ (Xᶜ)) :=
begin
  /-
    What we want is the argmax of f on S: this is our candidate for X.
    However, we must first establish that such an argmax exists.
     
    First, we construct an  M that is our candidate for X.
    It is the supremum of 
   -/
  let S:set (set α) := {X:set α|le_on_subsets μ ν X},
  let f:set α → ennreal := (λ T:set α, (ν T) - (μ T)),
  -- M is unused.
  let M:ennreal := Sup (f '' S),
  begin
    
    have A2:S = {X:set α|le_on_subsets μ ν X} := rfl,
    have A3:f = (λ T:set α, (ν T) - (μ T)) := rfl,
    have A5:∀ X, le_on_subsets μ ν X → μ X < ⊤,
    {
      intros X A5A,
      apply lt_of_le_of_lt (le_on_subsets_self A5A),
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
      have B1F:le_on_subsets μ ν (T2 \ T1),
      {
        apply le_on_subsets_diff B1B B1A,
      },
      have B1G:T2 = T1 ∪ (T2 \ T1),
      { 
        rw set.union_diff_cancel,
        apply B1C,
      },
      rw B1G,
      rw le_on_subsets_add,
      apply @le_add_of_nonneg_right ennreal _,
      simp,
      {
        apply A5 T1 B1A,
      },
      {
        apply A5 _ B1F,
      },
      apply B1A,
      apply B1F, 
      apply set.disjoint_diff,
    },
    have B2B:(∀ h:ℕ → set α, set.range h ⊆ S → monotone h → (supr h)∈ S),
    {
      intros h B2C B2D,
      rw A2,
      rw supr_eq_Union,
      apply le_on_subsets_m_Union,
      apply B2D,
      intro n,
      have B2E:h n ∈ S,
      {
         apply B2C,
         simp,
      },
      rw A2 at B2E,
      simp at B2E, 
      apply B2E,
    },
    have B3:S.nonempty,
    {
      apply set.nonempty_of_mem,
      rw A2,
      simp,
      apply le_on_subsets_empty,
    },
    have B4:(∀ (a ∈ S) (b ∈ S), a ⊔ b ∈ S),
    {
      rw A2,
      simp,
      intros a B4A b B4B,
      have B4C:a ⊔ b = a ∪ b := rfl,
      --rw B4C,
      apply le_on_subsets_union B4A B4B,
    },
    have C1:=@Sup_apply_eq_supr_apply_of_closed'' (set α) _ S f B1 B2B B3 B4,
    cases C1 with g C1,
    apply exists.intro (supr g),
    have C2:le_on_subsets μ ν (supr g),
    {
      rw supr_eq_Union,
      apply le_on_subsets_m_Union,
      apply C1.right.left,
      intro n,
      have D1:=C1.left n,
      rw A2 at D1,
      apply D1,
    },
    apply and.intro C2,
    -- ⊢ le_on_subsets ν μ (-supr g)
    rw le_on_subsets_def,
    split,
    {
      apply is_measurable.compl,
      apply le_on_subsets_is_measurable C2,
    },
    {
      intros X' D1 D2,
      apply le_of_not_lt _,
      intro D3,
      have D4:= hahn_unsigned_inequality_decomp_junior μ ν D2 D3,
      cases D4 with X'' D4,
      have D5:f (X'' ∪ supr g) ≤  f (supr g),
      {
        rw C1.right.right,
        apply @le_Sup ennreal _ _,
        simp,
        apply exists.intro (X'' ∪ supr g),
        split,
        {
          apply le_on_subsets_union,
          apply D4.right.right,
          apply C2,
        },
        refl,
      },
      repeat {rw A6 at D5},
      rw le_on_subsets_add at D5,
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
      apply A5 _ D4.right.right,
      apply A5 _ C2,
      apply D4.right.right,
      apply C2,
      {
        apply @set.disjoint_of_subset_left _ _ _ ((supr g)ᶜ),
        apply set.subset.trans D4.left D1,
        apply set.disjoint.symm,
        apply set.disjoint_compl_right,
      },
    },
  end
end
