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

import algebra.ordered_ring
import data.nat.basic
import formal_ml.core



/-
  In order to understand all of the results about natural numbers,
  it is helpful to look at the instances for nat that are defined.
  Specifically, the naturals are:
  1. a canonically ordered commutative semiring
  2. a decidable linear ordered semiring.
-/

lemma lt_antirefl (n:ℕ):(n < n)→ false :=
begin
  apply nat.lt_irrefl,
end

--While this does solve the problem, it is not identical.
lemma lt_succ (n:ℕ):(n < nat.succ n) :=
begin
  apply nat.le_refl,
end

lemma lt_succ_of_lt (m n:ℕ):(m < n) → (m < nat.succ n) :=
begin
  intros a,
  apply nat.lt_succ_of_le,
  apply ((@nat.lt_iff_le_not_le m n).mp a).left,
end


lemma nat_lt_def (n m:ℕ): n < m ↔  (nat.succ n) ≤  m :=
begin
  refl,
end

lemma lt_succ_imp_le (a b:ℕ):a < nat.succ b → a ≤ b :=
begin
  intros a_1,
  rw nat_lt_def at a_1,
  apply nat.le_of_succ_le_succ,
  assumption,
end


lemma nat_fact_pos {n:ℕ}:0 < nat.factorial n :=
begin
  induction n,
  {
    simp,
  },
  {
    simp,
    apply n_ih,
  }
end


lemma nat_minus_cancel_of_le {k n:ℕ}:k≤ n → (n - k) + k = n :=
begin
  rw add_comm,
  apply nat.add_sub_cancel',
end

lemma nat_lt_of_add_lt {a b c:ℕ}:a + b < c → b < c :=
begin
  induction a,
  {
    simp,
  },
  {
    rw nat.succ_add,
    intro A1,
    apply a_ih,
    apply nat.lt_of_succ_lt,
    apply A1,
  }
end

lemma nat_fact_nonzero {n:ℕ}:nat.factorial n ≠ 0 :=
begin
  intro A1,
  have A2:0 < nat.factorial n := nat_fact_pos,
  rw A1 at A2,
  apply lt_irrefl 0 A2,
end

lemma nat_lt_sub_of_add_lt {k n n':ℕ}:n + k < n' → n < n' - k :=
begin
  revert n',
  revert n,
  induction k,
  {
    intros n n' A1,
    rw add_zero at A1,
    simp,
    apply A1,
  },
  {
    intros n n' A1,
    cases n',
    {
      exfalso,
      apply nat.not_lt_zero,
      apply A1,
    },
    {
      rw nat.succ_sub_succ_eq_sub,
      apply k_ih,
      rw nat.add_succ at A1,
      apply nat.lt_of_succ_lt_succ,
      apply A1,
    }
  }
end


lemma nat_zero_lt_of_nonzero {n:ℕ}:(n≠ 0)→ (0 < n) :=
begin
  intro A1,
  cases n,
  {
    exfalso,
    apply A1,
    refl,
  },
  {
    apply nat.zero_lt_succ,
  }
end

--In an earlier version, this was solvable via simp.
lemma nat_succ_one_add  {n:ℕ}:nat.succ n = 1 + n :=
begin
  rw add_comm,
end


lemma nat.le_add {a b:ℕ}:a ≤ a + b :=
begin
  simp,
end

-- mul_left_cancel' is the inspiration here.
-- However, it doesn't exist for nat.
lemma nat.mul_left_cancel_trichotomy {x : ℕ}:x ≠ 0 → ∀ {y z : ℕ}, 
  (x * y = x * z ↔ y = z)
  ∧ (x * y < x * z ↔ y < z) :=
begin
  induction x,
  {
    intros A1 y z,
    exfalso,
    apply A1,
    refl,
  },
  {
    intros A1 y z,
    rw nat_succ_one_add,
    rw right_distrib,
    rw one_mul,
    rw right_distrib,
    rw one_mul,
    cases x_n,
    {
      rw zero_mul,
      rw zero_mul,
      rw add_zero,
      rw add_zero,
      simp,
    },
    {
      have B1:nat.succ x_n ≠ 0,
      {
        have A2A:0 < nat.succ x_n,
        {
          apply nat.zero_lt_succ,
        },
        intro A2B,
        rw A2B at A2A,
        apply lt_irrefl 0 A2A,
      },
      have A2 := @x_ih B1 y z,
      have B2 := @x_ih B1 z y,
      cases A2 with A3 A4,
      cases B2 with B3 B4,
      have A5:y < z ∨ y = z ∨ z < y := lt_trichotomy y z,
      split;split;intros A6,
      {
        cases A5,
        {
          exfalso,
          have A7:y + nat.succ x_n * y < z + nat.succ x_n * z,
          {
            apply add_lt_add A5 (A4.mpr A5),
          },
          rw A6 at A7,
          apply lt_irrefl _ A7,
        },
        cases A5,
        {
          exact A5,
        },
        {
          exfalso,
          have A7:z + nat.succ x_n * z < y + nat.succ x_n * y,
          {
            apply add_lt_add A5 (B4.mpr A5),
          },
          rw A6 at A7,
          apply lt_irrefl _ A7,
        },
      },
      {
        rw A6,
      },
      {
        cases A5,
        {
          apply A5,
        },
        cases A5,
        {
          rw A5 at A6,
          exfalso,
          apply lt_irrefl _ A6,
        },
        {
          exfalso,
          apply not_lt_of_lt A6,        
          apply add_lt_add A5 (B4.mpr A5),
        },
      },
      {
        apply add_lt_add A6,
        apply A4.mpr A6,
      }
    }
  }
end

lemma nat.mul_left_cancel' {x : ℕ}:x ≠ 0 → ∀ {y z : ℕ}, 
  (x * y = x * z → y = z) :=
begin
  intros A1 y z A2,
  apply (@nat.mul_left_cancel_trichotomy x A1 y z).left.mp A2,
end


lemma nat.mul_eq_zero_iff_eq_zero_or_eq_zero {a b:ℕ}:
  a * b = 0 ↔ (a = 0 ∨ b = 0) :=
begin
  split;intros A1,
  {
    have A2:(a=0) ∨ (a ≠ (0:ℕ)) := eq_or_ne,
    cases A2,
    {
      left,
      apply A2,
    },
    {
      have A1:a * b = a * 0,
      {
        rw mul_zero,
        apply A1,
      },
      right,
      apply nat.mul_left_cancel' A2 A1,
    }
  },
  {
    cases A1;rw A1,
    {
      rw zero_mul,
    },
    {
      rw mul_zero,
    }
  }
end



lemma double_ne {m n:ℕ}:2 * m ≠ 1 + 2 * n :=
begin
  intro A1,
  have A2:=lt_trichotomy m n,
  cases A2,
  {
    have A3:0 + 2 * m < 1 + 2 * n,
    {
      apply add_lt_add,
      apply zero_lt_one,
      apply mul_lt_mul_of_pos_left A2 zero_lt_two,
    },
    rw zero_add at A3,
    rw A1 at A3,
    apply lt_irrefl _ A3,
  },
  cases A2,
  {
    rw A2 at A1,
    have A3:0 + 2 * n < 1 + 2 * n,
    {
      rw add_comm 0 _,
      rw add_comm 1 _,
      apply add_lt_add_left,
      apply zero_lt_one,
    },
    rw zero_add at A3,
    rw ← A1 at A3,
    apply lt_irrefl _ A3,    
  },
  {
    have A4:nat.succ n ≤ m,
    {
      apply nat.succ_le_of_lt A2,
    },
    have A5 := lt_or_eq_of_le A4,
    cases A5,
    {
      have A6:2 * nat.succ n < 2 * m,
      {
         apply mul_lt_mul_of_pos_left A5 zero_lt_two,
      },
      rw nat_succ_one_add at A6,
      rw left_distrib at A6,
      rw mul_one at A6,
      have A7:1 + 2 * n < 2 * m,
      {
        apply lt_trans _ A6,
        apply add_lt_add_right,
        apply one_lt_two,
      },
      rw A1 at A7,
      apply lt_irrefl _ A7,
    },
    {
      subst m,
      rw nat_succ_one_add at A1,
      rw left_distrib at A1,
      rw mul_one at A1,
      simp at A1,
      have A2:1 < 2 := one_lt_two,
      rw A1 at A2,
      apply lt_irrefl _ A2,
    }
  },
end


lemma nat.one_le_of_zero_lt {x:ℕ}:0 < x → 1 ≤ x := 
begin
  intro A1,
  apply nat.succ_le_of_lt,
  apply A1,
end


lemma nat.succ_le_iff_lt {m n:ℕ}:m.succ ≤ n ↔ m < n :=
begin
  apply nat.succ_le_iff,
end

lemma nat.zero_of_lt_one {x:ℕ}:x < 1 → x  = 0 :=
begin
  intro A1,
  have B1 := nat.le_pred_of_lt A1,
  simp at B1,
  apply B1,
end


-------------------------------------- Move these to some pow.lean file, or into mathlib ---------------

lemma linear_ordered_semiring.one_le_pow {α:Type*} [linear_ordered_semiring α]
   {a:α} {b:ℕ}:1 ≤ a → 1≤ a^b :=
begin
  induction b,
  {
    simp,
    intro A1,
    apply le_refl _,
  },
  {
    rw pow_succ,
    intro A1,
    have A2 := b_ih A1,
    have A3:1 * a^b_n ≤ a * (a^b_n),
    {
      apply mul_le_mul_of_nonneg_right,
      apply A1,
      apply le_of_lt,
      apply lt_of_lt_of_le zero_lt_one A2,
    },
    apply le_trans _ A3,
    simp [A2],
  },
end 

lemma linear_ordered_semiring.pow_monotone 
    {α:Type*} [linear_ordered_semiring α] [N:nontrivial α] {a:α} {b c:ℕ}:1 ≤ a → b ≤ c →  a^b ≤ a^c :=
begin
  intros A1 A2,
  rw le_iff_exists_add at A2,
  cases A2 with d A2,
  rw A2,
  rw pow_add,
  rw le_mul_iff_one_le_right,
  apply linear_ordered_semiring.one_le_pow A1,
  apply lt_of_lt_of_le zero_lt_one,
  apply linear_ordered_semiring.one_le_pow A1,
  apply N
end
