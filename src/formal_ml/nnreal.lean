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

import data.real.nnreal
import data.real.ennreal

import data.complex.exponential
import formal_ml.nat

lemma lt_imp_le (x y:real):(x < y) → (x ≤ y) :=
begin
  intro A1,
  have A2:x < y ↔ (x ≤ y ∧ ¬ y ≤ x),
  {
    apply decidable_linear_order.lt_iff_le_not_le,
  },
  apply (A2.mp A1).left,
end


lemma nnreal_add_sub_right (a b c:nnreal):a + b = c → c - b = a :=
begin
  intro A1,
  have A2:(a + b) - b = a,
  {
    apply nnreal.add_sub_cancel,
  },
  rw A1 at A2,
  exact A2,
end

lemma nnreal_add_sub_left (a b c:nnreal):a + b = c → c - a = b :=
begin
  intro A1,
  apply nnreal_add_sub_right,
  rw nnreal.comm_semiring.add_comm,
  exact A1,
end

lemma nnreal_sub_le_left (a b c:nnreal):b ≤ c → (a - c ≤ a - b) :=
begin
  intro A1,
  apply nnreal.of_real_le_of_real,
  apply sub_le_sub_left,
  apply A1,
end

noncomputable def nnreal.exp (x:real):nnreal := nnreal.of_real (real.exp x)

lemma nnreal_exp_eq (x:real):↑(nnreal.exp x) = real.exp x :=
begin
  unfold nnreal.exp,
  rw nnreal.coe_of_real,
  apply lt_imp_le,
  apply real.exp_pos,
end

-- This one is hard (and technically has nothing to do with nnreal).
-- The rest are easy after it is finished.
-- A standard proof would be to calculate the first and second derivative.
-- If you prove that the second derivative is non-negative, then there is a minimum
-- where the first derivative is zero. In this way you can establish that the minimum
-- is at zero, and it is zero.
-- Note this should solve the problem. however, there is a TODO.
-- My current thinking about the proof:




lemma nnreal_pow_succ (x:nnreal) (k:ℕ):x ^ nat.succ k = x * (x ^ k) :=
begin
  refl,
end

lemma nnreal_pow_mono (x y:nnreal) (k:ℕ):x ≤ y → x^k ≤ y^k :=
begin
  intro A1,
  induction k,
  {
    simp,
  },
  {
    rw nnreal_pow_succ,
    rw nnreal_pow_succ,
    apply mul_le_mul,
    {
      exact A1,
    },
    {
      apply k_ih,
    },
    {
      simp,
    },
    {
      simp,
    },
  }
end

lemma nnreal_eq (x y:nnreal):(x:real) = (y:real) → x = y :=
begin
  intro A1,
  apply nnreal.eq,
  apply A1,
end
lemma nnreal_exp_pow (x:real) (k:ℕ): nnreal.exp (k * x) = (nnreal.exp x)^k :=
begin
  apply nnreal.eq,
  rw nnreal.coe_pow,
  rw nnreal_exp_eq,
  rw nnreal_exp_eq,
  apply real.exp_nat_mul,
end

lemma to_ennreal_def (x:nnreal):(x:ennreal)= some x :=
begin
  refl
end

lemma nnreal_lt_ennreal_top (x:nnreal):(x:ennreal) < (⊤:ennreal) :=
begin
  rw to_ennreal_def,
  apply with_top.none_lt_some,
end

lemma nnreal_lt_some_ennreal (x y:nnreal):(x < y) → (x:ennreal) < (some y:ennreal) :=
begin
  intro A1,
  apply ennreal.coe_lt_coe.mpr,
  apply A1,
end

lemma some_ennreal_lt_nnreal (x y:nnreal):(x:ennreal) < (some y:ennreal) → (x < y) :=
begin
  intro A1,
  apply ennreal.coe_lt_coe.mp,
  apply A1,
end

lemma nnreal_add_eq_zero_iff (a b:nnreal): a + b = 0 ↔ a = 0 ∧ b = 0 :=
begin
  simp,
end


--Holds true for all commutative semirings?
lemma nnreal_add_monoid_smul_def{n:ℕ} {c:nnreal}:  n •ℕ c = ↑(n) * c :=
begin
  induction n,
  {
    simp,
  },
  {
    simp,
  }
end


lemma nnreal_sub_le_sub_of_le {a b c:nnreal}:b ≤ c → a - c ≤ a - b :=
begin
  intro A1,
  have A2:(a ≤ b)∨ (b ≤ a) := linear_order.le_total a b,
  have A3:(a ≤ c)∨ (c ≤ a) := linear_order.le_total a c,
  cases A2,
  {
    rw nnreal.sub_eq_zero,
    simp,
    apply le_trans A2 A1,
  },
  {
    cases A3,
    {
      rw nnreal.sub_eq_zero,
      simp,
      exact A3,
    },
    rw ← nnreal.coe_le_coe,
    rw nnreal.coe_sub,
    rw nnreal.coe_sub,
    apply sub_le_sub_left,
    rw nnreal.coe_le_coe,
    exact A1,
    exact A2,
    exact A3,
  },
end


lemma nnreal_sub_lt_sub_of_lt {a b c:nnreal}:b < c → b < a → a - c < a - b :=
begin
  intros A1 A2,
  --have A2:(a ≤ b)∨ (b ≤ a) := linear_order.le_total a b,
  have A3:(a ≤ c)∨ (c ≤ a) := linear_order.le_total a c,
  {
    cases A3,
    {
      rw nnreal.sub_eq_zero A3,
      apply nnreal.sub_pos.mpr A2,
    },
    rw ← nnreal.coe_lt_coe,
    rw nnreal.coe_sub,
    rw nnreal.coe_sub,
    apply sub_lt_sub_left,
    rw nnreal.coe_lt_coe,
    exact A1,
    apply (le_of_lt A2),
    exact A3,
  },
end
