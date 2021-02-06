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
import formal_ml.real
import formal_ml.rat




lemma nnreal_add_sub_right (a b c:nnreal):a + b = c → c - b = a :=
begin
  intro A1,
  --apply linarith [A1],
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

@[simp]
lemma nnreal_exp_eq (x:real):↑(nnreal.exp x) = real.exp x :=
begin
  unfold nnreal.exp,
  rw nnreal.coe_of_real,
  apply le_of_lt,
  apply real.exp_pos,
end

@[simp]
lemma nnreal.exp_zero_eq_one:(nnreal.exp 0) = 1 :=
begin
  unfold nnreal.exp,
  --rw nnreal.coe_eq_coe,
  have h1:(1:nnreal) = (nnreal.of_real 1),
  { simp },
  rw h1,
  simp,
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
  apply with_top.some_lt_none,
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

lemma nnreal.lt_of_add_le_of_pos {x y z:nnreal}:x + y ≤ z → 0 < y → x < z :=
begin
  cases x, cases y, cases z,
  repeat {rw ← nnreal.coe_lt_coe}, rw ← nnreal.coe_le_coe,repeat {rw nnreal.coe_add},
  simp, intros A1 A2,
  linarith [A1, A2],
end

lemma nnreal.not_add_le_of_lt {a b:nnreal}:
   (0 < b) → ¬(a + b) ≤ a :=
begin
  intros A1 A2,
  simp at A2,
  subst A2,
  apply lt_irrefl _ A1,
end

lemma nnreal.sub_lt_of_pos_of_pos {a b:nnreal}:(0 < a) → 
    (0 < b) → (a - b) < a :=
begin
  intros A1 A2,
  cases (le_total a b) with A3 A3,
  {
    rw nnreal.sub_eq_zero A3,
    apply A1,
  },
  {
    rw ← nnreal.coe_lt_coe,
    rw nnreal.coe_sub A3,
    rw ← nnreal.coe_lt_coe at A2,
    rw sub_lt_self_iff,
    apply A2,
  }
end


lemma nnreal.sub_eq_of_add_of_le {a b c:nnreal}:a = b + c →
  c ≤ a → a - c = b :=
begin
  intros A1 A2,
  have A3:a - c + c = b + c,
  {
    rw nnreal.sub_add_cancel_of_le A2,
    apply A1,  
  },
  apply add_right_cancel A3,
end

lemma nnreal.inverse_le_of_le {a b:nnreal}:
  0 < a →
  a ≤ b →
  b⁻¹ ≤ a⁻¹ :=
begin
  intros A1 A2, 
  have B1: (a⁻¹ * b⁻¹) * a ≤  (a⁻¹ * b⁻¹) * b,
  {
    apply mul_le_mul,
    apply le_refl _,
    apply A2,
    simp,
    simp,
  },
  rw mul_comm a⁻¹  b⁻¹ at B1,
  rw mul_assoc at B1,
  rw inv_mul_cancel at B1,
  rw mul_comm b⁻¹  a⁻¹ at B1,
  rw mul_assoc at B1,
  rw mul_one at B1,
  rw inv_mul_cancel at B1,
  rw mul_one at B1,
  apply B1,
  {
    have B1A := lt_of_lt_of_le A1 A2,
    intro B1B,
    subst b,
    simp at B1A,
    apply B1A,
  },
  {
    intro C1,
    subst a,
    simp at A1,
    apply A1,
  },
end

lemma nnreal.unit_frac_pos (n:ℕ):0 < (1/((n:nnreal) + 1)) :=
begin
  apply nnreal.div_pos,
  apply zero_lt_one,
  have A1:(0:nnreal) < (0:nnreal) + (1:nnreal),
  {
    simp,
    apply zero_lt_one,
  },
  apply lt_of_lt_of_le A1,
  rw add_comm (0:nnreal) 1,
  rw add_comm _ (1:nnreal),
  apply add_le_add_left,
  simp,
end


lemma nnreal.real_le_real {q r:ℝ}:q ≤ r → (nnreal.of_real q ≤ nnreal.of_real r) :=
begin
  intro A1,
  cases (le_total 0 q) with A2 A2,
  {
    have A3 := le_trans A2 A1,
    rw ←  @nnreal.coe_le_coe,
    rw nnreal.coe_of_real q A2,
    rw nnreal.coe_of_real r A3,
    apply A1,
  },
  {
    have B1 := nnreal.of_real_of_nonpos A2,
    rw B1,
    simp,
  },
end


lemma nnreal.rat_le_rat {q r:ℚ}:q ≤ r → (nnreal.of_real q ≤ nnreal.of_real r) :=
begin
  rw real.rat_le_rat_iff,
  apply nnreal.real_le_real,
end


lemma nnreal.real_lt_nnreal_of_real_le_real_of_real_lt_nnreal {q r:real} {s:nnreal}:
  q ≤ r → (nnreal.of_real r) < s → (nnreal.of_real q) < s :=
begin
  intros A1 A2,
  apply lt_of_le_of_lt _ A2,
  apply nnreal.real_le_real,
  apply A1,
end


lemma nnreal.rat_lt_nnreal_of_rat_le_rat_of_rat_lt_nnreal {q r:ℚ} {s:nnreal}:
  q ≤ r → (nnreal.of_real r) < s → (nnreal.of_real q) < s :=
begin
  
  intros A1 A2,
  rw real.rat_le_rat_iff at A1,
  apply nnreal.real_lt_nnreal_of_real_le_real_of_real_lt_nnreal A1 A2,
end


lemma nnreal.of_real_inv_eq_inv_of_real {x:real}:(0 ≤ x) →
    nnreal.of_real x⁻¹ = (nnreal.of_real x)⁻¹ :=
begin
  intro A1,
  rw ← nnreal.eq_iff,
  simp,
  have A2:0 ≤ x⁻¹,
  {
    apply inv_nonneg.2 A1,
  },
  rw nnreal.coe_of_real x A1,
  rw nnreal.coe_of_real _ A2,
end


/--TODO: replace with div_eq_mul_inv.-/
lemma nnreal.div_def {x y:nnreal}:x/y = x * y⁻¹ := begin
  rw div_eq_mul_inv,
end

lemma nnreal.one_div_eq_inv {x:nnreal}:1/x = x⁻¹ := 
begin
  rw nnreal.div_def,
  rw one_mul,
end

lemma nnreal.exists_unit_frac_lt_pos {ε:nnreal}:0 < ε → (∃ n:ℕ, (1/((n:nnreal) + 1)) < ε) :=
begin
  intro A1,
  have A2 := A1,
  rw nnreal.lt_iff_exists_rat_btwn at A2,
  cases A2 with q A2,
  cases A2 with A2 A3,
  cases A3 with A3 A4,
  simp at A3,
  have A5 := rat.exists_unit_frac_le_pos A3,
  cases A5 with n A5,
  apply exists.intro n,
  simp at A5,
  rw nnreal.one_div_eq_inv,
  have B2:(0:ℝ) ≤ 1,
  {
    apply le_of_lt,
    apply zero_lt_one,
  },
  have A7:nnreal.of_real 1 = (1:nnreal),
  {
    rw ← nnreal.coe_eq,
    rw nnreal.coe_of_real,
    rw nnreal.coe_one,
    apply B2,
  },
  rw ← A7,
  have A8:nnreal.of_real n = n,
  {
    rw ← nnreal.coe_eq,
    rw nnreal.coe_of_real,
    simp, 
    simp,
  },
  rw ← A8,
  have B1:(0:ℝ) ≤ n,
  {
    simp,  
  },
  have B3:(0:ℝ) ≤ n + (1:ℝ),
  {
    apply le_trans B1,
    simp,
    apply B2
  },

  rw ← nnreal.of_real_add B1 B2,
  rw ← nnreal.of_real_inv_eq_inv_of_real B3,
  have A9 := nnreal.rat_le_rat A5,
  have A10:((n:ℝ) + 1)⁻¹ = (↑((n:ℚ) + 1)⁻¹:ℝ),
  {
    simp,
  },
  rw A10,
  apply lt_of_le_of_lt A9 A4,
end

lemma nnreal.of_real_eq_coe_nat {n:ℕ}:nnreal.of_real n = n :=
begin
  rw ← nnreal.coe_eq,
  rw nnreal.coe_of_real,
  repeat {simp},
end

lemma nnreal.sub_le_sub_of_le {a b c:nnreal}:b ≤ a →
  c - a ≤ c - b :=
begin
  intro A1,
  cases (classical.em (a ≤ c)) with B1 B1,
  {
    rw ← nnreal.coe_le_coe,
    rw nnreal.coe_sub B1,
    have B2:=le_trans A1 B1,
    rw nnreal.coe_sub B2,
    rw ← nnreal.coe_le_coe at A1,    
    linarith [A1],
  },
  {
    simp only [not_le] at B1,
    have C1:= le_of_lt B1,
    rw nnreal.sub_eq_zero C1,
    simp
  },
end


--Replace c < b with c ≤ a.
lemma nnreal.sub_lt_sub_of_lt_of_lt {a b c:nnreal}:a < b →
  c ≤ a →
  a - c < b - c :=
begin
  intros A1 A2,
  rw ← nnreal.coe_lt_coe, 
  rw nnreal.coe_sub A2,
  have B1:=lt_of_le_of_lt A2 A1,
  have B2 := le_of_lt B1,
  rw nnreal.coe_sub B2,
  apply real.sub_lt_sub_of_lt,
  rw nnreal.coe_lt_coe,
  apply A1,
end


lemma nnreal.sub_lt_sub_of_lt_of_le {a b c d:nnreal}:a < b →
  c ≤ d →
  d ≤ a →
  a - d < b - c :=
begin
  intros A1 A2 A3,
  have A3:a - d < b - d,
  {
    apply nnreal.sub_lt_sub_of_lt_of_lt A1 A3,
  },
  apply lt_of_lt_of_le A3,
  apply nnreal.sub_le_sub_of_le A2,
end

lemma nnreal.eq_add_of_sub_eq {a b c:nnreal}:b ≤ a →
  a - b = c → a = b + c :=
begin
  intros A1 A2,
  apply nnreal.eq,
  rw  nnreal.coe_add,
  rw ← nnreal.eq_iff at A2,
  rw  nnreal.coe_sub A1 at A2,
  apply real.eq_add_of_sub_eq A2,
end


lemma nnreal.sub_add_sub {a b c:nnreal}:c ≤ b → b ≤ a → (a - b) + (b - c) = a - c :=
begin
  intros A1 A2,
  rw ← nnreal.coe_eq,
  rw nnreal.coe_add,
  repeat {rw nnreal.coe_sub},
  apply real.sub_add_sub,
  apply le_trans A1 A2,
  apply A1,
  apply A2,
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

lemma nnreal.le_sub_add' {a b:nnreal}:a ≤ a - b + b :=
begin
  cases decidable.em (b ≤ a),
  { apply nnreal.le_sub_add,
    apply le_refl _,
    apply h },
  { have h2:a≤ b,
    { apply le_of_not_ge h }, rw nnreal.sub_eq_zero,
    rw zero_add,
    apply h2,
    apply h2 },
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

----- From Radon Nikodym ---------------------------------

lemma nnreal.mul_lt_mul_of_pos_of_lt 
    {a b c:nnreal}:(0 < a) → (b < c) → (a * b < a * c) :=
begin
  intros A1 A2,
  apply mul_lt_mul',
  apply le_refl _,
  apply A2,
  simp,
  apply A1,
end

lemma canonically_ordered_add_monoid.zero_lt_iff_ne_zero 
  {α:Type*} [canonically_ordered_add_monoid α] {x:α}:0 < x ↔ x ≠ 0 :=
begin
  split,
  { intros h_zero_lt h_eq_zero,
    rw h_eq_zero at h_zero_lt,
    apply lt_irrefl _ h_zero_lt },
  { intros h_ne,
    rw lt_iff_le_and_ne,
    split,
    apply zero_le,
    symmetry,
    apply h_ne },
end


lemma nnreal.zero_lt_iff_ne_zero {x:nnreal}:0 < x ↔ x ≠ 0 := begin
  rw canonically_ordered_add_monoid.zero_lt_iff_ne_zero,
end

/-
  It is hard to generalize this.
 -/
lemma nnreal.mul_pos_iff_pos_pos 
    {a b:nnreal}:(0 < a * b) ↔ (0 < a)∧ (0 < b) :=
begin
  split;intros A1,
  {
    rw nnreal.zero_lt_iff_ne_zero at A1,
    repeat {rw nnreal.zero_lt_iff_ne_zero},
    split;intro B1;apply A1,
    {
       rw B1,
       rw zero_mul,
    },
    {
      rw B1,
      rw mul_zero,
    },
  },
  {
    have C1:0 ≤ a * 0,
    {
      simp,
    },
    apply lt_of_le_of_lt C1,
    apply nnreal.mul_lt_mul_of_pos_of_lt,
    apply A1.left,
    apply A1.right,
  },
end


lemma nnreal.inv_mul_eq_inv_mul_inv {a b:nnreal}:(a * b)⁻¹=a⁻¹ * b⁻¹ :=
begin
  rw nnreal.mul_inv,
  rw mul_comm,
end

-- TODO: replace with zero_lt_iff_ne_zero.
lemma nnreal.pos_iff {a:nnreal}:0 < a ↔ a ≠ 0 :=
begin
  rw nnreal.zero_lt_iff_ne_zero,
end

lemma nnreal.add_pos_le_false {x ε:nnreal}: (0 < ε) → (x + ε ≤ x) → false :=
begin
  cases x, cases ε,
  rw ← nnreal.coe_le_coe,
  rw ← nnreal.coe_lt_coe,
  rw nnreal.coe_add,
  simp,  
  intros h1 h2,
  linarith [h1, h2],
end 


lemma nnreal.lt_add_pos {x ε:nnreal}: (0 < ε) → (x < x + ε)  :=
begin
  cases ε; cases x; simp,
end
