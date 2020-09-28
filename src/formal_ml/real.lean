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
import data.real.basic
import topology.basic
import topology.instances.real
import data.complex.exponential
import topology.algebra.infinite_sum
import data.nat.basic
import analysis.specific_limits
import analysis.calculus.deriv
import analysis.asymptotics
import formal_ml.nat
import formal_ml.core




lemma abs_eq_norm {a:ℝ}:abs a = ∥a∥ := rfl

---Results about the reals--------------------------------------------------------------------------



--Unused (except in classical_limit.lean)
lemma inv_pow_cancel2 (x:ℝ) (n:ℕ):(x≠ 0) → (x⁻¹)^n * (x)^n = 1 :=
begin
  intro A1,
  rw ← mul_pow,
  rw inv_mul_cancel,
  simp,
  apply A1,
end

lemma abs_pow {x:ℝ} {n:ℕ}:(abs (x^n)) = (abs x)^n :=
begin
  induction n,
  {
    simp,
  },
  {
    rw pow_succ,
    rw pow_succ,
    rw abs_mul,
    rw n_ih,
  }
end

lemma real_nat_abs_coe {n:ℕ}:abs (n:ℝ)= (n:ℝ) :=
begin
  have A1:abs (n:ℝ) =((abs n):ℝ) := rfl,
  rw A1,
  simp,
end

lemma abs_pos_of_nonzero {x:ℝ}:x ≠ 0 → 0 < abs x :=
begin
  intro A1,
  have A2:x < 0 ∨ x = 0 ∨ 0 < x := lt_trichotomy x 0,
  cases A2,
  {
    apply abs_pos_of_neg A2,
  },
  cases A2,
  {
    exfalso,
    apply A1,
    apply A2,
  },
  {
    apply abs_pos_of_pos A2,
  }
end


lemma pow_two_pos (n:ℕ):0 < (2:ℝ)^n :=
begin
  apply pow_pos,
  apply zero_lt_two,
end



lemma pow_nonneg_of_nonneg {x:ℝ} {k:ℕ}:0 ≤ x → 0 ≤ x^k :=
begin
  intro A1,
  induction k,
  {
    simp,
    apply le_of_lt,
    apply zero_lt_one,
  },
  {
    rw pow_succ,
    apply mul_nonneg,
    apply A1,
    apply k_ih,
  }
end

lemma real_pow_mono {x y:real} {k:ℕ}:
  0 ≤ x →
x ≤ y → x^k ≤ y^k :=
begin
  intros A0 A1,
  induction k,
  {
    simp,
  },
  {
    rw pow_succ,
    rw pow_succ,
    apply mul_le_mul,
    {
      exact A1,
    },
    {
      apply k_ih,
    },
    {
      simp,
      apply pow_nonneg_of_nonneg,
      apply A0,
    },
    {
      simp,
      apply le_trans,
      apply A0,
      apply A1,
    },
  }
end


lemma div_inv (x:ℝ):1/x = x⁻¹ :=
begin
  simp,
end

lemma inv_exp (n:ℕ):((2:ℝ)^n)⁻¹  = ((2:ℝ)⁻¹)^n :=
begin
  induction n,
  {
    simp,
  },
  {
    have A1:nat.succ n_n = 1 + n_n,
    {
      apply nat_succ_one_add,
    },
    rw A1,
    rw pow_add,
    rw pow_add,
    simp,
    rw mul_inv',
  }
end


lemma abs_mul_eq_mul_abs (a b:ℝ):(0 ≤ a) → abs (a * b) = a * abs (b) :=
begin
  intro A1,
  rw abs_mul,
  rw abs_of_nonneg,
  apply A1,
end



lemma pos_of_pos_of_mul_pos {a b:ℝ}:(0 ≤ a) → (0 < a * b) → 0 < b :=
begin
  intros A1 A2,
  have A3:0 < b ∨ (b ≤ 0),
  {
    apply lt_or_ge,
  },
  cases A3,
  {
    apply A3,
  },
  {
    exfalso,
    have A3A:(a * b)≤ 0,
    {
      apply mul_nonpos_of_nonneg_of_nonpos,
      apply A1,
      apply A3,
    },
    apply not_lt_of_le A3A,
    apply A2,
  }
end


lemma inv_pos_of_pos {a:ℝ}:(0 < a) → 0 < (a⁻¹) :=
begin
  intro A1,
  apply pos_of_pos_of_mul_pos,
  apply le_of_lt,
  apply A1,
  rw mul_inv_cancel,
  apply zero_lt_one,
  intro A2,
  rw A2 at A1,
  apply lt_irrefl _ A1,
end


lemma inv_lt_one_of_one_lt {a:ℝ}:(1 < a) → (a⁻¹)< 1 :=
begin
  intro A1,
  have A2:0 < a,
  {
    apply lt_trans,
    apply zero_lt_one,
    apply A1,
  },
  have A3:0 < a⁻¹,
  {
    apply inv_pos_of_pos A2,
  },
  have A4:a⁻¹ * 1 < a⁻¹ * a,
  {
    apply mul_lt_mul_of_pos_left,
    apply A1,
    apply A3,
  },
  rw inv_mul_cancel at A4,
  rw mul_one at A4,
  apply A4,
  {
    intro A5,
    rw A5 at A2,
    apply lt_irrefl _ A2,
  }
end



--Lift to division_ring, or delete
lemma division_ring.div_def {α:Type*} [division_ring α] {a b:α}:a/b = a* b⁻¹ := rfl

lemma div_def {a b:ℝ}:a/b = a * b⁻¹ := rfl

--Raise to a linear ordered field (or a linear ordered division ring?).
--Unused.
lemma div_lt_div_of_lt_of_lt {a b c:ℝ}:(0<c) → (a < b) → (a/c < b/c) :=
begin
  intros A1 A2,
  rw division_ring.div_def,
  rw division_ring.div_def,
  apply mul_lt_mul_of_pos_right,
  apply A2,
  apply inv_pos_of_pos,
  apply A1,
end

--TODO: replace with half_lt_self
lemma epsilon_half_lt_epsilon {α:Type*} [linear_ordered_field α] {ε:α}: 0 < ε → (ε / 2) < ε :=
begin
 apply half_lt_self,
end

--TODO: replace with inv_nonneg.mpr.
lemma inv_nonneg_of_nonneg {a:ℝ}:(0 ≤ a) → (0 ≤ a⁻¹) :=
begin
  apply inv_nonneg.mpr,
end

lemma move_le {a b c:ℝ}:(0 < c) → (a ≤ b * c) → (a * c⁻¹) ≤ b :=
begin
  intros A1 A2,
  have A3:0 < c⁻¹ := inv_pos_of_pos A1,
  have A4:(a * c⁻¹) ≤ (b * c) * (c⁻¹),
  {
    apply mul_le_mul_of_nonneg_right,
    apply A2,
    apply le_of_lt,
    apply A3,
  },
  have A5:b * c * c⁻¹ = b,
  {
    rw mul_assoc,
    rw mul_inv_cancel,
    rw mul_one,
    symmetry,
    apply ne_of_lt,
    apply A1,
  },
  rw A5 at A4,
  apply A4,
end


lemma move_le2 {a b c:ℝ}:(0 < c) → (a * c⁻¹) ≤ b → (a ≤ b * c) :=
begin
  intros A1 A2,
  have A4:(a * c⁻¹) * c ≤ (b * c),
  {
    apply mul_le_mul_of_nonneg_right,
    apply A2,
    apply le_of_lt,
    apply A1,
  },
  have A5:a * c⁻¹ * c = a,
  {
    rw mul_assoc,
    rw inv_mul_cancel,
    rw mul_one,
    symmetry,
    apply ne_of_lt,
    apply A1,
  },
  rw A5 at A4,
  apply A4,
end

--Probably a repeat.
--nlinarith failed.
lemma inv_decreasing {x y:ℝ}:(0 < x) → (x < y)→ (y⁻¹ < x⁻¹) :=
begin
  intros A1 A2,
  have A3:0< y,
  {
    apply lt_trans,
    apply A1,
    apply A2,
  },
  have A4:0 < x * y,
  {
    apply mul_pos;assumption,
  },
  have A5:x⁻¹ * x < x⁻¹ * y,
  {
    apply mul_lt_mul_of_pos_left,
    apply A2,
    apply inv_pos_of_pos,
    apply A1,
  },
  rw inv_mul_cancel at A5,
  have A6:1 * y⁻¹ < x⁻¹ * y * y⁻¹,
  {
    apply mul_lt_mul_of_pos_right,
    apply A5,
    apply inv_pos_of_pos,
    apply A3,
  },
  rw one_mul at A6,
  rw mul_assoc at A6,
  rw mul_inv_cancel at A6,
  rw mul_one at A6,
  apply A6,
  {
    intro A7,
    rw A7 at A3,
    apply lt_irrefl 0 A3,
  },
  {
    intro A7,
    rw A7 at A1,
    apply lt_irrefl 0 A1,
  }
end

lemma abs_nonzero_pos {x:ℝ}:(x ≠ 0) → (0 < abs (x)) :=
begin
  intro A1,
  have A2:(x < 0 ∨ x = 0 ∨ 0 < x) := lt_trichotomy x 0,
  cases A2,
  {
    apply abs_pos_of_neg,
    apply A2,
  },
  cases A2,
  {
    exfalso,
    apply A1,
    apply A2,
  },
  {
    apply abs_pos_of_pos,
    apply A2,
  },
end



lemma diff_ne_zero_of_ne {x x':ℝ}:(x ≠ x') → (x - x' ≠ 0) :=
begin
  intro A1,
  intro A2,
  apply A1,
  linarith [A2],
end

--nlinarith failed
lemma abs_diff_pos {x x':ℝ}:(x ≠ x') → (0 < abs (x - x')) :=
begin
  intro A1,
  apply abs_nonzero_pos,
  apply diff_ne_zero_of_ne A1,
end


--nlinarith failed
lemma neg_inv_of_neg {x:ℝ}:x < 0 → (x⁻¹ < 0) :=
begin
  intro A1,
  have A2:x⁻¹ < 0 ∨ (0 ≤ x⁻¹) := lt_or_le x⁻¹ 0,
  cases A2,
  {
    apply A2,
  },
  {
    exfalso,
    have A3:(x * x⁻¹ ≤ 0),
    {
      apply mul_nonpos_of_nonpos_of_nonneg,
      apply le_of_lt,
      apply A1,
      apply A2,
    },
    rw mul_inv_cancel at A3,

    apply not_lt_of_le A3,
    apply zero_lt_one,
    intro A4,
    rw A4 at A1,
    apply lt_irrefl (0:ℝ),
    apply A1,
  }
end

lemma sub_inv {a b:ℝ}:a - (a - b) = b :=
begin
  linarith,
end


--Classical, but filter_util.lean still has dependencies.
lemma x_in_Ioo {x r:ℝ}:(0 < r) → (x∈ set.Ioo (x- r) (x + r)) :=
begin
  intro A1,
  simp,
  split,
  {
    apply lt_of_sub_pos,
    rw sub_inv,
    apply A1,
  },
  {
    apply A1,
  }
end

--Classical.
lemma abs_lt2 {x x' r:ℝ}:
  (abs (x' - x) < r) ↔ ((x - r < x') ∧  (x' < x + r)) :=
begin
  rw abs_lt,
  split;intros A1;cases A1 with A2 A3;split,
  {
    apply add_lt_of_lt_sub_left A2,
  },
  {
    apply lt_add_of_sub_left_lt A3,
  },
  {
    apply lt_sub_left_of_add_lt A2,
  },
  {
    apply sub_left_lt_of_lt_add A3,
  }
end

--Classical.
lemma abs_lt_iff_in_Ioo {x x' r:ℝ}:
  (abs (x' - x) < r) ↔ x' ∈ set.Ioo (x - r) (x + r) :=
begin
  apply iff.trans,
  apply abs_lt2,
  simp,
end

--TODO: replace with neg_neg_of_pos
lemma neg_lt_of_pos {x:ℝ}:(0 < x) → (-x < 0) :=
begin
  apply neg_neg_of_pos,
end

--Classical.
lemma abs_lt_iff_in_Ioo2 {x x' r:ℝ}:
  (abs (x - x') < r) ↔ x' ∈ set.Ioo (x - r) (x + r) :=
begin
  have A1:abs (x - x')=abs (x' - x),
  {
    have A1A:x' - x = -(x - x'),
    {
      simp,
    },
    rw A1A,
    rw abs_neg,
  },
  rw A1,
  apply abs_lt_iff_in_Ioo,
end


--Unlikely novel.
lemma real_lt_coe {a b:ℕ}:a < b → (a:ℝ) < (b:ℝ) :=
begin
  simp,
end


lemma add_of_sub {a b c:ℝ}:a - b = c ↔ a = b + c :=
begin
  split;intros A1;linarith [A1],
end

--linarith and nlinarith fails.
lemma sub_half_eq_half {a:ℝ}:(a - a * 2⁻¹)=a * 2⁻¹ :=
begin
    rw add_of_sub,
    rw ← division_ring.div_def,
    simp,
end

--linarith and nlinarith fails.
lemma half_pos2:0 < (2:ℝ)⁻¹ :=
begin
  apply inv_pos_of_pos,
  apply zero_lt_two,
end

/- The halfway point is in the middle. -/
lemma half_bound_lower {a b:ℝ}:a < b → a < (a + b)/2 :=
begin
  intro A1,
  linarith [A1],
end

lemma half_bound_upper {a b:ℝ}:a < b → (a + b)/2 < b :=
begin
  intro A1,
  linarith [A1],
end

lemma lt_of_sub_lt_sub {a b c:ℝ}:a - c < b - c → a < b :=
begin
  intro A1,
  linarith [A1],
end


lemma abs_antisymm {a b:ℝ}:abs (a - b) = abs (b - a) :=
begin
  have A1:-(a-b)=(b - a),
  {
    simp,
  },
  rw ← A1,
  rw abs_neg,
end

lemma add_sub_triangle {a b c:ℝ}:(a - b) = (a - c) + (c - b) :=
begin
  linarith,
end

lemma abs_triangle {a b c:ℝ}:abs (a - b) ≤ abs (a - c) + abs (c - b) :=
begin
  have A1:(a - b) = (a - c) + (c - b) := add_sub_triangle,
  rw A1,
  apply abs_add_le_abs_add_abs,
end

lemma pow_complex {x:ℝ} {n:ℕ}:((x:ℂ)^n).re=(x^n) :=
begin
  induction n,
  {
    simp,
  },
  {
    rw pow_succ,
    rw pow_succ,
    simp,
    rw n_ih,
  }
end

lemma div_complex {x y:ℝ}:((x:ℂ)/(y:ℂ)).re=x/y :=
begin
  rw complex.div_re,
  simp,
  have A1:y=0 ∨ y≠ 0 := eq_or_ne,
  cases A1,
  {
    rw A1,
    simp,
  },
  {
    rw mul_div_mul_right,
    apply A1,
  }
end

lemma complex_norm_sq_nat {y:ℕ}:complex.norm_sq (y:ℂ) = ((y:ℝ) * (y:ℝ)) :=
begin
  unfold complex.norm_sq,
  simp,
end

lemma num_denom_eq (a b c d:ℝ): (a = b) → (c = d) → (a/c)=(b/d) :=
begin
  intros A1 A2,
  rw A1,
  rw A2,
end

lemma complex_pow_div_complex_re {x:ℝ} {n:ℕ} {y:ℕ}:(((x:ℂ)^n)/(y:ℂ)).re=x^n/(y:ℝ) :=
begin
  rw complex.div_re,
  simp,
  have A1:(y:ℝ)=0 ∨ (y:ℝ) ≠ 0 := eq_or_ne,
  cases A1,
  {
    rw A1,
    simp,
  },
  {
    rw complex_norm_sq_nat,
    rw mul_div_mul_right,
    apply num_denom_eq,
    {
      rw pow_complex,
    },
    {
      refl,
    },
    apply A1,
  }
end

lemma half_lt_one:(2:ℝ)⁻¹ < 1 :=
begin
  have A1:1/(2:ℝ) < 1 := epsilon_half_lt_epsilon zero_lt_one,
  rw division_ring.div_def at A1,
  rw one_mul at A1,
  apply A1,
end

lemma half_pos_lit:0 < (2:ℝ)⁻¹ :=
begin
  apply inv_pos_of_pos,
  apply zero_lt_two,
end

/-
lemma div_re_eq_re_div_re (x y:ℂ):(x / y).re = (x.re)/(y.re) :=
begin
  simp,
end
-/

--It is a common pattern that we calculate the distance to the middle,
--and then show that if you add or subtract it, you get to that middle.
lemma half_equal {x y ε:ℝ}:ε = (x - y)/2 → x - ε = y + ε :=
begin
  intro A1,
  have A2:(x - ε) + (ε - y) = (y + ε) + (ε - y),
  {
    rw ← add_sub_triangle,
    rw ← add_sub_assoc,
    
    rw add_comm (y+ε),
    rw add_comm y ε,
    rw ← add_assoc,
    rw add_sub_assoc,
    rw sub_self,
    rw add_zero,
    rw A1,
    simp,
  },
  apply add_right_cancel A2,
end
