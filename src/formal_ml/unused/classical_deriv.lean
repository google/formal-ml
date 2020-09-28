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
import formal_ml.sum
import formal_ml.real


--classical limit and derivative of a real function-------------------------------------------------
/-
  The classical limit is dramatically different than the topological
  limit. Specifically, the topological concept of limit assumes
  f x = y. However, the concept of limit from analysis explicitly
  excludes the point itself. This allows us to define derivatives in
  terms of limits.

  The nuance of the classical definition is that it requires some
  creative interpretation of division by zero. However, we already
  have to deal with this when it comes to fields, so avoiding it here
  is kind of pointless.

  Thus, note that the derivatives in mathlib are defined in terms
  of Landau notation: i.e., that the difference between the function
  and an affine function goes to zero in a (little o) way.
-/
def has_classical_rlimit (f:ℝ → ℝ) (x:ℝ) (y:ℝ):Prop :=
  ∀ ε:ℝ, (0 < ε)→
  ∃ δ:ℝ, (0 < δ)∧
  ∀ x':ℝ, (x'≠ x) → (abs (x-x') < δ) → abs (f x' - y)<ε


lemma has_classical_rlimit_def {f:ℝ → ℝ} {x:ℝ} {y:ℝ}:
  (has_classical_rlimit f x y) ↔
  (∀ ε:ℝ, (0 < ε)→
  ∃ δ:ℝ, (0 < δ)∧
  ∀ x':ℝ, (x'≠ x) → (abs (x-x') < δ) → abs (f x' - y)<ε) :=
begin
  refl,
end

def has_classical_rderiv_at  (f:ℝ → ℝ) (f':ℝ) (x:ℝ):Prop :=
  has_classical_rlimit (λ x':ℝ, (f x' - f x)/(x' - x)) x f'


lemma has_classical_rderiv_at_defh (f:ℝ → ℝ)  (f' x x':ℝ):
    (x' ≠ x)→
    abs (f x' + (-f x + -((x' + -x) * f'))) * (abs (x' - x))⁻¹=
    abs ((f x' - f x) / (x' - x) - f') :=
begin
  intro A1,
  rw ← abs_inv,
  rw ← abs_mul,
  have B1:(f x' + (-f x + -((x' + -x) * f'))) * (x' - x)⁻¹ = (f x' - f x) / (x' - x) - f',
  {
    have A2:(f x' + (-f x + -((x' + -x) * f')))=(f x' -f x) + -((x' + -x) * f'),
    {
      rw ← add_assoc,
      refl,
    },
    rw A2,
    rw right_distrib,
    have A3:-((x' + -x) * f') * (x' - x)⁻¹ = -f',
    {
      rw mul_comm (x' + -x) f',
      simp,
      rw mul_assoc,
      rw sub_eq_add_neg,
      rw mul_inv_cancel,
      simp,
      apply diff_ne_zero_of_ne,
      apply A1,
    },
    rw A3,
    simp,
    rw div_def,
    rw sub_eq_add_neg _ f',
  },
  rw B1,
end



lemma has_classical_rderiv_at_def (f:ℝ → ℝ)  (f':ℝ) (x:ℝ):
has_classical_rderiv_at f f' x ↔
  has_deriv_at f f' x :=
begin
  unfold has_classical_rderiv_at,
  unfold has_deriv_at,
  unfold has_deriv_at_filter,
  unfold has_fderiv_at_filter,
  unfold asymptotics.is_o,
  unfold has_classical_rlimit,
  unfold asymptotics.is_O_with,
    have B1:∀ x' x, (x' * f' - x * f') = ((x' + -x) * f'),
    {
      intros x' x,
      rw ← mul_sub_right_distrib,
      have B1A:(x' - x) = (x' + -x) := rfl,
      rw B1A,
    },
  split,
  {
    intros A1 c A2,
    have A3:=A1 c A2,
    cases A3 with δ A4,
    cases A4 with A5 A6,
    simp,
    apply @mem_nhds_intro_real _ x (x-δ) (x + δ),
    {
      apply x_in_Ioo A5,
    },
    {
      rw set.subset_def,
      intro x',
      intro A7,
      rw ← abs_lt_iff_in_Ioo2 at A7,
      simp,
      have A8:x' = x ∨ (x' ≠ x) := eq_or_ne,
      cases A8,
      {
        rw A8,
        simp,
      },
      {
        have A9 := A6 x' A8 A7,
        rw ← has_classical_rderiv_at_defh at A9,
        rw ← abs_eq_norm,
        rw ← abs_eq_norm,
        apply move_le2,
        apply abs_diff_pos,
        apply A8,
        apply le_of_lt,
        rw sub_eq_add_neg,
        rw sub_eq_add_neg,
        rw ← add_assoc (f x') (-f x) at A9,
        rw B1,
        apply A9,
        apply A8,
      }
    }
  },
  {
    intros A1 ε A2,
    have A3:0 < ε/2 := half_pos A2,
    have A4:=A1 A3,
    rw filter.eventually_iff at A4,
    -- This simp has caused issues. However, I don't know what
    -- to do with a continuous_linear_map.
    simp at A4,

    have A5:∃ r:ℝ,∃  (H:r > 0), (set.Ioo (x-r) (x+r)) ⊆ {x_1 : ℝ | ∥f x_1 -f x -((x_1 + -x) * f')∥
       ≤ ε / 2 * ∥x_1 + -x∥},
    {
      /-
      mem_nhds_elim_real_bound :
  ∀ (b : set ℝ) (x : ℝ), b ∈ nhds x → (∃ (r : ℝ) (H : r > 0), set.Ioo (x - r) (x + r) ⊆ b)
      -/
      --sorry,
      apply @mem_nhds_elim_real_bound {x_1 : ℝ | ∥f x_1  - f x -((x_1 + -x) * f')∥
       ≤ ε / 2 * ∥x_1 + -x∥}x,
      have B2:{x_1 : ℝ | ∥f x_1 - f x - (x_1 * f' - x * f')∥ ≤ ε / 2 * ∥x_1 - x∥} = 
              {x_1 : ℝ | ∥f x_1 - f x - (x_1 + -x) * f'∥ ≤ ε / 2 * ∥x_1 + -x∥},
      {
        ext x'',
        simp,split;intro B2A,
        {
          rw ← B1 x'' x,
          rw ← sub_eq_add_neg x'' x,
          apply B2A,
        },
        {
          rw ← B1 x'' x at B2A,
          rw ← sub_eq_add_neg x'' x at B2A,
          apply B2A,
        },
      },
      rw ← B2,
      apply A4,
    },
    cases A5 with r A6,
    cases A6 with A7 A8,
    apply exists.intro r,
    split,
    {
      apply A7,
    },
    {
      intros x' A9 A10,
      rw abs_lt_iff_in_Ioo2 at A10,
      rw set.subset_def at A8,
      have A11 := A8 x' A10,
      simp at A11,
      rw ← abs_eq_norm at A11,
      rw ← abs_eq_norm at A11,
      have A12:abs (f x' - f x  - ((x' + -x) * f')) * (abs (x' - x))⁻¹ ≤ ε /2,
      {
        apply move_le,
        apply abs_diff_pos,
        apply A9,
        apply A11,
      },
      have A13:abs (f x' -f x  -((x' + -x) * f')) * (abs (x' - x))⁻¹ < ε,
      {
        apply lt_of_le_of_lt,
        apply A12,
        apply epsilon_half_lt_epsilon,
        apply A2,
      },
      rw ← has_classical_rderiv_at_defh,
      rw sub_eq_add_neg at A13,
      rw sub_eq_add_neg at A13,
      rw add_assoc at A13,
      apply A13,
      apply A9,
    }
  }
end

lemma has_classical_rderiv_at_def2  (f:ℝ → ℝ) (f':ℝ) (x:ℝ):
  has_classical_rderiv_at f f' x  ↔ has_classical_rlimit (λ x':ℝ, (f x' - f x)/(x' - x)) x f' :=
begin
  refl
end



lemma has_classical_rlimit_intro2 (f:ℝ → ℝ) (x:ℝ) (y:ℝ):(
  ∀ ε:ℝ, (0 < ε)→
  ∃ δ:ℝ, (0 < δ) ∧
  ∀ h:ℝ, (h≠ 0) → (abs(h) < δ) → abs (f (x + h) - y)<ε) → has_classical_rlimit f x y :=
begin
  intro A1,
  unfold has_classical_rlimit,
  intros ε A2,
  have A3:=A1 ε A2,
  cases A3 with δ A4,
  cases A4 with A5 A6,
  apply exists.intro δ,
  split,
  {
    apply A5,
  },
  {
    intros x' A7 A8,
    let h:= x' - x,
    begin
      have A9:h = x' - x := rfl,
      have A10:h ≠ 0,
      {
        rw A9,
        intro A10,
        apply A7,
        apply eq_of_sub_eq_zero A10,
      },
      have A11:abs h < δ,
      {
        rw A9,
        rw abs_antisymm,
        apply A8
      },
      have A12:= A6 h A10 A11,
      have A13:x+h = x',
      {
        rw A9,
        simp,
      },
      rw A13 at A12,
      apply A12,
    end
  }
end

lemma add_cancel_left {x y z:ℝ}:x + y = x + z ↔ y = z :=
begin
  split,
  intros A1,
  {
    simp at A1,
    apply A1,
  },
  {
    simp,
  }
end

lemma add_cancel_right {x y z:ℝ}:y + x = z + x ↔ y = z :=
begin
  split,
  intros A1,
  {
    simp at A1,
    apply A1,
  },
  {
    simp,
  }
end

lemma has_classical_rlimit_offset {f:ℝ → ℝ} {x y k:ℝ}:
  has_classical_rlimit f x y → has_classical_rlimit (f∘ (λ h,k + h)) (x - k) y :=
begin
  intro A1,
  apply has_classical_rlimit_intro2,
  intros ε A2,
  unfold has_classical_rlimit at A1,
  have A3:= A1 ε A2,
  cases A3 with δ A4,
  cases A4 with A5 A6,
  apply exists.intro δ,
  split,
  {
    apply A5,
  },
  {
    intros h A7 A8,
    simp,
    rw sub_eq_add_neg _ k,
    rw add_assoc x (-k) h,
    rw add_comm (-k) h,
    rw ← add_assoc x h (-k),
    rw add_comm (x + h) (-k),
    rw ← add_assoc (k) (-k) (x + h),
    rw add_right_neg,
    rw zero_add,
    let x' := x + h,
    begin
      have A9:x' = x + h := rfl,
      rw ← A9,
      have A13:h = x' - x,
      {
        rw ← @add_cancel_right (x),
        simp,
      },
      apply A6,
      {
        intro A11,
        apply A7,
        rw A11 at A13,
        simp at A13,
        apply A13,
      },
      {
        rw abs_antisymm,
        rw ← A13,
        apply A8,
      }
    end
  }
end

lemma has_classical_rlimit_offset2 {f:ℝ → ℝ} {x y k:ℝ}:
  has_classical_rlimit f x y ↔  has_classical_rlimit (f∘ (λ h,k + h)) (x - k) y :=
begin
  split;intros A1,
  {
    apply has_classical_rlimit_offset A1,
  },
  {
    have A2:f = (f ∘ λ (h : ℝ), k + h) ∘ (λ (h : ℝ), (-k) + h),
    {
      ext n,
      simp,
    },
    have A3:(x - k) - (-k) = x,
    {
      simp,
    },
    rw ← A3,
    rw A2,
    apply @has_classical_rlimit_offset (f ∘ λ (h : ℝ), k + h) (x - k) y (-k),
    apply A1,
  }
end

lemma has_classical_rlimit_def2 {f:ℝ → ℝ} {x:ℝ} {y:ℝ}:
  has_classical_rlimit f x y ↔ has_classical_rlimit (f∘ (λ h,x + h)) 0 y :=
begin
  rw (@has_classical_rlimit_offset2 f x y x),
  simp,
end

lemma has_classical_rlimit_subst {f g:ℝ → ℝ} {x:ℝ} {y:ℝ}:
  (∀ x'≠ x, f x' = g x') →
  has_classical_rlimit f x y → has_classical_rlimit g x y :=
begin
  intros A1 A2,
  rw has_classical_rlimit_def,
  intros ε A3,
  rw has_classical_rlimit_def at A2,
  have A4 := A2 ε A3,
  cases A4 with δ A5,
  cases A5 with A6 A7,
  apply exists.intro δ,
  split,
  {
    apply A6,
  },
  {
    intros x' A8 A9,
    have A10 := A1 x' A8,
    rw ← A10,
    apply A7,
    apply A8,
    apply A9,
  }
end


lemma has_classical_rderiv_at_def3  (f:ℝ → ℝ) (f':ℝ) (x:ℝ):
  has_classical_rderiv_at f f' x  ↔ has_classical_rlimit (λ h:ℝ, (f (x + h) - f x)/h) 0 f' :=
begin
  rw has_classical_rderiv_at_def2,
  rw has_classical_rlimit_def2,
  have A1:((λ (x' : ℝ), (f x' - f x) / (x' - x)) ∘ λ (h : ℝ), x + h)=
  (λ (h : ℝ), (f (x + h) - f x) / h),
  {
    ext x',
    simp,
  },
  rw A1,
end


/- TODO: rewrite this using has_classical_rderiv_at_def3 -/
lemma has_classical_rderiv_at_intro2 (f:ℝ → ℝ)  (f':ℝ) (x:ℝ):(
  ∀ ε:ℝ, (0 < ε)→
  ∃ δ:ℝ, (0 < δ) ∧
  ∀ h:ℝ, (h≠ 0) → (abs(h) < δ) → abs ((f (x + h) - f x) / h - f')<ε) → has_classical_rderiv_at f f' x :=
begin
  intro A1,
  unfold has_classical_rderiv_at,
  apply has_classical_rlimit_intro2,
  intros ε A3,
  have A4:=A1 ε A3,
  cases A4 with δ A5,
  cases A5 with A6 A7,
  apply exists.intro δ,
  split,
  {
    apply A6,
  },
  {
    intros h A8 A9,
    have A10:x + h -x = h,
    {
      simp,
    },
    rw A10,
    have A11 := A7 h A8 A9,
    apply A11,
  },
end

/-
real.is_topological_basis_Ioo_rat :
  topological_space.is_topological_basis (⋃ (a b : ℚ) (h : a < b), {set.Ioo ↑a ↑b})
-/




lemma center_in_ball {x:ℝ} {r:ℝ}:(0 < r) → (x∈ set.Ioo (x-r) (x + r)) :=
begin
  intro A1,
  rw ← abs_lt_iff_in_Ioo,
  simp,
  apply A1,
end

lemma ball_subset_Ioo {a b:ℝ} {x:ℝ}:
  x ∈ set.Ioo a b →
  ∃ r>0, set.Ioo (x - r) (x + r) ⊆ set.Ioo a b :=
begin
  intro A1,
  let r := min (x-a) (b-x),
  begin
    apply exists.intro r,
    simp at A1,
    cases A1 with A2 A3,
    have A4:0 < x - a := sub_pos_of_lt A2,
    have A5:0 < b - x := sub_pos_of_lt A3,
    have A6:0 < r := lt_min A4 A5,
    split,
    {
      apply A6,
    },
    {
      rw set.Ioo_subset_Ioo_iff,
      {
        split,
        {
          apply le_sub_left_of_add_le,
          apply add_le_of_le_sub_right,
          apply min_le_left,
        },
        {
          rw add_comm,
          apply add_le_of_le_sub_right,
          apply min_le_right,
        }
      },
      {
        rw ← set.nonempty_Ioo,
        have B1:x ∈ set.Ioo (x - r) (x + r) := center_in_ball A6,
        apply set.nonempty_of_mem,
        apply B1,
      }
    }
  end
end


lemma is_open_iff_ball_subset' {V:set ℝ}:
  is_open V ↔ (∀ x∈ V, ∃ ε>0, set.Ioo (x - ε) (x+ ε )⊆ V) :=
begin
  have A0 := real.is_topological_basis_Ioo_rat,
  split;intros A1,
  {
    intros x A2,
    have A3 := topological_space.mem_basis_subset_of_mem_open A0 A2 A1,
    cases A3 with V2 A4,
    cases A4 with A5 A6,
    cases A6 with A7 A8,
    simp at A5,
    cases A5 with a A9,
    cases A9 with b A10,
    cases A10 with A11 A12,
    subst V2,
    have A13 := ball_subset_Ioo A7,
    cases A13 with r A14,
    cases A14 with A15 A16,
    apply exists.intro r,
    split,
    {
      apply A15,
    },
    {
      apply set.subset.trans A16 A8,
    }
  },
  {
    rw is_open_iff_forall_mem_open,
    intros x A2,
    have A3 := A1 x A2,
    cases A3 with ε A4,
    cases A4 with A5 A6,
    apply exists.intro (set.Ioo (x - ε) (x + ε)),
    split,
    {
      apply A6,
    },
    split,
    {
      apply @is_open_Ioo ℝ _ _ _  (x -ε) (x + ε),
    },
    {
      apply center_in_ball A5,
    },
  }
end

lemma continuous_iff_has_classical_rlimit {f:ℝ → ℝ}:
  (∀ x:ℝ, has_classical_rlimit f x (f x)) ↔ continuous f :=
begin
  split;intros A1,
  {
    intros V A2,
    rw is_open_iff_ball_subset',
    intros x A3,
    have A4 := A1 x,
    unfold has_classical_rlimit at A4,
    rw is_open_iff_ball_subset' at A2,
    have A5 := A2 (f x) A3,
    cases A5 with ε A6,
    cases A6 with A7 A8,
    have A9 := A4 ε A7,
    cases A9 with δ A10,
    cases A10 with A11 A12,
    apply exists.intro δ,
    split,
    {
      apply A11,
    },
    {
      rw set.subset_def,
      intros x' A13,
      rw ← abs_lt_iff_in_Ioo at A13,
      rw abs_antisymm at A13,
      have A14:(x'=x)∨ (x'≠ x) := eq_or_ne,
      cases A14,
      {
        subst x',
        apply A3,
      },
      {
        have A15 := A12 x' A14 A13,
        simp,
        apply A8,
        rw ← abs_lt_iff_in_Ioo,
        apply A15,
      }
    }
  },
  {
    intro x,
    unfold continuous at A1,
    unfold has_classical_rlimit,
    intros ε A2,
    have A3:is_open (set.Ioo (f x - ε) (f x + ε)),
    {
      apply @is_open_Ioo ℝ _ _ _  (f x -ε) (f x + ε),
    },
    have A4 := A1 (set.Ioo (f x - ε) (f x + ε)) A3,
    have A5 :x ∈ f⁻¹' (set.Ioo (f x - ε) (f x + ε)),
    {
      simp,
      split,
      {
        apply sub_lt_of_sub_lt,
        rw sub_self,
        apply A2,
      },
      {
        apply A2,
      }
    },
    rw is_open_iff_ball_subset' at A4,
    have A6 := A4 x A5,
    cases A6 with δ A7,
    cases A7 with A8 A9,
    apply exists.intro δ,
    split,
    apply A8,
    intros x' A10 A11,
    rw abs_lt_iff_in_Ioo,
    apply A9,
    rw abs_antisymm at A11,
    rw abs_lt_iff_in_Ioo at A11,
    apply A11,
  }
end

lemma classical_rlimit_continuous_def {f:ℝ → ℝ} {x:ℝ}:
  (has_classical_rlimit f x (f x)) ↔ (∀ ε > 0, ∃ δ > 0, ∀ x', (abs (x' - x) < δ → abs (f x' - f x) < ε)) :=
begin
  split;intros A1,
  {
    intros ε A2,
    unfold has_classical_rlimit at A1,
    have A3 := A1 ε A2,
    cases A3 with δ A4,
    cases A4 with A5 A6,
    apply exists.intro δ,
    split,
    {
      apply A5,
    },
    {
      intros x' A7,
      have A8:x' = x ∨ (x' ≠ x) := eq_or_ne,
      cases A8,
      {
        subst x',
        simp,
        apply A2,
      },
      {
        have A9 := A6 x' A8,
        apply A9,
        rw abs_antisymm,
        apply A7,
      }
    }
  },
  {
    unfold has_classical_rlimit,
    intros ε A2,
    have A3 := A1 ε A2,
    cases A3 with δ A4,
    cases A4 with A5 A6,
    apply exists.intro δ,
    split,
    {
      apply A5,
    },
    {
      intros x' A7 A8,
      rw abs_antisymm at A8,
      apply A6 x' A8,
    }
  }
end

lemma classical_rlimit_continuous_all_def {f:ℝ → ℝ}:
  (∀ x, (has_classical_rlimit f x (f x))) ↔
  (∀ x, (∀ ε > 0, ∃ δ > 0, ∀ x', (abs (x' - x) < δ → abs (f x' - f x) < ε))) :=
begin
  split;intros A1,
  {
    intro x,
    have A2 := A1 x,
    rw classical_rlimit_continuous_def at A2,
    apply A2,
  },
  {
    intro x,
    have A2 := A1 x,
    rw ← classical_rlimit_continuous_def at A2,
    apply A2,
  },
end

lemma continuous_def {f:ℝ → ℝ}:
  continuous f ↔  (∀ x, ∀ ε > 0, ∃ δ > 0, ∀ x', (abs (x' - x) < δ → abs (f x' - f x) < ε)) :=
begin
  rw  ← continuous_iff_has_classical_rlimit,
  rw classical_rlimit_continuous_all_def,
end


lemma continuous_elim {f:ℝ → ℝ} (x:ℝ):
  continuous f →  (∀ ε > 0, ∃ δ > 0, ∀ x', (abs (x' - x) < δ → abs (f x' - f x) < ε)) :=
begin
  intro A1,
  rw continuous_def at A1,
  apply (A1 x),
end
