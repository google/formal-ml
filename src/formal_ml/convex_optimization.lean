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
/-
  This file proves that if a convex function (by the derivative definition) has a derivative
  of zero at a point x, then that is a minimum.
 -/

import analysis.calculus.mean_value
import data.complex.exponential
import formal_ml.real


/-
  Note: consider dropping this definition, and proving this using has_deriv_at already provided.
  has_derivative f f' ↔ differentiable f ∧ deriv f = f'
 -/
def has_derivative (f f':ℝ → ℝ):Prop := (∀ x, has_deriv_at f (f' x) x)

lemma has_derivative.differentiable (f f':ℝ → ℝ):(has_derivative f f') → differentiable ℝ f :=
begin
  intro A1,
  unfold differentiable,
  intro x,
  apply has_deriv_at.differentiable_at,
  apply A1,
end

lemma differentiable.has_derivative (f:ℝ → ℝ):differentiable ℝ f → (has_derivative f (deriv f)) :=
begin
  intro A1,
  unfold differentiable at A1,
  intro x,
  apply differentiable_at.has_deriv_at,
  apply A1,
end

--Unused
lemma has_derivative_add (f f' g g':ℝ → ℝ):
  has_derivative f f' →
  has_derivative g g' →
  has_derivative (f + g) (f' + g') :=
begin
  intros A1 A2 x,
  apply has_deriv_at.add,
  {
    apply A1,
  },
  {
    apply A2,
  }
end

--Used in exp_bound.lean
lemma has_derivative_sub (f f' g g':ℝ → ℝ):
  has_derivative f f' →
  has_derivative g g' →
  has_derivative (f - g) (f' - g') :=
begin
  intros A1 A2 x,
  apply has_deriv_at.sub,
  {
    apply A1,
  },
  {
    apply A2,
  }
end

--Unused
lemma has_derivative_const (k:ℝ):
  has_derivative (λ x:ℝ, k)  (λ x:ℝ, 0) :=
begin
  intro x,
  simp,
  apply has_deriv_at_const,
end

lemma has_derivative_id:
  has_derivative (λ x:ℝ, x)  (λ x:ℝ, 1) :=
begin
  intro x,
  simp,
  apply has_deriv_at_id,
end

lemma has_derivative_neg (f f':ℝ → ℝ):
  has_derivative f f' →
  has_derivative (-f)  (-f') :=
begin
  intros A1 x,
  apply has_deriv_at.neg,
  apply A1,
end

--Used in exp_bound.lean
lemma has_derivative_add_const (f f':ℝ → ℝ) (k:ℝ):
  has_derivative f f' →
  has_derivative (λ x:ℝ, f x + k)  (f') :=
begin
  intros A1 x,
  apply has_deriv_at.add_const,
  apply A1,
end


section convex_optimization
variables (f f' f'': ℝ → ℝ)

lemma exists_has_deriv_at_eq_slope_total (x y:ℝ):
  (has_derivative f f') →
  (x < y) →
  (∃ c ∈ set.Ioo x y, f' c = (f y - f x) / (y - x)) :=
begin
  intros A1 A2,
  apply exists_has_deriv_at_eq_slope,
  {
    exact A2,
  },
  {
    have B1:differentiable ℝ f := has_derivative.differentiable _ _ A1,
    apply continuous.continuous_on,
    apply differentiable.continuous B1,
  },
  {
    intros z C1,
    apply A1,
  }
end


lemma zero_lt_of_neg_lt (x:ℝ):(0 < x) → (-x < 0) := neg_lt_zero.mpr


lemma div_pos_of_pos_of_pos {a b:ℝ}:(0 < a) → (0 < b) → 0 < (a/b) :=
begin
  intros A1 A2,
  rw div_def,
  apply mul_pos,
  apply A1,
  rw inv_pos,
  apply A2,
end


lemma is_minimum (x y:ℝ):
  (has_derivative f f') →
  (has_derivative f' f'')→
  (∀ z, 0 ≤ (f'' z))→
  (f' x = 0) →
  (f x ≤ f y) :=
begin
  intros A1 A2 A3 A4,

  have A5:differentiable ℝ f := has_derivative.differentiable _ _ A1,
  have A6:differentiable ℝ f' := has_derivative.differentiable _ _ A2,
  have A7:continuous f := differentiable.continuous A5,
  have A8:continuous f' := differentiable.continuous A6,
  have A9:(x < y)∨ (x=y) ∨ (y < x) := lt_trichotomy x y,
  cases A9,
  {
    have B1:¬(f y < f x),
    {
      intro B0,
      have B1C:∃ c ∈ set.Ioo x y, f' c = (f y - f x) / (y - x),
      {
        apply exists_has_deriv_at_eq_slope_total,
        apply A1,
        apply A9,
      },
      cases B1C with c B1D,
      cases B1D with B1E B1F,
      have B1G:f' c < 0,
      {
        rw B1F,
        apply div_neg_of_neg_of_pos,
        { -- ⊢ f y - f x < 0
          apply sub_lt_zero.mpr,
          apply B0,
        },
        { -- ⊢ 0 < y - x
          apply sub_pos.mpr,
          apply A9,
        },
      },
      have B1H:x < c,
      {
        have B1H1:x < c ∧ c < y,
        {
          apply set.mem_Ioo.mp,
          exact B1E,
        },
        apply B1H1.left,
      },
      have B1I:∃ d ∈ set.Ioo x c, f'' d = (f' c - f' x) / (c - x),
      {
        apply exists_has_deriv_at_eq_slope_total,
        apply A2,
        apply B1H,
      },
      cases B1I with d B1J,
      cases B1J with BIK B1L,
      have B1M:¬ (f'' d < 0),
      {
        apply not_lt_of_le,
        apply A3,
      },
      apply B1M,
      rw B1L,
      apply div_neg_of_neg_of_pos,
      {
        rw A4,
        simp,
        apply B1G,
      },
      {
        apply sub_pos.mpr,
        apply B1H,
      }
    },
    apply le_of_not_lt B1,
  },
  {
    cases A9,
    {
      rw A9,
    },
    {
      have B1:¬(f y < f x),
      {
        intro B0,
        have B1A:continuous_on f (set.Icc x y),
        {
          apply continuous.continuous_on A7,
        },
        have B1B:differentiable_on ℝ f (set.Ioo y x),
        {
          apply differentiable.differentiable_on A5,
        },
        have B1C:∃ c ∈ set.Ioo y x, f' c = (f x - f y) / (x - y),
        {
          apply exists_has_deriv_at_eq_slope_total,
          apply A1,
          apply A9,
        },
        cases B1C with c B1D,
        cases B1D with B1E B1F,
        have B1G:0 < f' c,
        {
          rw B1F,
          -- y < x, f y < f x ⊢ 0 < (f x - f y) / (x - y)
          -- 0 < x - y, 0 < f x - f y ⊢ 0 < (f x - f y) / (x - y)
          apply div_pos_of_pos_of_pos,
          { -- ⊢ f y - f x < 0
            apply sub_pos.mpr,
            apply B0,
          },
          { -- ⊢ 0 < y - x
            apply sub_pos.mpr,
            apply A9,
          },
        },
        have B1H:c < x,
        {
          have B1H1:y < c ∧ c < x,
          {
            apply set.mem_Ioo.mp,
            exact B1E,
          },
          apply B1H1.right,
        },
        have B1I:∃ d ∈ set.Ioo c x, f'' d = (f' x - f' c) / (x - c),
        {
          apply exists_has_deriv_at_eq_slope_total,
          apply A2,
          apply B1H,
        },
        cases B1I with d B1J,
        cases B1J with BIK B1L,
        have B1M:¬ (f'' d < 0),
        {
          apply not_lt_of_le,
          apply A3,
        },
        apply B1M,
        rw B1L,
        apply div_neg_of_neg_of_pos,
        {
          rw A4,
          simp,
          --apply zero_lt_of_neg_lt,
          apply B1G,
        },
        {
          apply sub_pos.mpr,
          apply B1H,
        }
      },
      apply le_of_not_lt B1,
    }
  }
end

/-
  Lifting the theorem to the mathlib terminology
 -/
lemma is_minimum' (x y:ℝ):
  differentiable ℝ f →
  differentiable ℝ (deriv f) →
  (0 ≤ (deriv (deriv  f)))→
  (deriv f x = 0) →
  (f x ≤ f y) :=
begin
  intros A1 A2 A3 A4,
  let f' := deriv f,
  let f'' := deriv f',
  begin
    have B1:f' = deriv f := rfl,
    have B2:f'' = deriv f' := rfl,
    have C1:=differentiable.has_derivative f A1,
    rw ← B1 at A2,
    have C2:=differentiable.has_derivative f' A2,
    rw ← B2 at C2,
    rw ← B1 at C1,
    rw ← B1 at A3,
    rw ← B2 at A3,
    rw ← B1 at A4,
    apply is_minimum f f' f'' x y C1 C2 A3 A4,
  end
end

end convex_optimization

