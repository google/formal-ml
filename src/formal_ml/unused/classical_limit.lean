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
import formal_ml.unused.classical_deriv
import formal_ml.filter_util



---Results about limits--------------------------------------------------------------------------
-- cf decidable_linear_ordered_add_comm_group.tendsto_nhds
-- This seems to cover the connection to a classical limit. 
def has_classical_limit (f:ℕ → ℝ) (x:ℝ):Prop := ∀ ε:ℝ,
  0 < ε → ∃ n, ∀ n', n<n' →  abs (f n' - x) < ε

def exists_classical_limit (f:ℕ → ℝ):Prop := ∃ x:ℝ,
  has_classical_limit f x


lemma has_classical_limit_def (f:ℕ → ℝ) (x:ℝ):
  has_classical_limit f x ↔ filter.tendsto f filter.at_top (@nhds ℝ _ x) :=
begin
  split;intro A1,
  {
    apply filter_tendsto_intro,
    intros b A2,
    unfold set.preimage,
    unfold has_classical_limit at A1,
    have A3:(∃ r>0, (set.Ioo (x-r) (x+r)) ⊆ b) := mem_nhds_elim_real_bound _ _ A2,
    cases A3 with r A4,
    cases A4 with A5 A6,
    have A7 := A1 r A5,
    cases A7 with n A8,
    apply @mem_filter_at_top_intro ℕ _ {x : ℕ | f x ∈ b} (nat.succ n),
    rw set.subset_def,
    intros n' A9,
    simp at A9,
    have A10:=nat.lt_of_succ_le A9,
    have A11 := A8 n' A10,
    rw set.subset_def at A6,
    apply A6,
    rw ← abs_lt_iff_in_Ioo,
    apply A11,
  },
  {
    unfold has_classical_limit,
    intros ε A2,
    have A3:set.Ioo (x -ε) (x + ε) ∈ nhds x := Ioo_nbhd A2,
    have A4:=filter_tendsto_elim A1 A3,
    unfold filter.tendsto at A1,
    have A5 := filter_le_elim A1 A3,
    have A6 := mem_filter_at_top_elim A5,
    cases A6 with n A7,
    rw set.subset_def at A7,
    apply exists.intro n,
    intros n' A8,
    have A9 := A7 n',
    --simp at A9,
    rw abs_lt_iff_in_Ioo,
    apply A9,
    apply le_of_lt,
    apply A8,
  }
end

section functional_def

local attribute [instance] classical.prop_decidable

noncomputable def classical_limit (f:ℕ → ℝ):ℝ :=
    if h:exists_classical_limit f then classical.some h else 0

end functional_def



lemma has_classical_limit_neg {f:ℕ → ℝ} {x:ℝ}:
  has_classical_limit f x →
  has_classical_limit (-f) (-x)  :=
begin
  unfold has_classical_limit,
  intros A1 ε A2,
  have A3 := A1 ε A2,
  cases A3 with n A4,
  apply exists.intro n,
  intros n',
  intro A5,
  have A6 := A4 n' A5,
  simp,
  rw abs_antisymm,
  apply A6,
end


lemma has_classical_limit_subst (f g:ℕ → ℝ) (x:ℝ):
  (f = g) →
  has_classical_limit f x = has_classical_limit g x :=
begin
  intro A1,
  rw A1,
end



lemma has_classical_limit_const {k:ℝ}:has_classical_limit (λ x:ℕ, k) k :=
begin
  intros ε A1,
  apply exists.intro 0,
  intros n' A2,
  simp,
  exact A1,
end

lemma has_classical_limit_sum {f g:ℕ → ℝ} {x y:ℝ}:
  has_classical_limit f x →
  has_classical_limit g y →
  has_classical_limit (f + g) (x + y) :=
begin
  unfold has_classical_limit,
  intros A1 B1 ε C1,
  have C2:0 < (ε/2) := half_pos C1,
  have A2 := A1 (ε/2) C2,
  have B2 := B1 (ε/2) C2,
  cases A2 with nA A3,
  cases B2 with nB B3,
  let n := max nA nB,
  begin
    apply exists.intro n,
    intros n' C3,
    have A4:nA < n',
    {
      apply lt_of_le_of_lt,
      apply le_max_left nA nB,
      apply C3,
    },
    have B4:nB < n',
    {
      apply lt_of_le_of_lt,
      apply le_max_right nA nB,
      apply C3,
    },
    have A5 := A3 n' A4,
    have B5 := B3 n' B4,
    have C6:abs ((f + g) n' - (x + y)) ≤ abs (f n' - x)  + abs (g n' - y),
    {
      have C6A:((f + g) n' - (x + y))=((f n' - x) + (g n' - y)),
      {
        simp,
        rw ← sub_sub,
        rw sub_eq_add_neg,
        rw sub_eq_add_neg,
        rw sub_eq_add_neg,
        rw add_assoc _ (g n'),
        rw add_comm (g n'),
        rw ← add_assoc,
        rw sub_eq_add_neg,
        rw ← add_assoc,
      },
      rw C6A,
      apply abs_add,
    },
    apply lt_of_le_of_lt,
    apply C6,
    have C7: ε = (ε /2 +  ε /2),
    {
      simp,
    },
    rw C7,
    apply add_lt_add A5 B5,
  end
end

lemma has_classical_limit_sub {f g:ℕ → ℝ} {x y:ℝ}:
  has_classical_limit f x →
  has_classical_limit g y →
  has_classical_limit (f - g) (x - y) :=
begin
  intros A1 A2,
  rw sub_eq_add_neg,
  rw sub_eq_add_neg,
  apply has_classical_limit_sum A1,
  apply has_classical_limit_neg A2,
end


lemma has_classical_limit_unique {f:ℕ → ℝ} {x y:ℝ}:
  has_classical_limit f x →
  has_classical_limit f y →
  (x = y) :=
begin
  rw has_classical_limit_def,
  rw has_classical_limit_def,
  apply tendsto_nhds_unique,
end

lemma has_classical_limit_classical_limit {f:ℕ → ℝ}:
  exists_classical_limit f →
  has_classical_limit f (classical_limit f) :=
begin
  unfold exists_classical_limit,
  intro A1,
  unfold classical_limit,
  rw dif_pos,
  apply classical.some_spec A1,
end

lemma exists_classical_limit_intro {f:ℕ → ℝ} {x:ℝ}:
  has_classical_limit f x →
  exists_classical_limit f :=
begin
  intro A1,
  unfold exists_classical_limit,
  apply exists.intro x,
  apply A1,
end

lemma eq_classical_limit {f:ℕ → ℝ} {x:ℝ}:
  has_classical_limit f x →
  x = classical_limit f :=
begin
  intro A1,
  have A2:exists_classical_limit f :=exists_classical_limit_intro A1,
  have A3:has_classical_limit f (classical_limit f) := has_classical_limit_classical_limit A2,
  apply has_classical_limit_unique A1 A3,
end


/-

  This is trivial, because the reals are a topological monoid.

  The classical way would be to break it apart into two pieces.
  abs (f' * g' - f * g)< ε,
  abs (f' * g' - f' * g + f' * g - f * g) < ε
  abs (f' * (g' -  g) + (f' - f) * g) < ε
  abs (f' * (g' -  g) + (f' - f) * g) < ε
  abs (f' * (g' -  g)) + abs((f' - f) * g) < ε
  abs (f' * (g' -  g)) < ε/2 ∧ abs((f' - f) * g) < ε/2
-/
lemma has_classical_limit_mul {f g:ℕ → ℝ} (x y:ℝ):
  has_classical_limit f x →
  has_classical_limit g y →
  has_classical_limit (f * g) (x * y) :=
begin
  rw has_classical_limit_def,
  rw has_classical_limit_def,
  rw has_classical_limit_def,
  apply filter.tendsto.mul,
end


lemma has_classical_limit_mul_const {f:ℕ → ℝ} {k x:ℝ}:
  has_classical_limit f x →
  has_classical_limit (λ n, k * (f n)) (k * x) :=
begin
  intro A1,
  have A2:(λ n:ℕ, k * (f n)) = (λ n:ℕ, k) * f,
  {
    ext n,
    simp,
  },
  rw A2,
  apply has_classical_limit_mul,
  {
    apply has_classical_limit_const,
  },
  {
    apply A1,
  }
end

lemma has_classical_limit_mul_const_zero {f:ℕ → ℝ} {k:ℝ}:
  has_classical_limit f 0 →
  has_classical_limit (λ n, k * (f n)) 0 :=
begin
  intro A1,
  have A2:has_classical_limit (λ n, k * (f n)) (k * 0),
  {
    apply has_classical_limit_mul_const A1,
  },
  rw mul_zero at A2,
  apply A2,
end

lemma has_classical_limit_exp (x:ℝ):
  (0 ≤ x) →
  (x < 1) →
  has_classical_limit (λ n, x^n) 0 :=
begin
  intros A1 A2,
  rw has_classical_limit_def,
  apply tendsto_pow_at_top_nhds_0_of_lt_1,
  apply A1,
  apply A2,
end


lemma has_classical_limit_inv_zero:
  has_classical_limit (λ n:ℕ, (n:ℝ)⁻¹) 0 :=
begin
  unfold has_classical_limit,
  intros ε A1,
  apply exists.intro (nat_ceil (ε⁻¹)),
  intros n' A2,
  simp,
  -- ⊢ abs ((n':ℝ)⁻¹) < ε
  have A4:0 ≤ (n':ℝ)⁻¹,
  {
    apply inv_nonneg_of_nonneg,
    simp,
  },
  have A5:(ε⁻¹)⁻¹ = ε,
  {
    simp,
  },
  rw abs_of_nonneg A4,
  rw ← A5,
  apply inv_decreasing,
  {
    apply inv_pos_of_pos,
    apply A1,
  },
  apply lt_of_le_of_lt,
  apply le_nat_ceil,
  apply real_lt_coe,
  apply A2,
end

lemma has_classical_limit_eq_after {f g:ℕ → ℝ} {x:ℝ} {n:ℕ}:
  has_classical_limit f x →
  (∀ n':ℕ, n < n' → (f n' = g n')) →
  has_classical_limit g x :=
begin
  unfold has_classical_limit,
  intros A1 A2 ε A3,
  have A4 := A1 ε A3,
  cases A4 with n' A5,
  apply exists.intro (max n' n),
  intros n'' A6,
  have A7 := A2 n'' (lt_of_le_of_lt (le_max_right n' n) A6),
  have A8 := A5 n'' (lt_of_le_of_lt (le_max_left n' n) A6),
  rw ← A7,
  apply A8,
end


lemma has_classical_limit_ratio_one:
  has_classical_limit (λ n:ℕ, ((n + 1):ℝ) * (n:ℝ)⁻¹) 1 :=
begin
  have A2:has_classical_limit (λ n:ℕ, (1:ℝ) + (n:ℝ)⁻¹) 1,
  {
    have A2A:(λ n:ℕ, (1:ℝ) + (n:ℝ)⁻¹)=(λ n:ℕ, (1:ℝ)) + (λ n:ℕ, (n:ℝ)⁻¹),
    {
      ext n,
      simp,
    },
    rw A2A,
    have A2B:(1:ℝ) = (1:ℝ) + (0:ℝ),
    {
      simp,
    },
    rw A2B,
    apply has_classical_limit_sum,
    {
      simp,
      apply has_classical_limit_const,
    },
    {
      apply has_classical_limit_inv_zero,
    }
  },
  apply has_classical_limit_eq_after A2,
  {
    intros n A1A,
    simp,
    rw right_distrib,
    simp,
    rw mul_inv_cancel,
    intro A1B,
    simp at A1B,
    rw A1B at A1A,
    apply lt_irrefl 0 A1A,
  },
end




lemma has_classical_limit_abs_zero {f:ℕ → ℝ}:
  has_classical_limit (abs ∘ f) 0 ↔
  has_classical_limit f 0 :=
begin
  unfold has_classical_limit,split;
  intros A1 ε A2;
  have A3:= A1 ε A2;
  cases A3 with n A4;
  apply exists.intro n;
  intros n' A5;
  have A6:= A4 n' A5;
  simp at A6,
  {
    rw abs_abs at A6,
    simp,
    apply A6,
  },
  {
    simp,
    rw abs_abs,
    apply A6,
  }
end

lemma has_classical_limit_half_abs_zero {f g:ℕ → ℝ}:
  has_classical_limit (f * g) 0 ↔
  has_classical_limit (f * (abs ∘ g)) 0 :=
begin
  have A1:∀ n',abs ((f * g) n' - 0)=abs ((f * abs ∘ g) n' - 0),
  {
    intro n',
    simp,
    rw abs_mul,
    rw abs_mul,
    rw abs_abs,
  },
  unfold has_classical_limit,
  split;intros A2 ε A3;have A4:=A2 ε A3;cases A4 with n A5;apply exists.intro n;intros n' A6;
       have A7:=A5 n' A6,
  {
    rw ← A1,
    apply A7,
  },
  {
    rw A1,
    apply A7,
  }
end


lemma has_classical_limit_bound {f:ℕ → ℝ} (g:ℕ → ℝ):
  has_classical_limit g 0 →
  (∃ (n:ℕ), ∀ (n':ℕ), n < n' → abs (f n') ≤ g n') →
  has_classical_limit f 0 :=
begin
  intros A1 A2,
  unfold has_classical_limit,
  cases A2 with n₁ A3,
  intros ε A4,
  unfold has_classical_limit at A1,
  have A5 := A1 ε A4,
  cases A5 with n₂ A6,
  apply exists.intro (max n₁ n₂),
  intros n' A7,
  have A8 := A3 n' (lt_of_le_of_lt (le_max_left n₁ n₂) A7),
  have A9 := A6 n' (lt_of_le_of_lt (le_max_right n₁ n₂) A7),
  rw sub_zero,
  rw sub_zero at A9,
  have A10:g n' < ε,
  {
    rw abs_of_nonneg at A9,
    {
      apply A9,
    },
    {
      apply le_trans,
      apply abs_nonneg (f n'),
      apply A8,
    }
  },
  apply lt_of_le_of_lt,
  apply A8,
  apply A10,
end


/-
   r < (1 + r)/2
 -/




lemma bound_ratio_inductive {a b c d:ℝ}:
  0 < a → 0 < c → a ≤ b→  c * a⁻¹ ≤ d → c ≤ d * b :=
begin
  intros A1' A2' A3 A4,
  have A1 := (le_of_lt A1'),
  have A2 := (le_of_lt A2'),

  have A5:0 ≤ c * a⁻¹ :=mul_nonneg A2 (inv_nonneg_of_nonneg (A1)),
  have A6:(c * a⁻¹) * a ≤ d * b := mul_le_mul A4 A3 (A1) (le_trans A5 A4),
  rw mul_assoc at A6,
  rw inv_mul_cancel at A6,
  rw mul_one at A6,
  apply A6,
  intro A7,
  rw A7 at A1',
  apply lt_irrefl (0:ℝ) A1',
end




lemma has_classical_limit_ratio_lt_oneh2 {f:ℕ→ ℝ} {k:ℝ} {r:ℝ} {n:ℕ}:
  (0≤ k) →
  (r < 1) →
  (∀ n, 0 < f n) →
  (f n = k * r^n) →
  (∀ n',n ≤ n' → f (nat.succ n') * (f n')⁻¹ ≤ r) →
  (∀ n',n ≤ n' → f n' ≤ k * r^n') :=
begin
  intros A1 A3 A4 A5 A6,
  intro n',
  induction n',
  {
    intros B1,
    simp at B1,
    rw B1 at A5,
    rw A5,
  },
  {
    intro C1,
    rw le_iff_lt_or_eq at C1,
    cases C1,
    {
      have C2:n ≤ n'_n := nat.lt_succ_iff.mp C1,
      have C3:=n'_ih C2,
      have C4:=A6 n'_n C2,
      have C5:k * r ^ nat.succ n'_n=r * (k * r^n'_n),
      {
        rw pow_succ,
        rw ← mul_assoc,
        rw mul_comm k r,
        rw mul_assoc,
      },
      rw C5,
      apply bound_ratio_inductive,
      {
        apply A4 n'_n,
      },
      {
        apply A4 (nat.succ n'_n),
      },
      {
        apply C3,
      },
      {
        apply C4,
      },

    },
    {
      rw ← C1,
      rw ← A5,
    }
  }
end




/-
  If the ratio of one value to the next approaches a value between 0 and 1 exclusive, then
  there is an n where the ratio is always in (0,r'), where r' < 1.
  This implies that abs (f n') < k (r')^n', and we can prove that k (r')^n' → 0.

  There is a section in specific_limits.lean, edist_le_geometric, that has a similar
  flavor.

  NOTE: after writing this, I reviewed later unproven lemmas, and there would be a significant
  advantage to have the constraints be:
  (r < 1)
  has_classical_limit (λ n:ℕ, (abs ∘ f (nat.succ n)) * (abs (f n)⁻¹) r →
  which is basically what I am using anyway. Specifically, this resolves the limit
  for x^n/n!, i.e. the terms in the exponential series.
-/


lemma has_classical_limit_ratio_lt_one2 {f:ℕ → ℝ} {r:ℝ}:
  has_classical_limit (λ n:ℕ, (f (nat.succ n)) * (f n)⁻¹) r →
  (r < 1) →
  (0 ≤ r) →
  (∀ n, 0 < f n) →
  has_classical_limit f 0 :=
begin
  intros A1 A2 A3 D1,
  let r' := (1+r)/2,
  begin
    have A4:r' = (1+r)/2 := rfl,
    have C4:r' = (r + 1)/2,
    {
      rw add_comm,
    },
    have C5:r < r',
    {
      rw C4,
      apply half_bound_lower,
      apply A2,
    },
    unfold has_classical_limit at A1,
    have A5 : 0 < (r' - r),
    {
      apply sub_pos_of_lt,
      apply C5,
    },
    have C1:0 < r',
    {
      apply lt_of_le_of_lt A3 C5,
    },
    have C2:r' ≠ 0,
    {
      intro C2A,
      rw C2A at C1,
      apply lt_irrefl 0 C1,
    },
    have C3:r' < 1,
    {
      rw C4,
      apply half_bound_upper,
      apply A2,
    },
    have A6 := A1 (r' - r) A5,
    cases A6 with n A7,
    let ns := (nat.succ n);
    let k := (abs (f ns))*(((r')⁻¹)^(ns));
    let g:ℕ → ℝ := λ n:ℕ, k * ((r')^n),
    begin
      have B1:ns = (nat.succ n) := rfl,
      have B2:k = (abs (f ns))*(((r')⁻¹)^(ns)) := rfl,
      have B3:g = λ n:ℕ, k * ((r')^n) := rfl,
      have B4:has_classical_limit g 0,
      {
        have B4A:k * 0 = 0 := mul_zero k,
        rw ← B4A,
        rw B3,
        apply has_classical_limit_mul_const,
        apply has_classical_limit_exp,
        apply le_of_lt,
        apply C1,
        apply C3,
      },
      apply has_classical_limit_bound g B4,
      have B5:∀ n',ns ≤ n' → (abs ∘ f) n' ≤ k * (r')^n',
      {
        apply has_classical_limit_ratio_lt_oneh2,
        {
          rw B2,
          apply mul_nonneg,
          {
            apply abs_nonneg,
          },
          {
            apply le_of_lt,
            apply pow_pos,
            apply inv_pos_of_pos,
            apply C1,
          }
        },
        {
          apply C3,
        },
        {
          intro n',
          simp,
          apply abs_pos_of_pos,
          apply D1,
        },
        {
          rw B2,
          rw mul_assoc,
          rw inv_pow_cancel2,
          rw mul_one,
          apply C2,
        },
        {
          intros n' B5A,
          have B5B:abs (f (nat.succ n') * (f n')⁻¹ - r) <  (r' - r),
          {
            apply A7,
            rw B1 at B5A,
            apply B5A,
          },
          have B5C:f (nat.succ n') * (f n')⁻¹ < r',
          {
            have B5CB:f (nat.succ n') * (f n')⁻¹ - r < (r' - r),
            {
              apply lt_of_le_of_lt,
              apply le_abs_self,
              apply B5B,
            },
            apply lt_of_sub_lt_sub B5CB,
          },
          have B5D:0 < (f (nat.succ n') * (f n')⁻¹),
          {
            apply mul_pos,
            apply D1,
            apply inv_pos_of_pos,
            apply D1,
          },

          have B5E:abs (f (nat.succ n') * (f n')⁻¹) = (abs (f (nat.succ n'))) * (abs (f n'))⁻¹,
          {
            rw ← abs_inv,
            rw abs_mul,
          },
          simp,
          rw ← B5E,
          rw abs_of_pos,
          apply le_of_lt,
          apply B5C,
          apply B5D,
        }
      },
      apply exists.intro ns,
      intros n' B6,
      apply B5,
      apply le_of_lt,
      apply B6
    end
  end
end


/-

lemma has_classical_limit_eq_after {f g:ℕ → ℝ} {x:ℝ} {n:ℕ}:
  has_classical_limit f x →
  (∀ n':ℕ, n < n' → (f n' = g n')) →
  has_classical_limit g x :=
begin


-/

lemma has_classical_limit_ratio_lt_one3 {f:ℕ → ℝ} {r:ℝ} {k:ℕ}:
  has_classical_limit (λ n:ℕ, (f (nat.succ n)) * (f n)⁻¹) r →
  (r < 1) →
  (0 ≤ r) →
  (∀ n, k < n → 0 < f n) →
  has_classical_limit f 0 :=
begin
  intros A1 A2 A3 A4,
  let g:ℕ → ℝ := λ n, if (k < n) then f n else 1,
  begin
    have A6:g = λ n, if (k < n) then f n else 1 := rfl,

    have A5:has_classical_limit (λ n:ℕ, (g (nat.succ n)) * (g n)⁻¹) r,
    {
       have A5A:∀ n:ℕ, k < n →
           (λ n:ℕ,(f (nat.succ n)) * (f n)⁻¹) n=
           (λ n:ℕ, (g (nat.succ n)) * (g n)⁻¹) n,
      {
        intros n A5A1,
        rw A6,
        simp,
        rw if_pos,
        rw if_pos,
        apply A5A1,
        apply lt_trans,
        apply A5A1,
        apply lt_succ,
      },
      apply has_classical_limit_eq_after A1 A5A,
    },
    have A7:has_classical_limit g 0,
    {
      apply has_classical_limit_ratio_lt_one2,
      apply A5,
      apply A2,
      apply A3,
      {
        intro n,
        rw A6,
        simp,
        have A7A:k < n ∨ ¬ (k < n) := lt_or_not_lt,
        cases A7A,
        {
          rw if_pos,
          apply A4,
          apply A7A,
          apply A7A,
        },
        {
          rw if_neg,
          apply zero_lt_one,
          apply A7A,
        }
      }
    },
    have A8:∀ n:ℕ, k < n → g n = f n,
    {
      intros n A8A,
      rw A6,
      simp,
      rw if_pos,
      apply A8A,
    },
    apply has_classical_limit_eq_after A7 A8,
  end
end



lemma pow_cancel_ne_zero {r:ℝ} {n:ℕ}:((r≠ 0) → (r^(nat.succ n)) * (r^n)⁻¹ = r) :=
begin
  intro A0,
  induction n,
  {
    simp,
  },
  {
    rw pow_succ,
    have A1:(r^(nat.succ n_n))⁻¹=r⁻¹ * (r^(n_n))⁻¹,
    {
      rw pow_succ,
      rw mul_inv',
    },
    rw A1,
    rw mul_comm r,
    rw mul_assoc,
    rw ← mul_assoc r (r⁻¹),
    rw mul_inv_cancel,
    rw one_mul,
    rw n_ih,
    apply A0,
  }
end


lemma has_classical_limit_ratio_one_exp {f:ℕ → ℝ} {r:ℝ} {k:ℕ}:
  (∀ n:ℕ, k < n → 0 < f n) →
  has_classical_limit (λ n:ℕ, (f (nat.succ n)) * (f n)⁻¹) 1 →
  (r < 1) →
  (0 < r) →
  has_classical_limit (λ n:ℕ, f n * r^n) 0
  :=
begin
  intros A1 A2 A3 A4,
  let g :=  (λ n:ℕ, f n * r^n),
  begin
    have A5:g = (λ n:ℕ, f n * r^n) := rfl,
    have A6:has_classical_limit (λ n:ℕ, (g (nat.succ n)) * (g n)⁻¹) r,
    {
      have A6A:1 * r = r := one_mul r,
      have A6B:(λ n:ℕ, (g (nat.succ n)) * (g n)⁻¹) =
               (λ (n:ℕ), (f (nat.succ n)) * (f n)⁻¹ * r),
      {
        ext n,
        rw A5,
        simp,
        rw mul_comm (f n) (r^n),
        rw @mul_inv' _ _ (r^n) (f n),
        rw mul_assoc,
        rw ← mul_assoc (r^(nat.succ n)) (r^n)⁻¹  (f n)⁻¹,
        rw pow_cancel_ne_zero,
        {
          rw mul_comm r,
          rw mul_assoc,
        },
        {
          intro A7,
          rw A7 at A4,
          apply lt_irrefl (0:ℝ),
          apply A4,
        }
      },
      rw ← A6A,
      rw A6B,
      apply has_classical_limit_mul,
      {
        apply A2,
      },
      {
        apply has_classical_limit_const,
      }
    },
    apply has_classical_limit_ratio_lt_one3,
    {
      apply A6,
    },
    {
      apply A3,
    },
    {
      apply le_of_lt,
      apply A4,
    },
    {
      intros n B1,
      apply mul_pos,
      {
        apply A1,
        apply B1,
      },
      {
        apply pow_pos,
        apply A4,
      }
    }
  end
end

lemma has_classical_limit_poly_ratio {k:ℕ}:
  has_classical_limit (λ (n : ℕ), ((nat.succ n):ℝ) ^ k * ((n:ℝ) ^ k)⁻¹) 1 :=
begin
  induction k,
  {
    simp,
    apply has_classical_limit_const,
  },
  {
    have A1: (λ (n : ℕ), ((nat.succ n):ℝ) ^ nat.succ k_n * ((n:ℝ) ^ nat.succ k_n)⁻¹) =
       (λ (n : ℕ), ((nat.succ n):ℝ ) * ((n:ℝ))⁻¹) *
       (λ (n : ℕ), ((nat.succ n):ℝ) ^ k_n * ((n:ℝ) ^ k_n)⁻¹),
    {
      ext n,
      simp,
      rw pow_succ,
      rw pow_succ,
      rw mul_inv',
      --rw mul_comm (↑n ^ k_n)⁻¹ (↑n)⁻¹,
      rw ← mul_assoc,
      rw mul_assoc ((n:ℝ) + 1) (((n:ℝ) + 1) ^ k_n)  ((n:ℝ)⁻¹),
      rw mul_comm (((n:ℝ) + 1) ^ k_n)  ((n:ℝ)⁻¹),
      rw ← mul_assoc ((n:ℝ) + 1)   ((n:ℝ)⁻¹) (((n:ℝ) + 1) ^ k_n),
      rw mul_assoc,
    },
    have A2:(1:ℝ) = (1:ℝ) * (1:ℝ),
    {
      rw mul_one,
    },
    rw A2,
    rw A1,
    apply has_classical_limit_mul,
    {
       apply has_classical_limit_ratio_one,
    },
    {
      apply k_ih,
    }
  }
end

lemma has_classical_limit_poly_exp (x:ℝ) (k:ℕ):
  (x < 1) →
  (0 < x) →
  has_classical_limit (λ n, n^k * x^n) 0 :=
begin
  intros A1 A2,
  apply has_classical_limit_ratio_one_exp,
  {
    intros n A3,
    apply pow_pos,
    simp,
    apply A3,
  },
  {
    apply has_classical_limit_poly_ratio,
  },
  {
    apply A1,
  },
  {
    apply A2,
  }
end


lemma has_classical_limit_zero_exp {f:ℕ → ℝ}:has_classical_limit (λ n:ℕ, (0:ℝ)^n * (f n)) 0 :=
begin
  unfold has_classical_limit,
  intros ε A1,
  apply exists.intro 0,
  intros n' A2,
  rw zero_pow A2,
  simp,
  exact A1,
end


lemma has_classical_limit_offset {f:ℕ → ℝ} {x:ℝ} {k:ℕ}:
  has_classical_limit f x ↔ has_classical_limit (f ∘ (λ n,k+n)) x :=
begin
  unfold has_classical_limit,
  split;intros A1 ε A2;have A3 := A1 ε A2;cases A3 with n A4,
  {
    apply exists.intro n,
    intros n' A5,
    have A6:n < k + n',
    {
      apply lt_of_lt_of_le,
      apply A5,
      simp,
    },
    have A7 := A4 (k + n') A6,
    simp,
    apply A7,
  },
  {
    apply exists.intro (n + k),
    intros n' A5,
    have A6:n < n' - k,
    {
      apply nat_lt_sub_of_add_lt,
      apply A5,
    },
    have A7 := A4 (n' - k) A6,
    simp at A7,
    have A8:k + (n' - k) = n',
    {
      rw add_comm,
      apply nat_minus_cancel_of_le,
      apply le_of_lt,
      apply nat_lt_of_add_lt,
      apply A5,
    },
    rw A8 at A7,
    apply A7,
  }
end

lemma has_classical_limit_ratio_power_fact {x:ℝ}:
   has_classical_limit
     (λ (n : ℕ), (x ^ (nat.succ n) * ((nat.fact (nat.succ n)):ℝ)⁻¹) *
     (x ^ n * ((nat.fact n):ℝ)⁻¹)⁻¹ ) 0 :=
begin
  have A1:x = 0 ∨ (x ≠ 0) := eq_or_ne,
  cases A1,
  {
     rw A1,
     have A2:(λ (n : ℕ), 0 ^ nat.succ n * ((nat.fact (nat.succ n)):ℝ)⁻¹ *
       (0 ^ n * ((nat.fact n):ℝ )⁻¹)⁻¹)=λ (n:ℕ), (0:ℝ),
     {
       ext,
       rw pow_succ,
       simp,
     },
     rw A2,
     apply has_classical_limit_const,
  },
  {
    have A2:(λ (n : ℕ), (x ^ (nat.succ n) * ((nat.fact (nat.succ n)):ℝ)⁻¹) *
      (x ^ n * ((nat.fact n):ℝ)⁻¹)⁻¹ ) =(λ (n : ℕ), (x  * (((nat.succ n)):ℝ)⁻¹)),
    {
      ext n,
      rw pow_succ,
      rw mul_inv',
      rw inv_inv',
      rw ← mul_assoc,
      simp,
      rw mul_inv',
      rw ← mul_assoc,
      rw mul_assoc ( x * x ^ n  * ((n:ℝ) + 1)⁻¹) (((nat.fact n):ℝ)⁻¹),
      rw mul_comm _ (x^n)⁻¹,
      rw mul_assoc,
      rw mul_assoc (x^n)⁻¹,
      rw @inv_mul_cancel ℝ _ ↑(n.fact),
      rw mul_one,
      rw mul_assoc,
      rw mul_comm (((n:ℝ) + 1)⁻¹) ((x^n)⁻¹),
      rw ← mul_assoc,
      rw mul_assoc x (x ^ n),
      rw mul_inv_cancel,
      rw mul_one,
      apply pow_ne_zero,
      apply A1,
      simp,
      apply nat_fact_nonzero,
    },
    rw A2,
    have A3:x * 0 = 0 := mul_zero x,
    rw ← A3,
    apply has_classical_limit_mul_const,
    have A4:(λ (n : ℕ), ((nat.succ n):ℝ)⁻¹)=(λ (n : ℕ), (↑(n))⁻¹) ∘ (λ n:ℕ, 1 + n),
    {
      ext n,
      simp,
      rw add_comm,
    },
    rw A4,
    rw ← has_classical_limit_offset,
    apply has_classical_limit_inv_zero,
  }
end


lemma has_classical_limit_supr_of_monotone_of_bdd_above {f:ℕ → ℝ}:
  (monotone f) → (bdd_above (set.range f)) → has_classical_limit f (⨆ n, f n) :=
begin
  intros A1 A2,
  unfold has_classical_limit,
  intros ε A3,
  --have A4:∃ (x:ℝ) (H:x∈ (set.range f)), (⨆ n, f n) - ε < x,
  have A4:∃ (n:ℕ), (⨆ n, f n) - ε < f n,
  {
     apply exists_lt_of_lt_csupr,
     simp,
     apply sub_lt_of_sub_lt,
     rw sub_self,
     apply A3,
  },
  cases A4 with n A5,
  apply exists.intro n,
  intros n' A6,
  rw abs_lt_iff_in_Ioo,
  split,
  {
    apply lt_of_lt_of_le A5,
    apply A1,
    apply le_of_lt A6,
  },
  {
    have A7:f n' ≤ (⨆ n, f n),
    {
      apply le_csupr,
      apply A2,
    },
    apply lt_of_le_of_lt A7,
    simp,
    apply A3,
  }
end

lemma exists_classical_limit_of_monotone_of_bdd_above {f:ℕ → ℝ}:
  (monotone f) → (bdd_above (set.range f)) → exists_classical_limit f :=
begin
  intros A1 A2,
  have A3:=has_classical_limit_supr_of_monotone_of_bdd_above A1 A2,
  apply exists_classical_limit_intro A3,
end




/-
  This is useful for any type which doesn't have a bottom.
-/
def multiset.max {α:Type*} [decidable_linear_order α]: multiset α → option α :=
  (multiset.fold  (option.lift_or_get max) none) ∘ (multiset.map some)

lemma multiset.max_insert {α:Type*} [decidable_linear_order α] {a:α} {s:multiset α}:
  (insert a s).max = option.lift_or_get max (some a) s.max :=
begin
  unfold multiset.max,
  simp,
end

lemma multiset.max_insert2 {α:Type*} [decidable_linear_order α] {a:α} {s:multiset α}:
  (a::s).max = option.lift_or_get max (some a) s.max :=
begin
  unfold multiset.max,
  simp,
end

lemma option_max {α:Type*} [decidable_linear_order α] {a:α} {b:option α} {c:α}:
  option.lift_or_get max (some a) b = some c
  → a ≤ c :=
begin
  intro A1,
  cases b,
  {
    unfold option.lift_or_get at A1,
    simp at A1,
    rw A1,
  },
  {
    unfold option.lift_or_get at A1,
    simp at A1,
    subst c,
    apply le_max_left,
  }
end


lemma option_max_some {α:Type*} [decidable_linear_order α] {a:α} {b:α} {c:α}:
  option.lift_or_get max (some a) (some b) = some c
  ↔ max a b = c :=
begin
  unfold option.lift_or_get,
  simp,
end

lemma option_max_some_nonempty {α:Type*} [decidable_linear_order α] {a:α} {b:option α}:
  ∃ c:α, c∈ option.lift_or_get max (some a) b :=
begin
  cases b;unfold option.lift_or_get;simp,
end

lemma multiset.max_some_nonempty {α:Type*} [decidable_linear_order α] {a:α} {s:multiset α}:
  (a∈ s) → (∃ b, s.max = some b) :=
begin
  apply multiset.induction_on s,
  {
    simp,
  },
  {
    intros c t A1 A2,
    rw multiset.max_insert2,
    apply option_max_some_nonempty,
  }
end


-- See:




theorem le_max_of_mem {S : multiset ℝ} {a: ℝ}:
  a∈ S → (∃ b ∈ S.max,  a ≤ b) :=
begin
  apply multiset.induction_on S,
  {
    intros A1,
    simp at A1,
    exfalso,
    apply A1,
  },
  {
    intros c T A2 A3,
    have A4:=multiset.max_some_nonempty A3,
    cases A4 with b A5,
    simp at A3,
    apply exists.intro b,
    simp,
    split,
    {
      apply A5,
    },
    {
      cases A3,
      {
        subst c,
        unfold multiset.max at A5,
        simp at A5,
        apply option_max A5,
      },
      {
        have A6 := A2 A3,
        cases A6 with d A7,
        cases A7 with A8 A9,
        rw multiset.max_insert2 at A5,
        simp at A8,
        rw A8 at A5,
        rw option_max_some at A5,
        have A10 := le_max_right c d,
        rw A5 at A10,
        apply le_trans,
        apply A9,
        apply A10,
      }
    }
  }
end






/-
  There is probably the equivalent of this somewhere in the library.
-/
lemma bdd_above_of_exists_classical_limit {f:ℕ → ℝ}:
  exists_classical_limit f → (bdd_above (set.range f)) :=
begin
  intros A1,
  /-
    First, we choose an arbitrary boundary around the limit, say (x - 1) (x + 1).
    Then, we use the definition of limit to prove that past some N, the value of
    f is less than (x + 1). Then, below N, we take the max.
  -/
  unfold exists_classical_limit at A1,
  cases A1 with x A2,
  unfold has_classical_limit at A2,
  have A3:(0:ℝ)<(1:ℝ) := zero_lt_one,
  have A4 := A2 1 A3,
  cases A4 with n A5,
  unfold bdd_above,
  have A6:∃ x1:ℝ, multiset.max (multiset.map f (multiset.range (nat.succ n))) = some x1,
  {
    have A6A:(f 0) ∈ (multiset.map f (multiset.range (nat.succ n))),
    {
      simp,
      cases n,
      {
        left,refl,
      },
      {
        right,
        apply exists.intro 0,
        split,
        simp,
      }
    },
    apply multiset.max_some_nonempty,
    apply A6A,
  },
  cases A6 with x1 A7,
  let x2 := max x1 (x + 1),
  begin
    have A8 : x2  = max x1 (x + 1) := rfl,
    apply exists.intro x2,
    unfold upper_bounds,
    simp,
    intros n',
    have A10: (n < n')  ∨ n' ≤  n:= lt_or_le n n',
    cases A10,
    {
      right,
      have A11 := A5 n' A10,
      rw abs_lt_iff_in_Ioo at A11,
      simp at A11,
      apply le_of_lt A11.right,
    },
    {
      left,
      have A11:f n' ∈ (multiset.map f (multiset.range (nat.succ n))),
      {
        rw le_iff_lt_or_eq at A10,
        simp,
        cases A10,
        {
          right,
          apply exists.intro n',
          split,
          apply A10,
          refl,
        },
        {
          left,
          rw A10,
        }
      },
      have A12:=le_max_of_mem A11,
      cases A12 with b A13,
      cases A13 with A14 A15,
      rw A7 at A14,
      simp at A14,
      rw A14,
      apply A15,
    }
  end
end


lemma has_classical_limit_supr_of_monotone_of_exists_classical_limit {f:ℕ → ℝ}:
  monotone f →
  exists_classical_limit f →
  has_classical_limit f (⨆ n, f n)  :=
begin
  intros A1 A2,
  have A3:(bdd_above (set.range f)) := bdd_above_of_exists_classical_limit A2,
  apply has_classical_limit_supr_of_monotone_of_bdd_above A1 A3,
end

lemma has_classical_limit_le {f g:ℕ → ℝ} {x y:ℝ}:
  has_classical_limit f x →
  has_classical_limit g y →
  f ≤ g → x ≤ y :=
begin
  intros A1 A2 A3,
  apply le_of_not_lt,
  intro A4,
  let ε := (x - y)/2,
  begin
    have A5:ε = (x - y)/2 := rfl,
    have A6:0 < ε,
    {
      apply half_pos,
      apply sub_pos_of_lt A4,
    },
    have A7 := A1 ε A6,
    cases A7 with nf A8,
    have A9 := A2 ε A6,
    cases A9 with ng A10,
    let n' := nat.succ (max nf ng),
    begin
      have A11:n' = nat.succ (max nf ng) := rfl,
      have A12:nf < n',
      {
        rw A11,
        apply nat.lt_succ_of_le,
        apply le_max_left,
      },
      have A13:ng < n',
      {
        rw A11,
        apply nat.lt_succ_of_le,
        apply le_max_right,
      },
      have A14 := A8 n' A12,
      have A15 := A10 n' A13,
      have A16:x - ε < f n',
      {
        rw abs_lt2 at A14,
        apply A14.left,
      },
      have A17:g n' < y + ε,
      {
        rw abs_lt2 at A15,
        apply A15.right,
      },
      have A18:x - ε = y + ε,
      {
        apply half_equal A5,
      },
      have A19:g n' < f n',
      {
        apply lt_trans,
        apply A17,
        rw ← A18,
        apply A16,
      },
      have A20:f n' ≤ g n',
      {
        apply A3,
      },
      apply not_lt_of_le A20,
      apply A19,
    end
  end
end
