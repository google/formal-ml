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
import formal_ml.classical_deriv
import formal_ml.classical_limit


lemma tsum_replace {α β:Type*} [add_comm_monoid α] [topological_space α] [t2_space α] {g:β  → α} {x:α}:
  (has_sum g x) →
  tsum g = x :=
begin
  intro A1,
  have A2:summable g := exists.intro x A1,
  have A3:=has_sum_tsum A2,
  apply has_sum.unique A3 A1,
end

---Results about sums--------------------------------------------------------------------------


/- Analytic functions are based upon conditional (as opposed to absolute) sums. -/



def has_conditional_sum (f:ℕ → ℝ) (x:ℝ):Prop :=
  has_classical_limit (λ n:ℕ, (finset.range n).sum  f) x

lemma has_conditional_sum_def (f:ℕ → ℝ) (x:ℝ):
  has_conditional_sum f x = has_classical_limit (λ n:ℕ, (finset.range n).sum  f) x := rfl



def conditionally_summable (f:ℕ → ℝ):Prop := ∃ x, has_conditional_sum f x

--This is equivalent to summable.
def absolutely_summable (f:ℕ → ℝ):Prop := conditionally_summable (λ y, abs (f y))

def has_absolute_sum (f:ℕ → ℝ) (x:ℝ):Prop :=
  absolutely_summable f  ∧ has_conditional_sum f x



section functional_def

local attribute [instance] classical.prop_decidable

noncomputable def conditional_sum (f:ℕ → ℝ):ℝ :=
    if h:conditionally_summable f then classical.some h else 0

lemma conditional_sum_def (f:ℕ → ℝ):
  conditional_sum f = classical_limit (λ n:ℕ, (finset.range n).sum  f) := rfl

noncomputable def absolute_sum (f:ℕ → ℝ):ℝ :=
    if absolutely_summable f then (conditional_sum f) else 0

end functional_def

notation `∑ₚ ` binders `, ` r:(scoped f, conditional_sum f) := r



lemma has_conditional_sum_unique {f:ℕ → ℝ} {x y:ℝ}:
  has_conditional_sum f x →
  has_conditional_sum f y →
  (x = y) :=
begin
  unfold has_conditional_sum,
  apply has_classical_limit_unique,
end



lemma conditionally_summable_elim {f:ℕ → ℝ}:
  conditionally_summable f → (∃ x:ℝ, has_conditional_sum f x) :=
begin
  unfold conditionally_summable,
  intro A1,
  apply A1,
end


lemma conditionally_summable_of_has_conditional_sum {f:ℕ → ℝ} {x:ℝ}:
  has_conditional_sum f x →
  conditionally_summable f :=
begin
  intro A1,
  unfold conditionally_summable,
  apply exists.intro x A1,
end

lemma has_conditional_sum_conditional_sum_of_conditionally_summable {f:ℕ → ℝ}:
  conditionally_summable f →
  has_conditional_sum f (conditional_sum f) :=
begin
  intro A1,
  simp [A1, conditional_sum],
  apply classical.some_spec A1,
end

lemma conditional_sum_replace {f:ℕ → ℝ} {x:ℝ}:
  has_conditional_sum f x →
  conditional_sum f = x :=
begin
  intro A1,
  have A2:conditionally_summable f := conditionally_summable_of_has_conditional_sum A1,
  have A3:has_conditional_sum f (conditional_sum f) :=
      has_conditional_sum_conditional_sum_of_conditionally_summable A2,
  apply has_conditional_sum_unique A3 A1,
end



lemma absolutely_summable_of_nonneg_of_conditionally_summable {f:ℕ → ℝ}:
  0 ≤ f →
  conditionally_summable f →
  absolutely_summable f :=
begin
  intros A1 A2,
  unfold absolutely_summable,
  have A3:(λ (y : ℕ), abs (f y)) = f,
  {
     ext y,
     rw abs_of_nonneg,
     apply A1,
  },
  rw A3,
  apply A2,
end



lemma has_conditional_sum_neg {f:ℕ → ℝ} {x:ℝ}:
  has_conditional_sum f x →
  has_conditional_sum (-f) (-x)  :=
begin
  unfold has_conditional_sum,
  intro A1,
  have A2:(λ (n:ℕ),finset.sum (finset.range n) (-f)) =
      -(λ (n:ℕ),finset.sum (finset.range n) (f)),
  {
    ext n,
    simp,
  },
  rw A2,
  apply has_classical_limit_neg,
  apply A1,
end

lemma conditionally_summable_neg {f:ℕ → ℝ}:
  conditionally_summable f →
  conditionally_summable (-f) :=
begin
  unfold conditionally_summable,
  intro A1,
  cases A1 with x A2,
  apply exists.intro (-x),
  apply has_conditional_sum_neg,
  apply A2,
end

lemma conditionally_summable_neg2 {f:ℕ → ℝ}:
  conditionally_summable (-f) →
  conditionally_summable (f) :=
begin
  intro A1,
  have A2:-(-f)=f := neg_neg_func,
  rw ← A2,
  apply conditionally_summable_neg A1,
end

lemma conditional_sum_neg_of_conditionally_summable {f g:ℕ → ℝ}:
  conditionally_summable f →
  conditional_sum (-f) = -(conditional_sum f) :=
begin
  intro A1,
  cases (conditionally_summable_elim A1) with x A2,
  have A3:=has_conditional_sum_neg A2,
  rw conditional_sum_replace A2,
  rw conditional_sum_replace A3,
end

lemma has_conditional_sum_add {f g:ℕ → ℝ} {x y:ℝ}:
  has_conditional_sum f x →
  has_conditional_sum g y →
  has_conditional_sum (f + g) (x + y) :=
begin
  unfold has_conditional_sum,
  intros A1 A2,

  have A3: (λ (n : ℕ), finset.sum (finset.range n) (f + g)) =
    (λ (n : ℕ), finset.sum (finset.range n) (f)) +
    (λ (n : ℕ), finset.sum (finset.range n) (g)),
  {
    ext n,
    simp,
    rw finset.sum_add_distrib,
  },
  rw A3,
  apply has_classical_limit_sum;assumption,
end


lemma conditionally_summable_add {f g:ℕ → ℝ}:
  conditionally_summable f →
  conditionally_summable g →
  conditionally_summable (f + g) :=
begin
  unfold conditionally_summable,
  intros A1 A2,
  cases A1 with x A3,
  cases A2 with y A4,
  apply exists.intro (x + y),
  apply has_conditional_sum_add A3 A4,
end



lemma conditional_sum_add_of_conditionally_summable {f g:ℕ → ℝ}:
  conditionally_summable f →
  conditionally_summable g →
  conditional_sum (f + g) =  conditional_sum f + conditional_sum g :=
begin
  intros A1 A2,
  cases (conditionally_summable_elim A1) with x A3,
  cases (conditionally_summable_elim A2) with y A4,
  have A5:conditionally_summable (f + g) := conditionally_summable_add A1 A2,
  have A6:=has_conditional_sum_add A3 A4,
  rw conditional_sum_replace A6,
  rw conditional_sum_replace A3,
  rw conditional_sum_replace A4,
end

lemma has_conditional_sum_sub {f g:ℕ → ℝ} {x y:ℝ}:
  has_conditional_sum f x →
  has_conditional_sum g y →
  has_conditional_sum (f - g) (x - y) :=
begin
  unfold has_conditional_sum,
  intros A1 A2,
  have A3:(λ (n : ℕ), finset.sum (finset.range n) (f - g))=
    (λ (n : ℕ), ((finset.range n).sum f) - ((finset.range n).sum g)),
  {
    ext n,
    have A3A:(λ m:ℕ, f m - g m) = f - g,
    {
      refl,
    },
    rw ← A3A,
    rw @finset.sum_sub_distrib ℕ ℝ (finset.range n) f g,
  },
  rw A3,
  apply has_classical_limit_sub A1 A2,
end


lemma conditionally_summable_sub {f g:ℕ → ℝ}:
  conditionally_summable f →
  conditionally_summable g →
  conditionally_summable (f - g) :=
begin
  intros A1 A2,
  cases (conditionally_summable_elim A1) with x A3,
  cases (conditionally_summable_elim A2) with y A4,
  apply exists.intro (x - y),
  apply has_conditional_sum_sub A3 A4,
end



lemma conditional_sum_sub_of_conditionally_summable {f g:ℕ → ℝ}:
  conditionally_summable f →
  conditionally_summable g →
  conditional_sum (f - g) =  conditional_sum f - conditional_sum g :=
begin
  intros A1 A2,
  cases (conditionally_summable_elim A1) with x A3,
  cases (conditionally_summable_elim A2) with y A4,
  have A5:conditionally_summable (f + g) := conditionally_summable_add A1 A2,
  have A6:=has_conditional_sum_sub A3 A4,
  rw conditional_sum_replace A6,
  rw conditional_sum_replace A3,
  rw conditional_sum_replace A4,
end


lemma has_conditional_sum_mul_const_of_has_conditional_sum {f:ℕ → ℝ} {x k:ℝ}:
  has_conditional_sum f x →
  has_conditional_sum (λ n, k * (f n)) (k * x) :=
begin
  rw has_conditional_sum_def,
  rw has_conditional_sum_def,
  intro A1,
  have A2:(λ n, finset.sum (finset.range n) (λ (m:ℕ), k * f m)) =
          (λ n, k * finset.sum (finset.range n) (λ (m:ℕ), f m)),
  {
    ext n,
    rw finset_sum_mul_const,
  },
  rw A2,
  apply has_classical_limit_mul_const A1,
end

lemma conditional_summable_mul_const_of_conditionally_summable {f:ℕ → ℝ} {k:ℝ}:
  conditionally_summable f →
  conditionally_summable (λ n, k * (f n)) :=
begin
  intro A1,
  cases (conditionally_summable_elim A1) with x A2,
  apply exists.intro (k * x),
  apply has_conditional_sum_mul_const_of_has_conditional_sum A2,
end

lemma conditional_sum_mul_const_of_conditionally_summable {f:ℕ → ℝ} {k:ℝ}:
  conditionally_summable f →
  conditional_sum (λ n, k * (f n)) = k * conditional_sum f :=
begin
  intro A1,
  cases (conditionally_summable_elim A1) with x A2,
  have A3:=@has_conditional_sum_mul_const_of_has_conditional_sum f x k A2,
  rw conditional_sum_replace A3,
  rw conditional_sum_replace A2,
end

lemma has_conditional_sum_zero:
  has_conditional_sum 0 0 :=
begin
  rw has_conditional_sum_def,
  simp,
  apply has_classical_limit_const,
end


lemma absolutely_summable_neg  (f:ℕ → ℝ):
  absolutely_summable f →
  absolutely_summable (-f) :=
begin
  unfold absolutely_summable,
  intro A1,
  have A2:(λ (y : ℕ), abs (f y)) = (λ (y : ℕ), abs ((-f) y)),
  {
    ext n,
    simp,
  },
  rw ← A2,
  apply A1,
end

lemma absolutely_summable_of_nonpos_of_conditionally_summable (f:ℕ → ℝ):
  f ≤ 0 →
  conditionally_summable f →
  absolutely_summable f :=
begin
  intros A1 A2,
  have A3:conditionally_summable (-f),
  {
    apply conditionally_summable_neg,
    apply A2,
  },
  unfold absolutely_summable,
  have A4:(λ (y : ℕ), abs (f y)) = -f,
  {
    ext,
    apply abs_of_nonpos,
    apply A1,
  },
  rw A4,
  apply A3,
end


lemma monotone_partial_sum_of_nonneg {f:ℕ → ℝ}:
  0≤ f → monotone (λ n:ℕ, (finset.range n).sum  f) :=
begin
  intro A1,
  have A2:(λ n:ℕ, (finset.range n).sum  f) = (λ S:finset ℕ, S.sum  f) ∘ finset.range := rfl,
  rw A2,
  apply monotone.comp,
  apply sum_monotone_of_nonneg A1,
  apply finset.range_mono,
end

lemma upper_bound_finset_range {S:finset ℕ}:
  S ⊆ finset.range (nat.succ (finset.sup S id)) :=
begin
  rw finset.subset_iff,
  intros x A1,
  simp,
  apply nat.lt_succ_of_le,
  have A2:id x = x := rfl,
  rw ← A2,
  apply finset.le_sup A1,
end


lemma bdd_above_iff_bdd_above_of_nonneg {f:ℕ → ℝ}:
  0≤ f → (bdd_above (set.range (λ n:ℕ, (finset.range n).sum  f)) ↔
  bdd_above (set.range (λ S:finset ℕ, S.sum  f))) :=
begin
  intro A1,
  unfold bdd_above upper_bounds,
  split;
  intro A2;
  cases A2 with x A3;
  apply exists.intro x;
  simp;
  simp at A3;
  intros z,
  {
    intros S A4,
    subst z,
    let n := nat.succ ((finset.sup S) id),
    let T := finset.range n,
    begin
      have A5:finset.sum T f = finset.sum T f := rfl,
      have A6 := A3 n A5,
      have A7: S ≤ T := upper_bound_finset_range,
      have A8:= sum_monotone_of_nonneg A1 A7,
      apply le_trans,
      apply A8,
      apply A6,
    end
  },
  {
    intros n A4,
    subst z,
    have A5:finset.sum (finset.range n) f = finset.sum (finset.range n) f := rfl,
    apply A3 (finset.range n) A5,
  }
end



lemma cSup_le_cSup2 {A B:set ℝ}:(A.nonempty) → (bdd_above B) → (∀ a∈ A, ∃ b∈ B, a ≤ b) →
  Sup A ≤ Sup B :=
begin
  intros A1 A2 A3,
  apply cSup_le A1,
  intros a A4,
  have A5:=A3 a A4,
  cases A5 with b A6,
  cases A6 with A7 A8,
  apply le_trans A8,
  apply le_cSup A2 A7,
end


lemma supr_eq_supr_of_nonneg_of_bdd_above {f:ℕ → ℝ}:
  0≤ f → (bdd_above (set.range (λ n:ℕ, (finset.range n).sum  f))) →
  (⨆ n, (finset.range n).sum f) = (⨆ (S:finset ℕ), S.sum f) :=
begin
  intros A1 A2,
  have A3:bdd_above (set.range (λ S:finset ℕ, S.sum f)) := (bdd_above_iff_bdd_above_of_nonneg A1).mp A2,
  unfold supr,
  apply le_antisymm,
  {
    apply cSup_le_cSup2 _ A3,
    {
      intros a A4,
      simp at A4,
      cases A4 with n A5,
      subst a,
      apply exists.intro (finset.sum (finset.range n) f),
      simp,split,
      {
        apply exists.intro (finset.range n),
        refl,
      },
      {
        apply le_refl,
      }
    },
    {
      apply set_range_inhabited_domain,
    }
  },
  {
    apply cSup_le_cSup2 _ A2,
    {
      intros a A4,
      simp at A4,
      cases A4 with S A5,
      subst a,
      let n := nat.succ ((finset.sup S) id),
      let T := finset.range n,
      begin
        have A5:finset.sum T f = finset.sum T f := rfl,
        apply exists.intro (finset.sum T f),
        split,
        {
          simp,
          apply exists.intro n,
          refl,
        },
        {
          apply sum_monotone_of_nonneg A1,
          apply upper_bound_finset_range,
        }
      end
    },
    {
      apply set_range_inhabited_domain,
    }
  }
end


lemma supr_eq_supr_of_nonneg_of_bdd_above2 {f:ℕ → ℝ}:
  0≤ f → bdd_above (set.range (λ S:finset ℕ, S.sum f)) →
  (⨆ n, (finset.range n).sum f) = (⨆ (S:finset ℕ), S.sum f) :=
begin
  intros A1 A2,
  have A3:(bdd_above (set.range (λ n:ℕ, (finset.range n).sum  f))) := (bdd_above_iff_bdd_above_of_nonneg A1).mpr A2,
  apply supr_eq_supr_of_nonneg_of_bdd_above A1 A3,
end





lemma has_conditional_sum_iff_has_sum_of_nonneg {f:ℕ → ℝ} {x:ℝ}:
  0 ≤ f →
  (has_conditional_sum f x ↔ has_sum f x) :=
begin
  intro A1,
  have A1B := monotone_partial_sum_of_nonneg A1,
  split;intro A2,
  {
    unfold has_conditional_sum at A2,
    have A3:=exists_classical_limit_intro A2,
    have A4:=has_classical_limit_supr_of_monotone_of_exists_classical_limit A1B A3,
    have A5:=bdd_above_of_exists_classical_limit A3,
    have A6:bdd_above (set.range (λ S:finset ℕ, S.sum f)) := (bdd_above_iff_bdd_above_of_nonneg A1).mp A5,
    apply has_sum_of_bdd_above A1 A6,
    have A8:=has_classical_limit_supr_of_monotone_of_exists_classical_limit A1B A3,
    have A9:=supr_eq_supr_of_nonneg_of_bdd_above2 A1 A6,
    rw ← A9,
    apply has_classical_limit_unique A2 A8,
  },
  {
    unfold has_conditional_sum,
    have A3:=bdd_above_of_has_sum A1 A2,
    have A4:= (bdd_above_iff_bdd_above_of_nonneg A1).mpr A3,
    have A5:=supr_eq_supr_of_nonneg_of_bdd_above2 A1 A3,
    have A6:=supr_of_has_sum A1 A2,
    subst x,
    rw ← A5,
    apply has_classical_limit_supr_of_monotone_of_bdd_above A1B A4,
  }
end


lemma has_conditional_sum_iff_has_sum_of_nonpos {f:ℕ → ℝ} {x:ℝ}:
  f ≤ 0 →
  (has_conditional_sum f x ↔ has_sum f x) :=
begin
  intro A1,
  have A3:-(-f)=f:=neg_neg_func,
  have A3B:-(-x)=x,
  {
    simp,
  },
  have A1B:0 ≤ -f := nonpos_iff_neg_nonneg_func.mp A1,
  split;intros A2,
  {
    rw ← A3,
    rw ← A3B,
    apply has_sum.neg,
    have A4:has_conditional_sum (-f) (-x),
    {
      apply has_conditional_sum_neg A2,
    },
    apply (has_conditional_sum_iff_has_sum_of_nonneg A1B).mp A4,
  },
  {
    rw ← A3,
    rw ← A3B,
    have A4:has_sum (-f) (-x),
    {
      apply has_sum.neg A2,
    },
    have A5:has_conditional_sum (-f) (-x),
    {
      apply (has_conditional_sum_iff_has_sum_of_nonneg A1B).mpr A4,
    },
    apply has_conditional_sum_neg A5,
  }
end

lemma conditionally_summable_iff_summable_of_nonneg {f:ℕ → ℝ}:
  0 ≤ f →
  (conditionally_summable f ↔ summable f) :=
begin
  intro A1,
  unfold conditionally_summable,
  unfold summable,

  split;intros A2;cases A2 with x A3;apply exists.intro x,
  {
    apply (has_conditional_sum_iff_has_sum_of_nonneg A1).mp A3,
  },
  {
    apply (has_conditional_sum_iff_has_sum_of_nonneg A1).mpr A3,
  }
end

lemma conditionally_summable_iff_summable_of_nonpos {f:ℕ → ℝ}:
  f ≤ 0 →
  (conditionally_summable f ↔ summable f) :=
begin
  intro A1,
  have A1B:0 ≤ -f := nonpos_iff_neg_nonneg_func.mp A1,
  split;intros A2,
  {
    have A3:-(-f)=f:=neg_neg_func,
    rw ← A3,
    apply summable.neg,
    have A4:conditionally_summable (-f),
    {
      apply conditionally_summable_neg A2,
    },
    apply (conditionally_summable_iff_summable_of_nonneg A1B).mp A4,
  },
  {
    have A3:-(-f)=f:=neg_neg_func,
    have A4:summable (-f),
    {
      apply summable.neg A2,
    },
    have A5:conditionally_summable (-f),
    {
      apply (conditionally_summable_iff_summable_of_nonneg A1B).mpr A4,
    },
    apply conditionally_summable_neg2 A5,
  }
end





lemma finset_range_diff {n:ℕ} {f:ℕ → ℝ}:
  finset.sum (finset.range (nat.succ n)) f - (finset.sum (finset.range n) f) = f n :=
begin
  rw finset.range_succ,
  simp,
end

lemma conditionally_summable_bound (f g:ℕ → ℝ):
  (0 ≤ f) →
  (f ≤ g) →
  conditionally_summable g →
  conditionally_summable f :=
begin
  intros A1 A2 A3,
  have A4:0≤ g,
  {
    apply le_func_trans A1 A2,
  },
  have A5:=(conditionally_summable_iff_summable_of_nonneg A4).mp A3,
  rw (conditionally_summable_iff_summable_of_nonneg A1),
  apply has_sum_of_le_of_le_of_has_sum A1 A2 A5,
end

lemma has_classical_limit_of_conditional_summable (f:ℕ → ℝ):
  conditionally_summable f → has_classical_limit f 0 :=
begin
  intro A1,
  unfold conditionally_summable at A1,
  unfold has_classical_limit,
  intros ε A2,
  cases A1 with x A3,
  unfold has_conditional_sum at A3,
  unfold has_classical_limit at A3,
  have A4:0 < (ε/2) := zero_lt_epsilon_half_of_zero_lt_epsilon A2,
  have A5:= A3 (ε/2) A4,
  cases A5 with n A6,
  apply exists.intro n,
  intros n' A7,
  --rw abs_lt_iff_in_Ioo,
  have A9:= A6 n' A7,
  have A10:n < nat.succ n',
  {
    apply lt_trans,
    apply A7,
    apply nat.lt_succ_self,
  },
  have A11:= A6 (nat.succ n') A10,
  have A12:abs (finset.sum (finset.range (nat.succ n')) f - finset.sum (finset.range n') f) ≤
  abs (finset.sum (finset.range (nat.succ n')) f - x) + abs (finset.sum (finset.range n') f - x),
  {
    rw @abs_antisymm (finset.sum (finset.range n') f) x,
    apply abs_triangle,
  },
  rw finset_range_diff at A12,
  simp,
  apply lt_of_le_of_lt A12,
  have A13:ε/2 + ε/2 = ε,
  {
    simp,
  },
  rw ← A13,
  apply lt_trans,
  apply add_lt_add_left A9,
  apply add_lt_add_right A11,
end



lemma has_conditional_sum_le {f g:ℕ → ℝ} {x y:ℝ}:
  has_conditional_sum f x →
  has_conditional_sum g y →
  f ≤ g → x ≤ y :=
begin
  intros A1 A2 A3,
  apply has_classical_limit_le,
  {
    rw has_conditional_sum_def at A1,
    apply A1,
  },
  {
    rw has_conditional_sum_def at A2,
    apply A2,
  },
  {
    rw le_func_def,
    intro n,
    apply finset_sum_le3 A3,
  },
end

lemma has_conditional_sum_nonneg {f:ℕ → ℝ} {x:ℝ}:
  has_conditional_sum f x →
  0 ≤ f → 0 ≤ x :=
begin
  intro A1,
  apply has_conditional_sum_le,
  apply has_conditional_sum_zero,
  apply A1,
end




lemma abs_nonneg_func {f:ℕ → ℝ}:0 ≤ abs ∘ f :=
begin
  rw le_func_def,
  intro n,
  apply abs_nonneg,
end


lemma absolutely_summable_def {f:ℕ → ℝ}:absolutely_summable f ↔ summable f :=
begin
  symmetry,
  apply iff.trans,
  apply summable_iff_abs_summable,
  unfold absolutely_summable,
  symmetry,
  apply conditionally_summable_iff_summable_of_nonneg,
  apply abs_nonneg_func,
end


lemma conditionally_summable_of_absolutely_summable {f:ℕ → ℝ}:
  absolutely_summable f → conditionally_summable f :=
begin
  intro A1,
  have A2:summable f,
  {
    apply absolutely_summable_def.mp A1,
  },
  have A3:(summable (pos_only ∘ f) ∧ summable (neg_only ∘ f)),
  {
    apply summable_iff_pos_only_summable_neg_only_summable.mp A2,
  },
  cases A3 with A4 A5,
  have A7:(conditionally_summable (pos_only ∘ f)),
  {
    apply (conditionally_summable_iff_summable_of_nonneg pos_only_nonneg).mpr A4,
  },
  have A9:(conditionally_summable (neg_only ∘ f)),
  {
    apply (conditionally_summable_iff_summable_of_nonpos neg_only_nonpos).mpr A5,
  },
  have A10:(conditionally_summable (pos_only ∘ f + neg_only ∘ f)),
  {
    apply conditionally_summable_add A7 A9,
  },
  rw pos_only_add_neg_only_eq at A10,
  apply A10,
end

lemma conditionally_summable_of_summable {f:ℕ → ℝ}:
  summable f →
  conditionally_summable f :=
begin
  intro A1,
  apply conditionally_summable_of_absolutely_summable,
  rw absolutely_summable_def,
  apply A1,
end

lemma summable_of_nonneg_of_conditionally_summable {f:ℕ → ℝ}:
  0 ≤ f →
  conditionally_summable f →
  summable f :=
begin
  intros A1 A2,
  rw ← absolutely_summable_def,
  apply absolutely_summable_of_nonneg_of_conditionally_summable A1 A2,
end



lemma has_absolute_sum_absolute_sum_of_absolutely_summable (f:ℕ → ℝ):
  absolutely_summable f →
  has_absolute_sum f (absolute_sum f) :=
begin
  intro A1,
  split,
  apply A1,
  unfold absolute_sum,
  rw if_pos,
  apply has_conditional_sum_conditional_sum_of_conditionally_summable,
  apply conditionally_summable_of_absolutely_summable A1,
  apply A1,
end


lemma conditional_sum_eq_absolute_sum_of_absolutely_summable (f:ℕ → ℝ):
  absolutely_summable f →
  absolute_sum f = conditional_sum f :=
begin
  intro A1,
  unfold absolute_sum,
  rw if_pos,
  apply A1,
end

lemma has_conditional_sum_of_has_absolute_sum (f:ℕ → ℝ) (x:ℝ):
  has_absolute_sum f x → has_conditional_sum f x :=
begin
  intro A1,
  unfold has_absolute_sum at A1,
  cases A1 with A2 A3,
  apply A3,
end



/-This is a crazy proof. Forward: You basically prove that pos_only ∘ f and neg_only ∘ f are
  summable, to prove that they are conditionally summable, such that we can separate
  conditionally summable into positive and negative parts, so we prove that the
  sum is the same (whew!).
has_conditional_sum_iff_has_sum_of_nonneg :
  ∀ {f : ℕ → ℝ} {x : ℝ}, 0 ≤ f → (has_conditional_sum f x ↔ has_sum f x)
conditionally_summable_iff_summable_of_nonneg :
  ∀ {f : ℕ → ℝ}, 0 ≤ f → (conditionally_summable f ↔ summable f)

  It is likely that the return trip will be similar.


  Note: it also looks like I can do better by showing x exists.
  -/



lemma has_absolute_sum_has_conditional_sum_has_sum_of_absolutely_summable {f:ℕ → ℝ}:
  absolutely_summable f →
  ∃ x, has_absolute_sum f x ∧ has_conditional_sum f x ∧ has_sum f x :=
begin
  intro A1,
  have A2:summable f := absolutely_summable_def.mp A1,
  have A3:summable (pos_only∘f) ∧ summable (neg_only∘f)
      := summable_iff_pos_only_summable_neg_only_summable.mp A2,
  cases A3 with A4 A5,
  -- We could also establish has_sum x_pos and has_sum x_neg, then translate.
  rw ← (conditionally_summable_iff_summable_of_nonneg pos_only_nonneg) at A4,
  rw ← (conditionally_summable_iff_summable_of_nonpos neg_only_nonpos) at A5,
  have A6:pos_only ∘ f + neg_only ∘ f = f := pos_only_add_neg_only_eq,
  cases A4 with x_pos A8,
  cases A5 with x_neg A9,
  apply exists.intro (x_pos + x_neg),
  have A10:has_conditional_sum f (x_pos + x_neg),
  {
    rw ← A6,
    apply has_conditional_sum_add A8 A9,
  },
  split,
  {  -- ⊢ has_absolute_sum f (x_pos + x_neg)
    split,
    {
      apply A1,
    },
    {
      apply A10,
    }
  },
  split,
  {  -- ⊢ has_conditional_sum f (x_pos + x_neg)
    apply A10,
  },
  {
    rw (has_conditional_sum_iff_has_sum_of_nonneg pos_only_nonneg) at A8,
    rw (has_conditional_sum_iff_has_sum_of_nonpos neg_only_nonpos) at A9,
    rw ← A6,
    apply has_sum.add A8 A9,
  }
end


lemma absolutely_summable_of_has_absolute_sum {f:ℕ → ℝ} {x:ℝ}:
  has_absolute_sum f x →
  absolutely_summable f :=
begin
  unfold has_absolute_sum,
  intro A1,
  apply A1.left,
end

lemma has_absolute_sum_unique {f:ℕ → ℝ} {x y:ℝ}:
  has_absolute_sum f x →
  has_absolute_sum f y →
  x = y :=
begin
  unfold has_absolute_sum,
  intros A1 A2,
  apply has_conditional_sum_unique,
  {
    apply A1.right,
  },
  {
    apply A2.right,
  },
end



lemma absolute_sum_replace {f:ℕ → ℝ} {x:ℝ}:
  has_absolute_sum f x →
  absolute_sum f = x :=
begin
  intro A1,
  have A2:absolutely_summable f := absolutely_summable_of_has_absolute_sum A1,
  have A3:=has_absolute_sum_absolute_sum_of_absolutely_summable f A2,
  apply has_absolute_sum_unique A3 A1,
end


lemma has_absolute_sum_has_conditional_sum_has_sum_of_summable {f:ℕ → ℝ}:
  summable f →
  ∃ x, has_absolute_sum f x ∧ has_conditional_sum f x ∧ has_sum f x :=
begin
  intro A1,
  have A2:absolutely_summable f := absolutely_summable_def.mpr A1,
  apply has_absolute_sum_has_conditional_sum_has_sum_of_absolutely_summable A2,
end


lemma tsum_zero_of_not_summable {f:ℕ → ℝ}:
  ¬ (summable f) → (∑' i, f i) = 0 :=
begin
  intro A1,
  unfold tsum,
  rw dif_neg,
  apply A1,
end

lemma absolute_sum_zero_of_not_absolutely_summable {f:ℕ → ℝ}:
  ¬ (absolutely_summable f) → absolute_sum f = 0 :=
begin
  intro A1,
  unfold absolute_sum,
  rw if_neg,
  apply A1,
end

lemma tsum_eq_absolute_sum {f:ℕ → ℝ}:
  (∑' i, f i) = (absolute_sum f) :=
begin
  have A1:summable f ∨ ¬ (summable f),
  {
    apply classical.em,
  },
  cases A1,
  {
    have A2:=has_absolute_sum_has_conditional_sum_has_sum_of_summable A1,
    cases A2 with x A3,
    cases A3 with A4 A5,
    cases A5 with A6 A7,
    rw absolute_sum_replace A4,
    rw tsum_replace A7,
  },
  {
    rw absolute_sum_zero_of_not_absolutely_summable,
    rw tsum_zero_of_not_summable,
    apply A1,
    intro A2,
    apply A1,
    rw absolutely_summable_def at A2,
    apply A2,
  }
end

lemma tsum_eq_conditional_sum_of_summable {f:ℕ → ℝ}:
  summable f →
  (∑' i, f i) = (∑ₚ i, f i) :=
begin
  intro A1,
  rw tsum_eq_absolute_sum,
  have A2:absolutely_summable f := absolutely_summable_def.mpr A1,
  apply conditional_sum_eq_absolute_sum_of_absolutely_summable,
  apply A2,
end



lemma has_absolute_sum_iff_has_sum {f:ℕ → ℝ} {x:ℝ}:
  has_absolute_sum f x ↔ has_sum f x :=
begin
  split;intro A1,
  {
    unfold has_absolute_sum at A1,
    cases A1 with A2 A3,
    have A4 := has_absolute_sum_has_conditional_sum_has_sum_of_absolutely_summable A2,
    cases A4 with x2 A5,
    cases A5 with A6 A7,
    cases A7 with A8 A9,
    have A10:x = x2 := has_conditional_sum_unique A3 A8,
    subst x2,
    apply A9,
  },
  {
    have A2:summable f := summable_intro A1,
    have A4 := has_absolute_sum_has_conditional_sum_has_sum_of_summable A2,
    cases A4 with x2 A5,
    cases A5 with A6 A7,
    cases A7 with A8 A9,
    have A10:x = x2 := has_sum.unique A1 A9,
    subst x2,
    apply A6,
  }
end




def has_taylor_series (f:ℕ → ℝ) (x x':ℝ) (g:ℝ → ℝ):Prop
    := has_conditional_sum (λ n:ℕ, (f n) * (x' - x)^n) (g x')



def analytic_with_fn_at (g:ℝ → ℝ) (x:ℝ) (f:ℕ → ℝ):Prop := ∃ (V:set ℝ), (is_open V) ∧
(∀ y∈ V, has_taylor_series f x y g)

def analytic_at (g:ℝ → ℝ) (x:ℝ):Prop := ∃ (f:ℕ → ℝ), analytic_with_fn_at g x f

def analytic (g:ℝ → ℝ):Prop := ∀ x:ℝ, analytic_at g x

def is_maclaurin_fn (f:ℕ → ℝ) (g:ℝ → ℝ):Prop := ∀ x:ℝ,
  has_conditional_sum (λ n:ℕ, f n * x^n) (g x)


lemma is_maclaurin_fn_def (f:ℕ → ℝ) (g:ℝ → ℝ):
    is_maclaurin_fn f g = (∀ x, has_conditional_sum (λ n:ℕ, f n * x^n) (g x)) := rfl

def deriv_maclaurin_series (f:ℕ → ℝ) (n:ℕ):ℝ := (f (nat.succ n)) * (nat.succ n)

lemma deriv_maclaurin_series_def {f:ℕ → ℝ}:
  deriv_maclaurin_series f = (λ n, (f (nat.succ n)) * (nat.succ n)) := rfl
/- If we are concerned with functions that are everywhere analytic, then we need this
   guarantee to hold.
   Specifically, this guarantee is necessary for the series to be bounded at x, and such
   a guarantee is sufficient for it to be bounded anywhere "less than" x.
   -/
def bounded_maclaurin (f:ℕ → ℝ):Prop := ∀ x:ℝ,
  has_classical_limit (λ n:ℕ, x^n * f n) 0


noncomputable def maclaurin (f:ℕ → ℝ) (x:ℝ):ℝ := conditional_sum (λ n:ℕ, f n * x^n)

noncomputable def deriv_maclaurin (f:ℕ → ℝ):ℝ → ℝ := maclaurin (deriv_maclaurin_series f)


--This could be expanded to an arbitrary commutative group.

/- This is the key observation of analytic functions.
   If you go slightly further out, then you can prove that the
   series is converging exponentially fast.

   Note: prefer bounded_maclaurin_exponential.
    -/
lemma bounded_maclaurin_exponential {f:ℕ → ℝ} {x:ℝ}:
  bounded_maclaurin f →
  (∃ n:ℕ, ∀ n', n < n' → (abs (x^n' * (f n')) < ((2:ℝ)⁻¹)^(n'))) :=
begin
  intro A1,
  unfold bounded_maclaurin at A1,
  have A2:has_classical_limit (λ (n : ℕ), (2 * x) ^ n * f n) 0 := A1 (2 * x),
  unfold has_classical_limit at A2,
  have A3:(∃ (n : ℕ), ∀ (n' : ℕ), n < n' → abs ((2 * x) ^ n' * f n' - 0) < 1)
      := A2 (1:ℝ) (zero_lt_one),
  cases A3 with n A4,
  apply exists.intro n,
  intros n' A5,
  have A6:abs ((2 * x) ^ n' * f n' - 0) < 1 := A4 n' A5,
  simp at A6,
  rw pow_distrib at A6,
  rw mul_assoc at A6,
  rw abs_mul_eq_mul_abs at A6,
  --rw mul_assoc at A7,
  rw mul_comm at A6,
  rw ← lt_div_iff at A6,
  rw div_inv at A6,
  rw inv_exp at A6,
  apply A6,
  apply pow_two_pos,
  apply le_of_lt,
  apply pow_two_pos,
end

/- This is a more useful variant. -/
lemma bounded_maclaurin_exponential2 {f:ℕ → ℝ} {x:ℝ}:
  bounded_maclaurin f →
  (∃ n:ℕ, ∀ n', n < n' → (abs ((f n') * x^n') < ((2:ℝ)⁻¹)^(n'))) :=
begin
  intro A1,
  have A2:  (∃ n:ℕ, ∀ n', n < n' → (abs (x^n' * (f n')) < ((2:ℝ)⁻¹)^(n'))),
  {
    apply bounded_maclaurin_exponential,
    apply A1,
  },
  cases A2 with n A3,
  apply exists.intro n,
  intros n' A4,
  have A5 := A3 n' A4,
  rw mul_comm,
  apply A5,
end



lemma abs_nonneg_func2 {f:ℕ → ℝ}:0 ≤ f → (f  = (abs ∘ f)) :=
begin
  intro A1,
  ext n,
  simp,
  rw abs_of_nonneg,
  apply A1,
end

lemma absolutely_summable_bound2 {f:ℕ → ℝ} {g:ℕ → ℝ}:
  absolutely_summable g →
  (abs ∘ f) ≤ g →
  absolutely_summable f :=
begin
  unfold absolutely_summable,
  intros A1 A2,
  have A3:=@abs_nonneg_func f,
  have A4:=le_trans A3 A2,
  have A5:=abs_nonneg_func2 A4,
  have A6:abs ∘ f ≤ abs ∘ g,
  {
    rw ← A5,
    apply A2,
  },
  apply conditionally_summable_bound (abs ∘ f) (abs ∘ g) A3 A6,
  apply A1,
end


lemma range_sum_eq_after {f g:ℕ → ℝ} {n:ℕ}:
  (∀ n':ℕ, n < n' → (f n' = g n')) →
  (∀ n':ℕ, n < n' →
    finset.sum (finset.range n') f +
      (finset.sum (finset.range (nat.succ n)) g + -finset.sum (finset.range (nat.succ n)) f) =
    finset.sum (finset.range n') g) :=
begin
  intros A1 n',
  induction n',
  {
    intro A2,
    exfalso,
    apply nat.not_lt_zero n A2,
  },
  {
    intro A2,
    have A3:(n'_n = n)∨ (n'_n ≠ n) := eq_or_ne,
    cases A3,
    {
      subst n'_n,
      simp,
    },
    {
      have A4:n < n'_n,
      {
        have A4A:n ≤ n'_n := nat.le_of_lt_succ A2,
        apply lt_of_le_of_ne A4A,
        symmetry,
        apply A3,
      },
      have A5:= n'_ih A4,
      have A6:(finset.range (nat.succ n'_n)).sum f = f n'_n + (finset.range (n'_n)).sum f,
      {
        rw finset.range_succ,
        rw finset.sum_insert,
        simp,
      },
      have A7:(finset.range (nat.succ n'_n)).sum g = g n'_n + (finset.range (n'_n)).sum g,
      {
        rw finset.range_succ,
        rw finset.sum_insert,
        simp,
      },
      rw A6,
      rw A7,
      rw ← A5,
      rw A1 n'_n A4,
      rw add_assoc,
    }
  }
end

lemma has_conditional_sum_eq_after {f g:ℕ → ℝ} {x:ℝ} {n:ℕ}:
  has_conditional_sum f x →
  (∀ n':ℕ, n < n' → (f n' = g n')) →
  has_conditional_sum g (x + (finset.range (nat.succ n)).sum g - (finset.range (nat.succ n)).sum f) :=
begin
  rw has_conditional_sum_def,
  rw has_conditional_sum_def,
  intros A1 A2,
  let z:=(finset.range (nat.succ n)).sum g - (finset.range (nat.succ n)).sum f,
  let h:=λ n':ℕ, z + (finset.range n').sum f,
  begin
    have A3:z=(finset.range (nat.succ n)).sum g - (finset.range (nat.succ n)).sum f := rfl,
    have A4:h=λ n':ℕ, z + (finset.range n').sum f := rfl,
    have A5:h=(λ n':ℕ, z) + λ n':ℕ, (finset.range n').sum f := rfl,
    have A6:has_classical_limit h (z + x),
    {
      rw A5,
      apply has_classical_limit_sum,
      apply has_classical_limit_const,
      apply A1,
    },
    have A7:(∀ n':ℕ, n < n' → (h n' = (λ n'':ℕ, (finset.range n'').sum g) n')),
    {
      intros n' A7A,
      rw A4,
      rw A3,
      simp,
      rw sub_eq_add_neg,
      rw add_comm,
      apply range_sum_eq_after A2,
      apply A7A,
    },
    have  A8:(x + finset.sum (finset.range (nat.succ n)) g - finset.sum (finset.range (nat.succ n)) f)
      = z + x,
    {
      rw add_sub_assoc,
      rw ← A3,
      rw add_comm,
    },
    rw A8,
    apply has_classical_limit_eq_after A6 A7,
  end
end

lemma conditionally_summable_eq_after {f g:ℕ → ℝ} {n:ℕ}:
  conditionally_summable f →
  (∀ n':ℕ, n < n' → (f n' = g n')) →
  conditionally_summable g :=
begin
  unfold conditionally_summable,
  intros A1 A2,
  cases A1 with x A3,
  apply exists.intro (x + (finset.range (nat.succ n)).sum g - (finset.range (nat.succ n)).sum f),
  apply has_conditional_sum_eq_after A3 A2,
end

lemma absolutely_summable_eq_after {f g:ℕ → ℝ} {n:ℕ}:
  absolutely_summable f →
  (∀ n':ℕ, n < n' → (f n' = g n')) →
  absolutely_summable g :=
begin
  unfold absolutely_summable,
  intros A1 A2,
  have A3:(∀ n':ℕ, n < n' → ((abs ∘ f) n' = (abs ∘ g) n')),
  {
    intros n' A3A,
    simp,
    rw A2 n' A3A,
  },
  apply conditionally_summable_eq_after A1 A3,
end

lemma absolutely_summable_bound {f:ℕ → ℝ} {g:ℕ → ℝ}:
  absolutely_summable g →
  (∃ (n:ℕ), ∀ (n':ℕ), n < n' → abs (f n') ≤ g n') →
  absolutely_summable f :=
begin
  intros A1 A2,
  cases A2 with n A3,
  let h:ℕ → ℝ := λ n':ℕ, if n < n' then g n' else abs (f n'),
  begin
    have A4:h = λ n':ℕ, if n < n' then g n' else abs (f n') := rfl,
    have A5:(∀ n':ℕ, n < n' → (g n' = h n')),
    {
      intros n' A5A,
      rw A4,
      simp,
      rw if_pos A5A,
    },
    have A6:abs ∘ f ≤ h,
    {
      rw le_func_def,
      intro n',
      rw A4,
      have A6A:(n < n') ∨ ¬ (n < n') := lt_or_not_lt,
      cases A6A,
      {
        simp,
        rw if_pos A6A,
        --apply le_of_lt, -- Note: this means that the bound in the lemma is loose.
        apply A3 n' A6A,
      },
      {
        simp,
        rw if_neg A6A,
      }
    },
    have A7:absolutely_summable h := absolutely_summable_eq_after A1 A5,
    apply absolutely_summable_bound2 A7 A6,
  end
end



lemma has_absolute_sum_exp {x:ℝ}:
  (0 ≤ x) →
  (x < 1) →
  has_absolute_sum (λ n, x^n) (1-x)⁻¹ :=
begin
  intros A1 A2,
  rw has_absolute_sum_iff_has_sum,
  apply has_sum_geometric_of_lt_1 A1 A2,
end

lemma has_conditional_sum_exp {x:ℝ}:
  (0 ≤ x) →
  (x < 1) →
  has_conditional_sum (λ n, x^n) (1-x)⁻¹ :=
begin
  intros A1 A2,
  apply has_conditional_sum_of_has_absolute_sum,
  apply has_absolute_sum_exp,
  apply A1,
  apply A2,
end

lemma absolutely_summable_intro {f:ℕ→ ℝ} {x:ℝ}:
  has_absolute_sum f x → absolutely_summable f :=
begin
  intro A1,
  apply A1.left
end

lemma absolutely_summable_exp {x:ℝ}:
  (0 ≤ x) →
  (x < 1) →
  absolutely_summable (λ n, x^n) :=
begin
  intros A1 A2,
  have A3:=has_absolute_sum_exp A1 A2,
  apply absolutely_summable_intro A3,
end



noncomputable def exp_maclaurin (n:ℕ):ℝ := ((nat.fact n):ℝ)⁻¹


lemma exp_maclaurin_def:exp_maclaurin = (λ n, ((nat.fact n):ℝ)⁻¹) := rfl


lemma bounded_maclaurin_of_is_maclaurin_fn (f:ℕ → ℝ) {g:ℝ → ℝ}:
  is_maclaurin_fn f g →
  bounded_maclaurin f :=
begin
  intro A1,
  unfold bounded_maclaurin,
  intro x,
  unfold is_maclaurin_fn at A1,
  have A2 := A1 x,
  have A3:(λ n:ℕ, x^n * f n) = (λ n:ℕ, f n * x^n),
  {
    ext n,
    apply mul_comm,
  },
  rw A3,
  apply has_classical_limit_of_conditional_summable,
  apply conditionally_summable_of_has_conditional_sum A2,
end


lemma is_maclaurin_fn_of_bounded_maclaurin {f:ℕ → ℝ}:
  bounded_maclaurin f →
  is_maclaurin_fn f (maclaurin f) :=
begin
  intro A1,
  unfold is_maclaurin_fn,
  intro x,
  unfold maclaurin,
  apply has_conditional_sum_conditional_sum_of_conditionally_summable,
  apply conditionally_summable_of_absolutely_summable,
  have  A3:(∃ n:ℕ, ∀ n', n < n' → (abs ((f n') * x^n') < ((2:ℝ)⁻¹)^(n'))),
  {
    apply bounded_maclaurin_exponential2,
    apply A1,
  },

  apply absolutely_summable_bound,
  {
    apply @absolutely_summable_exp ((2:ℝ)⁻¹),
    {
      simp,
      apply le_of_lt,
      apply zero_lt_one,
    },
    {
      apply inv_lt_one_of_one_lt,
      apply one_lt_two,
    },
  },
  cases A3 with n A4,
  apply exists.intro n,
  intros n' A5,
  apply le_of_lt,
  apply A4 n' A5,
end




lemma forall_iff_forall_of_forall_iff (α:Type*) (P Q:α → Prop):
  (∀ a:α, P a ↔ Q a)→ ((∀ a:α, P a)↔ (∀ a:α, Q a)) :=
begin
  intros A1,
  split;intros A2 a;have A3 := A1 a;have A4 := A2 a,
  {
    apply A3.mp A4,
  },
  {
    apply A3.mpr A4,
  }
end

lemma bounded_maclaurin_iff_bounded_maclaurin_abs {f:ℕ → ℝ}:
  bounded_maclaurin f ↔ bounded_maclaurin (abs ∘ f) :=
begin
  unfold bounded_maclaurin,
  apply forall_iff_forall_of_forall_iff,
  intros x,
  have A3:(λ n:ℕ, x^n) * f = (λ n:ℕ, x^n * f n),
  {
    ext n,
    simp,
  },
  rw ← A3,
  have A4:(λ n:ℕ, x^n) * abs ∘ f = (λ n:ℕ, x^n * (abs ∘ f) n),
  {
    ext n,
    simp,
  },
  rw ← A4,
  apply has_classical_limit_half_abs_zero,
end


-- is_maclaurin_fn f (maclaurin f)
lemma absolutely_summable_of_bounded_maclaurin {f:ℕ → ℝ} {x:ℝ}:
    bounded_maclaurin f → (absolutely_summable (λ n:ℕ, f n * x^n )) :=
begin
  intro A1,
  unfold absolutely_summable,
  have A2:bounded_maclaurin (abs ∘ f),
  {
     rw bounded_maclaurin_iff_bounded_maclaurin_abs at A1,
     apply A1,
  },
  have A3:is_maclaurin_fn (abs ∘ f) (maclaurin (abs ∘ f)) := is_maclaurin_fn_of_bounded_maclaurin A2,

  let x':=abs x,
  begin
    unfold is_maclaurin_fn at A3,
    have A4:=A3 x',
    have A5:x' = abs x := rfl,
    have A6:(λ (n : ℕ), (abs ∘ f) n * x' ^ n)= (λ (n : ℕ), abs(f n * x ^ n)),
    {
      ext n,
      rw A5,
      rw pow_abs,
      simp,
      rw abs_mul,
    },
    rw ← A6,
    unfold conditionally_summable,
    apply exists.intro (maclaurin (abs ∘ f) x'),
    apply A4,
  end
end


lemma is_cau_seq_coe (f:ℕ → ℂ):is_cau_seq complex.abs f → is_cau_seq abs (λ n:ℕ, (f n).re) :=
begin
  unfold is_cau_seq,
  intros A1 ε A2,
  have A3 := A1 ε A2,
  cases A3 with i A4,
  apply exists.intro i,
  intros j A5,
  have A6 := A4 j A5,
  have A7:(f j).re - (f i).re = (f j - f i).re,
  {
    simp,
  },
  rw A7,
  apply lt_of_le_of_lt,
  apply complex.abs_re_le_abs,
  apply A6,
end



/-
lemma real.exp_def (x:ℝ):has_conditional_sum (λ n:ℕ, x^n * ((nat.fact n):ℝ)⁻¹) (real.exp x) :=
begin
  unfold has_conditional_sum,
  unfold real.exp complex.exp complex.exp',
  rw ← complex.lim_re,
  unfold cau_seq_re,

  rw is_cau_seq_coe,
end
-/



lemma cau_seq_eq2 {f:cau_seq ℝ abs} {g:ℕ → ℝ}:
  ⇑ f  = g →
  has_classical_limit g f.lim :=
begin
  intro A0,
  have A1:=cau_seq.complete f,
  cases A1 with b A1,
  have A3:f.lim = b := cau_seq.lim_eq_of_equiv_const A1,
  rw A3,
  unfold has_classical_limit,
  intros ε A2A,
  have A2B:=cau_seq.equiv_def₃  A1 A2A,
  cases A2B with n A2C,
  apply exists.intro n,
  intros n' A2D,
  have A2E:n ≤ n' := le_of_lt A2D,
  have A2F := A2C n' A2E,
  have A2G:n' ≤ n' := le_refl n',
  have A2H := A2F n' A2G,
  rw A0 at A2H,
  simp at A2H,
  apply A2H,
end



lemma cau_seq_eq {f:cau_seq ℝ abs} {g:ℕ → ℝ}:
  ⇑ f  = g →
  f.lim = classical_limit g :=
begin
  intro A1,
  apply eq_classical_limit,
  apply cau_seq_eq2,
  apply A1,
end

lemma cau_seq_re_val {f:cau_seq ℂ complex.abs} {n:ℕ}:((complex.cau_seq_re f) n) = (f n).re := rfl

lemma complex.exp_val {z:ℂ} {n:ℕ}:(complex.exp' z) n =
  (finset.range n).sum (λ m, z ^ m / ((nat.fact m):ℂ)) := rfl


noncomputable def complex.add_comm_monoid:add_comm_monoid ℂ := infer_instance



lemma is_add_monoid_hom_complex_re_map_add : ∀ x y:ℂ,
    complex.re (x + y) = complex.re x + complex.re y :=
begin
  intros x y,
  refl
end

/- This probably exists somewhere. -/
def is_add_monoid_hom_complex_re:is_add_monoid_hom complex.re := {
  map_zero:= rfl,
  map_add := is_add_monoid_hom_complex_re_map_add,
}

lemma finset_sum_re {α:Type*} {S:finset α} [decidable_eq α] {f:α → ℂ}:
   (finset.sum S (λ a:α, complex.re (f a))) = complex.re (finset.sum S f) :=
begin
  apply @finset.sum_hom α ℂ ℝ complex.add_comm_monoid real.add_comm_monoid S f complex.re
  is_add_monoid_hom_complex_re,
end


lemma exp_rewrite (x:ℝ):(λ n:ℕ, x^n/((nat.fact n):ℝ)) = (λ n:ℕ, ((nat.fact n):ℝ)⁻¹ * x^n) :=
begin
  ext n,
  rw mul_comm,
  refl,
end




lemma bounded_maclaurin_exp_maclaurinh {x:ℝ}:
    has_classical_limit (λ (n : ℕ), x ^ n * ((nat.fact n):ℝ)⁻¹) 0 :=
begin
  have A1:x = 0 ∨ (x ≠ 0) := eq_or_ne,
  cases A1,
  {
    rw A1,
    have A2:∀ n', 0 < n' → (λ (n:ℕ),(0:ℝ)) n' = (λ (n : ℕ), 0 ^ n * ((nat.fact n):ℝ)⁻¹) n',
    {
      intros n' A2A,
      simp,left,
      rw pow_zero_eq_zero_if_pos A2A,
    },
    apply has_classical_limit_eq_after (@has_classical_limit_const 0) A2,
  },
  {
    rw ← has_classical_limit_abs_zero,
    let z := abs x,
    begin
      have A2:z = abs x := rfl,
      have A3:0 < z,
      {
        rw A2,
        apply abs_pos_of_nonzero A1,
      },
      have A4:(abs ∘ λ (n : ℕ), x ^ n * (↑(nat.fact n))⁻¹)= (λ (n : ℕ), z ^ n * (↑(nat.fact n))⁻¹),
      {
        ext n,
        simp,
        rw abs_mul,
        rw abs_pow,
        rw abs_inv,
        rw real_nat_abs_coe,
      },
      rw A4,
      apply has_classical_limit_ratio_lt_one2,
      {
        apply has_classical_limit_ratio_power_fact,
      },
      {
        apply zero_lt_one,
      },
      {
        apply le_refl,
      },
      {
        intros n,
        apply mul_pos,
        apply pow_pos,
        apply A3,
        apply inv_pos_of_pos,
        simp,
        apply nat_zero_lt_of_nonzero,
        apply nat_fact_nonzero,
      },
    end
  }
end


lemma bounded_maclaurin_exp_maclaurin:bounded_maclaurin exp_maclaurin :=
begin
  unfold bounded_maclaurin,
  unfold exp_maclaurin,
  apply bounded_maclaurin_exp_maclaurinh,
end


lemma conditionally_summable_of_bounded_maclaurin (f:ℕ → ℝ) (x:ℝ):
    bounded_maclaurin f →
    conditionally_summable (λ (n : ℕ), f n * x ^ n) :=
begin
  intro A1,
  unfold conditionally_summable,
  apply exists.intro (maclaurin f x),
  apply is_maclaurin_fn_of_bounded_maclaurin,
  apply A1,
end






lemma real.exp_def (x:ℝ):has_conditional_sum (λ n:ℕ, ((nat.fact n):ℝ)⁻¹  * x^n) (real.exp x) :=
begin
  unfold has_conditional_sum,
  unfold real.exp,
  unfold complex.exp,
  rw ← complex.lim_re,
  have A1:⇑(complex.cau_seq_re (complex.exp' ↑x)) = (λ n:ℕ, (finset.range n).sum (λ n:ℕ,((nat.fact n):ℝ)⁻¹  * x^n)),
  {
    ext n,
    rw cau_seq_re_val,
    rw complex.exp_val,
    rw ← finset_sum_re,
    have A1A: (λ (a : ℕ), ((x:ℂ) ^ a / ((nat.fact a):ℂ)).re) = (λ (n : ℕ), ((nat.fact n):ℝ)⁻¹  * x^n),
    {
      rw ← exp_rewrite,
      ext n2,
      rw complex_pow_div_complex_re,
    },
    rw A1A,
  },
  rw cau_seq_eq A1,
  clear A1,
  rw ← has_conditional_sum_def,
  rw ← conditional_sum_def,
  apply has_conditional_sum_conditional_sum_of_conditionally_summable,
  apply conditionally_summable_of_bounded_maclaurin,
  apply bounded_maclaurin_exp_maclaurin,
end

lemma is_maclaurin_fn_exp:is_maclaurin_fn (λ n:ℕ, ((nat.fact n):ℝ)⁻¹) real.exp :=
begin
  unfold is_maclaurin_fn,
  intro x,
  apply real.exp_def,
end



----Goals -----------------------------------------------------------------------------------------



lemma zero_le_one_coe_real {n:ℕ}:(0:ℝ) ≤ (1:ℝ) + (n:ℝ) :=
begin
  have A1:(0:ℝ) ≤ (1:ℝ),
  {
    apply le_of_lt,
    apply zero_lt_one,
  },
  apply le_trans A1,
  simp,
end



lemma inv_pow_succ_2 {x:ℝ} {n:ℕ}:x⁻¹ * x ^ (nat.succ (nat.succ n))=x^ (nat.succ n) :=
begin
  have A1:x = 0 ∨ (x ≠ 0) := eq_or_ne,
  cases A1,
  {
    subst x,
    simp,
    rw pow_zero_eq_zero_if_pos,
    simp,
  },
  {
    rw @nat_succ_pow (nat.succ n),
    rw ← mul_assoc,
    rw inv_mul_cancel A1,
    rw one_mul,
  }
end


lemma is_maclaurin_derivative_bounded (f:ℕ → ℝ):
  bounded_maclaurin f →
  is_maclaurin_fn (deriv_maclaurin_series f) (maclaurin (deriv_maclaurin_series f))
  :=
begin
  intro A1,
  apply is_maclaurin_fn_of_bounded_maclaurin,
  unfold deriv_maclaurin_series bounded_maclaurin,
  intro x,
  have A6B:(x = 0) ∨ (x ≠ 0) := eq_or_ne,
  have A2:(∃ n:ℕ, ∀ n', n < n' → (abs (x^n' * (f n')) < (2:real)⁻¹ ^(n')))
      := @bounded_maclaurin_exponential _ x A1,
  cases A2 with n A4,
  have A7:has_classical_limit (λ n:ℕ, abs (x⁻¹) *  (2:real)⁻¹ ^(n + 1) * (1 + (n:ℝ))) 0,
  {
    cases A6B,
    {
      subst x,
      simp,
      apply has_classical_limit_const,
    },
    {
      have A7A:abs (x⁻¹) * 0 = 0 := mul_zero (abs (x⁻¹)),
      rw ← A7A,
      have A7B:(λ n:ℕ, abs (x⁻¹) *  (2:real)⁻¹ ^(n + 1) * (1 + (n:ℝ)))=
          (λ n:ℕ, abs (x⁻¹) *  ((2:real)⁻¹ ^(n + 1) * (1 + (n:ℝ)))),
      {
        ext n',
        rw mul_assoc,
      },
      rw A7B,
      apply has_classical_limit_mul_const,
      have A7C:(λ n:ℕ, (2:real)⁻¹ ^(n + 1) * (1 + (n:ℝ)))=
          (λ m:ℕ, (m:ℝ) * (2:real)⁻¹ ^(m)) ∘ (λ n:ℕ, 1 + n),
      {
        ext n',
        simp,
        rw add_comm n' 1,
        apply mul_comm,
      },
      rw A7C,
      rw ← @has_classical_limit_offset _ 0 1,
      have A7D:∀ (n : ℕ), 0 < n → 0 < (n:ℝ),
      {
        intros n A7D1,
        simp,
        apply A7D1
      },
      apply has_classical_limit_ratio_one_exp A7D,
      {
        apply has_classical_limit_ratio_one,
      },
      {
        apply half_lt_one,
      },
      {
        apply half_pos_lit,
      }
    }
  },
  apply has_classical_limit_bound,
  apply A7,
  {
    apply exists.intro n,
    intros n' A6A,
    have A6B:(x = 0) ∨ (x ≠ 0) := eq_or_ne,
    cases A6B,
    {
      subst x,
      simp,
      left,
      apply pow_zero_eq_zero_if_pos,
      apply lt_of_le_of_lt,
      apply nat.zero_le n,
      apply A6A,
    },
    {
      simp,
      have A6C:(abs x) * (abs (x ^ n' * (f (nat.succ n') * (1 + ↑n')))) ≤
        (abs x) * (abs (x⁻¹) * (2:real)⁻¹ ^(n' + 1) * (1 + ↑n')),
      {
        rw ← mul_assoc,
        rw ← mul_assoc,
        rw ← abs_mul,
        rw ← mul_assoc,
        rw ← mul_assoc,
        rw ← mul_assoc,

        rw ← abs_mul,

        rw ← nat_succ_pow,
        rw mul_inv_cancel A6B_1,
        simp,
        rw abs_mul,
        simp,
        have A6C1:0 ≤ (1+(n':ℝ)) := zero_le_one_coe_real,
        have A6C2:abs (1+(n':ℝ))=1 + (n':ℝ) := abs_of_nonneg A6C1,
        rw A6C2,
        apply mul_le_mul_of_nonneg_right _ A6C1,
        apply le_of_lt,
        have A6C3:n'+1 = nat.succ n',
        {
          simp,
        },
        rw A6C3,
        rw ← inv_pow_comm,
        apply A4 (nat.succ n'),
        apply lt_trans,
        apply A6A,
        apply nat.lt_succ_self,
      },
      rw add_comm (n':ℝ) 1,
      rw ← inv_pow_comm,
      apply le_of_mul_le_mul_left A6C,
      apply abs_pos_of_nonzero A6B_1,
    }
  },
end



/- Sum from m to infinity -/
noncomputable def conditional_sum_lb (m:ℕ) (f:ℕ→ℝ):ℝ :=
    conditional_sum (λ n, if (m ≤ n) then f n else 0)



lemma finset_range_disjoint {n n2:ℕ}:
    n ≤ n2  →
    disjoint (finset.range n) (finset.Ico n n2) :=
begin
  intro A1,
  rw ← finset.Ico.zero_bot,
  apply finset.Ico.disjoint_consecutive,
end


lemma finset_range_union {n n2:ℕ}:
    n ≤ n2  →
    (finset.range n) ∪ (finset.Ico n n2) = (finset.range n2) :=
begin
  intro A1,
  rw ← finset.Ico.zero_bot,
  rw ← finset.Ico.zero_bot,
  apply finset.Ico.union_consecutive,
  {
    simp,
  },
  {
    apply A1,
  }
end

lemma has_conditional_sum_lb_iff_has_conditional_sum {m:ℕ} {f:ℕ→ℝ} {x:ℝ}:
      has_conditional_sum (λ n, if (m ≤ n) then f n else 0) x ↔
      has_conditional_sum (f ∘ (λ k, m + k)) x :=
begin
  rw has_conditional_sum_def,
  rw has_conditional_sum_def,
  have A1:(λ (k : ℕ), finset.sum (finset.range k) (λ (n : ℕ), ite (m ≤ n) (f n) 0)) ∘ (λ z, m + z)=
          (λ (n : ℕ), finset.sum (finset.range n) (f∘  (λ k, m + k))),
  {
    ext k2,
    have A1C:m ≤ m + k2,
    {
      simp,
    },
    simp,
    rw ← @finset_range_union m (m + k2),
    rw finset.sum_union,
    have A1A:finset.sum (finset.range m) (λ (n : ℕ), ite (m ≤ n) (f n) 0) =
             finset.sum (finset.range m) (λ (n : ℕ), 0),
    {
      apply @finset_sum_subst2,
      intros s A1A1,
      rw if_neg,
      rw finset.mem_range at A1A1,
      apply not_le_of_lt A1A1,
    },
    have A1B: finset.sum (finset.Ico m (m + k2)) (λ (n : ℕ), ite (m ≤ n) (f n) 0) =
              finset.sum (finset.Ico (0 + m) (k2 + m)) f,
    {
      rw zero_add,
      rw add_comm k2 m,
      apply @finset_sum_subst2,
      intros s A1B1A,
      rw if_pos,
      rw finset.Ico.mem at A1B1A,
      apply A1B1A.left,
    },
    rw A1A,
    rw A1B,
    rw ← @finset.sum_Ico_add ℝ _ f 0 k2 m,
    rw finset.Ico.zero_bot,
    simp,

    apply finset_range_disjoint,
    apply A1C,
    apply A1C,
  },
  rw @has_classical_limit_offset
      (λ (k : ℕ), finset.sum (finset.range k) (λ (n : ℕ), ite (m ≤ n) (f n) 0)) x m,
  rw A1,
end


lemma conditional_sum_zero_of_not_conditionally_summable {f:ℕ → ℝ}:
  ¬ (conditionally_summable f) → (conditional_sum f = 0) :=
begin
  intro A1,
  unfold conditional_sum,
  rw dif_neg,
  apply A1,
end

lemma conditional_sum_lb_inc {k:ℕ} {f:ℕ→ℝ}:
    conditional_sum_lb k f = conditional_sum (f ∘ (λ m, k + m)) :=
begin

  have A1:conditionally_summable (f ∘ (λ m, k + m)) ∨ ¬(conditionally_summable (f ∘ (λ m, k + m)))
       := classical.em (conditionally_summable (f ∘ (λ m, k + m))),
  cases A1,
  {  -- conditionally_summable (f ∘ (λ m, k + m)) ⊢ ...
    unfold conditional_sum_lb,
    have B1:= has_conditional_sum_conditional_sum_of_conditionally_summable A1,
    have B2:= has_conditional_sum_lb_iff_has_conditional_sum.mpr B1,
    rw conditional_sum_replace B2,
  },
  {  -- ¬ (conditionally_summable (f ∘ (λ m, k + m))) ⊢ ...
    unfold conditional_sum_lb,
    have C1:¬conditionally_summable (λ (n : ℕ), ite (k ≤ n) (f n) 0),
    {
      intro C1A,
      apply A1,
      have C1B:= has_conditional_sum_conditional_sum_of_conditionally_summable C1A,
      have B2:= has_conditional_sum_lb_iff_has_conditional_sum.mp C1B,
      apply conditionally_summable_of_has_conditional_sum B2,
    },
    rw conditional_sum_zero_of_not_conditionally_summable A1,
    rw conditional_sum_zero_of_not_conditionally_summable C1,
  },
end

--conditional_sum (λ n, if (m ≤ n) then f n else 0)



lemma injective_prod_mk_left {m:ℕ}:function.injective (λ n:ℕ, prod.mk m n) :=
begin
  have A1:function.left_inverse  (@prod.snd ℕ ℕ) (λ n:ℕ, prod.mk m n),
  {
    unfold function.left_inverse,
    simp,
  },
  apply function.left_inverse.injective A1,
end

lemma injective_prod_mk_right {n:ℕ}:function.injective (λ m:ℕ, prod.mk m n) :=
begin
  have A1:function.left_inverse  (@prod.fst ℕ ℕ) (λ m:ℕ, prod.mk m n),
  {
    unfold function.left_inverse,
    simp,
  },
  apply function.left_inverse.injective A1,
end

lemma injective_prod_mk_right2 {β γ:Type*} {n:γ}:function.injective (λ m:β, prod.mk m n) :=
begin
  have A1:function.left_inverse  (@prod.fst β γ) (λ m:β, prod.mk m n),
  {
    unfold function.left_inverse,
    simp,
  },
  apply function.left_inverse.injective A1,
end

lemma injective_prod_mk_left2 {β γ:Type*} {m:β}:function.injective (λ n:γ, prod.mk m n) :=
begin
  have A1:function.left_inverse  (@prod.snd β γ) (λ n:γ, prod.mk m n),
  {
    unfold function.left_inverse,
    simp,
  },
  apply function.left_inverse.injective A1,
end


lemma summable_right_of_summable {g:ℕ → ℕ → ℝ} {n:ℕ}:
  summable (λ p:ℕ × ℕ,g p.fst p.snd) →
  summable (g n) :=
begin
  intro A1,
  have A2:(g n)=(λ p:ℕ × ℕ,g p.fst p.snd)∘ (λ m:ℕ, prod.mk n m),
  {
    ext m,
    simp,
  },
  rw A2,
  apply summable.comp_injective
      A1 (@injective_prod_mk_left n),
end

lemma summable_right_of_summable2 {g:ℕ × ℕ → ℝ} {n:ℕ}:
  summable g →
  summable (λ m:ℕ, g ⟨n, m⟩ ) :=
begin
  intro A1,
  have A2:(λ m:ℕ, g ⟨n, m⟩ )=g ∘ (λ m:ℕ, prod.mk n m),
  {
    ext m,
    simp,
  },
  rw A2,
  apply summable.comp_injective
      A1 (@injective_prod_mk_left n),
end

lemma summable_left_of_summable {g:ℕ → ℕ → ℝ} {n:ℕ}:
  summable (λ p:ℕ × ℕ,g p.fst p.snd) →
  summable (λ m:ℕ, g  m n) :=
begin
  intro A1,
  have A2:(λ m:ℕ, g  m n)=(λ p:ℕ × ℕ,g p.fst p.snd)∘ (λ m:ℕ, prod.mk m n),
  {
    ext m,
    simp,
  },
  rw A2,
  apply summable.comp_injective A1
      (@injective_prod_mk_right n),
end

lemma summable_left_of_summable2 {g:ℕ × ℕ → ℝ} {n:ℕ}:
  summable g →
  summable (λ m:ℕ, g ⟨m, n⟩ ) :=
begin
  intro A1,
  have A2:(λ m:ℕ, g  ⟨ m,  n ⟩ )=g ∘ (λ m:ℕ, prod.mk m n),
  {
    ext m,
    simp,
  },
  rw A2,
  apply summable.comp_injective
      A1 (@injective_prod_mk_right n),
end

lemma summable_left_of_summable3 {α β γ:Type*} [add_comm_group α]
  [uniform_space α] [uniform_add_group α] [complete_space α]
  {g:β × γ → α} {n:γ}:
  summable g →
  summable (λ m:β, g ⟨m, n⟩ ) :=
begin
  intro A1,
  have A2:(λ m:β, g  ⟨ m,  n ⟩ )=g ∘ (λ m:β, prod.mk m n),
  {
    ext m,
    simp,
  },
  rw A2,
  apply summable.comp_injective
      A1 (@injective_prod_mk_right2 _ _ n),
end

lemma summable_right_of_summable3 {α β γ:Type*} [add_comm_group α]
  [uniform_space α] [uniform_add_group α] [complete_space α]
  {g:β × γ → α} {m:β}:
  summable g →
  summable (λ n:γ, g ⟨m, n⟩ ) :=
begin
  intro A1,
  have A2:(λ n:γ, g  ⟨ m,  n ⟩ )=g ∘ (λ n:γ, prod.mk m n),
  {
    ext m,
    simp,
  },
  rw A2,
  apply summable.comp_injective
      A1 (@injective_prod_mk_left2 _ _ m),
end

/-
summable :
  Π {α : Type u_1} {β : Type u_2} [_inst_1 : add_comm_monoid α] [_inst_2 : topological_space α],
    (β → α) → Prop
-/
lemma summable_elim {α β:Type*} [add_comm_monoid α] [topological_space α] {g:β  → α}:
  summable g → (∃ x, has_sum g x) :=
begin
  intro A1,
  apply A1,
end


lemma equiv_to_fun_injective {β γ:Type*} (E:equiv β γ):
  function.injective E.to_fun := function.left_inverse.injective E.left_inv

lemma equiv_to_fun_bijective {β γ:Type*} {E:equiv β γ}:
  function.bijective E.to_fun :=
begin
  unfold function.bijective function.surjective,
  split,
  {
    apply equiv_to_fun_injective,
  },
  {
    have A1:function.has_right_inverse E.to_fun := exists.intro E.inv_fun E.right_inv,
    apply function.has_right_inverse.surjective A1,
  }
end

lemma sigma_equiv_prod_to_fun_bijective {β γ:Type*}:
  function.bijective (equiv.sigma_equiv_prod β γ).to_fun :=
begin
  apply equiv_to_fun_bijective,
end



def make_set_element {α:Type*} {s:set α} {x:α} {H:x∈ s}:{a // a∈ s}:=
begin
  apply @subtype.mk α s x H,
end

/-
  has_sum_iff_has_sum_of_ne_zero_bij shows that if there is a bijection between the
  nonzero values of two types, then two sums are equal. This just shows that if there
  is a traditional bijection, the two sums are equal.
-/
lemma has_sum_bijective {α β γ:Type*} [ACM:add_comm_monoid α] [T:topological_space α]
  [TAM:has_continuous_add α] (f:β → α)
  {h:γ  → β} (a:α):
  function.bijective h → (has_sum f a ↔ has_sum (f∘ h) a) :=
begin
  intros A1,
  unfold function.bijective at A1,
  cases A1 with A6 A7,
  unfold function.injective at A6,
  unfold function.surjective at A7,

  let i:= (λ (c:function.support (f ∘ h)),
                 h c),
  begin
    have A5:i = (λ (c:function.support (f ∘ h)),
                 h c) := rfl,
    apply has_sum_iff_has_sum_of_ne_zero_bij i,
    {
      intros c₁ c₂ A2,
      rw A5 at A2,
      simp at A2,
      apply A6,
      apply A2,
    },
    {
      rw set.subset_def,
      intros x B1,
      rw set.mem_range,
      have B2 := A7 x,
      cases B2 with c B3,
      rw function.mem_support at B1,
      rw ← B3 at B1,
      have B4:f (h c) = (f ∘ h) c := rfl,
      rw B4 at B1,
      rw ← @function.mem_support γ α _ (f ∘ h) at B1,
      apply exists.intro (subtype.mk c B1),
      rw A5,
      simp,
      rw B3,
    },
    {
      intro x,
      rw A5,
    },
  end
end

-- See also tsum_equiv
lemma equiv_sigma_prod_sum {α β γ:Type*} [ACM:add_comm_monoid α] [T:topological_space α]
  [TAM:has_continuous_add α] {f:β × γ → α} {a:α}:
  has_sum f a → (has_sum (λ p:(Σ (b : β), (λ b:β, γ) b), f ((equiv.sigma_equiv_prod β γ).to_fun p)) a)  :=
begin
  intro A1,
  have A2:(λ p:(Σ (b : β), (λ b:β, γ) b), f ((equiv.sigma_equiv_prod β γ).to_fun p)) =
      f ∘ (@equiv.sigma_equiv_prod β γ).to_fun := rfl,
  rw A2,
  have A3:function.bijective (@equiv.sigma_equiv_prod β γ).to_fun := sigma_equiv_prod_to_fun_bijective,
  apply (has_sum_bijective f a A3).mp A1,
end


/-
  At its essence, this is the core of Fubini's theorem, but at such a level of abstraction
  that it is obvious.
  mathlib's has_sum is a generalization of an absolute sum. There is no concept of ordering
  over the indices. Thus, flipping pairs is a noop.
-/
lemma equiv_prod_comm_sum {α β γ:Type*} [ACM:add_comm_monoid α] [T:topological_space α]
  [TAM:has_continuous_add α] {f:β × γ → α} {a:α}:
  has_sum f a → (has_sum (λ p:γ × β, f ((equiv.prod_comm γ  β).to_fun p)) a)  :=
begin
  intro A1,
  have A2:(λ p:γ × β, f ((equiv.prod_comm γ β).to_fun p)) =
      f ∘ (@equiv.prod_comm γ β).to_fun := rfl,
  rw A2,
  have A3:function.bijective (equiv.prod_comm γ β).to_fun := equiv_to_fun_bijective,
  apply (has_sum_bijective f a A3).mp A1,
end

lemma has_sum_prod {α β:Type*} [ACM:add_comm_monoid α] [T:topological_space α]
  [TAM:has_continuous_add α] [R:regular_space α] {γ:Type*} {f:β × γ → α} {g:β → α} {a:α}:
  (∀ b:β, has_sum (λ c:γ, f ⟨b, c⟩) (g b)) → has_sum f a → has_sum g a :=
begin
  /-
    The proof of this basically leverages the equivalence of (Σ (b : β), γ) and β × γ.
    has_sum_sigma can be utilized.
  -/
  intros A1 A2,
  let γ2:=λ b:β, γ,
  let f2:=λ p:(Σ (b : β), γ2 b), f ((@equiv.sigma_equiv_prod β γ).to_fun p),
  begin
    --have AX:(λ (b:β), γ) ≃ β × γ := equiv.sigma_equiv_prod β γ,

    --rw @equiv.sigma_equiv_prod,
    have A3:has_sum f2 a,
    {
      have A3B:f2 = λ p:(Σ (b : β), γ2 b), f ((@equiv.sigma_equiv_prod β γ).to_fun p) := rfl,
      rw A3B,
      apply equiv_sigma_prod_sum A2,
    },
    apply @has_sum.sigma α β ACM T TAM R γ2 f2 g a  A3 A1,
  end
end


lemma summable_prod {α β:Type*} [ACM:add_comm_group α]
   [R:uniform_space α] [R2:regular_space α]  [TAM:has_continuous_add α]
   [UAG:uniform_add_group α] [C:complete_space α]
    {γ:Type*} {f:β × γ → α}:
  summable f → summable (λ b:β, ∑' c:γ, f ⟨b, c⟩) :=
begin
  intro A0,
  have A1:(∀ b:β, summable (λ c:γ, f ⟨b, c⟩)),
  {
    intro b,
    apply @summable_right_of_summable3 α β γ ACM R UAG C f b A0,
  },
  let g := (λ b:β, ∑' c:γ, f ⟨b, c⟩),
  let a := (∑' p:β × γ, f p),
  begin
    have A2:g = (λ b:β, ∑' c:γ, f ⟨b, c⟩) := rfl,
    have A2A:a = (∑' p:β × γ, f p) := rfl,

    have A3:(∀ b:β, has_sum (λ c:γ, f ⟨b, c⟩) (g b)),
    {
      intro b,
      rw A2,
      simp,
      apply has_sum_tsum,
      apply A1 b,
    },
    unfold summable,
    apply exists.intro a,
    rw ← A2,
    apply has_sum_prod A3,
    rw A2A,
    apply has_sum_tsum,
    apply A0,
  end
end

lemma has_sum_prod2 {α β:Type*} [ACM:add_comm_monoid α] [T:topological_space α]
  [TAM:has_continuous_add α] [R:regular_space α] {γ:Type*} {f:β × γ → α} {g:γ → α} {a:α}:
  (∀ c:γ, has_sum (λ b:β, f ⟨b, c⟩) (g c)) → has_sum f a → has_sum g a :=
begin
  intros A1 A2,
  let f2 := λ p:(γ × β), f ((@equiv.prod_comm γ β).to_fun p),
  begin
    have A3:has_sum f2 a,
    {
      have A3B:f2 = λ p:(γ × β), f ((@equiv.prod_comm γ β).to_fun p) := rfl,
      rw A3B,
      apply equiv_prod_comm_sum A2,
    },
    apply @has_sum_prod α γ ACM T TAM R β f2 g a A1 A3,
  end
end


lemma summable_prod2 {α β:Type*} [ACM:add_comm_group α]
   [R:uniform_space α] [R2:regular_space α]  [TAM:has_continuous_add α]
   [UAG:uniform_add_group α] [C:complete_space α]
    {γ:Type*} {f:β × γ → α}:
  summable f → summable (λ c:γ, ∑' b:β, f ⟨b, c⟩) :=
begin
  intro A1,
  let f2 := λ p:(γ × β), f ((@equiv.prod_comm γ β).to_fun p),
  begin
    have A4:f2=λ p:(γ × β), f ((@equiv.prod_comm γ β).to_fun p) := rfl,
    have A5:f2=f ∘ (@equiv.prod_comm γ β) := rfl,
    have A2:summable f2,
    {
       rw A5,
       have A6:= equiv_to_fun_injective (@equiv.prod_comm γ β),
       apply summable.comp_injective A1 A6,
    },
    have A3:summable (λ b:γ, ∑' c:β, f2 ⟨b, c⟩) := summable_prod A2,
    rw A4 at A3,
    simp at A3,
    apply A3,
  end
end

lemma summable_prod2_real {β:Type*}
    {γ:Type*} {f:β × γ → ℝ}:
  summable f → summable (λ c:γ, ∑' b:β, f ⟨b, c⟩) :=
begin
  apply summable_prod2,
end

lemma summable_prod3_real {β:Type*}
    {γ:Type*} {f:β → γ → ℝ}:
  summable (function.uncurry f) → summable (λ c:γ, ∑' b:β, f b c) :=
begin
  intro A1,
  let g := (function.uncurry f),
  begin
    have A2:summable (λ c:γ, ∑' b:β, g ⟨b, c⟩),
    {
      apply summable_prod2_real,
      apply A1,
    },
    have A3:(λ c:γ, ∑' b:β, g ⟨b, c⟩) = (λ c:γ, ∑' b:β, f b c),
    {
      ext c,
      have A3A:(λ b, g ⟨b, c⟩)=(λ b, f b c),
      {
        ext b,
        refl,
      },
      rw A3A,
    },
    rw ← A3,
    apply A2,
  end
end



lemma fubinis_theorem_discrete_left2 {f:ℕ → ℕ → ℝ} {X:ℝ}:
  has_sum (λ p:ℕ × ℕ,f p.fst p.snd) X →
  has_sum (λ i, ∑' j, f i j) X :=
begin
  intro A2,
  have A1:=has_sum.summable A2,
  let f2:ℕ × ℕ → ℝ := (λ p:ℕ × ℕ,f p.fst p.snd),
  let g:ℕ → ℝ := λ i:ℕ, ∑' j:ℕ, f2 ⟨i, j⟩,
  begin
    have A4:g = λ i:ℕ, ∑' j:ℕ, f2 ⟨i, j⟩ := rfl,
    have A8:f2 = (λ  (p:ℕ × ℕ), f p.fst p.snd) := rfl,
    have A3:(∀ i:ℕ, has_sum (λ j:ℕ, f2 ⟨i, j⟩) (g i)),
    {
      intro i,
      have A3A:summable (λ j:ℕ, f2 ⟨i, j⟩) := @summable_right_of_summable2 f2 i A1,
      have A3D:=has_sum_tsum A3A,
      rw A4,
      simp,
      apply A3D,
    },
    apply has_sum_prod A3 A2,
  end
end

lemma fubinis_theorem_discrete_left {f:ℕ → ℕ → ℝ}:
  summable (λ p:ℕ × ℕ,f p.fst p.snd) →
  (∑'  (p:ℕ × ℕ), f p.fst p.snd) = (∑' i, ∑' j, f i j) :=
begin
  intro A1,
  cases (summable_elim A1) with X A2,
  have A3:=fubinis_theorem_discrete_left2 A2,
  rw tsum_replace A2,
  rw tsum_replace A3,
end

lemma fubinis_theorem_discrete_right {f:ℕ → ℕ → ℝ}:
  summable (λ p:ℕ × ℕ,f p.fst p.snd) →
  (∑'  (p:ℕ × ℕ), f p.fst p.snd) = (∑' j, ∑' i, f i j) :=
begin
  intro A1,
  cases (summable_elim A1) with X A2,
  let f2:ℕ × ℕ → ℝ := (λ p:ℕ × ℕ,f p.fst p.snd),
  let g:ℕ → ℝ := λ i:ℕ, ∑' j:ℕ, f2 ⟨j, i⟩,
  begin
    have A4:g = λ i:ℕ, ∑' j:ℕ, f2 ⟨j, i⟩ := rfl,
    have A8:f2 = (λ  (p:ℕ × ℕ), f p.fst p.snd) := rfl,
    have A5:summable f2,
    {
      rw A8,
      apply A1,
    },
    have A3:(∀ i:ℕ, has_sum (λ j:ℕ, f2 ⟨j, i⟩) (g i)),
    {
      intro i,
      have A3A:summable (λ j:ℕ, f2 ⟨j, i⟩) := @summable_left_of_summable2 f2 i A5,
      have A3D:=has_sum_tsum A3A,
      rw A4,
      simp,
      apply A3D,
    },
    cases A5 with a A6,
    have A7:has_sum g a := has_sum_prod2 A3 A6,
    rw ← A8,
    rw tsum_replace A6,
    rw tsum_replace A7,
  end
end

lemma fubinis_theorem_discrete {f:ℕ → ℕ → ℝ}:
  summable (λ p:ℕ × ℕ,f p.fst p.snd) →
  (∑' i, ∑' j, f i j) =  (∑' i, ∑' j, f j i) :=
begin
  intro A1,
  have A2:(∑'  (p:ℕ × ℕ), f p.fst p.snd) = (∑' j, ∑' i, f i j) := fubinis_theorem_discrete_right A1,
  have A3:(∑'  (p:ℕ × ℕ), f p.fst p.snd) = (∑' i, ∑' j, f i j) := fubinis_theorem_discrete_left A1,
  apply trans,
  symmetry,
  apply A3,
  apply A2,
end




lemma curry_def {α β γ:Type*}:@function.curry α β γ = λ (f:α × β → γ) (a:α) (b:β), f (a, b) := rfl



lemma unique_right_inverse_def {α β:Type*} {f:α → β} {g h:β → α}:
  f ∘ g = f ∘ h →
  function.left_inverse g f →
  g = h :=
begin
  intros A1 A2,
  ext b,
  have A3:f (g b) = f (h b),
  {
    have A3A:(f ∘ g) b = (f ∘ h) b,
    {
      rw A1,
    },
    simp at A3A,
    apply A3A,
  },
  have A4:g (f (g b)) = g (f (h b)),
  {
    rw A3,
  },
  unfold function.left_inverse at A2,
  rw A2 at A4,
  rw A2 at A4,
  apply A4,
end

lemma left_inverse_uncurry_curry {α β γ:Type*}:
   function.left_inverse (@function.uncurry α β γ) (@function.curry α β γ) :=
begin
  unfold function.left_inverse,
  intro f,
  simp,
end

/-
  While being the true definition, this gets us into trouble,
  simplifying to prod.rec. uncurry_def2 is more useful.
-/
lemma uncurry_def {α β γ:Type*}:@function.uncurry α β γ =
    λ f ⟨a, b⟩, f a b :=
begin
  have A1:(@function.curry α β γ)∘ ((@function.uncurry α β γ)) =
          function.curry  ∘ (λ f ⟨a, b⟩, f a b),
  {
    ext f,
    simp,
    rw curry_def,
  },
  apply unique_right_inverse_def A1 left_inverse_uncurry_curry,
end

lemma id_rhs_def {α:Type*} {a:α}:id_rhs α a = a := rfl

lemma uncurry_def2 {α β γ:Type*}:@function.uncurry α β γ =
    λ f p, f p.fst p.snd :=
begin
  have A1:(@function.curry α β γ)∘ ((@function.uncurry α β γ)) =
          function.curry  ∘ (λ f p, f p.fst p.snd),
  {
    ext f,
    simp,
    rw curry_def,
  },
  apply unique_right_inverse_def A1 left_inverse_uncurry_curry,
end

lemma uncurry_def3 {α β γ:Type*} {g:α → β → γ} {a:α} {b:β}:
    function.uncurry g (prod.mk a b) = g a b :=
begin
  rw uncurry_def2,
end


lemma uncurry_abs {α β:Type*} {f:α → β → ℝ}:abs ∘ (function.uncurry f)  =
   function.uncurry (λ a:α, abs ∘ f a) :=
begin
  ext ab,
  rw uncurry_def2,
end






lemma tsum_tsum_conditional_sum_conditional_sum_of_summable {f:ℕ → ℕ → ℝ}:
  summable (function.uncurry f) →
  (∑' j, ∑' i, f i j) = (∑ₚ n, ∑ₚ m, f m n) :=
begin
  intro A0,
  have B1:summable (λ p:ℕ × ℕ, f p.fst p.snd),
  {
    have A2A:(function.uncurry f) = (λ p:ℕ × ℕ, f p.fst p.snd),
    {
      rw uncurry_def2,
    },
    rw ← A2A,
    apply A0,
  },
  have B2:∀ i:ℕ, summable (λ j:ℕ, f j i),
  {
    intro i,
    apply summable_left_of_summable B1,
  },

  let g:ℕ → ℝ := λ i:ℕ, ∑' j:ℕ, f j i,
  begin
    -- Delete this
    have A2:∀ i, has_sum (λ j, f j i) (∑' j:ℕ, f j i),
    {
      intro i,
      apply has_sum_tsum,
      apply B2 i,
    },
    --have A3:∀ i, has_conditional_sum (λ j, f j i) (∑' j:ℕ, f j i),
    have A4:∀ i, conditional_sum (λ j, f j i) = (∑' j:ℕ, f j i),
    {
      intro i,
      symmetry,
      apply tsum_eq_conditional_sum_of_summable,
      apply B2 i,
    },
    have A5:(λ i, conditional_sum (λ j, f j i)) = (λ i, (∑' j:ℕ, f j i)),
    {
      ext i,
      apply A4,
    },
    rw A5,
    have A7:summable (λ i, (∑' j:ℕ, f j i)),
    {
      apply summable_prod3_real A0,
    },
    have A8:tsum (λ i, (∑' j:ℕ, f j i)) = conditional_sum (λ i, (∑' j:ℕ, f j i))
        := tsum_eq_conditional_sum_of_summable A7,
    rw A8,
  end

end


lemma tsum_tsum_conditional_sum_conditional_sum_of_summable2 {f:ℕ → ℕ → ℝ}:
  summable (function.uncurry f) →
  (∑' j, ∑' i, f j i) = (∑ₚ n, ∑ₚ m, f n m) :=
begin
  intro A0,
  let g:ℕ → ℕ → ℝ := λ m:ℕ, λ n:ℕ, f n m,
  begin
    have A3:g = (λ m:ℕ, λ n:ℕ, f n m) := rfl,
    have A1:summable (function.uncurry g),
    {
      rw A3,
      have A1A:(function.uncurry f) ∘ ((@equiv.prod_comm ℕ ℕ).to_fun) = (function.uncurry g),
      {
        rw uncurry_def2,
        rw A3,
        --simp,
        ext p,
        simp,
      },
      rw ← A1A,
      have A1B:= equiv_to_fun_injective (@equiv.prod_comm ℕ ℕ),
      apply summable.comp_injective,
      apply A0,
      apply A1B,
    },
    have A2:=tsum_tsum_conditional_sum_conditional_sum_of_summable A1,
    rw A3 at A2,
    simp at A2,
    simp,
    apply A2,
  end
end


lemma summable_iff_has_sum_tsum {α β:Type*} [add_comm_monoid α]
    [add_comm_monoid α] [topological_space α] {f : β → α}:
    summable f ↔ has_sum f (∑' (b : β), f b) :=
begin
  split;intro A1,
  {
    apply has_sum_tsum A1,
  },
  {
    apply summable_intro A1,
  }
end

lemma tsum_nonneg2 {β:Type*} {f:β → ℝ}:
  0 ≤ f → 0 ≤ tsum f :=
begin
  intro A1,
  apply tsum_nonneg,
  intro b,
  apply A1,
end

lemma op_has_sum_le_has_sum_op {β:Type*} [decidable_eq β] {f:β → ℝ} {g:ℝ → ℝ} {x y:ℝ}:
  (∀ S:finset β, g (S.sum f) ≤ S.sum (g ∘ f)) →
  continuous g →
  has_sum f x →
  has_sum (g ∘ f) y →
  g x ≤ y :=
begin
  intros A1 A2 A3 A4,
  apply le_of_not_lt,
  intro A5,
  /-
    Proof by contradiction.
    Assume y < g x.
    If we set ε = (g x - y)/2, because g is continuous, then there should exist a δ > 0
    such that if   |x' - x| < δ, then |g x' - g x| < ε. Now, there must exist a set (S:finset β)
    such that for all supersets T of S, |T.sum f - x| < δ. Thus, g (T.sum f) ≤ T.sum (g ∘ f),
    and therefore g x - (ε/2) < T.sum (g ∘ f).

    On the flip side, for ε/2 there exists S' such that for all supersets T' of S',
    |T'.sum (g ∘ f) - y | < ε/2. Yet, there exists S∪  S', which must be in both sets, a
    contradiction.

  -/
  let ε := (g x - y)/2,
  begin
    have A6 :0 < ε,
    {
      apply half_pos,
      apply sub_pos_of_lt A5,
    },
    have A7 := (continuous_elim x A2) ε A6,
    cases A7 with δ A8,
    cases A8 with A9 A10,
    rw ← has_sum_real at A3,
    have A11 := A3 δ A9,
    cases A11 with S A12,
    rw ← has_sum_real at A4,
    have A13 := A4 ε A6,
    cases A13 with S' A14,
    have A15 := finset.subset_union_left S S',
    have A16 := finset.subset_union_right S S',

    have A17 := A14 (S ∪ S') A16,
    have A18 := A12 (S ∪ S') A15,
    have A19 := A10 (finset.sum (S ∪ S') f) A18,
    rw abs_lt2 at A17,
    cases A17 with A20 A21,
    -- A21 : finset.sum (S ∪ S') (g ∘ f) < y + ε
    rw abs_lt2 at A19,
    cases A19 with A22 A23,
    -- A22 : g x - ε < g (finset.sum (S ∪ S') f),
    have A24 : g x - ε < finset.sum (S ∪ S') (g ∘ f),
    {
      apply lt_of_lt_of_le,
      apply A22,
      apply A1,
    },
    have A25 : g x - ε = y + ε,
    {
      have A25A:ε= (g x - y)/2 := rfl,
      apply half_equal A25A,
    },
    rw A25 at A24,
    apply lt_irrefl (finset.sum (S ∪ S') (g ∘ f)),
    apply lt_trans A21 A24,
  end
end

lemma abs_abs_sub_abs_le_abs {a b:ℝ}:
  abs (abs a - abs b) ≤ abs (a - b) :=
begin
  have A1:0 ≤ (abs a - abs b) ∨ ((abs a - abs b) < 0) := le_or_lt 0 (abs a - abs b),
  cases A1,
  {
    rw abs_of_nonneg A1,
    apply abs_sub_abs_le_abs_sub,
  },
  {
    rw abs_of_neg A1,
    rw abs_antisymm,
    have A2:-(abs a - abs b)=abs b - abs a,
    {
      simp,
    },
    rw A2,
    apply abs_sub_abs_le_abs_sub,
  }
end

lemma continuous_abs:continuous (@abs ℝ _) :=
begin
  rw ← continuous_iff_has_classical_rlimit,
  intros x ε A1,
  apply exists.intro ε,
  split,
  {
    apply A1,
  },
  {
    intros x' A2 A3,
    have A4:abs (abs x' - abs x) ≤ abs (x - x'),
    {
      rw abs_antisymm,
      apply abs_abs_sub_abs_le_abs,
    },
    apply lt_of_le_of_lt,
    apply A4,
    apply A3,
  }
end

/-
  Several functions satisfy the constraints for g.
  In particular √x, |x|, and other norms.
-/
lemma op_has_sum_le_has_sum_op2 {β:Type*} [D:decidable_eq β] {f:β → ℝ} {g:ℝ → ℝ} {x y:ℝ}:
  (∀ a b, g (a + b) ≤ (g a) + (g b)) →
  (g 0 = 0) →
  continuous g →
  has_sum f x →
  has_sum (g ∘ f) y →
  g x ≤ y :=
begin
  intros A1 A2 A3 A4 A5,
  have A6:(∀ S:finset β, g (S.sum f) ≤ S.sum (g ∘ f)),
  {
    intros S,
    apply finset.le_sum_of_subadditive _ A2 A1,
  },
  apply op_has_sum_le_has_sum_op A6 A3 A4 A5,
end


lemma abs_has_sum_le_has_sum_abs {β:Type*} [D:decidable_eq β] {f : β → ℝ} {x y:ℝ}:
  has_sum f x →
  has_sum (abs ∘ f) y →
  abs x ≤ y :=
begin
  intros A1 A2,
  have A3:abs (0:ℝ) = 0,
  {
    simp,
  },
  have A5:continuous (@abs ℝ _) := continuous_abs,
  have A7:=@abs_add_le_abs_add_abs ℝ _,
  apply op_has_sum_le_has_sum_op2 A7 A3 A5 A1 A2,
end

lemma abs_tsum_le_tsum_abs {β:Type*} [D:decidable_eq β] {f : β → ℝ}:
    abs (tsum f) ≤ tsum (abs ∘ f) :=
begin
  have A6:abs (0:ℝ) = 0,
  {
    simp,
  },
  have A1:summable f ∨ ¬(summable f) := classical.em (summable f),
  cases A1,
  {
    have A2:has_sum f (tsum f) := has_sum_tsum A1,
    have A3:summable (abs ∘ f) := (summable_iff_abs_summable.mp A1),
    have A4:has_sum (abs ∘ f) (tsum (abs ∘ f)) := has_sum_tsum A3,
    have A5:continuous (@abs ℝ _) := continuous_abs,
    apply abs_has_sum_le_has_sum_abs A2 A4,
  },
  {
    have A2:¬summable (abs ∘ f),
    {
      intro A2A,
      apply A1,
      apply summable_iff_abs_summable.mpr A2A,
    },
    unfold tsum,
    rw dif_neg,
    rw dif_neg,
    rw A6,
    apply A2,
    apply A1,
  }
end



lemma empty_finset_false {α:Type*} [decidable_eq α]:
  {x//x∈ (∅:finset α)} → false :=
begin
  intro A1,
  have A2 := A1.property,
  simp at A2,
  apply A2,
end

def empty_finset_fn {α β:Type*} [decidable_eq α]:
  {x//x∈ (∅:finset α)} → β :=
begin
  intro A1,
  exfalso,
  apply empty_finset_false A1,
end



def finset_insert_fn {α β:Type*} [D:decidable_eq α] (a:α) (b:β) (s:finset α)
  (f:{x//x∈s} → β) (x:{x//x∈ insert a s}):β := @dite (x.val ∈ s) _ β
  (λ h, (f (subtype.mk (x.val) h))) (λ _, b)


lemma coe_finset_subtype {α:Type*} [D:decidable_eq α] {S:finset α} {a:{x//x∈ S}} {a':α}:
  (a.val = a') → ((a:α)=a') :=
begin
  intro A1,
  rw ← A1,
  refl,
end


lemma finset_axiom_of_choice {α β:Type*} [D:decidable_eq α] {P:α → β → Prop} {S:finset α}:
  (∀ s∈ S, ∃ b:β, P s b) →
  (∃ (f:{x // x∈S} → β), ∀ x:{x // x∈S}, P x (f x)) :=
begin
  apply finset.induction_on S,
  {
    intro A1,
    apply exists.intro empty_finset_fn,
    intro x,
    exfalso,
    apply empty_finset_false x,
    apply D,
  },
  {
    intros a s A1 A2 A3,
    have A4:(∀ (a2 : α), a2 ∈ s → (∃ (b : β), P a2 b)),
    {
      intros a2 A4A,
      have A4B:= A3 a2,
      have A4C:a2∈ insert a s,
      {
        simp,
        right,
        exact A4A,
      },
      apply A4B A4C,
    },
    have A5 := A2 A4,
    cases A5 with f' A6,
    have A7:∃ b':β, P a b',
    {
      have A7A: a ∈ insert a s,
      {
        simp,
      },
      apply A3 a A7A,
    },
    cases A7 with b' A8,
    let f:{x // x ∈ insert a s} → β := finset_insert_fn a b' s f',
    begin
      have A9:f=finset_insert_fn a b' s f' := rfl,
      apply exists.intro f,
      intro x,
      have A10:=x.property,
      --simp at A10,
      rw finset.mem_insert at A10,
      cases A10,
      {
        have A11:f x = b',
        {
          rw A9,
          unfold finset_insert_fn,
          rw dif_neg,
          rw A10,
          apply A1,
        },
        rw A11,
        have A12:(x:α) = a,
        {
          apply coe_finset_subtype,
          apply A10,
        },
        rw A12,
        apply A8,
      },
      {
        rw A9,
        unfold finset_insert_fn,
        rw dif_pos,
        have A11:∀ a'':α,∀ h:a''∈ s, P a'' (f' (subtype.mk a'' h)),
        {
          intros a'' A11A,
          apply A6 (subtype.mk a'' A11A),
        },
        apply A11 x.val A10,
      },
    end
  }
end



def finset.Union {α β:Type*} [Dβ:decidable_eq β] {S:finset α}
   (f:{x//x∈ S}→ finset β):finset β :=
  finset.fold (@has_union.union (finset β) (@finset.has_union β Dβ))
  ∅ f (finset.attach S)


lemma finset_Union_empty {α β:Type*} [decidable_eq β]
   (f:{x//x∈ (∅:finset α)}→ finset β):finset.Union f = (∅:finset β) :=
begin
  unfold finset.Union,
  simp,
end



def finset_insert_constrain {α β:Type*} [decidable_eq α]   {a:α} {S:finset α}
  (f:{x//x∈ (insert a S)}→ β) (s:{x//x∈ S}):β := f (subtype.mk s.val
  (finset.mem_insert_of_mem s.property) )

lemma finset_insert_constrain_def {α β:Type*} [decidable_eq α]   {a:α} {S:finset α}
  (f:{x//x∈ (insert a S)}→ β) (s:{x//x∈ S}):
  finset_insert_constrain f s = f (subtype.mk s.val (finset.mem_insert_of_mem s.property) ) := rfl

lemma finset_insert_constrain_def2 {α β:Type*} [decidable_eq α]   {a:α} {S:finset α}
  (f:{x//x∈ (insert a S)}→ β):
  finset_insert_constrain f = λ (s:{x//x∈ S}),
  f (subtype.mk s.val (finset.mem_insert_of_mem s.property) ) := rfl


-- This generalizes to when a∈S too...
lemma finset_Union_insert {α β:Type*} [decidable_eq α] [decidable_eq β]  {a:α} {S:finset α}
   (f:{x//x∈ (insert a S)}→ finset β):a∉ S →
   finset.Union f = (f (subtype.mk a (finset.mem_insert_self a S)))
   ∪ (finset.Union (finset_insert_constrain f))
    :=
begin
  intro A1,
  unfold finset.Union finset_insert_constrain,
  rw finset.attach_insert,
  rw finset.fold_insert,
  rw finset_insert_constrain_def2,
  simp,
  simp,
  apply A1,
end

lemma finset_mem_Union_intro {α β:Type*} [decidable_eq α] [decidable_eq β]  {b:β} {S:finset α}:
   ∀ a:{x//x∈ S},
   ∀ f:{x//x∈ S}→ finset β,
   b∈ f a →
   b∈ finset.Union f :=
begin
  apply finset.induction_on S,
  {
    intros a f A1,
    exfalso,
    have A2 := a.property,
    apply A2,
  },
  {
    intros a s A1 A2 a' f A3,
    rw finset_Union_insert f A1,
    rw finset.mem_union,
    have A4 := a'.property,
    rw finset.mem_insert at A4,
    cases A4,
    {
      left,
      have A5:subtype.mk a _ = a',
      {
        apply subtype.eq,
        symmetry,
        apply A4,
      },
      rw A5,
      apply A3,
    },
    {
      right,
      apply A2 (subtype.mk a'.val A4),
      unfold finset_insert_constrain,
      simp,
      apply A3,
    }
  }
end

lemma finset_mem_Union_elim {α β:Type*} [decidable_eq α] [decidable_eq β]  {S:finset α}:
   ∀ f:{x//x∈ S}→ finset β,
   ∀ b∈ finset.Union f,
   ∃ a:{x//x∈ S},
   b∈ f a :=
begin
  apply finset.induction_on S,
  {
    intros f b A1,
    rw finset_Union_empty at A1,
    exfalso,
    apply A1,
  },
  {
    intros a s A1 A2 f b A3,
    rw finset_Union_insert at A3,
    rw finset.mem_union at A3,
    cases A3,
    {
      let a':{x//x∈ insert a s} := (subtype.mk a (finset.mem_insert_self a s)),
      begin
        apply exists.intro a',
        apply A3,
      end
    },
    {
      have A4 := A2 (finset_insert_constrain f) b A3,
      cases A4 with a' A5,
      let a'':{x//x∈ insert a s} := subtype.mk a'.val (finset.mem_insert_of_mem a'.property),
      begin
        apply exists.intro a'',
        unfold finset_insert_constrain at A5,
        apply A5,
      end
    },
    {
      apply A1,
    }
  }
end

def finset.relation {α β:Type*} [decidable_eq α] [decidable_eq β] {S:finset α}
   (f:{x//x∈ S}→ finset β):finset (α × β) :=
  finset.Union (λ x, finset.product ({x.val}) (f x))


lemma finset_relation_empty {α β:Type*} [decidable_eq α] [decidable_eq β]
   (f:{x//x∈ (∅:finset α)}→ finset β):finset.relation f = (∅:finset (α × β)) :=
begin
  unfold finset.relation,
  rw finset_Union_empty,
end

lemma finset_relation_insert {α β:Type*} [decidable_eq α] [decidable_eq β]  {a:α} {S:finset α}
   (f:{x//x∈ (insert a S)}→ finset β):a∉ S →
   finset.relation f =
   finset.product ({a}) (f (subtype.mk a (finset.mem_insert_self a S)))
   ∪ (finset.relation (finset_insert_constrain f)) :=
begin
  intro A1,
  unfold finset.relation,
  rw finset_Union_insert,
  refl,
  apply A1,
end

lemma mem_fst_finset_relation {α β:Type*} [decidable_eq α] [decidable_eq β] {S:finset α} {ab:α × β}
   :(∀ f:{x//x∈ S}→ finset β, ab∈ (finset.relation f) → ab.fst ∈ S) :=
begin
  apply finset.induction_on S,
  {
    intros f A1,
    rw finset_relation_empty at A1,
    apply A1,
  },
  {
    intros a s A1 A2 f A3,
    rw finset_relation_insert at A3,
    rw finset.mem_insert,
    rw finset.mem_union at A3,
    cases A3,
    {
      rw finset.mem_product at A3,
      cases A3 with A4 A5,
      simp at A4,
      left,
      apply A4,
    },
    {
      right,
      apply A2 (finset_insert_constrain f) A3,
    },
    {
      apply A1,
    }
  }
end


lemma finset_product_empty_right {α β:Type*}
  {S:finset α}:finset.product S (∅:finset β) = ∅ :=
begin
  ext ab,
  split;intros A1;exfalso;simp at A1;apply A1,
end

--This is probably in core.lean or something.
lemma and_or_distrib {P Q R:Prop}:P ∧ (Q∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
  split;intros A1,
  {
    cases A1 with A2 A3,
    cases A3,
    {
      left,
      apply and.intro A2 A3,
    },
    {
      right,
      apply and.intro A2 A3,
    }
  },
  {
    cases A1;cases A1 with A2 A3;split,
    {
      apply A2,
    },
    {
      left,apply A3,
    },
    {
      apply A2,
    },
    {
      right,apply A3,
    }
  }
end

lemma finset_product_insert_right {α β:Type*}  [decidable_eq α] [decidable_eq β]
  {A:finset α} {B:finset β} {b:β}:finset.product A (insert b B) =
  (finset.product A {b}) ∪ (finset.product A B)  :=
begin
  ext ab,
  rw finset.mem_product,
  rw finset.mem_union,
  rw finset.mem_product,
  rw finset.mem_insert,
  simp,
  apply and_or_distrib,
end

lemma finset_product_singleton {α β:Type*} {a:α} {b:β}:
    (@finset.product α β {a} {b})={prod.mk a b} :=
begin
  refl,
end


lemma finset_product_disjoint_right {α β:Type*} [decidable_eq α] [decidable_eq β]
    {A1 A2:finset α} {B1 B2:finset β}:
    disjoint B1 B2 → disjoint (finset.product A1 B1) (finset.product A2 B2) :=
begin
  intro C1,
  apply finset_disjoint_intro,
  intros ab C2,
  rw finset.mem_product at C2,
  cases C2 with C3 C4,
  have C5:ab.snd ∉ B2 := finset_disjoint_elim ab.snd C1 C4,
  intro C6,
  rw finset.mem_product at C6,
  apply C5,
  cases C6 with C7 C8,
  apply C8,
end


lemma finset_sum_uncurry {α β:Type*} [decidable_eq α] [decidable_eq β] {g:α → β → ℝ}
   {a:α} {S:finset β}:
 finset.sum (finset.product ({a}) S) (function.uncurry g) =
    finset.sum S (g a) :=
begin
  apply finset.induction_on S,
  {
    rw finset_product_empty_right,
    simp,
  },
  {
    intros a2 S2 A1 A2,
    rw finset_product_insert_right,
    rw finset.sum_union,
    rw A2,
    rw finset_product_singleton,
    rw finset.sum_singleton,
    rw finset.sum_insert,
    rw uncurry_def3,
    apply A1,
    apply finset_product_disjoint_right,
    simp,
    apply A1,
  }
end

lemma finset_relation_sum {α β:Type*} [decidable_eq α] [decidable_eq β] {g:α → β → ℝ}
   {S:finset α}:∀ f:{x//x∈ S}→ finset β,
  (finset.relation f).sum (function.uncurry g) =
  (finset.attach S).sum (λ x, (f x).sum (g x.val)) :=
begin
  apply finset.induction_on S,
  {
    intro f,
    rw finset_relation_empty,
    simp,
  },
  {
    intros a s A1 A2 f,
    rw finset.attach_insert,
    rw finset.sum_insert,
    rw finset_relation_insert,
    rw finset.sum_union,
    rw A2 (finset_insert_constrain f),
    rw finset_insert_constrain_def2,
    simp,
    rw finset_sum_uncurry,
    {
      apply finset_disjoint_intro,
      intros ab A3,
      intro A4,
      apply A1,
      rw finset.mem_product at A3,
      cases A3 with A5 A6,
      rw finset.mem_singleton at A5,
      rw ← A5,
      apply mem_fst_finset_relation (finset_insert_constrain f) A4,
    },
    {
      apply A1,
    },
    {
      simp,
      apply A1,
    }
  }
end


lemma finset_mem_relation  {α β:Type*} [decidable_eq α] [decidable_eq β] {S:finset α} {ab:α × β}
   {f:{x//x∈ S}→ finset β}
   :(ab ∈ (finset.relation f)) ↔ (∃ H:ab.fst∈ S, ab.snd∈ f (subtype.mk ab.fst H)) :=
begin
  -- If there was a finset_mem_Union, this proof would be easier.
  split;intros A1,
  {
    unfold finset.relation at A1,
    have A2:=finset_mem_Union_elim _ ab A1,
    cases A2 with a A3,
    simp at A3,
    cases A3 with A4 A5,
    have A4':ab.fst = a.val,
    {
      rw A4,
      refl,  
    },
    have A6:=a.property,
    rw ← A4' at A6,
    apply exists.intro A6,
    have A7:a = ⟨ ab.fst, A6 ⟩,
    {
      apply subtype.eq,
      simp,
      symmetry,
      apply A4,
    },
    rw ← A7,
    apply A5,
  },
  {
    unfold finset.relation,
    cases A1 with A2 A3,
    apply finset_mem_Union_intro ⟨ab.fst, A2⟩,
    rw finset.mem_product,
    split,
    {
      rw finset.mem_singleton,
    },
    {
      apply A3,
    }
  }
end


lemma bdd_above_def3 {α:Type*}  [preorder α] {S:set α}:
(bdd_above S) ↔ (∃ (x : α), x ∈ upper_bounds S) :=
begin
  rw bdd_above_def,
  unfold set.nonempty,
end

lemma bdd_above_def2 {α:Type*}  [preorder α] {S:set α}:
(bdd_above S) ↔ (∃ (x : α), ∀ s∈ S, s ≤ x) :=
begin
  rw bdd_above_def3,
  unfold upper_bounds,
  simp,
end

def proj_left {α β:Type*} [decidable_eq α] (S:finset (α × β)):finset α :=
  multiset.to_finset (multiset.map (@prod.fst α β) S.val)

lemma proj_left_def {α β:Type*} [decidable_eq α] (S:finset (α × β)):
  proj_left S = multiset.to_finset (multiset.map (@prod.fst α β) S.val) := rfl


lemma mem_proj_left {α β:Type*} [decidable_eq α] {S:finset (α × β)} {a:α}:
    a∈ proj_left S ↔ (∃ b:β, prod.mk a b ∈ S) :=
begin
  split;intros A1,
  {
    rw proj_left_def at A1,
    simp at A1,
    apply A1,
  },
  {
    rw proj_left_def,
    simp,
    apply A1,
  }
end

def proj_right {α β:Type*} [decidable_eq β] (S:finset (α × β)):finset β :=
  multiset.to_finset (multiset.map (@prod.snd α β) S.val)

lemma proj_right_def {α β:Type*} [decidable_eq β] (S:finset (α × β)):
  proj_right S = multiset.to_finset (multiset.map (@prod.snd α β) S.val) := rfl


lemma mem_proj_right {α β:Type*} [decidable_eq β] {S:finset (α × β)} {b:β}:
    b ∈ proj_right S ↔ (∃ a:α, prod.mk a b ∈ S) :=
begin
  split;intros A1,
  {
    rw proj_right_def at A1,
    simp at A1,
    apply A1,
  },
  {
    rw proj_right_def,
    simp,
    apply A1,
  }
end

def decidable_pred_eq_fst {α β:Type*} [D:decidable_eq α] {a:α}:
    decidable_pred (λ ab:α× β, a=ab.fst) := (λ ab:α× β, D a ab.fst)

def image_right {α β:Type*} [decidable_eq α] [decidable_eq β] (S:finset (α × β)) (a:α):finset β :=
    proj_right (@finset.filter (α × β) (λ ab:α× β, a=ab.fst) (@decidable_pred_eq_fst α β _ a) S)



def finset_mem_image_right {α β:Type*} [decidable_eq α] [decidable_eq β] {S:finset (α × β)}
    {a:α} {b:β}:b∈ image_right S a ↔ prod.mk a b ∈ S :=
begin
  unfold image_right,
  rw mem_proj_right,
  split,intros A1,
  {
    cases A1 with a' A2,
    rw finset.mem_filter at A2,
    cases A2 with A3 A4,
    simp at A4,
    subst A4,
    apply A3,
  },
  {
    intro A2,
    apply exists.intro a,
    rw finset.mem_filter,
    split,
    apply A2,
    refl,
  }
end


lemma finset_relation_image_right {α β:Type*} [decidable_eq α] [decidable_eq β]
    {S:finset (α × β)}:
    (finset.relation (λ a:{x//x ∈ (proj_left S)}, image_right S (a.val))) = S :=
begin
  ext ab,
  rw finset_mem_relation,
  split;intros A1,
  {
    cases A1 with A2 A3,
    rw finset_mem_image_right at A3,
    simp at A3,
    apply A3,
  },
  {
    have A2:∃ b:β, prod.mk ab.fst b ∈ S,
    {
      apply exists.intro ab.snd,
      simp,
      apply A1,
    },
    rw ← mem_proj_left at A2,
    apply exists.intro A2,
    simp,
    rw finset_mem_image_right,
    simp,
    apply A1,
  }
end

--Should replace with finset.sum_attach, but the call site is complex.
lemma finset_sum_attach_simp {α:Type*} {S:finset α} [decidable_eq α] {f:α → ℝ}:
  (finset.attach S).sum (λ x, f (x.val)) = S.sum f :=
begin
  apply finset.sum_attach,
end
/-
  Okay I am revisiting this proof YET AGAIN.
  First, we switch to absolute values. In fact, it is probably a better
  idea to first prove this for 0 ≤ f, and then prove it in general.

  Okay, assuming 0 ≤ f, then we need to prove that
  tsum (λ n:ℕ, tsum ((f n))) is an upper bound for any S:finset (N× N),
  S.sum (function.uncurry f). All we have to do is divide the function by


  What I need to prove is that there exists an upper bound on any
  finite sum. In particular, one can break apart any finite sum into pieces,
  based upon projections into the first index.

-/

lemma mem_upper_bounds_range_elim {α:Type*} {x:ℝ} {f:α → ℝ} {a:α}:
  x ∈ upper_bounds (set.range f) →
  f a ≤ x :=
begin
  intro A1,
  unfold upper_bounds at A1,
  simp at A1,
  have A2:f a = f a := rfl,
  apply A1 a A2,
end

lemma summable_function_uncurry4 {f:ℕ → ℕ → ℝ}:
  0 ≤ f →
  (∀ i:ℕ, summable (f i)) →
  summable (λ n:ℕ, tsum (f n)) →
  summable (function.uncurry f) :=
begin
  intros A1 A2 A3,
  apply summable_of_bdd_above,
  {
    rw le_func_def,
    intro ab,
    rw uncurry_def2,
    simp,
    apply A1,
  },
  rw bdd_above_def2,
  apply exists.intro (tsum (λ n:ℕ, tsum (f n))),
  intros x A4,
  simp at A4,
  cases A4 with S A6,
  subst x,
  have A7:=@finset_relation_image_right _ _ _ _ S,
  rw ← A7,
  rw finset_relation_sum,
  have A8:finset.sum (finset.attach (proj_left S))
      (λ (x : {x // x ∈ proj_left S}), finset.sum (image_right S (x.val)) (f (x.val))) ≤
          finset.sum (finset.attach (proj_left S))
      (λ (x : {x // x ∈ proj_left S}), tsum (f (x.val))),
  {
    apply finset_sum_le2,
    intros x A8X,
    have A8A:=A2 (x.val),
    have A8B:0 ≤ (f (x.val)),
    {
      apply A1,
    },
    have A8C:= tsum_in_upper_bounds_of_summable A8B A8A,
    apply mem_upper_bounds_range_elim A8C,
  },
  apply le_trans,
  apply A8,
  rw @finset_sum_attach_simp ℕ (proj_left S) _ (λ n,(tsum (f n))),
  have A9:(0:ℕ → ℝ) ≤ (λ n:ℕ, tsum (f n)),
  {
    rw le_func_def,
    intro n,
    apply tsum_nonneg2,
    apply A1,
  },
  have A10:= tsum_in_upper_bounds_of_summable A9 A3,
  apply mem_upper_bounds_range_elim A10,
end



--def finset_p (a:ℕ) (S:finset ℕ):=finset.product (finset.singleton a) S
--lemma finset_union




--Rearrange the indices to be in order.
lemma summable_function_uncurry3 {f:ℕ → ℕ → ℝ}:
  (∀ i:ℕ, summable (f i)) →
  summable (λ n:ℕ, tsum (abs ∘ (f n))) →
  summable (function.uncurry f) :=
begin
  /-
    Consider g = (λ a:ℕ, abs ∘ (f n)), the absolute variant of f.
    We prove summable (function.uncurry g) using summable_function_uncurry4,
    and then prove the result here.
  -/
  let g := (λ a:ℕ, abs ∘ (f a)),
  begin
    intros A1 A2,
    have A3:g = (λ a:ℕ, abs ∘ (f a)) := rfl,
    have A4:(0:ℕ → ℕ → ℝ)≤ g,
    {
      rw A3,
      have A4A:∀ a:ℕ, (0:ℕ → ℕ → ℝ) a ≤ g a,
      {
        intro a,
        rw le_func_def,
        rw A3,
        intro b,
        simp,
        apply abs_nonneg,
      },
      apply A4A,
    },
    have A5:(∀ i:ℕ, summable (g i)),
    {

      intro i,
      rw ← summable_iff_abs_summable,
      apply A1,
    },
    have A6:summable (λ n:ℕ, tsum ((g n))),
    {
      rw A3,
      simp,
      apply A2,
    },
    rw summable_iff_abs_summable,
    have A7:abs ∘ function.uncurry f = function.uncurry g,
    {
      rw A3,
      rw uncurry_def2,
    },
    rw A7,
    apply summable_function_uncurry4 A4 A5 A6,
  end
end

lemma summable_function_uncurry {f:ℕ → ℕ → ℝ}:
  (∀ i:ℕ, absolutely_summable (f i)) →
  conditionally_summable (λ n:ℕ,conditional_sum (abs ∘ (f n))) →
  summable (function.uncurry f) :=
begin
  intros A1 A2,
  have A3:∀ i:ℕ, summable (f i),
  {
    intro i,
    rw ← absolutely_summable_def,
    apply A1,
  },
  have A3B:∀ i:ℕ, summable (abs ∘ (f i)),
  {
    intro i,
    rw ← summable_iff_abs_summable,
    apply A3,
  },

  let g := (λ n:ℕ,conditional_sum (abs ∘ (f n))),
  begin
    have A4:∀ n:ℕ, conditional_sum (abs ∘ (f n))=tsum (abs ∘ (f n)),
    {
       intro n,
       symmetry,
       apply tsum_eq_conditional_sum_of_summable,
       apply A3B n,
    },
    have A5:conditionally_summable (λ n:ℕ,tsum (abs ∘ (f n))),
    {
       have A5A:(λ n:ℕ,conditional_sum (abs ∘ (f n)))= (λ n:ℕ,tsum (abs ∘ (f n))),
       {
         ext n,
         apply A4,
       },
       rw ← A5A,
       apply A2,
    },
    have A6:summable (λ n:ℕ,tsum (abs ∘ (f n))),
    {
       have A6A:(0:ℕ → ℝ) ≤ (λ n:ℕ,tsum (abs ∘ (f n))),
       {
         rw le_func_def,
         intro n,
         apply tsum_nonneg2,
         rw le_func_def,
         intro n2,
         apply abs_nonneg,
       },
       apply summable_of_nonneg_of_conditionally_summable A6A A5,
    },
    apply summable_function_uncurry3 A3 A6,
  end
end

lemma fubinis_theorem_discrete2 {f:ℕ → ℕ → ℝ}:
  (∀ i:ℕ, absolutely_summable (f i)) →
  conditionally_summable (λ n:ℕ,conditional_sum (abs ∘ (f n))) →
  (∑ₚ m, ∑ₚ n, f m n) = (∑ₚ n, ∑ₚ m, f m n) :=
begin
  intros A1 A2,
  have A3:summable (function.uncurry f) := summable_function_uncurry A1 A2,
  have A4: (∑' j, ∑' i, f j i) = (∑ₚ n, ∑ₚ m, f n m)
     := tsum_tsum_conditional_sum_conditional_sum_of_summable2 A3,
  have A5:(∑' j, ∑' i, f i j) = (∑ₚ n, ∑ₚ m, f m n) :=
      tsum_tsum_conditional_sum_conditional_sum_of_summable A3,
  rw ← A4,
  rw ← A5,
  apply fubinis_theorem_discrete,
  rw function.uncurry_def at A3,
  apply A3,
end


lemma pair_conditional_sum_subst {g h:ℕ → ℕ → ℝ}:
g = h →
(∑ₚ  (m n : ℕ), (g m n)) =
(∑ₚ  (m n : ℕ), (h m n)) :=
begin
  intro A1,
  rw A1,
end


lemma fubinis_theorem_discrete3 {g:ℕ → ℕ → ℝ}:
  conditionally_summable (λ n:ℕ,(finset.range n).sum (abs ∘ (g n))) →
  conditional_sum (λ n:ℕ,(finset.range n).sum ((g n))) =
  conditional_sum (λ m:ℕ, conditional_sum_lb (m + 1) (λ n:ℕ, g n m)) :=
begin
  intro A1,
  --∑' n, ∑_m=0^n-1 (g n m)
  let h:ℕ→ ℕ → ℝ:=λ m n, if (n < m) then (g m n) else (0:ℝ),
  begin
    have A1B:h = λ m n, if (n < m) then (g m n) else (0:ℝ) := rfl,
    -- A1C required.
    have A1E:∀ n, (∀ (b : ℕ), b ∉ (finset.range n) → (h n) b = 0),
    {
      intros n m A1EA,
      have A1EB:¬ (m < n),
      {
        intro A1EB1,
        apply A1EA,
        rw finset.mem_range,
        apply A1EB1,
      },
      rw A1B,
      simp,
      rw if_neg,
      apply A1EB,
    },
    have A1C:∀ n, summable (h n),
    {
      intro n,
      apply summable_of_ne_finset_zero,
      apply A1E,
    },
    have A1D:∀ n, ∀ m∈ (finset.range n), (h n) m=(g n) m,
    {
      intros n m A1D1,
      rw A1B,
      rw finset.mem_range at A1D1,
      simp,
      rw if_pos,
      apply A1D1,
    },
    have A2:∀ n, tsum (h n) = (finset.range n).sum (g n),
    {
      intro n,
      have A2A:tsum (h n) = (finset.range n).sum (h n),
      {
        rw tsum_eq_sum,
        apply A1E,
      },
      rw A2A,
      rw finset_sum_subst2 (A1D n),
    },
    have A3:∀ n, absolutely_summable (h n),
    {
      intro n,
      rw absolutely_summable_def,
      apply A1C,
    },
    have A4:∀ n, summable (abs ∘ (h n)),
    {
      intro n,
      have A4A:=A1C n,
      rw summable_iff_abs_summable at A4A,
      apply A4A,
    },
    -- Similar to proof of A2 above.
    have A5:∀ n, tsum (abs ∘ (h n)) = (finset.range n).sum (abs ∘ (g n)),
    {
      intro n,
      have A5A:(∀ (b : ℕ), b ∉ (finset.range n) → (abs ∘ (h n)) b = 0),
      {
        intros m A5A1,
        simp,
        apply A1E n m A5A1,
      },
      have A5B:tsum (abs ∘ (h n)) = (finset.range n).sum (abs ∘ (h n)),
      {
        rw tsum_eq_sum,
        apply A5A,
      },
      rw A5B,
      have A5C:∀ m∈ (finset.range n), (abs ∘ (h n)) m=(abs ∘ (g n)) m,
      {
        intros m A5C1,
        have A5C2 := A1D n m A5C1,
        simp,
        rw A5C2,
      },
      rw finset_sum_subst2 (A5C),
    },
    have A6:∀ n, conditional_sum (abs ∘ (h n)) = (finset.range n).sum (abs ∘ (g n)),
    {
      intro n,
      rw ← tsum_eq_conditional_sum_of_summable (A4 n),
      apply A5,
    },
    -- A7 Required
    have A7:conditionally_summable (λ n:ℕ,conditional_sum (abs ∘ (h n))),
    {
      have A7A:(λ (n:ℕ), conditional_sum (abs ∘ (h n))) =
          (λ (n : ℕ), finset.sum (finset.range n) (abs ∘ g n)),
      {
        ext n,
        apply A6,
      },
      rw A7A,
      apply A1,
    },
    -- A8 Required
    have A8:(λ n:ℕ,(finset.range n).sum (g n)) = (λ n, conditional_sum (h n)),
    {
      ext n,
      rw ← tsum_eq_conditional_sum_of_summable (A1C n),
      rw (A2 n),
    },
    rw A8,
    unfold conditional_sum_lb,
    have A9: (∑ₚ  (m n : ℕ), ite (m + 1 ≤ n) (g n m) 0)=
    (∑ₚ  (m n : ℕ), h n m),
    {
      apply pair_conditional_sum_subst,
      ext m n,
      rw A1B,
      simp,
      have A9A:m < n ∨ n ≤ m := lt_or_le m n,
      cases A9A,
      {
        rw if_pos,
        rw if_pos,
        apply A9A,
        apply A9A,
      },
      {
        rw if_neg,
        rw if_neg,
        apply not_lt_of_le A9A,
        simp,
        rw nat.lt_succ_iff,
        apply A9A,
      }
    },
    rw A9,
    apply fubinis_theorem_discrete2,
    apply A3,
    apply A7,
  end
end



lemma bounded_maclaurin_def {f:ℕ → ℝ}:
  bounded_maclaurin f  ↔ (∀ x, has_classical_limit (λ (n : ℕ), x ^ n * f n) 0)  :=
begin
  refl
end

lemma bounded_maclaurin_intro {f:ℕ → ℝ}:
  (∀ x, x≠ 0 → has_classical_limit (λ (n : ℕ), x ^ n * f n) 0) →
  bounded_maclaurin f :=
begin
  intros A1 x,
  have A2:x = 0 ∨ x ≠ 0 := eq_or_ne,
  cases A2,
  {
    rw A2,
    rw (@has_classical_limit_offset _ _ 1),
    have B1:(λ n:ℕ, 1 + n) = nat.succ,
    {
      ext n,
      rw nat_succ_one_add,
    },
    rw B1,
    have A3:((λ (n : ℕ), 0 ^ n * f n) ∘ (nat.succ)) = (λ n:ℕ, 0),
    {
      ext n,
      simp,
      left,
      apply pow_zero_eq_zero_if_pos,
      simp,
    },
    rw A3,
    apply has_classical_limit_const,
  },
  {
    apply A1 x A2,
  }
end



lemma bounded_maclaurin_succ {f:ℕ → ℝ}:
  bounded_maclaurin f →
  bounded_maclaurin (f ∘ nat.succ) :=
begin
  unfold bounded_maclaurin,
  intros A1 x,
  apply bounded_maclaurin_intro,
  intros x A2,
  have A3:(λ (n : ℕ), x ^ n * (f ∘ nat.succ) n) =
          (λ (n : ℕ), x⁻¹ * (x ^ (nat.succ n) * (f ∘ nat.succ) n)),
  {
    ext n,
    simp,
    rw nat_succ_pow,
    rw ← mul_assoc,
    rw ← mul_assoc,
    rw inv_mul_cancel A2,
    rw one_mul,
  },
  rw A3,
  apply has_classical_limit_mul_const_zero,
  have A5:(λ (n : ℕ), x ^ (nat.succ n) * (f ∘ nat.succ) n) =
       ((λ (n : ℕ), x ^ n * f n) ∘ (λ n:ℕ, 1 + n)),
  {
    ext n,
    simp,
    rw nat_succ_one_add,
  },
  rw A5,
  rw ← @has_classical_limit_offset (λ (n : ℕ), x ^ n * f n) 0 1,
  apply A1,
end



lemma has_conditional_sum_succ {f:ℕ → ℝ} {x:ℝ}:
  has_conditional_sum f x →
  has_conditional_sum (f ∘ nat.succ) (x - (f 0)) :=
begin
  intro A1,
  rw has_conditional_sum_def,
  have A2:(λ (n : ℕ), finset.sum (finset.range n) (f ∘ nat.succ))=
    (λ (n : ℕ), finset.sum (finset.Ico 1 (nat.succ n)) (f)),
  {
    ext n,
    simp,
    have A2A:nat.succ n = n + 1,
    {
      simp,
    },

    rw A2A,
    have A2B: (λ (n' : ℕ), f (nat.succ n')) = (λ n':ℕ, f (1 + n')),
    {
      ext n',
      have A2B1:nat.succ n' = 1 + n',
      {
        apply nat_succ_one_add,
      },
      rw A2B1,
    },
    rw A2B,
    have A2C:finset.Ico 0 n = finset.range n  := finset.Ico.zero_bot n,
    rw ← A2C,
    rw finset.sum_Ico_add,
  },
  have A3:(λ (n : ℕ), finset.sum (finset.range n) (f ∘ nat.succ))=
    (λ (n : ℕ), (-(f 0)) + (finset.sum (finset.Ico 0 (nat.succ n)) (f)) ),
  {
    rw A2,
    ext n,
    have A3A:0 < nat.succ n := nat.zero_lt_succ n,
    rw finset.sum_eq_sum_Ico_succ_bot A3A,
    rw ← add_assoc,
    simp,
  },
  rw A3,
  have A4:x - (f 0) = (-(f 0)) + x,
  {
    rw sub_eq_add_neg,
    rw add_comm,
  },
  rw A4,
  apply has_classical_limit_sum,
  apply has_classical_limit_const,
  have A5:(λ (n : ℕ), finset.sum (finset.Ico 0 (nat.succ n)) (f))=
    (λ (n : ℕ), finset.sum (finset.range n) f) ∘ (λ m:ℕ, 1 + m),
  {
    ext n,
    rw finset.Ico.zero_bot,
    simp,
    rw nat_succ_one_add,
  },
  rw A5,
  rw ← has_classical_limit_offset,
  apply A1,
end


lemma is_maclaurin_fn_elim {f:ℕ → ℝ} {x:ℝ} {g:ℝ → ℝ}:
  is_maclaurin_fn f g →
  has_conditional_sum  (λ (n : ℕ), f n * x ^ n) (g x) :=
begin
  intro A1,
  unfold is_maclaurin_fn at A1,
  apply A1 x,
end

lemma is_maclaurin_fn_unique {f:ℕ → ℝ} {g h:ℝ → ℝ}:
  is_maclaurin_fn f g →
  is_maclaurin_fn f h →
  g = h :=
begin
  intros A1 A2,
  unfold is_maclaurin_fn at A1,
  unfold is_maclaurin_fn at A2,
  ext x,
  have A3 := A1 x,
  have A4 := A2 x,
  apply has_conditional_sum_unique A3 A4,
end


lemma maclaurin_of_is_maclaurin_fn {f:ℕ → ℝ} {g:ℝ → ℝ}:
  is_maclaurin_fn f g →
  g = maclaurin f :=
begin
  intro A1,
  apply is_maclaurin_fn_unique A1,
  apply is_maclaurin_fn_of_bounded_maclaurin,
  apply bounded_maclaurin_of_is_maclaurin_fn f A1,
end


lemma has_sum_of_is_maclaurin_fn {f:ℕ → ℝ} {x:ℝ} {g:ℝ → ℝ}:
  is_maclaurin_fn f g →
  has_sum  (λ (n : ℕ), f n * x ^ n) (g x) :=
begin
  intro A1,
  have A2 := bounded_maclaurin_of_is_maclaurin_fn _ A1,
  have A3 := @absolutely_summable_of_bounded_maclaurin _ x A2,
  have A4 := @is_maclaurin_fn_elim _ x _ A1,
  have A5 := has_absolute_sum_has_conditional_sum_has_sum_of_absolutely_summable A3,
  cases A5 with z A6,
  cases A6 with A7 A8,
  cases A8 with A9 A10,
  have A11 := has_conditional_sum_unique A9 A4,
  rw A11 at A10,
  apply A10,
end

lemma bounded_maclaurin_elim {f:ℕ → ℝ} {x:ℝ}:
  bounded_maclaurin f →
  has_conditional_sum  (λ (n : ℕ), f n * x ^ n) (maclaurin f x) :=
begin
  intro A1,
  have A2:=is_maclaurin_fn_of_bounded_maclaurin A1,
  apply is_maclaurin_fn_elim A2,
end

lemma has_sum_of_bounded_maclaurin {f:ℕ → ℝ} {x:ℝ}:
  bounded_maclaurin f →
  has_sum  (λ (n : ℕ), f n * x ^ n) (maclaurin f x) :=
begin
  intro A1,
  have A2:=is_maclaurin_fn_of_bounded_maclaurin A1,
  apply has_sum_of_is_maclaurin_fn A2,
end


lemma add_maclaurin {f:ℕ → ℝ} {x:ℝ}:
  bounded_maclaurin f →
  f 0 + x * maclaurin (f ∘ nat.succ) x = maclaurin f x :=
begin
  intro A1,
  have A2:bounded_maclaurin (f ∘ nat.succ) := bounded_maclaurin_succ A1,
  have A4:=@bounded_maclaurin_elim _ x A1,
  have A6:=@bounded_maclaurin_elim _ x A2,
  have A7: has_conditional_sum (λ (n : ℕ), x * ((f ∘ nat.succ) n * x ^ n)) (x * maclaurin (f ∘ nat.succ) x),
  {
    apply has_conditional_sum_mul_const_of_has_conditional_sum A6,
  },
  have A8:(λ (n : ℕ), x * ((f ∘ nat.succ) n * x ^ n))=(λ (m : ℕ), (f m * x ^ m)) ∘ nat.succ,
  {
    ext n,
    simp,
    rw ← mul_assoc,
    rw mul_comm x,
    rw mul_assoc,
    refl,
  },
  rw A8 at A7,
  have A9:has_conditional_sum ((λ (m : ℕ), (f m * x ^ m)) ∘ nat.succ)
      (maclaurin f x - ((λ (m : ℕ), (f m * x ^ m)) 0)),
  {
    apply has_conditional_sum_succ A4,
  },
  have A10:(x * maclaurin (f ∘ nat.succ) x) = (maclaurin f x - ((λ (m : ℕ), (f m * x ^ m)) 0)),
  {
    apply has_conditional_sum_unique A7 A9,
  },
  have A11:((λ (m : ℕ), (f m * x ^ m)) 0) = f 0,
  {
    simp,
  },
  rw A11 at A10,
  have A12:f 0 + (x * maclaurin (f ∘ nat.succ) x) = f 0 + (maclaurin f x +  (-f 0)),
  {
    rw A10,
    rw sub_eq_add_neg,
  },
  rw A12,
  simp,
end


lemma monotone_nonneg_maclaurin {f:ℕ → ℝ} {x y:ℝ}:
  bounded_maclaurin f →
  0 ≤ f →
  0 ≤ x →
  x ≤ y →
  maclaurin f x ≤ maclaurin f y :=
begin
  intros A1 A2 A3 A4,
  have A7:=@bounded_maclaurin_elim _ x A1,
  have A8:=@bounded_maclaurin_elim _ y A1,
  apply has_conditional_sum_le A7 A8,
  rw le_func_def,
  intro n,
  apply mul_le_mul_of_nonneg_left,
  apply real_pow_mono A3 A4,
  apply A2,
end

lemma monotone_nonneg_maclaurin2 {f g:ℕ → ℝ} {x:ℝ}:
  bounded_maclaurin f →
  bounded_maclaurin g →
  0 ≤ x →
  f ≤ g →
  maclaurin f x ≤ maclaurin g x :=
begin
  intros A1 A2 A3 A4,
  have A5:=@bounded_maclaurin_elim _ x A1,
  have A6:=@bounded_maclaurin_elim _ x A2,
  apply has_conditional_sum_le A5 A6,
  rw le_func_def,
  intro n,
  apply mul_le_mul_of_nonneg_right,
  apply A4,
  apply pow_nonneg,
  apply A3,
end


lemma bounded_maclaurin_zero:bounded_maclaurin 0 :=
begin
  unfold bounded_maclaurin,
  intro x,
  simp,
  apply has_classical_limit_const,
end

lemma maclaurin_zero_eq_zero {x:ℝ}:maclaurin 0 x = 0 :=
begin
  have A1:=@bounded_maclaurin_elim (0:ℕ → ℝ) x (bounded_maclaurin_zero),
  simp at A1,
  have A2:=has_conditional_sum_zero,
  apply has_conditional_sum_unique A1 A2,
end


lemma nonneg_maclaurin {f:ℕ → ℝ} {x:ℝ}:
  bounded_maclaurin f →
  0 ≤ f →
  0 ≤ x →
  0 ≤ maclaurin f x :=
begin
  intros A1 A2 A3,
  rw ← @maclaurin_zero_eq_zero x,
  apply monotone_nonneg_maclaurin2,
  apply bounded_maclaurin_zero,
  apply A1,
  apply A3,
  apply A2,
end


lemma maclaurin_le_maclaurin_abs {f:ℕ → ℝ} {x:ℝ}:
  bounded_maclaurin f →
  abs (maclaurin f x) ≤ maclaurin (abs ∘ f) (abs x) :=
begin
  intro A1,
  have A2:= bounded_maclaurin_iff_bounded_maclaurin_abs.mp A1,
  have A3:=@has_sum_of_bounded_maclaurin _ x A1,
  have A4:=@has_sum_of_bounded_maclaurin _ (abs x) A2,
  have A5:(λ (n : ℕ), (abs ∘ f) n * abs x ^ n) = abs ∘ (λ (n : ℕ), f n * x ^ n),
  {
    ext n,
    simp,
    rw abs_mul,
    rw abs_pow,
  },
  rw A5 at A4,
  apply abs_has_sum_le_has_sum_abs A3 A4,
end


--Note that this has to be a canonically ordered semiring, because 0 < 1.
lemma mul_lt_of_lt_one {α:Type*} [ordered_semiring α] {a b:α}:
  0 ≤ a →
  a < 1 →
  0 < b → a * b < b :=
begin
  intros A0 A1 A2,
  have A2:a * b < 1 * b,
  {
    apply mul_lt_mul_of_pos_right,
    apply A1,
    apply A2,
  },
  rw one_mul at A2,
  exact A2,
end

lemma mul_lt_mul_alt {α:Type*} [ordered_semiring α] {a b c d:α}:
  (a < c) →
  (b ≤ d) →
  (0 < d) →
  (0 ≤ a) →
  (a * b < c * d) :=
begin
  intros A1 A2 A3 A4,
  have A6:a * b ≤ a * d,
  {
    apply mul_le_mul_of_nonneg_left A2 A4,
  },
  apply lt_of_le_of_lt,
  apply A6,
  {
    apply mul_lt_mul_of_pos_right A1 A3,

  }
end
/-
  This is significantly harder than I thought it was.
  f 0 + x * maclaurin (f ∘ nat.succ) x = maclaurin f x
  |x * maclaurin (f ∘ nat.succ) x| < |x| * maclaurin (abs ∘ f ∘ nat.succ) x
  monotone (maclaurin (abs ∘ f ∘ nat.succ))
  x ≤ 1 → |x * maclaurin (f ∘ nat.succ) x| < |x| * maclaurin (abs ∘ f ∘ nat.succ) (1:ℝ)
  if maclaurin (abs ∘ f ∘ nat.succ) (1:ℝ)=0, then done.
  Else,
  δ = ε * (maclaurin (abs ∘ f ∘ nat.succ) (1:ℝ))⁻¹
-/
lemma continuous_at_zero_maclaurin {f:ℕ → ℝ}:
  bounded_maclaurin f →
  (has_classical_rlimit (maclaurin f) 0 (f 0)) :=
begin
  intro A1,
  intros ε A1A,
  have C1:bounded_maclaurin (abs ∘ f ∘ nat.succ),
  { -- ⊢ bounded_maclaurin (abs ∘ f ∘ nat.succ)
    apply bounded_maclaurin_iff_bounded_maclaurin_abs.mp,
    apply bounded_maclaurin_succ,
    exact A1,
  },
  have C2:0 ≤  (abs ∘ f ∘ nat.succ),
  { -- ⊢ 0 ≤  (abs ∘ f ∘ nat.succ)
    rw le_func_def,
    intro n,
    simp,
    apply abs_nonneg,
  },

  let r := (maclaurin (abs ∘ f ∘ nat.succ) (1:ℝ)),
  begin
    have A1B:r = (maclaurin (abs ∘ f ∘ nat.succ) (1:ℝ)) := rfl,
    have A2:r = 0 ∨ r ≠ 0 := eq_or_ne,
    cases A2,
    {
      apply exists.intro (1:ℝ),
      split,
      {
        apply zero_lt_one,
      },
      {
        intros x' A3 A4,
        have B1:abs (maclaurin (f ∘ nat.succ) x') = 0,
        {
          apply le_antisymm,
          {
            have B1A:abs (maclaurin (f ∘ nat.succ) x') ≤ (maclaurin (abs ∘ f ∘ nat.succ) (abs x')),
            {
              apply maclaurin_le_maclaurin_abs,
              apply bounded_maclaurin_succ,
              exact A1,
            },
            apply le_trans B1A,
            simp at A4,
            rw ← A2,
            rw A1B,
            apply monotone_nonneg_maclaurin,
            { -- ⊢ bounded_maclaurin (abs ∘ f ∘ nat.succ)
              apply C1,
            },
            { -- ⊢ 0 ≤  (abs ∘ f ∘ nat.succ)
              apply C2,
            },
            {
              apply abs_nonneg,
            },
            {
              apply le_of_lt A4,
            }
          },
          {
            apply abs_nonneg,
          }
        },
        rw ← add_maclaurin A1,
        simp,
        rw abs_mul,
        rw B1,
        rw mul_zero,
        apply A1A,
      }
    },
    {
      have A3:0 ≤ r,
      {
        apply nonneg_maclaurin,
        apply C1,
        rw le_func_def,
        intro n,
        simp,
        apply abs_nonneg,
        apply le_of_lt zero_lt_one,
      },
      have A4:0 < r,
      {
        rw lt_iff_le_and_ne,
        split,
        apply A3,
        intro A4,
        apply A2,
        rw A4,
      },
      apply exists.intro (min (ε * r⁻¹) (1:ℝ)),
      split,
      {
        apply lt_min,
        { -- ⊢ 0 < (ε * r⁻¹)
          apply mul_pos,
          apply A1A,
          apply inv_pos_of_pos A4,
        },
        { -- 0 < 1
          apply zero_lt_one,
        }
      },
      {
        intros x' A5 A6,
        rw ← add_maclaurin A1,
        have A7:f 0 + x' * maclaurin (f ∘ nat.succ) x' - f 0 = x' * maclaurin (f ∘ nat.succ) x',
        {
          simp,
        },
        rw A7,
        rw abs_mul,
        have A8:ε = ε * r⁻¹ * r,
        {
          rw mul_assoc,
          rw inv_mul_cancel,
          rw mul_one,
          apply A2,
        },
        rw A8,
        simp at A6,
        cases A6 with A9 A10,
        apply mul_lt_mul_alt,
        { -- ⊢ abs x' < ε * r⁻¹
          apply A9,
        },
        { -- ⊢ abs (maclaurin (f ∘ nat.succ) x') ≤ r
          rw A1B,
          apply le_trans,
          {
            apply maclaurin_le_maclaurin_abs,
            apply bounded_maclaurin_succ A1,
          },
          {
            apply monotone_nonneg_maclaurin C1,
            apply C2,
            apply abs_nonneg,
            apply le_of_lt,
            apply A10,
          }
        },
        {
          apply A4,
        },
        {
          apply abs_nonneg,
        },
      }
    }
  end
end

/-
has_sum_of_bounded_maclaurin :
  ∀ {f : ℕ → ℝ} {x : ℝ}, bounded_maclaurin f → has_sum (λ (n : ℕ), f n * x ^ n) (maclaurin f x)
summable_function_uncurry3 :
  ∀ {f : ℕ → ℕ → ℝ},
    (∀ (i : ℕ), summable (f i)) → summable (λ (n : ℕ), tsum (abs ∘ f n)) → summable (function.uncurry f)
has_sum_sum_of_ne_finset_zero :
  ∀ {α : Type u_1} {β : Type u_2} [_inst_1 : add_comm_monoid α] [_inst_2 : topological_space α] {f : β → α}
  {s : finset β}, (∀ (b : β), b ∉ s → f b = 0) → has_sum f (finset.sum s f)
-/
lemma has_sum_finset_sum {f:ℕ → ℝ} {S:finset ℕ}:
  has_sum (λ n, if (n ∈ S) then f n else 0) (finset.sum S f) :=
begin
  have A1:finset.sum S f = finset.sum S (λ n, if (n ∈ S) then f n else 0),
  {
    apply finset_sum_subst2,
    intros s A1A,
    rw if_pos,
    exact A1A,
  },
  rw A1,
  apply has_sum_sum_of_ne_finset_zero,
  intros b A2,
  rw if_neg,
  exact A2,
end


lemma if_subst {α:Type*} {P Q:Prop} [D:decidable P] [decidable Q] {m n:α}:
  (P ↔ Q) →
  (if P then m else n) = (if Q then m else n) :=
begin
  intro A1,
  have A2:decidable P,
  {
    apply D,
  },
  cases A2,
  {
    rw if_neg,
    rw if_neg,
    { -- ⊢ ¬Q
      intro A2A1,
      apply A2,
      rw A1,
      apply A2A1,
    },
    apply A2,
  },
  {
    rw if_pos,
    rw if_pos,
    {
      rw ← A1,
      apply A2,
    },
    {
      apply A2,
    }
  }
end

lemma has_sum_finset_range_succ {f:ℕ → ℝ} {m:ℕ}:
  has_sum (λ n, if (n ≤ m) then f n else 0) (finset.sum (finset.range (nat.succ m)) f) :=
begin
  have A1:(λ n, if (n ≤ m) then f n else 0) =
      (λ n, if (n ∈ finset.range (nat.succ m)) then f n else 0),
  {
    ext n,
    rw @if_subst ℝ (n ≤ m) (n ∈ finset.range (nat.succ m)),
    rw finset.mem_range,
    symmetry,
    apply nat.lt_succ_iff,
  },
  rw A1,
  apply has_sum_finset_sum,
end

/-
finset.mul_sum :
  ∀ {α : Type u_1} {β : Type u_2} {s : finset α} {f : α → β} {b : β} [_inst_1 : semiring β],
    b * finset.sum s f = finset.sum s (λ (x : α), b * f x)
-/

lemma binomial_maclaurinh {f:ℕ → ℝ} {x y:ℝ} {n:ℕ}:
  has_sum (λ (m : ℕ), if (m ≤ n) then (f n *
           x ^ m * y ^ (n - m) * ↑(nat.choose n m)) else 0) (f n * (x + y) ^ n) :=
begin
  have A3A:f n * (x + y) ^ n = f n * finset.sum (finset.range (nat.succ n)) (λ (m : ℕ), x ^ m * y ^ (n - m) * ↑(nat.choose n m)),
  {
    rw add_pow,
  },
  /-
  have A4A:(λ (m2:ℕ), (f n) * (λ (m : ℕ),
          x ^ m * y ^ (n - m) * ↑(nat.choose n m)) m2)
          =(λ (m : ℕ), (f n) *
          x ^ m * y ^ (n - m) * ↑(nat.choose n m)),
  {
    ext m2,
    simp,
    rw ← mul_assoc,
    rw ← mul_assoc,
  },-/

  rw finset.mul_sum at A3A,
  rw A3A,
  have A3B := @has_sum_finset_range_succ
        (λ (x_1 : ℕ), f n * (x ^ x_1 * y ^ (n - x_1) * ↑(nat.choose n x_1))) n,
  have A3C:(λ (n_1 : ℕ), ite (n_1 ≤ n) ((λ (x_1 : ℕ), f n * (x ^ x_1 * y ^ (n - x_1) * ↑(nat.choose n x_1))) n_1) 0)
      =(λ (m : ℕ), if (m ≤ n) then (f n *
          x ^ m * y ^ (n - m) * ↑(nat.choose n m)) else 0),
  {
    ext m,
    simp,
    have A3CA:(f n * (x ^ m * y ^ (n - m) * ↑(nat.choose n m))) =
        (f n * x ^ m * y ^ (n - m) * ↑(nat.choose n m)),
    {
      rw ← mul_assoc,
      rw ← mul_assoc,
    },
    rw A3CA,
  },
  rw A3C at A3B,
  apply A3B,
end

lemma fubinis_theorem_discrete6 {q:ℕ → ℕ → ℝ} {z:ℝ}:
  (∀ n:ℕ, summable (q n)) →
  summable (λ n:ℕ, tsum  (abs ∘ (q n))) →
  has_sum (λ n:ℕ, tsum (q n)) z →
  has_sum (function.uncurry q) z :=
begin
  intros A1 A2 A3,
  have A4:summable (function.uncurry q) := summable_function_uncurry3 A1 A2,
  let g := λ n, tsum (q n),
  let f := function.uncurry q,
  begin
    have B1:g = λ n, tsum (q n) := rfl,
    have B2:f = function.uncurry q := rfl,
    have B3:summable f := A4,
    have B4:has_sum f (tsum f) := has_sum_tsum B3,
    have B5:(∀ (b : ℕ), has_sum (λ (c : ℕ), f (b, c)) (g b)),
    {
      intro b,
      rw B2,
      rw B1,
      simp,
      rw function.uncurry_def,
      simp,
      apply has_sum_tsum,
      apply A1,
    },
    rw ← B2,
    have B6:has_sum g (tsum f),
    {
      apply has_sum_prod B5 B4,
    },
    rw B1 at B6,
    have B7:tsum f = z,
    {
      apply has_sum.unique B6 A3,
    },
    rw ← B7,
    apply has_sum_tsum B3,
  end
end


lemma if_map {α β:Type*} {f:α → β} {u v:α} {P:Prop} [D:decidable P]:
    f (if P then u else v) = (if P then (f u) else (f v)) :=
begin
  have A1:=D,
  cases A1,
  {
    rw if_neg,
    rw if_neg,
    apply A1,
    apply A1,
  },
  {
    rw if_pos,
    rw if_pos,
    apply A1,
    apply A1,
  }
end

-- This theorem is inferior in all ways to fubinis_theorem_discrete4
lemma fubinis_theorem_discrete5 {q:ℕ → ℕ → ℝ} {z:ℝ}:
  summable (λ n:ℕ, (finset.sum (finset.range (nat.succ n)) (abs ∘ (q n)))) →
  has_sum (λ n:ℕ, (finset.sum (finset.range (nat.succ n)) (q n))) z →
  has_sum (λ (p : ℕ × ℕ), if (p.snd ≤ p.fst) then (q (p.fst) (p.snd)) else 0) z :=
begin
  intros A1 A2,
  /-
    Alright, we can lift this theorem up to fubinis_theorem_discrete6.
    First, we create a variant of q so that it is zero everywhere we don't want to sum.
    This proof is longer than I anticipated.
  -/
  let q2:ℕ → ℕ → ℝ := (λ m n:ℕ, if (n ≤ m) then (q m n) else 0),
  begin
    have A5:q2 = (λ m n:ℕ, if (n ≤ m) then (q m n) else 0) := rfl,
    have A3:∀ m, (has_sum (λ n, if (n ≤ m) then q m n else 0)
                 (finset.sum (finset.range (nat.succ m)) (q m))),
    {
      intro m,
      apply has_sum_finset_range_succ,
    },
    have A4:function.uncurry q2 =
            (λ (p : ℕ × ℕ), if (p.snd ≤ p.fst) then (q (p.fst) (p.snd)) else 0),
    {
      rw A5,
      ext p,
      rw function.uncurry_def,
    },
    rw ← A4,
    apply fubinis_theorem_discrete6,
    { -- ⊢ ∀ (n : ℕ), summable (q2 n)
      intro m,
      rw A5,
      have B1:has_sum ((λ (m n : ℕ), ite (n ≤ m) (q m n) 0) m)
                      (finset.sum (finset.range (nat.succ m)) (q m)),
      {
        apply @has_sum_finset_range_succ (q m),
      },
      apply has_sum.summable B1,
    },
    { -- ⊢ summable (λ (n : ℕ), tsum (abs ∘ q2 n))
      rw A5,
      have C1:(λ (n : ℕ), tsum (abs ∘ (λ (m n : ℕ), ite (n ≤ m) (q m n) 0) n))
              = (λ n:ℕ, (finset.sum (finset.range (nat.succ n)) (abs ∘ (q n)))),
      {
        ext n,
        simp,
        have C1A:(abs ∘ λ (n_1 : ℕ), ite (n_1 ≤ n) (q n n_1) 0)=
                 (λ n_1:ℕ, ite (n_1 ≤ n) (abs (q n n_1)) 0),
        {
          ext n_1,
          simp,
          have C1A1:(n_1 ≤ n) ∨ ¬(n_1≤ n) := le_or_not_le,
          cases C1A1,
          {
            rw if_pos C1A1,
            rw if_pos C1A1,
          },
          {
            rw if_neg C1A1,
            rw if_neg C1A1,
            rw abs_of_nonneg,
            simp,
          }
        },
        rw C1A,
        have C1B:has_sum (λ (n_1 : ℕ), ite (n_1 ≤ n) (abs (q n n_1)) 0)
                 (finset.sum (finset.range (nat.succ n)) (λ (x : ℕ), abs (q n x))),
        {
          apply @has_sum_finset_range_succ,
        },
        have C1C:=has_sum.summable C1B,
        have C1D:=has_sum_tsum C1C,
        apply has_sum.unique C1D C1B,
      },
      rw C1,
      apply A1,
    },
    { -- ⊢ has_sum (λ (n : ℕ), tsum (q2 n)) z
      rw A5,
      have D1:(λ (n : ℕ), tsum (q2 n))=(λ m, (finset.sum (finset.range (nat.succ m)) (q m))),
      {
        ext m,
        rw A5,
        have D1A:has_sum ((λ (m n : ℕ), ite (n ≤ m) (q m n) 0) m)
                        (finset.sum (finset.range (nat.succ m)) (q m)),
        {
          apply @has_sum_finset_range_succ (q m),
        },
        have D1B:=has_sum.summable D1A,
        have D1C:=has_sum_tsum D1B,
        apply has_sum.unique D1C D1A,
      },
      rw D1,
      apply A2,
    }
  end
end



lemma fubinis_theorem_discrete4 {q:ℕ → ℕ → ℝ} {z:ℝ}:
  summable (λ n:ℕ, (finset.sum (finset.range (nat.succ n)) (abs ∘ (q n)))) →
  has_sum (λ n:ℕ, (finset.sum (finset.range (nat.succ n)) (q n))) z →
  has_sum (λ p:ℕ × ℕ, q (p.fst + p.snd) (p.fst)) z :=
begin
  intros A1 A2,
  /-
    This consists of two steps.
    In the first step, we show:
    has_sum (λ p:ℕ × ℕ, if (j ≤ i) then (f i j) else 0) z
    Then, we use
    has_sum_iff_has_sum_of_ne_zero_bij
    We have the map <m,n> → <m + n, n>
    or we can use
    We have the map <m,n> → <m + n, m>
  -/

  -- The indices are all backwards!!!
  let f:ℕ × ℕ → ℝ := (λ p:ℕ × ℕ, q (p.fst + p.snd) (p.fst)),
  let g:ℕ × ℕ → ℝ := (λ p:ℕ × ℕ, if (p.snd ≤ p.fst) then (q p.fst p.snd) else 0),
  let i:function.support g → (ℕ × ℕ):=λ a:function.support g, (a.val.snd, a.val.fst - a.val.snd),
  begin
    let A3:f = (λ p:ℕ × ℕ, q (p.fst + p.snd) (p.fst)) := rfl,
    let A4:g = (λ p:ℕ × ℕ, if (p.snd ≤ p.fst) then (q p.fst p.snd) else 0) := rfl,
    let A5:i = λ a:function.support g, (a.val.snd, a.val.fst - a.val.snd) := rfl,


    have A6:∀ p:ℕ × ℕ, g p ≠ 0 → (p.snd ≤ p.fst),
    { -- Proof by contradiction.
      intro p,
      have A6A:(p.snd ≤ p.fst) ∨ ¬ (p.snd ≤ p.fst) := le_or_not_le,
      cases A6A,
      {
        intro A6A1,
        apply A6A,
      },
      {
        intro A6A1,
        exfalso,
        apply A6A1,
        rw A4,
        simp,
        rw if_neg,
        apply A6A,
      }
    },
    rw ← A3,
    rw (@has_sum_iff_has_sum_of_ne_zero_bij ℝ (ℕ × ℕ) (ℕ × ℕ) _ _
          f z g i),
    {  -- ⊢ has_sum g z
      rw A4,
      -- ⊢ has_sum (λ (p : ℕ × ℕ), ite (p.snd ≤ p.fst) (q (p.fst) (p.snd)) 0) z
      apply fubinis_theorem_discrete5 A1 A2,
    },
    { -- ⊢ ∀ ⦃c₁ c₂ : ℕ × ℕ⦄ (h₁ : g c₁ ≠ 0) (h₂ : g c₂ ≠ 0), i h₁ = i h₂ → c₁ = c₂
      intros p1 p2 C1,
      have G1:p1.val = (@coe (function.support g) (ℕ × ℕ) _ p1) := rfl,
      have G2:p2.val = (@coe (function.support g) (ℕ × ℕ) _ p2) := rfl,
      rw A5 at C1,
      simp at C1,
      cases C1 with C4 C5,
      rw C4 at C5,
      have C6 := A6 p1.val p1.property,
      have C7 := A6 p2.val p2.property,
      rw ← G1 at C4,
      rw ← G2 at C4,
      rw C4 at C6,
      rw ← G1,
      rw ← G2,
      have C5B := nat.sub_cancel C6 C7 C5,
      ext,
      apply C5B,
      apply C4,
    },
    { -- ⊢ ∀ ⦃b : ℕ × ℕ⦄, f b ≠ 0 → (∃ (c : ℕ × ℕ) (h : g c ≠ 0), i h = b)
      intros p D1,
      let p_img:ℕ × ℕ := ⟨ p.fst + p.snd, p.fst ⟩,
      begin
        have D2:p_img = ⟨ p.fst + p.snd, p.fst ⟩ := rfl,
        have D3:g p_img = f p,
        {
          rw D2,
          rw A4,
          simp,
        },
        rw set.mem_range,
        have G3:p_img ∈ function.support g,
        {
          rw function.mem_support,
          rw function.mem_support at D1,
          rw D3,
          apply D1,
        },
        apply exists.intro (@subtype.mk (ℕ × ℕ) (function.support g) p_img G3),
        rw A5,
        simp,
      end
    },
    { -- ⊢ ∀ ⦃c : ℕ × ℕ⦄ (h : g c ≠ 0), f (i h) = g c
      intro x,
      rw A5,
      have H1:x.val = (@coe (function.support g) (ℕ × ℕ) _ x) := rfl,
      rw A3,
      rw ← H1,
      have A4B:g x.val = 
          (λ (p : ℕ × ℕ), ite (p.snd ≤ p.fst) (q p.fst p.snd) 0) x.val := rfl,
      rw A4B,
      simp,
      have H2:(@coe (function.support g) (ℕ × ℕ) _ x).snd ≤ 
              (@coe (function.support g) (ℕ × ℕ) _ x).fst,
      {
        apply A6,
        apply x.property,
      },
      rw if_pos,
      rw nat.add_sub_cancel' H2,
      apply H2,
    }
  end
end


/- Rearranging the binomial into a function -/
lemma binomial_maclaurin2A {f:ℕ → ℝ} {x y:ℝ} {n:ℕ}:
  f n * (x + y) ^ n =
    finset.sum (finset.range (nat.succ n)) (λ (m : ℕ), f n * (x ^ m * y ^ (n - m) * ↑(nat.choose n m)))
 :=
begin
  have A3A:f n * (x + y) ^ n = f n * finset.sum (finset.range (nat.succ n)) (λ (m : ℕ), x ^ m * y ^ (n - m) * ↑(nat.choose n m)),
  {
    rw add_pow,
  },
  rw finset.mul_sum at A3A,
  apply A3A,
end

lemma binomial_maclaurin2B {f:ℕ → ℝ} {x y:ℝ}:
  bounded_maclaurin f →
  has_sum (λ n:ℕ, finset.sum (finset.range (nat.succ n))
     (λ (m : ℕ), f n * (x ^ m * y ^ (n - m) * ↑(nat.choose n m))))
     ((maclaurin f) (x + y)) :=
begin
  intro A1,
  have A2:=@has_sum_of_bounded_maclaurin f (x + y) A1,
  {
    have A3A: (λ (n : ℕ), f n * (x + y) ^ n) =
              (λ n:ℕ, finset.sum (finset.range (nat.succ n))
     (λ (m : ℕ), f n * (x ^ m * y ^ (n - m) * ↑(nat.choose n m)))),
    {
      ext n,
      apply @binomial_maclaurin2A f x y,
    },
    rw A3A at A2,
    apply A2,
  },

end


lemma binomial_maclaurin {f:ℕ → ℝ} {x y:ℝ}:
  bounded_maclaurin f →
  has_sum (λ p:ℕ × ℕ, x^(p.fst) * y^(p.snd) *
                      (nat.choose (p.fst + p.snd) p.fst) *
                      (f (p.fst + p.snd)))
  ((maclaurin f) (x + y)) :=
begin
  intro A1,
  have A2:=@has_sum_of_bounded_maclaurin f (x + y) A1,
  have A3:=@binomial_maclaurin2B f  x y A1,
  let g := (λ n:ℕ,
     (λ (m : ℕ), f n * (x ^ m * y ^ (n - m) * ↑(nat.choose n m)))),
  begin
    have A4:g = (λ n:ℕ,
     (λ (m : ℕ), f n * (x ^ m * y ^ (n - m) * ↑(nat.choose n m)))) := rfl,
    have A5:(λ n:ℕ, finset.sum (finset.range (nat.succ n))
     (λ (m : ℕ), f n * (x ^ m * y ^ (n - m) * ↑(nat.choose n m))))
     =(λ n:ℕ, finset.sum (finset.range (nat.succ n)) (g n)),
    {
      ext n,
      rw A4,
    },
    rw A5 at A3,
    have A6:summable (λ n:ℕ, (finset.sum (finset.range (nat.succ n)) (abs ∘ (g n)))),
    {
      rw A4,
      have A6A:bounded_maclaurin (abs ∘ f) := bounded_maclaurin_iff_bounded_maclaurin_abs.mp A1,
      have A6B:=@binomial_maclaurin2B (abs ∘ f)  (abs x) (abs y) A6A,
      have A6C:summable (λ (n : ℕ),
      finset.sum (finset.range (nat.succ n))
      (λ (m : ℕ), (abs ∘ f) n * (abs x ^ m * abs y ^ (n - m) * ↑(nat.choose n m)))),
      {
        apply exists.intro (maclaurin (abs ∘ f) (abs x + abs y)) A6B,
      },
      have A6D:(λ (n : ℕ),
       finset.sum (finset.range (nat.succ n))
         (λ (m : ℕ), (abs ∘ f) n * (abs x ^ m * abs y ^ (n - m) * ↑(nat.choose n m)))) =
         (λ n:ℕ, (finset.sum (finset.range (nat.succ n)) (abs ∘ (g n)))),
      {
        ext n,
        apply finset_sum_subst2,
        intros m A6D1,
        rw A4,
        simp,
        rw abs_mul,
        rw abs_mul,
        rw abs_mul,
        rw abs_pow,
        rw abs_pow,
        simp,
      },
      rw A6D at A6C,
      apply A6C,
    },
    have A8 := fubinis_theorem_discrete4 A6 A3,
    have A9:(λ (p : ℕ × ℕ), (λ (n : ℕ), g n) (p.fst + p.snd) (p.fst)) =
             (λ (p : ℕ × ℕ), x ^ p.fst * y ^ p.snd * ↑(nat.choose (p.fst + p.snd) (p.fst)) * f (p.fst + p.snd)),
    {
       ext p,
       rw A4,
       simp,
       rw mul_comm _ (f (p.fst + p.snd)),
     },
     rw A9 at A8,
     apply A8,
  end
end


lemma binomial_maclaurin2 {f:ℕ → ℝ} {x y:ℝ} {m:ℕ}:
  bounded_maclaurin f →
  summable (λ n:ℕ, x^m * y^n * (nat.choose (m + n) m) * (f (m + n))) :=
begin
  intro A1,
  have A2 := @binomial_maclaurin f x y A1,
  have A3 := has_sum.summable A2,
  apply summable_right_of_summable3 A3,
end


lemma bounded_maclaurin_of_conditionally_summable {f:ℕ → ℝ}:
  (∀ y:ℝ, conditionally_summable (λ n:ℕ, f n * y^n)) →
  bounded_maclaurin f :=
begin
  intro A1,
  apply @bounded_maclaurin_of_is_maclaurin_fn f (λ y, conditional_sum (λ n:ℕ, f n * y^n)),
  unfold is_maclaurin_fn,
  intro x,
  apply has_conditional_sum_conditional_sum_of_conditionally_summable (A1 x),
end




lemma bounded_maclaurin_of_summable {f:ℕ → ℝ}:
  (∀ y:ℝ, summable (λ n:ℕ, f n * y^n)) →
  bounded_maclaurin f :=
begin
  intro A1,
  apply bounded_maclaurin_of_conditionally_summable,
  intro y,
  apply conditionally_summable_of_summable,
  apply A1,
end


lemma binomial_maclaurin3 {f:ℕ → ℝ} {y:ℝ} {m:ℕ}:
  bounded_maclaurin f →
  summable (λ n:ℕ, y^n * (nat.choose (m + n) m) * (f (m + n))) :=
begin
  intro A1,
  have A2:=@binomial_maclaurin2 f (1:ℝ) y m A1,
  simp at A2,
  apply A2,
end

lemma bounded_maclaurin_binomial_maclaurin {f:ℕ → ℝ} {m:ℕ}:
  bounded_maclaurin f →
  bounded_maclaurin (λ n:ℕ, (nat.choose (m + n) m) * (f (m + n))) :=
begin
  intro A1,
  apply bounded_maclaurin_of_summable,
  intro y,
  have A2:(λ n:ℕ, y^n * (nat.choose (m + n) m) * (f (m + n)))
          =(λ n:ℕ, (nat.choose (m + n) m) * (f (m + n)) * y^n),
  {
    ext n,
    rw mul_assoc,
    rw mul_comm,
  },
  rw ← A2,
  apply binomial_maclaurin3 A1,

end


/-

binomial_maclaurin :
  ∀ {f : ℕ → ℝ} {x y : ℝ},
    bounded_maclaurin f →
    has_sum (λ (p : ℕ × ℕ), x ^ p.fst * y ^ p.snd * ↑(nat.choose (p.fst + p.snd) (p.fst)) * f (p.fst + p.snd))
      (maclaurin f (x + y))
fubinis_theorem_discrete_left :
  ∀ {f : ℕ → ℕ → ℝ},
    summable (λ (p : ℕ × ℕ), f (p.fst) (p.snd)) →
    ((∑' (p : ℕ × ℕ), f (p.fst) (p.snd)) = ∑' (i j : ℕ), f i j)

-/


/-
  Looking at this more closely, this is a perfect candidate for applying has_sum_prod DIRECTLY.
  has_sum_prod :
  ∀ {α : Type u_1} {β : Type u_2} [ACM : add_comm_monoid α] [T : topological_space α]
  [TAM : has_continuous_add α] [R : regular_space α] {γ : Type u_3} {f : β × γ → α} {g : β → α}
  {a : α}, (∀ (b : β), has_sum (λ (c : γ), f (b, c)) (g b)) → has_sum f a → has_sum g a
-/
lemma binomial_maclaurin4 {f:ℕ → ℝ} {x y:ℝ}:
  bounded_maclaurin f →
  has_sum (λ m:ℕ, x^m *
          tsum (λ n:ℕ, y^n *
                      (nat.choose (m + n) m) *
                      (f (m + n))))
  ((maclaurin f) (x + y)) :=
begin
  intro A1,
  have A2:=@binomial_maclaurin f x y A1,
  apply has_sum_prod _ A2,
  simp,
  intro m,
  have A7:=@binomial_maclaurin3 f y m A1,
  have A8:=has_sum_tsum A7,
  have A9:=has_sum.mul_left (x^m) A8,
  simp at A9,
  have A10:(λ (b : ℕ), x ^ m * (y ^ b * ↑(nat.choose (m + b) m) * f (m + b)))=
           (λ (c : ℕ), x ^ m * y ^ c * ↑(nat.choose (m + c) m) * f (m + c)),
  {
    ext b,
    rw mul_assoc (x^m),
    rw mul_assoc (x^m),
  },
  rw ← A10,
  apply A9,
end


lemma has_conditional_sum_of_has_sum {f:ℕ → ℝ} {x:ℝ}:
  has_sum f x → has_conditional_sum f x :=
begin
  intro A1,
  have A2:=has_sum.summable A1,
  have A3:=has_absolute_sum_has_conditional_sum_has_sum_of_summable A2,
  cases A3 with x2 A4,
  cases A4 with A5 A6,
  cases A6 with A7 A8,
  have A9 := has_sum.unique A8 A1,
  subst x2,
  apply A7,
end

lemma binomial_maclaurin5 {f:ℕ → ℝ} {y:ℝ}:
  bounded_maclaurin f →
  is_maclaurin_fn (λ m:ℕ,
          tsum (λ n:ℕ, y^n *
                      (nat.choose (m + n) m) *
                      (f (m + n))))
  (λ x, ((maclaurin f) (x + y))) :=
begin
  intro A1,
  unfold is_maclaurin_fn,
  intro x,
  apply has_conditional_sum_of_has_sum,
  have A2:(λ (n : ℕ), (∑' (n_1 : ℕ), y ^ n_1 * ↑(nat.choose (n + n_1) n) * f (n + n_1)) * x ^ n)
          = (λ m:ℕ, x^m * tsum (λ n:ℕ, y^n * (nat.choose (m + n) m) * (f (m + n)))),
  {
    ext n,
    rw mul_comm,
  },
  rw A2,
  apply binomial_maclaurin4,
  apply A1,
end




lemma tsum_eq_maclaurin_of_bounded_maclaurin {f:ℕ → ℝ} {y:ℝ}:
  bounded_maclaurin f →
  (∑' n:ℕ, f n * y^n) = maclaurin f y :=
begin
  intro A1,
  unfold maclaurin,
  have A2:=@absolutely_summable_of_bounded_maclaurin f y A1,
  rw absolutely_summable_def at A2,
  apply tsum_eq_conditional_sum_of_summable A2,
end

lemma binomial_maclaurin6 {f:ℕ → ℝ} {x y:ℝ}:
  bounded_maclaurin f →
  ((maclaurin f) (x + y)) =
   (maclaurin f y) + x * (maclaurin  ((λ m:ℕ,
          tsum (λ n:ℕ, y^n *
                      (nat.choose (m + n) m) *
                      (f (m + n))))∘ nat.succ) x) :=
begin
  intro A1,
  have A2:=@binomial_maclaurin5 f y A1,
  have A3:=bounded_maclaurin_of_is_maclaurin_fn _ A2,
  have A4:=(@maclaurin_of_is_maclaurin_fn _ _ A2),
  have A5: (λ (x : ℝ), maclaurin f (x + y)) x =
    maclaurin (λ (m : ℕ), ∑' (n : ℕ), y ^ n * ↑(nat.choose (m + n) m) * f (m + n)) x,
  {
    rw A4,
  },
  simp at A5,
  rw A5,
  rw ← add_maclaurin A3,
  simp,
  have A6:(λ n, f n * y^n) = (λ n, y^n * f n),
  {
    ext n,
    rw mul_comm,
  },
  rw ← A6,
  apply @tsum_eq_maclaurin_of_bounded_maclaurin f y A1
end


lemma bounded_maclaurin_approx_deriv {f:ℕ → ℝ} {x:ℝ}:
  bounded_maclaurin f →
  bounded_maclaurin
  ((λ m:ℕ,
          tsum (λ n:ℕ, x^n *
                      (nat.choose (m + n) m) *
                      (f (m + n))))∘ nat.succ) :=
begin
  intro A1,
  apply bounded_maclaurin_succ,
  apply bounded_maclaurin_of_is_maclaurin_fn,
  apply binomial_maclaurin5 A1,
end

lemma approx_deriv_is_almost_maclaurin_fn {f:ℕ → ℝ} {x h:ℝ}:
  bounded_maclaurin f →
  h≠ 0 →
  maclaurin
  ((λ m:ℕ,
          tsum (λ n:ℕ, x^n *
                      (nat.choose (m + n) m) *
                      (f (m + n))))∘ nat.succ) h =
  ((maclaurin f) (x + h) - (maclaurin f) x)/h :=
begin
  intros A1 A2,
  rw add_comm x h,
  rw binomial_maclaurin6 A1,
  simp,
  rw mul_div_cancel_left,
  apply A2,
end


lemma deriv_maclaurin_def2 {f:ℕ → ℝ} {x:ℝ}:
  bounded_maclaurin f →
  deriv_maclaurin f x = ∑' (n : ℕ), x ^ n * (1 + ↑n) * f (n + 1) :=
begin
  intro A1,
  unfold deriv_maclaurin,
  have A2:=is_maclaurin_derivative_bounded f A1,
  have A3:=bounded_maclaurin_of_is_maclaurin_fn _ A2,
  have A4:=@tsum_eq_maclaurin_of_bounded_maclaurin _ x A3,
  rw ← A4,
  have A5: (λ (n : ℕ), deriv_maclaurin_series f n * x ^ n) =
           λ (n : ℕ), x ^ n * (1 + ↑n) * f (n + 1),
  {
    ext n,
    unfold deriv_maclaurin_series,
    simp,
    have A5A:nat.succ n = n + 1,
    {
      simp,
    },
    rw A5A,
    rw mul_comm _ (x^n),
    rw mul_comm (f (n + 1)),
    rw mul_assoc,
    rw add_comm 1 (n:ℝ),
  },
  rw A5,
end


lemma deriv_maclaurin_def {f:ℕ → ℝ} {x:ℝ} {g:ℝ → ℝ}:
  is_maclaurin_fn f g →
  has_classical_rderiv_at g (deriv_maclaurin f x) x :=
begin
  intro A1,
  rw has_classical_rderiv_at_def3,
  rw maclaurin_of_is_maclaurin_fn A1,
  have A2:=bounded_maclaurin_of_is_maclaurin_fn f A1,
  have A4:=@bounded_maclaurin_approx_deriv _ x A2,
  have A5:=continuous_at_zero_maclaurin A4,
  have A7:(deriv_maclaurin f x)=
         (((λ (m : ℕ), ∑' (n : ℕ), x ^ n * ↑(nat.choose (m + n) m) * f (m + n)) ∘ nat.succ) 0),
  {
    simp,
    have A7A:(λ (n : ℕ), x ^ n * (1 + ↑n) * f (1 + n))=
             (λ (n : ℕ), x ^ n * (1 + ↑n) * f (n + 1)),
    {
      ext n,
      rw add_comm n 1,
    },
    rw A7A,
    apply @deriv_maclaurin_def2 _ x A2,
  },
  rw ← A7 at A5,
  rw has_classical_rlimit_def at A5,
  rw has_classical_rlimit_def,
  intros ε B1,
  have B2 := A5 ε B1,
  cases B2 with δ B3,
  cases B3 with B4 B5,
  apply exists.intro δ,
  split,
  {
    apply B4,
  },
  {
    intros h B6 B7,
    have B8 := B5 h B6 B7,
    have B9 := @approx_deriv_is_almost_maclaurin_fn f x h A2 B6,
    rw B9 at B8,
    apply B8,
  },
end


lemma deriv_maclaurin_def3 {f:ℕ → ℝ} {x:ℝ} {g:ℝ → ℝ}:
  is_maclaurin_fn f g →
  has_deriv_at g (deriv_maclaurin f x) x :=
begin
  intro A1,
  rw ← has_classical_rderiv_at_def,
  apply deriv_maclaurin_def A1,
end


lemma inv_mul_mul_cancel {a b:ℝ}:(a ≠ 0) →
  (a * b)⁻¹ * a = b⁻¹  :=
begin
  intro A1,
  rw mul_inv',
  rw mul_assoc,
  rw mul_comm _ a,
  rw ← mul_assoc,
  rw inv_mul_cancel,
  rw one_mul,
  apply A1,
end


lemma deriv_maclaurin_series_exp_maclaurin:
    deriv_maclaurin_series (exp_maclaurin) = exp_maclaurin :=
begin
  rw exp_maclaurin_def,
  rw deriv_maclaurin_series_def,
  ext n,
  simp,
  rw inv_mul_mul_cancel,
  have A1:0 < 1 + (n:ℝ),
  {
    apply lt_of_lt_of_le,
    apply zero_lt_one,
    simp,
  },
  intro A2,
  rw add_comm at A2,
  rw A2 at A1,
  apply lt_irrefl (0:ℝ) A1,
end


lemma has_deriv_at_exp {x:ℝ}:
  has_deriv_at (real.exp) (real.exp x) x :=
begin
  have A1:is_maclaurin_fn exp_maclaurin real.exp := is_maclaurin_fn_exp,
  have A2:has_deriv_at (real.exp) (deriv_maclaurin (exp_maclaurin) x) x,
  {
    apply deriv_maclaurin_def3 A1,
  },
  have A3:deriv_maclaurin (exp_maclaurin) = real.exp,
  {
    have A3A:deriv_maclaurin_series (exp_maclaurin) = exp_maclaurin :=
        deriv_maclaurin_series_exp_maclaurin,
    unfold deriv_maclaurin,
    rw A3A,
    symmetry,
    apply maclaurin_of_is_maclaurin_fn A1,
  },
  rw A3 at A2,
  exact A2,
end
