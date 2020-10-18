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
import formal_ml.hahn

/-
  This only works if the sum of g is finite.
  For example, if f = (λ i:ℕ, 1 + (1/((i + 1):ennreal)^2), and
  g = (λ i:ℕ, 1), then f - g =  (λ i:ℕ, (1/((i + 1):ennreal)^2), so
  ∑ (f - g) = π^2/6, but (∑ f) - (∑ g)=⊤ - ⊤ = 0. 
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

namespace measure_theory
namespace measure

/-- This is the equivalent of (a-b) ⊔ 0, if a and b were signed measures.
Compare with ennreal.has_sub. 
Specifically, note that if you have α = {1,2}, and  a {1} = 2, a {2} = 0, and 
b {2} = 2, b {1} = 0, then (a - b) {1, 2} = 2. However, if a ≤ b, and
b set.univ ≠ ⊤, then (a - b) + b = a. -/
noncomputable instance has_sub {α:Type*}
  [measurable_space α]:has_sub (measure_theory.measure α) := ⟨λa b, Inf {d | a ≤ d + b}⟩

lemma sub_def {α:Type*}
  [measurable_space α] {a b:measure_theory.measure α}:
  (a - b) = Inf {d | a ≤ d + b} := rfl

lemma le_zero_iff {Ω:Type*} [measurable_space Ω]
  (μ:measure_theory.measure Ω):μ ≤ 0 ↔ μ = 0 :=
begin
  split;intros A1,
  {
    apply le_antisymm A1,
    apply measure_theory.measure.zero_le,
  },
  {
    rw A1,
    apply le_refl _,
  },
end

lemma sub_eq_zero_if_le {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω):μ ≤ ν → μ - ν = 0 :=
begin
  intros A1,
  rw ← measure_theory.measure.le_zero_iff,
  rw measure_theory.measure.sub_def,
  apply @Inf_le (measure_theory.measure Ω) _ _,
  simp [A1],
end

lemma le_of_add_le_add_left {α:Type*} 
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

namespace sub

/--This is a function that is equivalent to subtraction above if
ν ≤ μ and ν is finite (ν set.univ ≠ ⊤).
Because the above definition is defined as an infimum, this
measure_sub_fn serves as an existence proof of that definition.-/
noncomputable def measure_sub_fn {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α):Π (s:set α),is_measurable s → ennreal := 
  λ (S:set α) (H:is_measurable S), (μ S - ν S)


lemma measure_sub_fn_apply {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (s:set α) (H:is_measurable s):
  measure_sub_fn μ ν s H = (μ s - ν s) := rfl


lemma measure_sub_fn_apply_empty {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α): 
  (measure_sub_fn μ ν) ∅ is_measurable.empty = 0 :=
begin
  rw measure_sub_fn_apply,
  rw measure_theory.measure_empty,
  rw measure_theory.measure_empty,
  rw ennreal.sub_zero,
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
  have A3:(λ n:ℕ, (measure_sub_fn μ ν (g n) (A1 n)))
      =(λ n:ℕ, (μ (g n)) - (ν (g n))),
  { apply funext, intro n, rw measure_sub_fn_apply},
  rw measure_sub_fn_apply,
  rw A3,
  rw ennreal.tsum_sub,
  repeat {rw measure_theory.measure_Union A2 A1},
  {
    rw ← measure_theory.measure_Union A2 A1,
    apply measure_theory.measure_ne_top,
  },
  {
    rw le_func_def2,
    intro i,
    apply H,
    apply A1,
  }, 
end

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


lemma measure_sub_add {α:Type*} [M:measurable_space α] 
    {μ ν:measure_theory.measure α} (H:ν ≤ μ) 
    [H2:measure_theory.finite_measure ν]:μ = ν + (measure_sub H) :=
begin
  apply measure_theory.measure.ext,
  intros s A3,
  simp,
  rw measure_sub_apply,
  rw add_comm,
  rw ennreal.sub_add_cancel_of_le,
  apply H,
  repeat {apply A3},
end

lemma measure_sub_eq {α:Type*} [M:measurable_space α] 
    (μ ν:measure_theory.measure α) (H:ν ≤ μ) 
    (H2:measure_theory.finite_measure ν):(μ - ν) = (measure_sub H) :=
begin
  rw measure_theory.measure.sub_def,
  have A1B:μ = ν + measure_sub H :=
          measure_sub_add H,

  apply le_antisymm,
  {
    have A1:μ ≤ (measure_sub H) + ν,
    {
      rw add_comm,
      rw ← A1B,
      apply le_refl μ,
    },
    have A2:(measure_sub H) ∈ {d|μ ≤ d + ν} := A1, 
    apply Inf_le A2,
  },
  {
    apply @le_Inf (measure_theory.measure α) _,
    intros b B1,
    simp at B1,
    rw A1B at B1,
    rw add_comm at B1,
    apply measure_theory.measure.le_of_add_le_add_right B1,
  },
end

end sub

lemma sub_apply {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω} [A2:measure_theory.finite_measure ν]:
  is_measurable S → 
  ν ≤ μ → (μ - ν) S = μ S - ν S :=
begin
  intros A1 A3,
  rw sub.measure_sub_eq μ ν A3 A2,
  apply sub.measure_sub_apply,
  apply A1,
end


end measure


end measure_theory

---------------------------------------------------------------------------------------------------

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
  have A4:(λ n, μ.with_density (h n) S) = (λ n,  ∫⁻ (ω:Ω), (set.indicator S (h n)) ω ∂ μ),
  {
    apply funext,
    intro n,
    rw measure_theory.with_density_apply2',
    apply A1,
  },
  rw A4,
  clear A4,
  rw measure_theory.with_density_apply2',
  rw supr_indicator,
  rw measure_theory.lintegral_supr2,
  {
    intro n,
    apply measurable.indicator,
    apply A2 n,
    apply A1,
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

--TODO: replace with measure_theory.measure.smul_apply
lemma ennreal_smul_measure_apply {α:Type*}
    [measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α)
    (s:set α) (H:is_measurable s):
    (x  • μ) s = x * (μ s) :=
begin
  rw measure_theory.measure.smul_apply,
end

def measure_theory.measure.is_support {α:Type*} [measurable_space α]
    (μ:measure_theory.measure α) (S:set α):Prop := is_measurable S ∧ μ (Sᶜ) = 0

lemma outer_measure_measure_of_le {Ω:Type*} {μ ν:measure_theory.outer_measure Ω}:
    μ ≤ ν ↔
    (μ.measure_of) ≤
    (ν.measure_of) :=
begin
  refl,
end

lemma measure_theory.measure.Union_nat {α : Type*} [M : measurable_space α] 
    {μ:measure_theory.measure α} {f:ℕ → set α}:μ (⋃ i, f i) ≤ ∑' i, μ (f i) :=
begin
  rw measure.apply,
  have A1:(λ i, μ (f i))=(λ i, μ.to_outer_measure.measure_of (f i)) := rfl,
  rw A1,
  apply measure_theory.outer_measure.Union_nat,
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

lemma with_density_le_with_density {Ω:Type*} {M:measurable_space Ω}
  {μ:measure_theory.measure Ω} {x y:Ω → ennreal} 
  {S:set Ω}:
  is_measurable S →
  (∀ ω ∈ S, x ω ≤ y ω) →  
  μ.with_density x S ≤ μ.with_density y S :=
begin
  intros A3 A4,
  rw measure_theory.with_density_apply2' μ x S A3,
  rw measure_theory.with_density_apply2' μ y S A3,
  apply measure_theory.lintegral_mono,

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


/-
  The Lebesgue-Radon-Nikodym theorem, while it delves deeply into the nuances of
  measure theory, provides the foundation for statistics and probability. Specifically,
  continuous random variables can be represented by a density function. The 
  Lebesgue-Radon-Nikodym theorem (and the Radon-Nikodym theorem) exactly characterize
  what probability measures have this simple representation: specifically, those that
  are absolutely continuous with respect to the Lebesgue measure. This theorem, like
  the fundamental theorem of calculus, provides a deep insight that can be easily used
  even by those who do not understand the nuances of the proof.
 -/
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

/-
  It is hard to generalize this.
 -/
lemma nnreal.mul_pos_iff_pos_pos 
    {a b:nnreal}:(0 < a * b) ↔ (0 < a)∧ (0 < b) :=
begin
  split;intros A1,
  {
    rw zero_lt_iff_ne_zero at A1,
    repeat {rw zero_lt_iff_ne_zero},
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

lemma nnreal.pos_iff {a:nnreal}:0 < a ↔ a ≠ 0 :=
begin
  split;intros B1,
  {
    intros C1,
    subst a,
    simp at B1,
    apply B1,
  },
  {
    apply by_contradiction,
    intros D1,
    apply B1,
    rw ← le_zero_iff_eq,
    apply le_of_not_lt D1,
  },
end


lemma ennreal.inv_mul_eq_inv_mul_inv {a b:ennreal}:(a≠ 0) → (b≠ 0) → (a * b)⁻¹=a⁻¹ * b⁻¹ :=
begin
  cases a;simp;cases b;simp,
  intros A1 A2,
  rw ← ennreal.coe_mul,
  repeat {rw ← ennreal.coe_inv},
  rw ← ennreal.coe_mul,
  rw ennreal.coe_eq_coe,
  apply @nnreal.inv_mul_eq_inv_mul_inv a b,
  apply A2,
  apply A1,
  rw ← @nnreal.pos_iff (a * b),
  rw nnreal.mul_pos_iff_pos_pos,
  repeat {rw zero_lt_iff_ne_zero},
  apply and.intro A1 A2,
end


lemma ennreal.div_dist {a b c:ennreal}:(b≠ 0) → (c≠ 0) → a/(b * c)=(a/b)/c :=
begin
  intros A1 A2,
  rw ennreal.div_def,
  rw ennreal.inv_mul_eq_inv_mul_inv,
  rw ← mul_assoc,
  rw ennreal.div_def,
  rw ennreal.div_def,
  apply A1,
  apply A2,
end


lemma ennreal.div_eq_zero_iff {a b:ennreal}:a/b=0 ↔ (a = 0) ∨ (b = ⊤) :=
begin
  cases a;cases b;split;simp;intros A1;simp;simp at A1,
end

/-
  Helper function to lift nnreal.exists_unit_frac_lt_pos to ennreal.
 -/
lemma ennreal.exists_unit_frac_lt_pos' {ε:nnreal}:0 < ε → (∃ n:ℕ, (1/((n:ennreal) + 1)) < (ε:ennreal)) :=
begin
  intros A1,
--  simp at A1,
  have C1:= nnreal.exists_unit_frac_lt_pos A1,   
  cases C1 with n A1,
  apply exists.intro n,
  have D1:((1:nnreal):ennreal) = 1 := rfl,
  rw ← D1,
  have D2:((n:nnreal):ennreal) = (n:ennreal),
  {
    simp,
  },
  rw ← D2,
  rw ← ennreal.coe_add,
  rw ← ennreal.coe_div,
  rw ennreal.coe_lt_coe,
  apply A1,
  simp,
end


lemma ennreal.exists_unit_frac_lt_pos {ε:ennreal}:0 < ε → (∃ n:ℕ, (1/((n:ennreal) + 1)) < ε) :=
begin
  cases ε,
  {
     intros A1,
     have B1:(0:nnreal) < (1:nnreal),
     {
       apply zero_lt_one,
     },
     have B1:=ennreal.exists_unit_frac_lt_pos' B1,
     cases B1 with n B1,
     apply exists.intro n,
     apply lt_of_lt_of_le B1,
     simp,
  },
  {
    intros A1,
    simp at A1,
    have C1:= ennreal.exists_unit_frac_lt_pos' A1,   
    apply C1,
  },
end


lemma ennreal.zero_of_le_all_unit_frac {x:ennreal}:
    (∀ (n:ℕ), (x ≤ 1/((n:ennreal) + 1))) →  (x = 0) :=
begin
  intros A1,
  rw ← not_exists_not at A1, 
  apply by_contradiction,
  intros B1,
  apply A1,
  have B2:0 < x,
  {
    rw  zero_lt_iff_ne_zero,
    apply B1,
  },
  have B3:= ennreal.exists_unit_frac_lt_pos B2,
  cases B3 with n B3,
  apply exists.intro n,
  apply not_le_of_lt,
  apply B3,
end



lemma ennreal.unit_frac_pos {n:ℕ}:(1/((n:ennreal) + 1))>0 :=
begin
  simp,
  intros B1,
  rw ennreal.add_eq_top at B1,
  simp at B1,
  apply B1,
end


lemma ennreal.div_eq_top_iff {a b:ennreal}:a/b=⊤ ↔ 
                             ((a = ⊤)∧(b≠ ⊤) )∨ ((a≠ 0)∧(b=0)):=
begin
  rw ennreal.div_def,
  cases a;cases b;simp,
end

lemma ennreal.unit_frac_ne_top {n:ℕ}:(1/((n:ennreal) + 1))≠ ⊤ :=
begin
  intro A1, 
  rw ennreal.div_eq_top_iff at A1,
  simp at A1,
  apply A1,
end

lemma lt_eq_le_compl {δ α:Type*}
  [linear_order α] {f g : δ → α}:{a | f a < g a} ={a | g a ≤ f a}ᶜ :=
begin
    apply set.ext,
    intros ω;split;intros A3A;simp;simp at A3A;apply A3A,
end

lemma ennreal.lt_add_self {a b:ennreal}:a < ⊤ → 0 < b → a < a + b :=
begin
  cases a;cases b;simp,
  intros A1,
  rw ← ennreal.coe_add,
  rw ennreal.coe_lt_coe,
  simp,
  apply A1,
end

---------------------------End theorems to move----------------------------------


lemma simple_restrict_eq_indicator_const {Ω:Type*} {M:measurable_space Ω} 
  (S:set Ω) (x:ennreal):(is_measurable S) →
  ⇑((measure_theory.simple_func.const Ω x).restrict S) = (set.indicator S (λ ω:Ω, x)) :=
begin
  intro A1,
  rw measure_theory.simple_func.coe_restrict,
  rw measure_theory.simple_func.coe_const,
  apply A1,
end

lemma with_density_const_apply {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {k:ennreal} {S:set Ω}:is_measurable S →
   μ.with_density (λ ω:Ω, k) S = k * μ S :=
begin
  intros B1,
  rw measure_theory.with_density_apply2',
  rw ← simple_restrict_eq_indicator_const,
  rw measure_theory.simple_func.lintegral_eq_lintegral,
  rw measure_theory.simple_func.restrict_const_lintegral,
  repeat {apply B1},
end

lemma measure_theory.outer_measure.Inf_gen_nonempty3 {α:Type*} (m : set (measure_theory.outer_measure α))
    (t:set α) :m.nonempty →
  measure_theory.outer_measure.Inf_gen m t =
   (⨅ (μ : measure_theory.outer_measure α) (H:μ∈ m), μ t) :=
begin
  intro A1,
  have B1:∃ μ:measure_theory.outer_measure α, μ ∈ m,
  {
    rw set.nonempty_def at A1,
    apply A1,
  },
  cases B1 with μ B1,
  rw measure_theory.outer_measure.Inf_gen_nonempty2 _ μ B1,
end

lemma measure_theory.outer_measure.of_function_def2 
  {α : Type*} (m : set α → ennreal) (m_empty : m ∅ = 0)  (s:set α):
  (measure_theory.outer_measure.of_function m m_empty) s
    = ⨅{f : ℕ → set α} (h : s ⊆ ⋃i, f i), ∑'i, m (f i)  := 
begin
  rw [measure_theory.outer_measure.of_function],
  rw ← measure_theory.outer_measure.measure_of_eq_coe,
end


lemma set.Union_inter_eq_inter_Union {α
   β:Type*} {f:α → set β} {T:set β}:
    (⋃ (a:α), f a ∩ T) =  T ∩ (⋃ (a:α), f a) :=
begin
  apply set.ext,
  intro b,split;intros B1;simp;simp at B1;
  apply and.intro B1.right B1.left,
end


lemma set.Union_union_eq_union_Union {α
   β:Type*} [NE:nonempty α] {f:α → set β} {T:set β}:
    (⋃ (a:α), f a ∪ T) =  T ∪ (⋃ (a:α), f a) :=
begin
  apply set.ext,
  intro b,split;intros B1;simp;simp at B1,
  {
    cases B1 with a B2,
    cases B2 with B3 B4,
    {
       right,
       apply exists.intro a B3,
    },
    {
      left,
      apply B4,
    },
  },
  {
    cases B1 with C1 C2,
    {
       apply nonempty.elim NE,
       intro a,
       apply exists.intro a,
       right,
       apply C1,
    },
    {
       cases C2 with a C3,
       apply exists.intro a,
       left,
       apply C3,
    },
  },
end

lemma set.subset_union_compl_of_inter_subset {α:Type*} {A B C:set α}:A ∩ B ⊆ C →
    A ⊆ C ∪ Bᶜ :=
begin
  intro D1,
  rw set.subset_def,
  intros x D2,
  rw set.subset_def at D1,
  simp,
  cases (classical.em (x∈ B)) with D3 D3,
  {
    left,
    apply D1,
    simp [D2,D3],
  },
  {
    right,
    apply D3,
  },
end 



lemma infi_le_trans {α β:Type*} [complete_lattice β] (a:α) (f:α → β) 
    (b:β):(f a ≤ b) → (⨅ (c:α), (f c)) ≤ b :=
begin
  intros A1,
  apply le_trans _ A1,
  apply @infi_le _ _ _, 
end

/-
  I saw this pattern a bunch below. It could be more widely used.
 -/
lemma infi_set_le_trans {α β:Type*} [complete_lattice β] (a:α) (P:α → Prop) (f:α → β) 
    (b:β):(P a) → (f a ≤ b) → (⨅ (c:α) (H:P c), f c) ≤ b :=
begin
  intros A1 A2,
  apply infi_le_trans a,
  rw infi_prop_def A1,
  apply A2,
end

lemma infi_set_image {α β γ:Type*} [complete_lattice γ] (S:set α) (f:α → β) 
    (g:β → γ):(⨅ (c∈ (f '' S)), g c) = ⨅  (a∈ S), (g ∘ f) a :=
begin
  apply le_antisymm;simp,
  {
    intros a B1,
    apply infi_le_trans (f a),
    apply infi_le_trans a,
    rw infi_prop_def,
    apply and.intro B1,
    refl,
  },
  {
    intros b a2 C1 C2,
    apply infi_le_trans a2,
    rw infi_prop_def C1,
    rw C2,
  },
end




lemma measure_theory.outer_measure.to_measure_to_outer_measure_eq_trim {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.outer_measure Ω} (H:M ≤ (μ).caratheodory):
    (μ.to_measure H).to_outer_measure = μ.trim :=
begin
  apply measure_theory.outer_measure.ext,
  intros S,
  unfold measure_theory.outer_measure.to_measure measure_theory.measure.to_outer_measure
    measure_theory.outer_measure.trim
    measure_theory.measure.of_measurable,
  simp,
  refl,
end




--Used in restrict_trimmed_of_trimmed
lemma measure_theory.le_extend2 {α:Type*} [measurable_space α] {x:ennreal} 
    {h:Π (s:set α), (is_measurable s)  → ennreal} (s:set α):
  (Π (H:is_measurable s), (x ≤ h s H)) → (x ≤ measure_theory.extend h s) :=
begin
  intros A1,
  cases (classical.em (is_measurable s)) with B1 B1,
  {
    apply le_trans (A1 B1),
    apply measure_theory.le_extend,
  },
  {
    unfold measure_theory.extend,
    apply @le_infi ennreal _ _,
    intros contra,
    exfalso,
    apply B1 contra,
  },
end 


--Beautiful, but useless.
lemma measure_theory.extend_le_extend_of_le {α:Type*} [measurable_space α]
 {f g : Π (s : set α), (is_measurable s)  → ennreal} (h_le_meas : ∀ (s : set α) (h:is_measurable s), f s h ≤ g s h) : 
  (measure_theory.extend f ≤ measure_theory.extend g) :=
begin
  intros s,
  cases (classical.em (is_measurable s)) with h_is_meas h_is_not_meas,
  { rw (measure_theory.extend_eq f h_is_meas),
    apply le_trans (h_le_meas s h_is_meas) (measure_theory.le_extend g h_is_meas) },
  { unfold measure_theory.extend,
    apply @le_infi ennreal _ _,
    intros contra,
    exfalso, apply h_is_not_meas contra },
end 


--@[simp]
lemma simple_logic {A B C:Prop}:(A ∨ B → C → A) ↔  (B → C → A) :=
begin
  split, intros h_A_of_C_of_A_or_B h_B h_C,
  apply h_A_of_C_of_A_or_B (or.inr h_B) h_C,
  intros h_A_of_B_of_C h_A_or_B h_C,
  cases (h_A_or_B) with h_A h_B,
  apply h_A,
  apply h_A_of_B_of_C h_B h_C,
end

--@[simp]
lemma contra_logic' {A B:Prop}:(¬A → (A) → B) ↔  true :=
begin
  simp,
  intros h_not_A h_A,
  exfalso, apply h_not_A h_A,
end

lemma measure_theory.measure.restrict_le_restrict_of_le {Ω:Type*} [measurable_space Ω]
  {μ ν:measure_theory.measure Ω} (S:set Ω):
  μ  ≤ ν → μ.restrict S ≤ ν.restrict S :=
begin
  intros A1,
  apply measure_theory.measure.restrict_mono,
  apply set.subset.refl,
  apply A1,
end

lemma measure_theory.measure.add_compl_inter {Ω:Type*} [measurable_space Ω]
  (μ:measure_theory.measure Ω) (S T:set Ω):(is_measurable S) → 
  (is_measurable T) →
  (μ T = μ (S ∩ T) + μ (Sᶜ ∩ T)) :=
begin
  intros A1 A2,
  have A3:T = (S∩ T) ∪ (Sᶜ ∩ T),
  {
    rw ← set.inter_distrib_right,
    rw set.union_compl_self,
    simp,
  },
  have A4:μ T =  μ ( (S∩ T) ∪ (Sᶜ ∩ T)),
  {
    rw ← A3,
  },
  rw A4,
  rw measure_theory.measure_union,
  rw set.inter_comm,
  rw set.inter_comm _ T,
  apply set.disjoint_inter_compl,
  apply is_measurable.inter A1 A2,
  apply is_measurable.inter (is_measurable.compl A1) A2,
end

lemma measure_theory.measure.le_of_partition {Ω:Type*} [M:measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S T:set Ω}:is_measurable S →
  is_measurable T →
  μ (S ∩ T) ≤ ν (S ∩ T) →
  μ (Sᶜ ∩ T) ≤ ν (Sᶜ ∩ T) →
  μ T ≤ ν T :=
begin
  intros A1 A2 A3 A4,
  rw measure_theory.measure.add_compl_inter μ S T,
  rw measure_theory.measure.add_compl_inter ν S T,
  have B1:μ (S ∩ T) + μ (Sᶜ ∩ T) ≤ ν (S ∩ T) + μ (Sᶜ ∩ T),
  {
    apply add_le_add_right A3,
  },
  apply le_trans B1,
  apply add_le_add_left A4,
  repeat {assumption},
end

lemma Inf_le_Inf' {α:Type*} [complete_lattice α] {S T:set α}:(∀ t∈ T, ∃ s∈ S,
  s ≤ t) → Inf S ≤ Inf T :=
begin
  intros A1,
  apply @le_Inf,
  intros t B1,
  have B2 := A1 t B1,
  cases B2 with s B2,
  cases B2 with B2 B3,
  apply le_trans _ B3,
  apply @Inf_le,
  apply B2
end

lemma measure_theory.outer_measure.le_top_caratheodory {Ω:Type*} [M:measurable_space Ω]:
  M ≤ (⊤:measure_theory.outer_measure Ω).caratheodory :=
begin
  rw measure_theory.outer_measure.top_caratheodory,
  simp
end

lemma measure_theory.measure.of_measurable_apply' {α:Type*} [M:measurable_space α]
(m : Π (s : set α), is_measurable s → ennreal)
  (m0 : m ∅ is_measurable.empty = 0)
  (mU : ∀ {{f : ℕ → set α}} (h : ∀i, is_measurable (f i)),
    pairwise (disjoint on f) →
    m (⋃i, f i) (is_measurable.Union h) = (∑'i, m (f i) (h i))) (S:set α):
  measure_theory.measure.of_measurable m m0 mU S = 
  measure_theory.induced_outer_measure m _ m0 S :=
begin
  unfold measure_theory.measure.of_measurable,
  simp,
  rw measure.apply, 
end

lemma measure_theory.outer_measure.top_eq {Ω:Type*} [M:measurable_space Ω]:
    ⇑(⊤:measure_theory.outer_measure Ω) = (λ (s:set Ω), (@ite (s=∅) (classical.prop_decidable (s=∅)) ennreal 0 ⊤)) :=
begin
  apply funext,
  intro S,
  cases (classical.em (S = ∅)) with B1 B1,
  {
    rw if_pos,
    subst S,
    apply measure_theory.outer_measure.empty',
    apply B1,
  },
  {
    rw if_neg,
    apply measure_theory.outer_measure.top_apply,
    rw ← set.ne_empty_iff_nonempty,
    apply B1,
    apply B1,
  },
end

lemma measure_theory.outer_measure.extend_top {Ω:Type*} [M:measurable_space Ω]:
  (measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), (⊤:measure_theory.outer_measure Ω) s))=(λ (s:set Ω), (@ite (s=∅) (classical.prop_decidable (s=∅)) ennreal 0 ⊤)) :=
begin
  apply funext,
  intro S,
  rw measure_theory.outer_measure.top_eq,
  cases (classical.em (is_measurable S)) with B1 B1,
  {
    unfold measure_theory.extend,
    rw infi_prop_def,
    apply B1,
  },
  {
    unfold measure_theory.extend,
    rw infi_prop_false,
    rw if_neg,
    intros B2,
    apply B1,
    subst S,
    simp,
    apply B1,
  },
end

lemma measure_theory.outer_measure.extend_top' {Ω:Type*} [M:measurable_space Ω]:
  (measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), (⊤:measure_theory.outer_measure Ω) s))=(⊤:measure_theory.outer_measure Ω) :=
begin
  rw measure_theory.outer_measure.extend_top,
  rw measure_theory.outer_measure.top_eq,
end


--Checked requirements to here.
lemma subst_apply_empty_zero {Ω:Type*} {f g:set Ω → ennreal}:(f = g) → (f ∅ = 0) → (g ∅ = 0) :=
begin
  intros A1 A2,
  subst f,
  apply A2,
end

lemma measure_theory.outer_measure.of_function_subst {Ω:Type*} [M:measurable_space Ω]
   {f g:set Ω → ennreal} {P:f ∅ = 0} (H:f = g):
  measure_theory.outer_measure.of_function f P =
  measure_theory.outer_measure.of_function g (subst_apply_empty_zero H P) :=
begin
  subst g,
end


lemma measure_theory.outer_measure.of_function_eq' {Ω:Type*} [M:measurable_space Ω]
  {μ:measure_theory.outer_measure Ω} (H:μ ∅ = 0): 
  measure_theory.outer_measure.of_function (⇑μ) H = μ :=
begin
  apply measure_theory.outer_measure.ext,
  intro S,
  apply measure_theory.outer_measure.of_function_eq,
  {
    intros T B1,
    apply measure_theory.outer_measure.mono',
    apply B1, 
  },
  {
    intros f,
    apply measure_theory.outer_measure.Union_nat,
  },
end


lemma measure_theory.outer_measure.top_eq_trim {Ω:Type*} [M:measurable_space Ω]:
  (⊤:measure_theory.outer_measure Ω).trim = ⊤ :=
begin
  unfold measure_theory.outer_measure.trim,
  unfold measure_theory.induced_outer_measure,
  have B1:= @measure_theory.outer_measure.extend_top' Ω M,
  rw measure_theory.outer_measure.of_function_subst B1,  
  rw measure_theory.outer_measure.of_function_eq',
end


lemma measure_theory.outer_measure.top_to_measure_to_outer_measure_eq_top {Ω:Type*} [M:measurable_space Ω]:
  ((⊤:measure_theory.outer_measure Ω).to_measure measure_theory.outer_measure.le_top_caratheodory).to_outer_measure  = ⊤ :=
begin
  apply measure_theory.outer_measure.ext,
  intro S,
  unfold measure_theory.outer_measure.to_measure,
  simp,
  rw measure_theory.measure.of_measurable_apply',
  unfold measure_theory.induced_outer_measure,
  have B1:= @measure_theory.outer_measure.extend_top' Ω M,
  rw measure_theory.outer_measure.of_function_subst B1,  
  rw measure_theory.outer_measure.of_function_eq',
end


/--
  One could extract many monotone relationships from this:
  induced_outer_measure, extend, of_function, et cetera.
  However, I wouldn't be surprised to find them in the library.
 -/
lemma measure_theory.outer_measure.trim_monotone {Ω:Type*} [M:measurable_space Ω]
  (μ ν:measure_theory.outer_measure Ω):μ ≤ ν → μ.trim ≤ ν.trim :=
begin
  intros A1,
  rw outer_measure_measure_of_le,
  unfold measure_theory.outer_measure.trim,
  unfold measure_theory.induced_outer_measure,
  unfold measure_theory.outer_measure.of_function,
  intros S,
  simp,
  intros f B1,
  have B2:(∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), μ s) (f i)) ≤
    ∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), ν s) (f i),
  {
    apply ennreal.tsum_le_tsum,
    unfold measure_theory.extend,
    intros n,
    simp,
    intros B2A,
    rw infi_prop_def,
    apply A1,
    apply B2A,
  },
  apply le_trans _ B2,
  have B3:(⨅ (h : S ⊆ ⋃ (i : ℕ), f i),(∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), μ s) (f i))) = ∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), μ s) (f i),
  {
    rw infi_prop_def,
    apply B1,
  }, 
  rw ← B3,
  apply @infi_le ennreal _ _,
end


lemma measure_theory.measure.to_outer_measure_eq_top {Ω:Type*} [M:measurable_space Ω]:
   (⊤:measure_theory.measure Ω).to_outer_measure = ⊤ := 
begin
  rw ← measure_theory.measure.trimmed,
  rw ← @top_le_iff (measure_theory.outer_measure Ω) _,
  have B1:((⊤:measure_theory.outer_measure Ω).to_measure measure_theory.outer_measure.le_top_caratheodory).to_outer_measure.trim ≤ (⊤:measure_theory.measure Ω).to_outer_measure.trim,
  {
    apply measure_theory.outer_measure.trim_monotone,
    apply measure_theory.measure.to_outer_measure_le.mpr,
    simp
  }, 
  rw measure_theory.outer_measure.top_to_measure_to_outer_measure_eq_top at B1,
  rw measure_theory.outer_measure.top_eq_trim at B1,
  apply B1,
end


lemma measure_theory.measure.top_apply {Ω:Type*} [M:measurable_space Ω]
   {S:set Ω}:S.nonempty → (⊤:measure_theory.measure Ω)(S) = (⊤:ennreal) :=
begin
  intro A1,
  rw measure.apply,
  rw measure_theory.measure.to_outer_measure_eq_top,
  simp,
  rw measure_theory.outer_measure.top_apply A1,
end

lemma measure_theory.measure.le_add {Ω:Type*} [M:measurable_space Ω] {μ ν:measure_theory.measure Ω}:μ ≤ μ + ν :=
begin
  intros S B1,
  simp [le_add_nonnegative],
end

lemma measure_theory.measure.sub_restrict_comm {Ω:Type*} [M:measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω}:is_measurable S →
  (μ - ν).restrict S = (μ.restrict S) - (ν.restrict S) :=
begin
  intro A1,
  rw measure_theory.measure.sub_def,
  rw measure_theory.measure.sub_def,
  have G1:{d : measure_theory.measure Ω | μ ≤ d + ν}.nonempty,
  {
    apply @set.nonempty_of_mem _ _ μ,
    simp,
    apply measure_theory.measure.le_add,
  },
  rw measure_theory.measure.restrict_Inf_eq_Inf_restrict _ G1 A1,
  apply le_antisymm,
  {
    apply @Inf_le_Inf' (measure_theory.measure Ω) _,
    intros t B1,
    simp at B1,
    apply exists.intro (t.restrict S),
    split,
    {
      simp,
      apply exists.intro (t + (⊤:measure_theory.measure Ω).restrict Sᶜ),
      split,
      { rw add_assoc,
        rw add_comm _ ν,
        rw ← add_assoc,
        rw measure_theory.measure.le_iff,
        intros T E1,
        have E2:is_measurable (S ∩ T) := is_measurable.inter A1 E1,
        --rw measure_theory.measure.add_apply,
        apply measure_theory.measure.le_of_partition _ _ A1 E1;
          rw measure_theory.measure.add_apply,
        {
          rw measure_theory.measure.restrict_apply E2,
          rw set.inter_assoc,
          rw set.inter_comm _ Sᶜ,
          rw ← set.inter_assoc,
          rw set.inter_compl_self,
          simp,
          --rw measure_theory.measure.le_iff at B1,
          have B2 := B1 (S ∩ T) E2,
          rw measure_theory.measure.add_apply at B2,
          rw measure_theory.measure.restrict_apply E2 at B2,
          rw measure_theory.measure.restrict_apply E2 at B2,
          have E3:S ∩ T ∩ S = S ∩ T,
          {
            rw set.inter_eq_self_of_subset_left,
            apply set.inter_subset_left S T,
          },
          rw E3 at B2,
          apply B2,
        },
        cases (@set.eq_empty_or_nonempty _ (Sᶜ ∩ T)) with E4 E4,
        {
          rw E4,
          simp,
        },

        {
          rw measure_theory.measure.restrict_apply,
          have E5:Sᶜ ∩ T ∩ Sᶜ = Sᶜ ∩ T,
          {
            rw set.inter_eq_self_of_subset_left,
            apply set.inter_subset_left Sᶜ T,
          },
          rw E5,
          have E6:(⊤:measure_theory.measure Ω)(Sᶜ ∩ T) = (⊤:ennreal),
          {
            apply measure_theory.measure.top_apply,
            apply E4,
          },
          rw E6,
          simp,
          apply is_measurable.inter (is_measurable.compl A1) E1,
        },
      },
      {
        apply measure_theory.measure.ext,
        intros T D1,
        rw measure_theory.measure.restrict_apply D1,
        rw measure_theory.measure.restrict_apply D1,
        rw measure_theory.measure.add_apply,
        rw measure_theory.measure.restrict_apply (is_measurable.inter D1 A1),
        have D2:T ∩ S ∩ Sᶜ = ∅,
        {
          rw set.inter_assoc,
          simp,
        },
        rw D2,
        simp,
      },
    },
    {
      apply measure_theory.measure.restrict_le_self,
    },
  },
  {
    apply @Inf_le_Inf' (measure_theory.measure Ω) _,
    intros s C1,
    simp at C1,
    cases C1 with t C1,
    cases C1 with C1 C2,
    subst s,
    apply exists.intro (t.restrict S),
    split,
    {
      simp,
      rw ← measure_theory.measure.restrict_add,
      apply measure_theory.measure.restrict_le_restrict_of_le,
      apply C1,
    },
    {
      apply le_refl _,
    },
  },
end

lemma jordan_decomposition_junior_zero {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S:set Ω)
  :μ.restrict S ≤ ν.restrict S → is_measurable S →
  (μ - ν) S = 0 :=
begin
  intros A1 B1,
  rw ← measure_theory.measure.restrict_apply_self _ B1,
  rw measure_theory.measure.sub_restrict_comm,
  rw measure_theory.measure.sub_eq_zero_if_le,
  repeat {simp [*]},
end

--This works with EITHER ν or μ being finite, or even ν S < ⊤.
lemma jordan_decomposition_junior_apply {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S:set Ω) [AX:measure_theory.finite_measure ν]:
  (ν.restrict S ≤ μ.restrict S) → (is_measurable S) →
  (μ - ν) S = μ S - ν S :=
begin
  intros A1 B1,
  rw ← measure_theory.measure.restrict_apply_self _ B1,
  rw measure_theory.measure.sub_restrict_comm _ _,
  rw @measure_theory.measure.sub_apply Ω _ _ _ S (measure_theory.finite_measure_restrict ν S) B1 A1,
  repeat {rw measure_theory.measure.restrict_apply_self},
  repeat {exact B1},
end


/--
  A jordan decomposition of subtraction.
 -/
lemma jordan_decomposition_nonneg_sub {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S T:set Ω) [A1:measure_theory.finite_measure μ]: 
    is_measurable T → is_measurable S → μ.restrict S ≤ ν.restrict S →
    ν.restrict Sᶜ ≤ μ.restrict Sᶜ →
    (ν - μ) T = ν (S ∩ T) - μ (S ∩ T) :=
begin
  intros A3 A2 A5 A6,
  
  have B1:(ν - μ) T = (ν - μ) (S∩ T) + (ν - μ) (Sᶜ ∩ T),
  {
    rw measure_theory.measure.add_compl_inter,
    apply A2,
    apply A3,
  },
  have B2:(ν - μ) (S∩ T) = ν (S ∩ T) - μ (S ∩ T),
  {
    apply jordan_decomposition_junior_apply,
    apply restrict_le_restrict_of_restrict_le_restrict_of_subset A5,
    repeat {simp [A2,A3]},
  },
  have B3:(ν - μ) (Sᶜ ∩ T) = 0,
  {
    apply jordan_decomposition_junior_zero,
    apply restrict_le_restrict_of_restrict_le_restrict_of_subset A6,
    simp,
    repeat {simp [A2,A3]},
  },
  rw [B1, B2, B3, add_zero],
end

--TODO: Move to hahn.lean (might be useful).
lemma inter_le_inter_of_restrict_le_restrict {Ω:Type*} [M:measurable_space Ω] 
    {μ ν:measure_theory.measure Ω} {T U:set Ω}:μ.restrict T ≤ ν.restrict T → 
    is_measurable T → is_measurable U → μ (T ∩ U) ≤ ν (T ∩ U) :=
begin
  intros A3 A1 A2,
  have B1:T ∩ U ⊆ T,
  {simp},
  apply @le_of_subset_of_restrict_le_restrict Ω M μ ν T (T ∩ U) B1 A3,
  repeat {simp [A1,A2]},
end

--This may be gotten by easier methods.
lemma measure_theory.measure.sub_le_sub {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (T:set Ω) [A1:measure_theory.finite_measure μ]:
    is_measurable T → (ν T - μ T) ≤ (ν - μ) T :=
begin
  intros A2,
  have B1 := hahn_unsigned_inequality_decomp' ν μ,
  cases B1 with U B1,
  cases B1 with C1 B1,
  rw jordan_decomposition_nonneg_sub μ ν Uᶜ,
  {
    rw measure_theory.measure.add_compl_inter ν _ _  C1 A2,
    rw measure_theory.measure.add_compl_inter μ _ _  C1 A2,
    rw ennreal.sub_le_iff_le_add,
    rw add_comm (μ (U ∩ T)) (μ (Uᶜ ∩ T)),
    rw ← add_assoc,
    have C4:ν (Uᶜ ∩ T) ≤ ν (Uᶜ ∩ T) - μ (Uᶜ ∩ T) + μ (Uᶜ ∩ T),
    {
      apply ennreal.le_sub_add_self,
    }, 
    have C5 := add_le_add_right C4 (μ (U ∩ T)),
    apply le_trans _ C5,
    rw add_comm,
    apply add_le_add_left _ _,
    apply inter_le_inter_of_restrict_le_restrict B1.left C1 A2,
  },
  repeat {simp [B1,A2,C1]},
end


--This is a natural break between subtraction and Radon-Nikodym.
lemma measure_theory.measure.is_support_def {α:Type*} [measurable_space α]
    (μ:measure_theory.measure α) (S:set α):
    μ.is_support S = (is_measurable S ∧ μ (Sᶜ) = 0) := rfl

def measure_theory.measure.perpendicular {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):Prop :=
    (∃ S T:set α, μ.is_support S ∧ ν.is_support T ∧  
    disjoint S T)


lemma measure_theory.measure.perpendicular_def {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):μ.perpendicular ν =
    (∃ S T:set α, μ.is_support S ∧ ν.is_support T ∧  
    disjoint S T) := rfl

lemma measure_theory.measure.perpendicular_def2 {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):μ.perpendicular ν ↔
    (∃ S:set α,  is_measurable S ∧ μ S = 0 ∧  ν (Sᶜ) = 0) :=
begin
  rw measure_theory.measure.perpendicular_def,
  split;intros B1,
  {
    cases B1 with S B1,
    cases B1 with T B1,
    cases B1 with B1 B2,
    cases B2 with B2 B3,
    rw measure_theory.measure.is_support_def at B1,
    rw measure_theory.measure.is_support_def at B2,

    apply exists.intro T,
    split,
    {
      apply B2.left,      
    },
    split,
    {
      cases B1 with C1 C2,
      rw ← le_zero_iff_eq,
      rw ← le_zero_iff_eq at C2,
      apply le_trans _ C2,
      apply measure_theory.measure_mono,
      rw set.disjoint_iff_inter_eq_empty at B3,
      rw set.inter_comm at B3,
      rw ← set.subset_compl_iff_disjoint at B3,
      apply B3,
    },
    {
      apply B2.right,
    },
  },
  {
    cases B1 with S B1,
    apply exists.intro Sᶜ,
    apply exists.intro S,
    split,
    {
      rw measure_theory.measure.is_support_def,
      apply and.intro (is_measurable.compl (B1.left)),
      simp,
      apply B1.right.left,
    },
    split,
    {
      rw measure_theory.measure.is_support_def,
      apply and.intro (B1.left) (B1.right.right),
    },
    {
      rw set.disjoint_iff_inter_eq_empty,
      rw ← set.subset_compl_iff_disjoint,
      apply set.subset.refl Sᶜ,
    },
  },
end


lemma measure_theory.measure.perpendicular_intro {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) {S:set α}:is_measurable S → 
    μ S = 0 → ν (Sᶜ) = 0 →
μ.perpendicular ν :=
begin
  intros A1 A2 A3,
  rw measure_theory.measure.perpendicular_def2,
  apply exists.intro S (and.intro A1 (and.intro A2 A3)),
end

lemma measure_theory.measure.not_perpendicular {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) {S:set α}:(¬(μ.perpendicular ν)) → is_measurable S → 
    μ S = 0 → 0 < ν (Sᶜ)  :=
begin
  intros A1 A2 A3,
  rw zero_lt_iff_ne_zero,
  intros A4,
  apply A1,
  apply measure_theory.measure.perpendicular_intro μ ν A2 A3 A4,
end


lemma measure_theory.measure.perpendicular_symmetric' {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):(μ.perpendicular ν) →
    (ν.perpendicular μ) :=
begin
  
  intro A1,
  rw measure_theory.measure.perpendicular_def2,
  rw measure_theory.measure.perpendicular_def2 at A1,
  cases A1 with S A1,
  apply exists.intro Sᶜ,
  apply and.intro (is_measurable.compl A1.left),
  apply and.intro A1.right.right,
  simp,
  apply A1.right.left,
end

--NOTE: everything below here is required for Radon-Nikodym, although it might not
--be unique.


--This looks familiar: I think that there was a similar, but longer proof.
lemma measure_theory.measure.sub_le {α:Type*}
    [measurable_space α] {μ ν:measure_theory.measure α}:μ - ν ≤ μ :=
begin
  rw measure_theory.measure.sub_def,
  apply @Inf_le (measure_theory.measure α) _ _,
  simp,
  apply measure_theory.measure.le_add,
end

lemma measure_theory.measure.smul_finite {α:Type*} [measurable_space α]
   {μ:measure_theory.measure α} {ε:ennreal} [measure_theory.finite_measure μ]:
   ε ≠ ⊤ → (measure_theory.finite_measure (ε• μ)) :=
begin  
  intros A1,
  apply measure_theory.finite_measure_of_lt_top,
  rw ennreal_smul_measure_apply,
  apply ennreal.mul_lt_top,
  rw lt_top_iff_ne_top,
  apply A1,
  apply measure_theory.measure_lt_top,
  --apply A2,
  simp,
end 

lemma set.compl_Union_eq_Inter_compl {α β:Type*} {f:α → set β}:(⋃ n, f n)ᶜ = (⋂ n, (f n)ᶜ) :=
begin
  ext b,
  split;intros A1;simp;simp at A1;apply A1,
end

lemma measure_theory.measure.perpendicular_of {α:Type*} [M:measurable_space α]
   {μ ν:measure_theory.measure α} [A2:measure_theory.finite_measure μ]
   [A3:measure_theory.finite_measure ν]: 
   (∀ ε:ennreal,  ε > 0 → μ.perpendicular (ν - (ε • μ)) ) → 
   μ.perpendicular ν  :=
begin
  intros A1,
  have B1:∀ n:ℕ,(∃ S:set α,  is_measurable S ∧ μ S = 0 ∧ 
          (ν - ((1/((n:ennreal) + 1))• μ)) (Sᶜ) = 0),
  {
    intros n,
    have B1A:(1/((n:ennreal) + 1))>0,
    {
      apply ennreal.unit_frac_pos,
    },
    have B1B := A1 _ B1A,
    rw measure_theory.measure.perpendicular_def2 at B1B,
    apply B1B,
  },
  have B2 := classical.some_func B1,
  cases B2 with f B2,
  let T := ⋃ n, f n,
  begin
    have C1:T = ⋃ n, f n := rfl,
    have C2:Tᶜ = ⋂ n, (f n)ᶜ,
    {
      rw C1,
      rw set.compl_Union_eq_Inter_compl,
    },
    have C3:is_measurable T,
    {
      rw C1,
      apply is_measurable.Union,
      intro n,
      apply (B2 n).left,
    },
    have C4:is_measurable Tᶜ,
    {
      apply is_measurable.compl C3,
    },
    have I1:∀ (n:ℕ), Tᶜ ⊆ (f n)ᶜ,
    {
      intro n,
      rw C2,
      apply @set.Inter_subset α ℕ (λ n, (f n)ᶜ),
    },
    have I2:∀ (n:ℕ), μ Tᶜ ≤ μ (f n)ᶜ,
    {
      intro n,      
      apply @measure_theory.measure_mono α M μ _ _ (I1 n),
    },
       
    apply @measure_theory.measure.perpendicular_intro α _ μ ν T,
    {
      apply is_measurable.Union,
      intro n,
      apply (B2 n).left,
    },
    {
       rw C1,
       rw ← le_zero_iff_eq,
       have D1:=@measure_theory.measure.Union_nat α _ μ f,
       apply le_trans D1,
       rw le_zero_iff_eq,
       have E1:(λ n, μ (f n)) = (λ (n:ℕ), (0:ennreal)),
       {
         apply funext,
         intro n,
         apply (B2 n).right.left,
       },
       rw E1,
       simp,
    },
    {
       --rw C2,       
       have H1:ν (Tᶜ)/(μ (Tᶜ)) = 0,
       {
          apply ennreal.zero_of_le_all_unit_frac,
          intro n,
          apply ennreal.div_le_of_le_mul,
          have H1X:measure_theory.finite_measure ((1 / ((n:ennreal) + 1)) • μ),
          {
            apply measure_theory.measure.smul_finite,
            {
              apply ennreal.unit_frac_ne_top,
            },
          },
          --have H1B := H1A n,
          have H1B:(ν) Tᶜ - ((1 / ((n:ennreal) + 1)) • μ) Tᶜ ≤ 
                   (ν - (1 / ((n:ennreal) + 1)) • μ) Tᶜ,
          {
            apply @measure_theory.measure.sub_le_sub α M ((1 / ((n:ennreal) + 1)) • μ) ν
                  Tᶜ H1X C4,
          },

          have H1C:(ν) Tᶜ - ((1 / ((n:ennreal) + 1)) • μ) Tᶜ = 0, 
          --have H1B:(ν - (1 / ((n:ennreal) + 1)) • μ) Tᶜ = 0,
          {
            rw ← le_zero_iff_eq,
            apply le_trans H1B,
            rw ← (B2 n).right.right,
            apply measure_theory.measure_mono (I1 n), 
          },
          rw ennreal_smul_measure_apply at H1C,
          apply ennreal.le_of_sub_eq_zero,
          apply H1C,
          apply C4,
       },
       rw ennreal.div_eq_zero_iff at H1,
       cases H1 with H1 H1,
       {
         apply H1,
       },
       {
         exfalso,
         apply measure_theory.measure_ne_top μ Tᶜ H1,
       },
    },
  end
end


lemma measure_theory.measure.exists_of_not_perpendicular {α:Type*} [measurable_space α]
   (μ:measure_theory.measure α) {ν:measure_theory.measure α} [A1:measure_theory.finite_measure μ] [A2:measure_theory.finite_measure ν]:
   (¬ (μ.perpendicular ν)) → 
   (∃ ε:ennreal,  ε > 0  ∧  ¬μ.perpendicular (ν - (ε • μ)) ) :=
begin
  intros A3,
  apply classical.exists_of_not_forall_not,
  intros B1,
  apply A3,
  apply measure_theory.measure.perpendicular_of,
  intros ε C1,
  have C2 := B1 ε,
  simp at C2,
  apply C2,
  apply C1,
end



--Similar, but slightly different than, measure_sub_add.
lemma measure_theory.measure.sub_add_cancel_of_le {α:Type*} [measurable_space α] {μ ν:measure_theory.measure α} [measure_theory.finite_measure μ]:
  μ ≤ ν → ν - μ + μ = ν :=
begin
  intros A1,
  apply measure_theory.measure.ext,
  intros S B1,
  rw measure_theory.measure.add_apply,
  rw jordan_decomposition_junior_apply,
  rw ennreal.sub_add_cancel_of_le,
  apply A1,
  exact B1,
  apply measure_theory.measure.restrict_le_restrict_of_le S A1,
  exact B1,
end


/- 
  This is taken from a step in Tao's proof of the Lebesgue-Radon-Nikodym Theorem.
  By the Hahn Decomposition Theorem, we can find a set where μ ≤ ν and μ S > 0.
 -/
lemma measure_theory.measure.perpendicular_sub_elim {α:Type*} [measurable_space α]
    (μ:measure_theory.measure α) {ν:measure_theory.measure α} 
    [A2:measure_theory.finite_measure ν]: 
    ¬(μ.perpendicular (ν - μ)) → 
    ∃ (S:set α), is_measurable S ∧ μ.restrict S ≤ ν.restrict S  ∧  0 < μ S :=
begin
  intros A3,
  have B1:=hahn_unsigned_inequality_decomp' μ ν,
  cases B1 with X B1,
  have C1:is_measurable (Xᶜ),
  {simp [B1]},
  have B2 := jordan_decomposition_junior_zero 
    ν μ Xᶜ B1.right.right C1,
  have B3 := B1.left,
  have B4:¬((ν - μ).perpendicular μ),
  {
    intro B4A,
    apply A3,
    apply measure_theory.measure.perpendicular_symmetric',
    apply B4A,
  },
  have B5 := measure_theory.measure.not_perpendicular (ν - μ) μ B4 C1 B2,
  simp at B5,
  apply exists.intro X,
  simp [B1, B5],
end

lemma measure_theory.measure.perpendicular_smul {Ω:Type*} [N:measurable_space Ω] (μ ν:measure_theory.measure Ω) {k:ennreal}: 0 < k → 
  (k • μ).perpendicular ν → μ.perpendicular ν :=
begin
  intros A1 A2,
  rw measure_theory.measure.perpendicular_def2,
  rw measure_theory.measure.perpendicular_def2 at A2,
  cases A2 with S A2,
  apply exists.intro S,
  apply and.intro A2.left,
  apply and.intro _ A2.right.right,
  have B1 := A2.right.left,
  rw ennreal_smul_measure_apply _ _ _ A2.left at B1,
  simp at B1,
  cases B1 with B1 B1,
  {
    exfalso,
    rw zero_lt_iff_ne_zero at A1,
    apply A1,
    apply B1,
  },
  {
    apply B1,
  },
end



lemma with_density_indicator_eq_restrict {Ω:Type*} [M:measurable_space Ω] 
    (μ:measure_theory.measure Ω) {S:set Ω} {f:Ω → ennreal}:
    (is_measurable S) → 
    μ.with_density (set.indicator S f) = (μ.restrict S).with_density f :=
begin
  intros A1, 
  apply measure_theory.measure.ext,
  intros T B1,
  rw measure_theory.with_density_apply2',
  rw measure_theory.with_density_apply2',
  rw ← measure_theory.lintegral_indicator,
  rw set.indicator_indicator,
  rw set.indicator_indicator,
  rw set.inter_comm,
  repeat {assumption},
end

lemma scalar_as_with_density {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {k:ennreal}:
  (k•μ) = μ.with_density (λ ω:Ω, k) :=
begin
  apply measure_theory.measure.ext,
  intros S B1,
  rw with_density_const_apply,
  rw ennreal_smul_measure_apply,
  apply B1,
  apply B1,
end


lemma with_density_indicator_eq_restrict_smul {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) {S:set Ω} {k:ennreal}:(is_measurable S) → μ.with_density (set.indicator S (λ ω:Ω, k)) = k • μ.restrict S :=
begin
  intro A1,
  rw with_density_indicator_eq_restrict,
  rw scalar_as_with_density,
  apply A1,
end

lemma smul_restrict_comm {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) {S:set Ω} {k:ennreal}:(is_measurable S) → (k • μ).restrict S = k • μ.restrict S :=
begin
  intros A1,
  apply measure_theory.measure.ext,
  intros T B1,
  rw ennreal_smul_measure_apply _ _ _ B1,
  rw measure_theory.measure.restrict_apply B1,
  rw measure_theory.measure.restrict_apply B1,
  rw ennreal_smul_measure_apply _ _ _ (is_measurable.inter B1 A1),
end


/-
  In the full version of Lebesgue-Radon-Nikodym theorem, μ is an unsigned 
  σ-finite measure, and ν is a signed σ-finite measure.

  The first stage of the proof focuses on finite, unsigned measures
  (see lebesgue_radon_nikodym_unsigned_finite). In that proof,
  there is a need to prove that if two measures are not perpendicular, then there
  exists some nontrivial f where μ.with_density f set.univ > 0 and 
  μ.with_density f ≤ ν. In Tao's An Epsilon of Room, this is to show that
  taking the f which maximizes μ.with_density f set.univ subject to
  μ.with_density f ≤ ν, when subtracted from ν, leaves a measure perpendicular to μ.
 -/
lemma lebesgue_radon_nikodym_junior {Ω:Type*} [N:measurable_space Ω] 
  (μ ν:measure_theory.measure Ω) [A1:measure_theory.finite_measure μ]
  [A2:measure_theory.finite_measure ν]:
  ¬(μ.perpendicular ν) →
  ∃ f:Ω → ennreal, 
  measurable f ∧
  μ.with_density f ≤ ν ∧
  0 < μ.with_density f (set.univ) :=
begin
  intros A3,
  have B1 := measure_theory.measure.exists_of_not_perpendicular μ A3,
  cases B1 with ε B1,
  have B2:¬((ε • μ).perpendicular (ν - ε • μ)),
  {
    intro B2A,
    apply B1.right,
    apply measure_theory.measure.perpendicular_smul _ _ B1.left,
    apply B2A,
  },
  have B3 := measure_theory.measure.perpendicular_sub_elim _ B2,
  cases B3 with S B3,
  let f := (set.indicator S (λ ω:Ω, ε)),
  begin
    have C1:f = (set.indicator S (λ ω:Ω, ε)) := rfl,
    apply exists.intro f,
    split,
    {
      apply measurable.indicator,
      apply measurable_const,
      apply B3.left,
    },
    split,
    {
      rw C1,
      rw with_density_indicator_eq_restrict_smul _ B3.left,
      rw ← smul_restrict_comm _ B3.left,
      apply le_trans _ (@measure_theory.measure.restrict_le_self _ _ _ S),
      apply B3.right.left,
    },
    {
      have C2:0 < μ S,
      {
        have C2A := B3.right.right,
        rw ennreal_smul_measure_apply _ _ _ B3.left at C2A,
        simp at C2A,
        apply C2A.right,
      },
      rw C1,
      rw with_density_indicator_eq_restrict_smul _ B3.left,
      rw ennreal_smul_measure_apply _ _ _ (is_measurable.univ),
      rw measure_theory.measure.restrict_apply is_measurable.univ,
      simp,
      apply and.intro (B1.left) C2,
    },
  end
end

lemma sup_indicator_partition {α:Type*} {x y:α → ennreal}:
   (x ⊔ y) = set.indicator {ω|y ω < x ω} x + set.indicator {ω|x ω ≤ y ω} y  :=
begin
  apply funext,
  intro a,
  simp,
  cases (classical.em (x a ≤ y a)) with B1 B1,
  {
    rw max_eq_right B1,
    rw set.indicator_of_not_mem,
    rw set.indicator_of_mem,
    simp,
    apply B1,
    simp,
    apply B1,
  },
  {
    have B2:=lt_of_not_ge B1,
    have B3:=le_of_lt B2,
    rw max_eq_left B3,
    rw set.indicator_of_mem,
    rw set.indicator_of_not_mem,                                
    simp,
    apply B1,
    apply B2,
  },
end


lemma with_density_restrict_le_with_density_restrict_le_on_subset {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal} {S:set Ω}:
    (is_measurable S) →
    (∀ ω∈ S,  x ω ≤ y ω) → 
    (μ.with_density x).restrict S ≤ (μ.with_density y).restrict S :=
begin
  intros A3 A4,
  intros X' B1,
  rw measure_theory.measure.restrict_apply B1,
  rw measure_theory.measure.restrict_apply B1,
  apply with_density_le_with_density,
  {simp [A3,B1]},  
  intros ω C1,
  apply A4 ω,
  simp at C1,
  apply C1.right,
end

lemma measure_theory.measure.sup_def {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}:μ ⊔ ν = Inf {d|μ ≤ d ∧ ν ≤ d} := rfl


lemma measure_theory.measure.le_sup {Ω:Type*} [measurable_space Ω] {μ ν d:measure_theory.measure Ω}:(∀ c, μ ≤ c → ν ≤ c → d ≤ c) → d ≤ μ ⊔  ν :=
begin
  rw measure_theory.measure.sup_def,
  intro A1,
  apply @le_Inf (measure_theory.measure Ω) _,
  intros c B1,
  apply A1;simp at B1,
  apply B1.left,
  apply B1.right, 
end

lemma measure_theory.measure.le_restrict_add_restrict {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}
  {S:set Ω}:is_measurable S → μ.restrict S ≤ ν.restrict S →  ν.restrict Sᶜ ≤ μ.restrict Sᶜ → 
   μ ≤ μ.restrict Sᶜ + ν.restrict S :=
begin
  intros B1 A1 A2,
  rw measure_theory.measure.le_iff,
  intros T C1,
  rw measure_theory.measure.add_compl_inter μ S T B1 C1,
  rw measure_theory.measure.add_apply,
  rw add_comm,
  apply @add_le_add ennreal _,
  {
    rw measure_theory.measure.restrict_apply C1,
    rw set.inter_comm,
    apply le_refl _,
  },
  {
    rw measure_theory.measure.restrict_apply C1,
    rw set.inter_comm T S,
    apply inter_le_inter_of_restrict_le_restrict A1 B1 C1,
  },
end


lemma measure_theory.measure.sup_eq {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}
  (S:set Ω):is_measurable S → μ.restrict S ≤ ν.restrict S → ν.restrict Sᶜ ≤ μ.restrict Sᶜ → 
   (μ ⊔ ν) = μ.restrict Sᶜ + ν.restrict S :=
begin
  intros D1 A1 A2,
  apply le_antisymm,
  {
    apply @sup_le (measure_theory.measure Ω) _,
    {
      apply measure_theory.measure.le_restrict_add_restrict D1 A1 A2,
    },
    {
      rw add_comm,
      have B1:ν.restrict Sᶜᶜ = ν.restrict S,
      {
        simp,
      },
      rw ← B1,
  
      apply measure_theory.measure.le_restrict_add_restrict,
      repeat {simp [A1,A2,D1]},
    },
  },
  {
     apply measure_theory.measure.le_sup,
     intros c C1 C2,
     rw measure_theory.measure.le_iff,
     intros T C3,
     simp,
     rw measure_theory.measure.restrict_apply C3,
     rw measure_theory.measure.restrict_apply C3,
     rw measure_theory.measure.add_compl_inter c S,
     rw add_comm,
     apply @add_le_add ennreal _,
     rw set.inter_comm,
     apply C2,
     apply is_measurable.inter D1 C3,
     rw set.inter_comm,
     apply C1,
     apply is_measurable.inter (is_measurable.compl D1) C3,
     apply D1,
     apply C3,
  },
end

lemma measure_theory.measure.with_density_restrict_comm {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω)
  {x:Ω → ennreal} {S:set Ω}:is_measurable S → (μ.with_density x).restrict S = (μ.restrict S).with_density x :=
begin
  intros A1,
  apply measure_theory.measure.ext,
  intros T B1,
  rw measure_theory.with_density_apply,
  rw measure_theory.measure.restrict_apply,
  rw measure_theory.measure.restrict_restrict,  
  rw ← measure_theory.lintegral_indicator,
  rw measure_theory.with_density_apply,
  rw measure_theory.lintegral_indicator,
  repeat {assumption <|> apply is_measurable.inter},
end



lemma measure_theory.measure.with_density_add {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal}:measurable x → measurable y → μ.with_density (x + y) = μ.with_density x + μ.with_density y :=
begin
  intros A1 A2,
  apply measure_theory.measure.ext,
  intros S B1,
  rw measure_theory.measure.add_apply,
  repeat {rw measure_theory.with_density_apply},
  simp only [pi.add_apply],
  rw measure_theory.lintegral_add,
  repeat{assumption <|> apply measurable.indicator},
end

lemma with_density_sup' {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal}:measurable x → measurable y → 
    μ.with_density (x ⊔ y) =
    (μ.with_density x).restrict {ω:Ω|y ω < x ω} 
    +
    (μ.with_density y).restrict {ω:Ω|x ω ≤ y ω} :=
begin
  intros A1 A2,
  rw sup_indicator_partition,
  rw measure_theory.measure.with_density_add,
  rw with_density_indicator_eq_restrict,
  rw with_density_indicator_eq_restrict,
  rw measure_theory.measure.with_density_restrict_comm,
  rw measure_theory.measure.with_density_restrict_comm,
  repeat {assumption <|> apply is_measurable_le <|> apply is_measurable_lt <|> apply measurable.indicator},
end

lemma with_density_sup {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal}:measurable x → measurable y → 
    μ.with_density (x ⊔ y) =
    measure_theory.measure.with_density μ x ⊔ measure_theory.measure.with_density μ y :=
begin
  intros A1 A2,
  have C1:=is_measurable_le A1 A2,
  rw with_density_sup' μ A1 A2,
  rw measure_theory.measure.sup_eq {ω:Ω|x ω ≤ y ω},
  have C1:=is_measurable_le A1 A2,
  rw lt_eq_le_compl,
  {
    apply C1,
  },
  {
    apply with_density_restrict_le_with_density_restrict_le_on_subset,
    apply C1,
    intro ω,
    simp,
  },
  {
    apply with_density_restrict_le_with_density_restrict_le_on_subset,
    apply is_measurable.compl (C1),
    simp,
    intros ω B3,
    apply le_of_lt B3,
  },
end

/--
  The difference of two finite measures is a finite measure.
 -/
def measure_theory.finite_measure_sub {Ω:Type*} [M:measurable_space Ω] 
  (μ ν:measure_theory.measure Ω) [measure_theory.finite_measure ν]:
  measure_theory.finite_measure (ν - μ) :=
begin
  apply measure_theory.finite_measure_of_le (ν - μ) ν,
  apply measure_theory.measure.sub_le,
end

lemma lebesgue_radon_nikodym_finite_unsigned {Ω:Type*} {N:measurable_space Ω} (μ ν:measure_theory.measure Ω) [A1:measure_theory.finite_measure μ]
  [A2:measure_theory.finite_measure ν]:
  ∃ f:Ω → ennreal, 
  ∃ μ₂:measure_theory.measure Ω,
  measurable f ∧ 
  ν = μ.with_density f + μ₂ ∧
  μ.perpendicular μ₂ :=
begin
  let S := {f:Ω → ennreal|measurable f ∧ (μ.with_density f ≤ ν)},
  let M := Sup ((λ f, μ.with_density f set.univ) '' S),
  begin
    have A4:S = {f:Ω → ennreal|measurable f ∧ (μ.with_density f ≤ ν)} := rfl,
    have B2:M = Sup ((λ f, μ.with_density f set.univ) '' S)
            := rfl,
    have B3:M < ⊤,
    {
     
      -- Because μ is finite.
      -- Or, because ν is finite, and μ... is less than ν.
      have B3A:M ≤ ν set.univ,
      {
        rw B2,
        apply @Sup_le ennreal _,
        intros b B3A1,
        simp at B3A1,
        cases B3A1 with f B3A1,
        cases B3A1 with B3A1 B3A2,
        subst b,
        cases B3A1 with B3A1 B3A3,
        have B3A4:μ.with_density f (set.univ) ≤ ν (set.univ),
        {apply B3A3,apply is_measurable.univ},
        simp at B3A4,
        apply B3A4,
      },
      apply lt_of_le_of_lt B3A,
      apply measure_theory.measure_lt_top,
    },
    have B1:∃ h:ℕ → Ω → ennreal, 
            (∀ n, h n ∈ S) ∧ 
            (monotone h) ∧
            (μ.with_density (supr h) set.univ) = M,
    {
--      have B1A:=
      apply @Sup_apply_eq_supr_apply_of_closed' (Ω → ennreal) 
          _ S (λ f:Ω → ennreal, μ.with_density f set.univ) _ _, 
      --cases B1A with h B1A,
      { -- ⊢ S.nonempty
        apply @set.nonempty_of_mem (Ω → ennreal) S 0,
        rw A4,
        simp,
        split,
        apply @measurable_const ennreal Ω _ N 0,
        rw with_density.zero,
        apply measure_theory.measure.zero_le,
      },
      { -- ⊢ ∀ a ∈ S, ∀  b ∈ S, a ⊔ b ∈ S
        intros a B1B1 b B1B2,
        cases B1B1 with B1B1 B1B3,
        cases B1B2 with B1B2 B1B4,
        simp,
        split,
        {
          apply measurable_sup B1B1 B1B2,
        },
        {
          rw (with_density_sup μ B1B1 B1B2),
          simp,
          apply and.intro B1B3 B1B4,
        },
      },
      { -- ⊢ ∀ a ∈ S,∀ b ∈ S,a ≤ b → 
        -- (μ.with_density a set.univ ≤ μ.with_density b set.univ),
        intros a B1C b B1D B1E,
        simp,
        rw A4 at B1C,
        rw A4 at B1D,
        --apply measure_theory.lintegral_le_lintegral,
        apply @measure_theory.lintegral_mono,
        simp,
        intros ω B1F,
        apply B1E,
      },
      {
        -- ⊢ ∀ (f : ℕ → Ω → ennreal),
        -- set.range f ⊆ S →
        -- monotone f →
        -- supr ((λ (f : Ω → ennreal), ⇑(μ.with_density f) set.univ) ∘ f) =
        -- (λ (f : Ω → ennreal), ⇑(μ.with_density f) set.univ) (supr f)
        intros f B1G B1H,
        --simp only [measure_theory.measure.restrict_univ, measure_theory.with_density_apply, is_measurable.univ],
        simp only [measure_theory.measure.restrict_univ, is_measurable.univ],
        rw supr_with_density_apply_eq_with_density_supr_apply _ _ B1H,
        simp,
        intros n,
        rw A4  at B1G,
        unfold set.range at B1G,
        rw set.subset_def at B1G,
        simp at B1G,
        apply (B1G n).left,
      },
    },
    cases B1 with h B1,
    have B4:∀ n, measurable (h n),
    {
      intros n,
      have B4A := (B1.left n),
      rw A4 at B4A,
      apply B4A.left,
    },
    let g := supr h,
    begin
      apply exists.intro g,
      have A5:g = supr h := rfl,
      have A6:μ.with_density g set.univ = M,
      {
        rw A5,
        rw ← B1.right.right,
      },
      have A7:μ.with_density g ≤ ν,
      {
        rw measure_theory.measure.le_iff,
        intros S A7A,
        rw ← supr_with_density_apply_eq_with_density_supr_apply,
        apply @supr_le ennreal _ _,
        intros i,
        have A7B := (B1.left i),
        simp at A7B,
        apply A7B.right,
        apply A7A,
        apply A7A,
        apply B4,
        apply B1.right.left,
      },
      apply exists.intro (ν - μ.with_density g),
      have C4:ν = μ.with_density g + (ν - μ.with_density g),
      {
        rw add_comm,
        have C4A:measure_theory.finite_measure (μ.with_density g),
        {
          apply measure_theory.finite_measure_of_lt_top,
          rw A6,
          apply B3,
        },
        rw @measure_theory.measure.sub_add_cancel_of_le Ω N (μ.with_density g) ν C4A,
        apply A7,       
      }, 
      have C5:measurable g,
      {
        rw A5,
        apply @measurable_supr_of_measurable,
        apply B4,
      },
      apply and.intro C5,
      apply and.intro C4,
      {
        apply by_contradiction,
        intros C1,
        have C2X:=measure_theory.finite_measure_sub (μ.with_density g) ν,
        have C2 := @lebesgue_radon_nikodym_junior Ω N 
          μ (ν - μ.with_density g) A1 C2X C1,
        cases C2 with f C2,
        have D1:M < μ.with_density (f + g) set.univ,
        {
          rw measure_theory.measure.with_density_add,
          rw measure_theory.measure.add_apply,
          rw A6,
          rw add_comm,
          apply ennreal.lt_add_self,
          apply B3,
          apply C2.right.right,
          apply C2.left,
          apply C5,
        },
        apply not_le_of_lt D1,
        rw B2,
        apply @le_Sup ennreal _,
        simp,
        apply exists.intro (f  + g),
        split,
        split,
        {
          apply measurable.add,
          apply C2.left,
          apply C5,
        },
        {
          rw C4,
          rw measure_theory.measure.with_density_add,
          rw add_comm,
          apply measure_theory.measure.add_le_add,
          apply le_refl _,
          apply C2.right.left,
          apply C2.left,
          apply C5,
        },
        refl,
      },
    end
  end
end



--Note that the Radon-Nikodym derivative is not necessarily unique.
def is_radon_nikodym_deriv  {Ω:Type*} {M:measurable_space Ω} (ν μ:measure_theory.measure Ω) (f:Ω → ennreal):Prop :=
   (measurable f) ∧ μ.with_density f = ν



lemma is_radon_nikodym_deriv_elim {Ω:Type*} {M:measurable_space Ω} (ν μ:measure_theory.measure Ω) (f:Ω → ennreal) (S:set Ω):
  (is_radon_nikodym_deriv ν μ f) →
  (is_measurable S) →
  (∫⁻ (a : Ω), (set.indicator S f) a ∂ μ = ν S) :=
begin
  intros A1 A2,
  unfold is_radon_nikodym_deriv at A1,
  cases A1 with A3 A1,
  subst ν,
  rw measure_theory.with_density_apply2',
  apply A2,
end

lemma measurable_of_is_radon_nikodym_deriv {Ω:Type*} {M:measurable_space Ω} (ν μ:measure_theory.measure Ω) (f:Ω → ennreal) (S:set Ω):
  (is_radon_nikodym_deriv ν μ f) →
  (measurable f) :=
begin
  intro A1,
  cases A1 with A1 A2,
  apply A1,
end

lemma is_radon_nikodym_deriv_intro {Ω:Type*} {M:measurable_space Ω} (ν μ:measure_theory.measure Ω) (f:Ω → ennreal):
  (measurable f) →
  (∀ S:set Ω, (is_measurable S) →
  (∫⁻ (a : Ω), (set.indicator S f) a ∂ μ = ν S)) →
  (is_radon_nikodym_deriv ν μ f)  :=
begin
  intros A1 A2,
  unfold is_radon_nikodym_deriv,
  split,
  apply A1,
  apply measure_theory.measure.ext,
  intros S A3,
  rw measure_theory.with_density_apply2',
  apply A2,
  repeat {apply A3},
end



/-
  As we move on to the later theorems, we need to be able to say that two
  functions are "almost everywhere equal". Specifically, given two radon-nikodym 
  derivatives of a measure, they are equal almost everywhere according to the
  base measure.
 -/

-- There used to be a definition close to this, measure_theory,measure.a_e, and
-- This used to be ∀ᶠ a in μ.a_e, P a
-- For now, we use a local definition.
def measure_theory.measure.all_ae {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P:Ω → Prop):Prop :=
   (μ ({ω:Ω|(P ω)}ᶜ)) = 0


lemma measure_theory.measure.all_ae_def2 {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P:Ω → Prop):
    μ.all_ae P = ( (μ ({ω:Ω|(P ω)}ᶜ)) = 0) :=
begin
  unfold measure_theory.measure.all_ae,
end


lemma measure_theory.measure.all_ae_and {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P Q:Ω → Prop):
    (μ.all_ae P) →
    (μ.all_ae Q) →
    (μ.all_ae (λ a, P a ∧ Q a)) := 
begin
  intros A1 A2,
  rw measure_theory.measure.all_ae_def2,
  have A3:{ω:Ω| P ω ∧ Q ω}ᶜ =  ({ω:Ω|P ω}ᶜ) ∪ ({ω:Ω|Q ω}ᶜ),
  {
    ext ω,
    split;intros A3A;simp;simp at A3A,
    {
      have A3B:P ω ∨ ¬(P ω) := classical.em (P ω),
      cases A3B,
      {
        apply or.inr (A3A A3B),
      },
      {
        apply or.inl A3B,
      },
    },
    {
      cases A3A,
      {
        intro A3B,
        exfalso,
        apply A3A,
        apply A3B,
      },
      {
        intro A3B,
        apply A3A,
      },
    },
  },
  rw A3,
  have A4:(⊥:ennreal)=(0:ennreal) := rfl,
  rw ← A4,
  rw ← le_bot_iff,
  apply le_trans (measure_theory.measure_union_le ({ω:Ω|P ω}ᶜ) ({ω:Ω|Q ω}ᶜ)),
  rw measure_theory.measure.all_ae_def2 at A1,
  rw measure_theory.measure.all_ae_def2 at A2,
  rw A1,
  rw A2,
  simp,
end


lemma measure_theory.all_ae_imp {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P Q:Ω → Prop):
    (μ.all_ae (λ a, P a → Q a)) →
    (μ.all_ae P) →
    (μ.all_ae Q) :=
begin
  intros A1 A2,
  rw measure_theory.measure.all_ae_def2 at A1,
  rw measure_theory.measure.all_ae_def2 at A2,
  rw measure_theory.measure.all_ae_def2,
  have A3:{ω:Ω|Q ω}ᶜ ⊆ ({ω:Ω|P ω → Q ω}ᶜ) ∪ ({ω:Ω|P ω}ᶜ),
  {
    rw set.subset_def,
    intro ω,
    simp,
    intro A3A,
    cases (classical.em (P ω)) with A3B A3B,
    {
      apply or.inl (and.intro A3B A3A),
    },
    {
      apply or.inr A3B,
    },
  },
  have A4:(⊥:ennreal)=(0:ennreal) := rfl,
  rw ← A4,
  rw ← le_bot_iff,
  apply le_trans (measure_theory.measure_mono A3),
  apply le_trans (measure_theory.measure_union_le ({ω:Ω|P ω → Q ω}ᶜ) ({ω:Ω|P ω}ᶜ)),
  rw A1,
  rw A2,
  simp,
end


lemma measure_theory.all_ae2_of_all {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P:Ω → Prop):
    (∀ a, P a) → 
    (μ.all_ae P) :=
begin
  intro A1,
  rw measure_theory.measure.all_ae_def2,
  have A2:{ω:Ω|P ω}ᶜ = ∅,
  {
    ext ω,split;intros A2A,
    exfalso,
    simp at A2A,
    apply A2A,
    apply A1,
    exfalso,
    apply A2A,
  },
  rw A2,
  simp,
end


lemma measure_theory.not_ae {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P:Ω → Prop):
  (∃ S:set Ω, (μ S > 0) ∧ (∀ ω∈ S, ¬ (P ω)) )→
  (¬(μ.all_ae P)) :=
begin
  intros A1 A2,
  cases A1 with S A3,
  cases A3 with A3 A4,
  rw measure_theory.measure.all_ae_def2 at A2,
  have A5:S⊆ {ω:Ω|P ω}ᶜ,
  {
    rw set.subset_def,
    intro ω,
    intro A5A,
    apply A4 _ A5A,
  },
  have A6 := measure_theory.outer_measure.mono (μ.to_outer_measure) A5,
  have A7 := lt_of_lt_of_le A3 A6,
  rw measure.apply at A2,
  rw A2 at A7,
  apply lt_irrefl (0:ennreal) A7,
end


/-
  Notice that it is not necessarily the case that a measurable set exists.
  For example, consider where Ω = {a,b}.
  The measurable sets are {} and {a,b}, where μ ∅ = 0 and μ {a,b} = 1.
  Define (P a) and (¬P b).
  Thus S={a}, which is not measurable.
-/
lemma measure_theory.not_ae_elim {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P:Ω → Prop):
  (¬(μ.all_ae P)) →
  (∃ S:set Ω, (μ S > 0) ∧ (∀ ω∈ S, ¬ (P ω)) ) :=
begin
  intro A1,
  rw measure_theory.measure.all_ae_def2 at A1,
  have A2 := ennreal.eq_zero_or_zero_lt A1,
  apply exists.intro ({ω : Ω | P ω}ᶜ),
  split,
  apply A2,
  intros ω A3,
  simp at A3,
  apply A3,
end
