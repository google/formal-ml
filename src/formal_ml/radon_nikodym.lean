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
import formal_ml.hahn


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

lemma ennreal.ne_zero_iff_zero_lt {x:ennreal}:x ≠ 0 ↔ 0 < x :=
begin
  split;intros A1,
  {
    apply lt_of_not_ge,
    intro B1,
    apply A1,
    simp at B1,
    apply B1,
  },
  {
    intros C1,
    subst x,
    simp at A1,
    apply A1,
  },
end


lemma real.sub_le_sub_of_le_of_le_of_le {a b c d:real}:
    a ≤ b → c ≤ d → a ≤ b - c + d :=
begin
  intros A1 A2,
  apply le_trans A1,
  have B1:b - c + c  ≤ b - c + d,
  {
    apply add_le_add,
    apply le_refl _,
    apply A2,
  },
  simp at B1,
  apply B1
end

lemma nnreal.sub_le_sub_of_le_of_le_of_le {a b c d:nnreal}:
    a ≤ b → c ≤ d → d ≤ a → a ≤ b - c + d :=
begin
  intros A1 A2 A3,
  rw ← nnreal.coe_le_coe,
  rw nnreal.coe_add,
  rw nnreal.coe_sub,
  apply real.sub_le_sub_of_le_of_le_of_le,
  {
    rw nnreal.coe_le_coe,
    apply A1,
  },
  {
    rw nnreal.coe_le_coe,
    apply A2,
  },
  apply le_trans A2,
  apply le_trans A3,
  apply le_trans A1,
  apply le_refl _,
end


lemma ennreal.sub_le_sub_of_le_of_le_of_le {a b c d:ennreal}:
    a ≤ b → c ≤ d → d ≤ a → a - d ≤ b - c :=
begin
  cases a;cases b;cases c;cases d;try {simp},
  intros A1 A2 A3,
  have B1:(a:ennreal) ≤ (b:ennreal) - (c:ennreal) + (d:ennreal),
  {
    rw ← ennreal.coe_sub,
    rw ← ennreal.coe_add,
    rw  ennreal.coe_le_coe,
    apply nnreal.sub_le_sub_of_le_of_le_of_le A1 A2 A3,
  },
  apply B1,  
end

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


lemma nnreal.le_zero_iff {a:nnreal}:a ≤ 0 ↔ a=0 :=
begin
  simp
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
    rw ← @nnreal.le_zero_iff a,
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

lemma nnreal.mul_le_mul_left' (a b:nnreal) (H:a≤ b) (c:nnreal):
    c * a ≤ c * b :=
begin
  cases (classical.em (c = 0)) with B1 B1,
  {
    subst c,
    simp,
  },
  {
    have C1:0 < c,
    {
      rw zero_lt_iff,
      intro C1A,
      apply B1,
      apply C1A,
    },
    rw mul_le_mul_left,
    apply H,
    apply C1,
  },
end

lemma ennreal.mul_le_mul_left' (a b:ennreal) (H:a≤ b) (c:ennreal):
    c * a ≤ c * b :=
begin
  revert H,
  cases c;cases a;cases b;try {simp},
  {
    intros A1,
    rw ennreal.top_mul,
    rw ennreal.top_mul,
    cases (classical.em (a = 0)) with B1 B1,
    {
       subst a,
       simp,
    },
    {
       have B2:0 < a,
       {
         rw zero_lt_iff_ne_zero,
         intro B2A,
         rw B2A at B1,
         simp at B1,
         apply B1,
       },
       have B3:0 < b,
       {
         apply lt_of_lt_of_le B2 A1,
       },
       have B4:(b:ennreal) ≠ 0,
       {
         rw zero_lt_iff_ne_zero at B3,
         intros B4A,
         apply B3,
         simp at B4A,
         apply B4A,
       },
       rw if_neg B4,
       simp,
    },
  },
  {
     apply le_refl _,
  },
  {
    rw ennreal.mul_top,
    cases (classical.em (c = 0)) with D1 D1,
    {
       subst c,
       simp,
    },
    {
       have E1:¬((c:ennreal) = 0),
       {
         intro E1A,
         apply D1,
         simp at E1A,
         apply E1A,
       },
       rw if_neg E1,
       simp,
    },
  },
  rw ← ennreal.coe_mul,
  rw ← ennreal.coe_mul,
  rw ennreal.coe_le_coe,
  intro F1,
  apply nnreal.mul_le_mul_left',
  apply F1,
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
  rw measure_theory.with_density_apply2,
  rw ← simple_restrict_eq_indicator_const,
  rw integral_const_restrict_def,
  refl,
  apply B1,
  apply B1,
  apply B1,
end


lemma measure_theory.measure.le_zero_iff {Ω:Type*} [measurable_space Ω]
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


lemma measure_theory.measure.sub_eq_zero_if_le {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω):μ ≤ ν → μ - ν = 0 :=
begin
  intros A1,
  rw ← measure_theory.measure.le_zero_iff,
  rw measure_theory.measure.sub_def,
  apply @Inf_le (measure_theory.measure Ω) _ _,
  simp [A1],
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


lemma le_of_le_measure_sub {α:Type*} [M:measurable_space α] 
    {μ ν₁ ν₂:measure_theory.measure α} [H2:measure_theory.finite_measure μ] 
   [H3:measure_theory.finite_measure ν₁]
    (H:ν₁ ≤ μ): 
    ν₂ ≤ (measure_sub H) →  ν₁ + ν₂ ≤ μ :=
begin
  intro A1,
  have B1:μ = ν₁ + (measure_sub H),
  {
    apply measure_sub_add,
  },
  rw B1,
  apply measure_theory.measure.add_le_add_left,
  apply A1,
end


lemma measure_theory.measure.sub_apply {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω} [A2:measure_theory.finite_measure ν]:
  is_measurable S → 
  ν ≤ μ → (μ - ν) S = μ S - ν S :=
begin
  intros A1 A3,
  rw measure_sub_eq μ ν A3 A2,
  apply measure_sub_apply,
  apply A1,
end


lemma measure_theory.measure.restrict_apply_subset {Ω:Type*} [measurable_space Ω]
  (μ:measure_theory.measure Ω) {S T:set Ω}:is_measurable S →
  S ⊆ T →
  (μ.restrict T) S = μ S :=
begin
  intros A1 A3,
  rw measure_theory.measure.restrict_apply A1,
  simp [set.inter_eq_self_of_subset_left,A3],
end 

lemma measure_theory.measure.restrict_apply_self {Ω:Type*} [measurable_space Ω]
  (μ:measure_theory.measure Ω) {S:set Ω} (H:is_measurable S):
  (μ.restrict S) S = μ S :=
begin
  rw measure_theory.measure.restrict_apply H,
  simp,
end 

lemma restrict_le_restrict_of_le_on_subsets {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω}:
  le_on_subsets μ ν S →
  (μ.restrict S) ≤ ν.restrict S :=
begin
  intros A1,
  rw le_on_subsets_def at A1,
  rw measure_theory.measure.le_iff,
  intros T B1,   
  rw measure_theory.measure.restrict_apply,
  rw measure_theory.measure.restrict_apply,
  apply A1.right,
  simp,
  apply is_measurable.inter,
  apply B1,
  apply A1.left,
  repeat {apply B1},
end

/-
  Not required, but completes the connection between le_on_subsets and restrict.
 -/
lemma le_on_subsets_of_is_measurable_of_restrict_le_restrict {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω}:is_measurable S →
  (μ.restrict S) ≤ ν.restrict S →
  le_on_subsets μ ν S  :=
begin
  intros A1 A2,
  rw measure_theory.measure.le_iff at A2,
  rw le_on_subsets_def,
  apply and.intro A1,
  intros X B1 B2,
  have B3 := A2 X B2,
  rw measure_theory.measure.restrict_apply_subset μ B2 B1 at B3,
  rw measure_theory.measure.restrict_apply_subset ν B2 B1 at B3,
  apply B3,
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
    = ⨅{f : ℕ → set α} (h : s ⊆ ⋃i, f i), ∑'i, m (f i)  := rfl


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



--Note that this does not hold true for empty S.
--If S2.nonempty, but S2 ∩ T = ∅, then ⊤ (S2 ∩ T) = 0, but ⊤ (S2) = ⊤.
lemma measure_theory.outer_measure.Inf_restrict {Ω:Type*} [measurable_space Ω]
  (S:set (measure_theory.outer_measure Ω)) {T:set Ω}:
  is_measurable T → (S.nonempty) →
  measure_theory.outer_measure.restrict T (Inf S) = Inf ((measure_theory.outer_measure.restrict T) '' S) := 
begin
  intros A1 B1,
  apply measure_theory.outer_measure.ext,
  intros S2,
  rw measure_theory.outer_measure.restrict_apply,
  rw measure_theory.outer_measure.Inf_eq_of_function_Inf_gen,
  rw measure_theory.outer_measure.Inf_eq_of_function_Inf_gen,
  rw measure_theory.outer_measure.of_function_def2,
  rw measure_theory.outer_measure.of_function_def2,
  have E1:((measure_theory.outer_measure.restrict T) '' S).nonempty,
  {
    apply set.nonempty_image_iff.mpr B1,
  },
  apply le_antisymm,
  {
    simp,
    intros f C1,
    let g := λ n, (f n) ∩ T,
    begin
      have C2:g = (λ n, (f n) ∩ T) := rfl,
      have C3: (∑' (i:ℕ), measure_theory.outer_measure.Inf_gen S (g i)) ≤
               ∑' (i : ℕ), measure_theory.outer_measure.Inf_gen (⇑(measure_theory.outer_measure.restrict T) '' S) (f i),
      {
        apply ennreal.tsum_le_tsum,
        intro n,
        rw measure_theory.outer_measure.Inf_gen_nonempty3 _ _ B1,
        rw measure_theory.outer_measure.Inf_gen_nonempty3 _ _ E1,
        simp,
        intros μ' μ C3A C3B,
        subst μ',
        rw measure_theory.outer_measure.restrict_apply,
        rw C2,
        simp,
        have C3C:(⨅ (H : μ ∈ S),
                 μ (f n ∩ T)) ≤ μ (f n ∩ T),
        {
          rw infi_prop_def,
          apply le_refl _,
          apply C3A,
        },
        apply le_trans _ C3C,
        apply @infi_le ennreal _ _,
      },
      apply le_trans _ C3,
      have C4:(⨅ (h : S2 ∩ T ⊆ ⋃ (i : ℕ), g i),
             (∑' (i:ℕ), measure_theory.outer_measure.Inf_gen S (g i))) ≤
             (∑' (i:ℕ), measure_theory.outer_measure.Inf_gen S (g i)),
      {
        rw infi_prop_def,
        apply le_refl _,
        rw C2,
        simp,
        rw set.Union_inter_eq_inter_Union,
        simp,
        apply set.subset.trans _ C1,
        apply set.inter_subset_left,
      },
      apply le_trans _ C4,
      apply @infi_le ennreal _ _,
    end
  },
  {
    simp,
    intros h D1,
    let g := λ n, (h n) ∪ Tᶜ, 
    begin
      have D2:g = λ n, (h n) ∪ Tᶜ := rfl,
      apply @infi_set_le_trans (ℕ → set Ω) ennreal _ g,
      {
        rw D2,
        simp,
        rw set.Union_union_eq_union_Union,
        rw set.union_comm,
        apply set.subset_union_compl_of_inter_subset,
        apply D1,
      },
      {
        apply ennreal.tsum_le_tsum,
        intro n,
        rw measure_theory.outer_measure.Inf_gen_nonempty3 _ _ B1,
        rw measure_theory.outer_measure.Inf_gen_nonempty3 _ _ E1,
        rw infi_set_image,
        simp,
        intros μ D3,
        apply @infi_set_le_trans (measure_theory.outer_measure Ω) ennreal _ μ,
        apply D3,
        {
          rw D2,
          simp,
          rw set.inter_distrib_right,
          simp,
          apply μ.mono,
          simp,
        },
      },
    end
  },
end  


lemma measure_theory.measure.lift_linear_def {α β:Type*} [measurable_space α] [Mβ:measurable_space β]
    (f : measure_theory.outer_measure α →ₗ[ennreal] measure_theory.outer_measure β)
    (H:∀ (μ : measure_theory.measure α), Mβ ≤ (f μ.to_outer_measure).caratheodory) 
    {μ:measure_theory.measure α}:
    (measure_theory.measure.lift_linear f H μ) = (f (μ.to_outer_measure)).to_measure (H μ) :=
begin
  apply measure_theory.measure.ext,
  intros S B1,
  unfold measure_theory.measure.lift_linear,
  simp,
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


lemma infi_prop_false2 {α:Type*} [complete_lattice α]
    {P:Prop} {v:P→ α} (H:¬P):(⨅ (H2:P), v H2) = ⊤ :=
begin
  apply le_antisymm,
  {
    simp,
  },
  {
    apply @le_infi α _ _,
    intro H2,
    exfalso,
    apply H,
    apply H2,
  },
end


lemma measure_theory.extend_top {α : Type*} {P : α → Prop} 
    {m : Π (s : α), P s → ennreal} {s : α}: ( ¬P s)→
    measure_theory.extend m s = ⊤ :=
begin
  intros A1,
  unfold measure_theory.extend,
  rw infi_prop_false2, 
  apply A1,
end


--Unused.
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
    rw measure_theory.extend_top B1, 
    simp,
  },
end 



/-
  This is a result that must be proven directly for restrict, but has
  larger implications.

  I am curious whether this follows from
  lift_linear constraint on the catheodary measurable space of the output outer
  measure of restrict. That would be a more general result, implying that this would
  hold for all places where lift_linear was used.
 -/
lemma measure_theory.outer_measure.restrict_trimmed_of_trimmed {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.outer_measure Ω} {S:set Ω}:is_measurable S → μ.trim = μ →
    (measure_theory.outer_measure.restrict S μ).trim = (measure_theory.outer_measure.restrict S μ) :=
begin
  intros A2 A1,
  apply measure_theory.outer_measure.ext,
  unfold measure_theory.outer_measure.trim,
  unfold measure_theory.induced_outer_measure,
  intros T,
  simp,
  rw measure_theory.outer_measure.of_function_def2,
  apply le_antisymm,
  {
    have B1:μ (T ∩ S) = μ.trim (T ∩ S),
    {
      rw A1,
    },
    rw B1,
    unfold measure_theory.outer_measure.trim,
    unfold measure_theory.induced_outer_measure,
    rw measure_theory.outer_measure.of_function_def2,
    simp,
    intros h B2,
    let g := λ (n:ℕ), (h n) ∪ Sᶜ,
    begin
      have B3:g = λ (n:ℕ), (h n) ∪ Sᶜ := rfl,
      have B4:(∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), 
              μ (s ∩ S)) (g i)) ≤
              ∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), 
             μ s) (h i),
      {
        apply ennreal.tsum_le_tsum,
        intros n,
        apply measure_theory.le_extend2,
        intro B4A,
        rw measure_theory.extend_eq,
        rw B3,
        simp,
        rw set.inter_distrib_right,
        simp,
        apply measure_theory.outer_measure.mono',
        simp,
        rw B3,
        simp,
        apply is_measurable.union B4A (is_measurable.compl A2),
      },
      apply le_trans _ B4,
      clear B4,
      have B5:(⨅ (h : T ⊆ ⋃ (i : ℕ), g i),
              ∑' (i : ℕ), measure_theory.extend 
             (λ (s : set Ω) (_x : is_measurable s), μ (s ∩ S)) (g i)) ≤
              ∑' (i : ℕ), measure_theory.extend 
             (λ (s : set Ω) (_x : is_measurable s), μ (s ∩ S)) (g i),
      {
        rw infi_prop_def,
        apply le_refl _,
        rw B3,
        simp,
        rw set.Union_union_eq_union_Union,
        rw set.union_comm,
        apply set.subset_union_compl_of_inter_subset B2,
      },
      apply le_trans _ B5,
      apply @infi_le ennreal _ _,
    end
  },
  {
    simp,
    intros h C1,
    let g := λ n:ℕ, h n ∩ S,
    begin
      have C2:g = λ n:ℕ, h n ∩ S := rfl,
      have C3:μ (T ∩ S) ≤ μ(set.Union g),
      {
        apply measure_theory.outer_measure.mono',
        rw C2,
        rw set.Union_inter_eq_inter_Union,
        rw set.inter_comm S,
        simp,
        apply set.subset.trans _ C1,
        simp,
      },
      apply le_trans C3,
      have C4:μ(set.Union g) ≤ ∑' (i:ℕ), μ (g i),
      {
        apply measure_theory.outer_measure.Union,
      },
      apply le_trans C4,
      apply ennreal.tsum_le_tsum,
      intro n,
      cases (classical.em (is_measurable (h n))) with C5 C5,
      {
        apply le_trans _ (measure_theory.le_extend _ C5),
        rw C2,
        apply le_refl _,
      },
      {
        rw measure_theory.extend_top C5,
        simp,
      },
    end
  },
end


lemma measure_theory.measure.to_outer_measure.restrict' {Ω:Type*} [measurable_space Ω]
    {μ:measure_theory.measure Ω} {S:set Ω}:is_measurable S →
    (μ.restrict S).to_outer_measure = measure_theory.outer_measure.restrict S (μ.to_outer_measure) :=
begin
  intros A1,
  apply measure_theory.outer_measure.ext,
  intro T,
  rw measure_theory.outer_measure.restrict_apply,
  simp,
  unfold measure_theory.measure.restrict,
  unfold measure_theory.measure.restrictₗ,
  rw measure_theory.measure.lift_linear_def,
  rw measure.apply,
  rw measure_theory.to_measure_to_outer_measure,
  --rw measure_theory.outer_measure.to_measure_to_outer_measure_eq_trim,
  rw measure_theory.outer_measure.restrict_trimmed_of_trimmed A1,
  simp,
  apply measure_theory.measure.trimmed,
end


lemma compose_image {α β γ:Type*} {f:α → β} {g:β → γ} {S:set α}:
  g '' (f '' S) = (g ∘ f) '' S :=
begin
  ext c,
  split;
  intros B1;simp;simp at B1;apply B1,
end


lemma measure_theory.measure.Inf_restrict {Ω:Type*} [measurable_space Ω]
  (S:set (measure_theory.measure Ω)) {T:set Ω}:S.nonempty → is_measurable T →
  (Inf S).restrict T = Inf ((λ μ:measure_theory.measure Ω,μ.restrict T) '' S) := 
begin
  intros AX A1,
  apply measure_theory.measure.ext,
  intros S2 B1,
  rw measure_theory.measure.Inf_apply B1,
  rw measure_theory.measure.restrict_apply B1,
  rw measure_theory.measure.Inf_apply (is_measurable.inter B1 A1),
  have B3:(measure_theory.measure.to_outer_measure '' ((λ (μ : measure_theory.measure Ω), μ.restrict T) '' S))
      = (measure_theory.outer_measure.restrict T) ''( measure_theory.measure.to_outer_measure '' S),
  {
    rw compose_image,
    rw compose_image,
    have B3A:(measure_theory.measure.to_outer_measure ∘ λ (μ : measure_theory.measure Ω), μ.restrict T) = (measure_theory.outer_measure.restrict T) ∘ (measure_theory.measure.to_outer_measure),
    {
      apply funext,
      intro μ,
      simp,
      apply measure_theory.measure.to_outer_measure.restrict',
      apply A1,
    },
    rw B3A,
  },
  rw B3,
  rw ← measure_theory.outer_measure.Inf_restrict _ A1,
  rw measure_theory.outer_measure.restrict_apply,
  apply set.nonempty_image_iff.mpr,
  apply AX,
end  

lemma measure_theory.measure.restrict_le_restrict_of_le {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω}:
  μ  ≤ ν  → μ.restrict S ≤ ν.restrict S :=
begin
  intros A1,
  apply measure_theory.measure.restrict_mono,
  apply set.subset.refl,
  apply A1,
end


lemma measure_theory.measure_partition_apply {Ω:Type*} [M:measurable_space Ω]
    (μ:measure_theory.measure Ω) (S T:set Ω):is_measurable S → is_measurable T →
  μ T = μ (S ∩ T) + μ (Sᶜ ∩ T) :=
begin
  intros A1 A2,
  rw set.inter_comm,
  rw set.inter_comm Sᶜ,

  have B1:T = (T∩ S) ∪ (T∩ Sᶜ),
  {
    rw set.inter_union_compl,
  },
  --have B2:μ T =
  rw ← @measure_theory.measure_union Ω M μ (T∩ S) _,
  rw ← B1,
  apply set.disjoint_inter_compl,
  apply is_measurable.inter,
  apply A2,
  apply A1,
  apply is_measurable.inter,
  apply A2,
  apply is_measurable.compl,
  apply A1,
end


lemma measure_theory.measure.le_of_partition {Ω:Type*} [M:measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S T:set Ω}:is_measurable S →
  is_measurable T →
  μ (S ∩ T) ≤ ν (S ∩ T) →
  μ (Sᶜ ∩ T) ≤ ν (Sᶜ ∩ T) →
  μ T ≤ ν T :=
begin
  intros A1 A2 A3 A4,
  rw measure_theory.measure_partition_apply μ S T,
  rw measure_theory.measure_partition_apply ν S T,
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


/-
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
  rw measure_theory.measure.le_iff,
  intros S B1,
  simp,
  apply le_add_nonnegative _ _,
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
  rw measure_theory.measure.Inf_restrict _ G1 A1,
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
      {
        rw add_assoc,
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
          rw measure_theory.measure.le_iff at B1,
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
--  [measure_theory.finite_measure ν]
:le_on_subsets μ ν S →
  (μ - ν) S = 0 :=
begin
  intro A1,
  have B1 := le_on_subsets_is_measurable A1,
  rw ← measure_theory.measure.restrict_apply_self _ B1,
  rw measure_theory.measure.sub_restrict_comm,
  rw measure_theory.measure.sub_eq_zero_if_le,
  simp,
  apply restrict_le_restrict_of_le_on_subsets _ _ A1,
  apply B1,
end


--This works with EITHER ν or μ being finite, or even ν S < ⊤.
lemma jordan_decomposition_junior_apply {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S:set Ω) [AX:measure_theory.finite_measure ν]:
  le_on_subsets ν μ S →
  (μ - ν) S = μ S - ν S :=
begin
  intros A1,
  have B1 := le_on_subsets_is_measurable A1,
  rw ← measure_theory.measure.restrict_apply_self _ B1,
  rw measure_theory.measure.sub_restrict_comm,
  have B2:measure_theory.finite_measure (ν.restrict S),
  {
    apply measure_theory.finite_measure_restrict,
  },
  rw @measure_theory.measure.sub_apply Ω _ _ _ S B2,
  rw measure_theory.measure.restrict_apply_self,
  rw measure_theory.measure.restrict_apply_self,
  apply B1,
  apply B1,
  apply B1,
  {
    --rw le_on_subsets_def at A1,
    apply restrict_le_restrict_of_le_on_subsets,
    apply A1,
  },
  apply B1,
end


/-
  A jordan decomposition of subtraction.
 -/
lemma jordan_decomposition_nonneg_sub {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S T:set Ω) [A1:measure_theory.finite_measure μ]: 
    is_measurable T → (le_on_subsets μ ν S) → (le_on_subsets ν μ Sᶜ) →
    (ν - μ) T = ν (S ∩ T) - μ (S ∩ T) :=
begin
  intros A3 A4 A5,
  have A2:is_measurable S,
  {
     apply le_on_subsets_is_measurable A4,
  },
  have B1:(ν - μ) T = (ν - μ) (S∩ T) + (ν - μ) (Sᶜ ∩ T),
  {
    rw measure_theory.measure_partition_apply,
    apply A2,
    apply A3,
  },
  have B2:(ν - μ) (S∩ T) = ν (S ∩ T) - μ (S ∩ T),
  {
    apply jordan_decomposition_junior_apply,
    apply le_on_subsets_subset _ _ _ _ A4,
    simp,
    apply is_measurable.inter A2 A3,
  },
  have B3:(ν - μ) (Sᶜ ∩ T) = 0,
  {
    apply jordan_decomposition_junior_zero,
    apply le_on_subsets_subset _ _ _ _ A5,
    simp,
    apply is_measurable.inter (is_measurable.compl A2) A3,
  },
  rw B1,
  rw B2,
  rw B3,
  rw add_zero,
end


lemma jordan_decomposition_nonneg_sub' {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S:set Ω) (T:set Ω) 
   [A1:measure_theory.finite_measure μ]: 
    (le_on_subsets μ ν S) → (le_on_subsets ν μ Sᶜ) →
    (is_measurable T) →
    (ν - μ) T = (ν.restrict S) T - (μ.restrict S) T :=
begin
  intros A2 A3 B1,
  rw jordan_decomposition_nonneg_sub μ ν S T B1 A2 A3,
  rw measure_theory.measure.restrict_apply B1,
  rw measure_theory.measure.restrict_apply B1,
  rw set.inter_comm T,
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


lemma le_on_subsets_inter {Ω:Type*} [measurable_space Ω] 
    {μ ν:measure_theory.measure Ω} {T U:set Ω}:is_measurable U →
    le_on_subsets μ ν T → μ (T ∩ U) ≤ ν (T ∩ U) :=
begin
  intros A1 A2,
  rw le_on_subsets_def at A2,
  apply A2.right,
  simp,
  apply is_measurable.inter A2.left A1,
end


--This may be gotten by easier methods.
lemma measure_theory.measure.sub_le_sub {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (T:set Ω) [A1:measure_theory.finite_measure μ]:
    is_measurable T → (ν T - μ T) ≤ (ν - μ) T :=
begin
  intros A2,
  have B1 := hahn_unsigned_inequality_decomp ν μ,
  cases B1 with U B1,
  have C1 := le_on_subsets_is_measurable B1.left,
  rw jordan_decomposition_nonneg_sub μ ν Uᶜ,
  {
    have C2:ν T = ν (U ∩ T) + ν (Uᶜ ∩ T),
    {
      apply measure_theory.measure.add_compl_inter _ _ _  C1 A2,
    },
    rw C2,
    have C3:μ T = μ (U ∩ T) + μ (Uᶜ ∩ T),
    {
      apply measure_theory.measure.add_compl_inter _ _ _  C1 A2,
    },
    rw C3,
    simp,
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
    apply le_on_subsets_inter A2 B1.left,
  },
  --apply A1,---???
  apply A2,
  apply B1.right,
  simp,
  apply B1.left,
end


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
      rw ← ennreal.le_zero_iff,
      rw ← ennreal.le_zero_iff at C2,
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


lemma measure_theory.measure.perpendicular_symmetric {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):(μ.perpendicular ν) ↔
    (ν.perpendicular μ) :=
begin
  split;apply measure_theory.measure.perpendicular_symmetric',
end


lemma measure_theory.measure.perpendicular_of_le {α:Type*}
    [measurable_space α] {μ ν ν':measure_theory.measure α}:μ.perpendicular ν →
    ν' ≤ ν → μ.perpendicular ν' :=
begin
  intros A1 A2,
  rw measure_theory.measure.perpendicular_def2,
  rw measure_theory.measure.perpendicular_def2 at A1,
  cases A1 with S A1,
  apply exists.intro S,
  apply and.intro A1.left,
  apply and.intro (A1.right.left),
  rw ← ennreal.le_zero_iff,
  rw ← A1.right.right,
  apply A2,
  apply is_measurable.compl (A1.left),
end

lemma measure_theory.measure.sub_le {α:Type*}
    [measurable_space α] {μ ν:measure_theory.measure α}:μ - ν ≤ μ :=
begin
  rw measure_theory.measure.sub_def,
  apply @Inf_le (measure_theory.measure α) _ _,
  simp,
  apply measure_theory.measure.le_add,
end


lemma measure_theory.measure.perpendicular_of_sub {α:Type*} [measurable_space α]
   {μ ν ν':measure_theory.measure α}:μ.perpendicular ν → (μ.perpendicular (ν - ν')) :=
begin
  intros A1,
  apply measure_theory.measure.perpendicular_of_le A1,
  apply measure_theory.measure.sub_le,
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



lemma le_on_subsets_of_zero {α:Type*} [measurable_space α] {μ:measure_theory.measure α}
   (ν:measure_theory.measure α)  {S:set α}:is_measurable S → μ S = 0 → le_on_subsets μ ν S := 
begin
  intros A1 A2,
  rw le_on_subsets_def,
  apply and.intro A1,
  intros X B1 B2,
  have B3:μ X ≤ μ S,
  {
    apply measure_theory.measure_mono,
    apply B1,
  },
  apply le_trans B3,
  rw A2,
  simp,
end


lemma measure_theory.measure.sub_zero_eq_self {α:Type*} [measurable_space α] {μ ν:measure_theory.measure α} {S:set α} [A2:measure_theory.finite_measure μ]:is_measurable S → 
  μ S = 0 → 
  (ν - μ) S = ν S :=
begin
  intros A1 A4,
  have B1 := le_on_subsets_of_zero ν A1 A4,
  rw jordan_decomposition_junior_apply,
  rw A4,
  simp,
  --apply A2,
  apply B1,
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
       rw ← ennreal.le_zero_iff,
       have D1:=@measure_theory.measure.Union_nat α _ μ f,
       apply le_trans D1,
       rw ennreal.le_zero_iff,
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
            rw ← ennreal.le_zero_iff,
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
  apply B1,
  --apply A2,
  rw le_on_subsets_def,
  apply and.intro B1,
  intros X' C1 C2,
  apply A1,
  apply C2,
end


/- 
  This is taken from a step in Tao's proof of the Lebesgue-Radon-Nikodym Theorem.
  By the Hahn Decomposition Theorem, we can find a set where μ ≤ ν and μ S > 0.
 -/
lemma measure_theory.measure.perpendicular_sub_elim {α:Type*} [measurable_space α]
    (μ:measure_theory.measure α) {ν:measure_theory.measure α} 
    [A2:measure_theory.finite_measure ν]: 
    ¬(μ.perpendicular (ν - μ)) → 
    ∃ (S:set α), is_measurable S ∧ le_on_subsets μ ν S ∧ 0 < μ S :=
begin
  intros A3,
  have B1:=hahn_unsigned_inequality_decomp μ ν,
  cases B1 with X B1,
  have B2 := jordan_decomposition_junior_zero ν μ Xᶜ B1.right,
  have B3 := le_on_subsets_is_measurable B1.right,
  have B4:¬((ν - μ).perpendicular μ),
  {
    intro B4A,
    apply A3,
    apply measure_theory.measure.perpendicular_symmetric',
    apply B4A,
  },
  have B5 := measure_theory.measure.not_perpendicular (ν - μ) μ B4 B3 B2,
  simp at B5,
  apply exists.intro X,
  apply and.intro (le_on_subsets_is_measurable B1.left) 
       (and.intro B1.left B5),
end


lemma ennreal_smul_smul_measure_assoc {Ω:Type*} [N:measurable_space Ω] 
    (μ:measure_theory.measure Ω) {a b:ennreal}:(a * b) • μ = a • (b • μ) :=
begin
  apply measure_theory.measure.ext,
  intros S B1,
  repeat {rw ennreal_smul_measure_apply _ _ S B1},
  rw mul_assoc,
end


lemma measure_theory.measure.perpendicular_zero {Ω:Type*} [N:measurable_space Ω] (μ:measure_theory.measure Ω): 
  (μ.perpendicular 0) :=
begin
  rw measure_theory.measure.perpendicular_def2,
  apply exists.intro (∅:set Ω),
  split,
  apply is_measurable.empty,
  split,
  apply measure_theory.measure_empty,
  simp,
end

lemma measure_theory.measure.perpendicular_smul' {Ω:Type*} [N:measurable_space Ω] (μ ν:measure_theory.measure Ω) {k:ennreal}: 
  (μ.perpendicular ν) → (k • μ).perpendicular ν :=
begin
  intros A2,
  rw measure_theory.measure.perpendicular_def2,
  rw measure_theory.measure.perpendicular_def2 at A2,
  cases A2 with S A2,
  apply exists.intro S,
  apply and.intro (A2.left),
  apply and.intro _ A2.right.right,
  rw ennreal_smul_measure_apply,
  rw A2.right.left,
  simp,
  apply A2.left,
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


lemma measure_theory.measure.restrict_integral_eq_integral_indicator {Ω:Type*} [M:measurable_space Ω] 
    (μ:measure_theory.measure Ω) {S:set Ω} {f:Ω → ennreal}:
    (is_measurable S) →
    (μ.restrict S).integral f = μ.integral (S.indicator f) :=
begin
  intros A1,
  
  unfold measure_theory.measure.integral,
  rw measure_theory.lintegral_indicator,
  apply A1,
end


lemma integral_eq {Ω:Type*} [M:measurable_space Ω] 
    (μ:measure_theory.measure Ω) {f g:Ω → ennreal}:(f = g) →
    μ.integral f = μ.integral g :=
begin
  intros A1,
  rw A1,
end

lemma with_density_indicator_eq_restrict {Ω:Type*} [M:measurable_space Ω] 
    (μ:measure_theory.measure Ω) {S:set Ω} {f:Ω → ennreal}:
    (is_measurable S) → 
    μ.with_density (set.indicator S f) = (μ.restrict S).with_density f :=
begin
  intros A1,
  apply measure_theory.measure.ext,
  intros T B1,
  rw measure_theory.with_density_apply2,
  rw measure_theory.with_density_apply2,
  rw measure_theory.measure.restrict_integral_eq_integral_indicator,
  {
    rw set.indicator_indicator,
    rw set.indicator_indicator,
    rw set.inter_comm,
  },
  {
    apply A1,
  },
  {
    apply B1,
  },
  {
    apply B1,
  },
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
      apply measurable_set_indicator,
      apply B3.left,
      apply measurable_const,
    },
    split,
    {
      rw C1,
      rw with_density_indicator_eq_restrict_smul _ B3.left,
      rw ← smul_restrict_comm _ B3.left,
      apply le_trans _ (@measure_theory.measure.restrict_le_self _ _ _ S),
      apply restrict_le_restrict_of_le_on_subsets,
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


lemma set.indicator_sup {Ω:Type*} {x y:Ω → ennreal} {S:set Ω}:
   (∀ ω∈ S,  x ω ≤ y ω) → 
   set.indicator S (x ⊔ y) = set.indicator S y :=
begin
  intros A1,
  apply funext,
  intro ω,
  cases (classical.em (ω ∈ S)) with B1 B1,
  {
    repeat {rw set.indicator_of_mem B1},
    simp,
    rw max_eq_right,
    apply A1,
    apply B1,
  },
  {
    repeat {rw set.indicator_of_not_mem B1},
  },
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


lemma with_density_le_sup_apply {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal} {S:set Ω}:
    (is_measurable S) →
    (∀ ω∈ S,  x ω ≤ y ω) → 
    μ.with_density (x ⊔ y) S =
    μ.with_density y S :=
begin
  intros A3 A4,
  rw measure_theory.with_density_apply2 _ _ _ A3,
  rw measure_theory.with_density_apply2 _ _ _ A3,
  rw set.indicator_sup A4,
end


lemma le_on_subsets_with_density_of_le {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal} {S:set Ω}:
    (is_measurable S) →
    (∀ ω∈ S,  x ω ≤ y ω) → 
    le_on_subsets (μ.with_density x) (μ.with_density y) S :=
begin
  intros A3 A4,
  rw le_on_subsets_def,
  apply and.intro A3,
  intros X' B1 B2,
  apply with_density_le_with_density B2,
  intros ω C1,
  apply A4 ω,
  apply B1,
  apply C1,
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
  {S:set Ω}:le_on_subsets μ ν S → le_on_subsets ν μ Sᶜ → 
   μ ≤ μ.restrict Sᶜ + ν.restrict S :=
begin
  intros A1 A2,
  have B1:is_measurable S := le_on_subsets_is_measurable A1,
  rw measure_theory.measure.le_iff,
  intros T C1,
  rw measure_theory.measure_partition_apply μ S T B1 C1,
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
    rw set.inter_comm,
    rw le_on_subsets_def at A1,
    apply A1.right,
    apply set.inter_subset_right,
    apply is_measurable.inter C1 B1,
  },
end

lemma measure_theory.measure.sup_eq {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}
  (S:set Ω):le_on_subsets μ ν S → le_on_subsets ν μ Sᶜ → 
   (μ ⊔ ν) = μ.restrict Sᶜ + ν.restrict S :=
begin
  intros A1 A2,
  have D1:is_measurable S := le_on_subsets_is_measurable A1,
  apply le_antisymm,
  {
    apply @sup_le (measure_theory.measure Ω) _,
    {
      apply measure_theory.measure.le_restrict_add_restrict A1 A2,
    },
    {
      rw add_comm,
      have B1:ν.restrict Sᶜᶜ = ν.restrict S,
      {
        simp,
      },
      rw ← B1,
  
      apply measure_theory.measure.le_restrict_add_restrict,
      apply A2,
      simp,
      apply A1,
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
     rw measure_theory.measure_partition_apply c S,
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


lemma set.indicator_add_comm {α β:Type*} [ordered_add_comm_monoid β] {f g:α → β} {S:set α}:
    S.indicator (f + g) = S.indicator f + S.indicator g :=
begin
  apply funext,
  intros a,
  simp,
  cases (classical.em (a∈ S)) with B1 B1,
  {
    repeat {rw set.indicator_of_mem B1},
    simp,
  },
  {
    repeat {rw set.indicator_of_not_mem B1},
    simp,
  },
end


lemma measure_theory.measure.with_density_restrict_comm {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω)
  {x:Ω → ennreal} {S:set Ω}:is_measurable S → (μ.with_density x).restrict S = (μ.restrict S).with_density x := 
begin
  intros A1,
  apply measure_theory.measure.ext,
  intros T B1,
  rw measure_theory.with_density_apply2,
  rw measure_theory.measure.restrict_integral_eq_integral_indicator,
  rw measure_theory.measure.restrict_apply,
  rw set.indicator_indicator,
  rw set.inter_comm,
  rw measure_theory.with_density_apply2,
  repeat {assumption <|> apply is_measurable.inter},
end

lemma measure_theory.measure.with_density_add {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal}:measurable x → measurable y → μ.with_density (x + y) = μ.with_density x + μ.with_density y :=
begin
  intros A1 A2,
  apply measure_theory.measure.ext,
  intros S B1,
  rw measure_theory.measure.add_apply,
  rw measure_theory.with_density_apply2 ,
  rw measure_theory.with_density_apply2 ,
  rw measure_theory.with_density_apply2 ,
  rw set.indicator_add_comm,
  rw measure_theory.measure.integral_add,
  repeat{assumption <|> apply measurable_set_indicator},
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
  repeat {assumption <|> apply is_measurable_le <|> apply is_measurable_lt <|> apply measurable_set_indicator},
end


--Oh dear. This may not be true: instead it might be an inequality.
lemma with_density_sup {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal}:measurable x → measurable y → 
    μ.with_density (x ⊔ y) =
    measure_theory.measure.with_density μ x ⊔ measure_theory.measure.with_density μ y :=
begin
  intros A1 A2,
  rw with_density_sup' μ A1 A2,
  rw measure_theory.measure.sup_eq {ω:Ω|x ω ≤ y ω},
  rw lt_eq_le_compl,
  {
    apply le_on_subsets_with_density_of_le,
    apply is_measurable_le A1 A2,
    simp,
  },
  {
    apply le_on_subsets_with_density_of_le,
    apply is_measurable.compl (is_measurable_le A1 A2),
    simp,
    intros ω B3,
    apply le_of_lt B3,
  },
end


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
        apply B3A1.right,
        apply is_measurable.univ,
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
        apply with_density_le_with_density,
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
        simp,
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
          --apply @add_le_add (measure_theory.measure Ω) _,
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
  (μ.integral (set.indicator S f) = ν S) :=
begin
  intros A1 A2,
  unfold is_radon_nikodym_deriv at A1,
  cases A1 with A3 A1,
  subst ν,
  rw measure_theory.with_density_apply2,
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
  (μ.integral (set.indicator S f) = ν S)) →
  (is_radon_nikodym_deriv ν μ f)  :=
begin
  intros A1 A2,
  unfold is_radon_nikodym_deriv,
  split,
  apply A1,
  apply measure_theory.measure.ext,
  intros S A3,
  rw measure_theory.with_density_apply2,
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

