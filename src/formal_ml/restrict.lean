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



namespace measure_theory

namespace outer_measure

/-- The trimmed property of a measure μ states that μ.to_outer_measure.trim = μ.to_outer_measure.
This theorem shows that a restricted trimmed outer measure is a trimmed outer measure. -/
lemma restrict_trimmed_of_trimmed {α : Type*} [measurable_space α]
    {μ : measure_theory.outer_measure α} {s : set α} (h_meas : is_measurable s) (h_eq_trim : μ.trim = μ) :
    (measure_theory.outer_measure.restrict s μ).trim = (measure_theory.outer_measure.restrict s μ) :=
begin
  apply measure_theory.outer_measure.ext, intro t,
  rw [trim_eq_infi, restrict_apply],
  apply le_antisymm,
  { have h_apply_eq_trim_apply : μ (t ∩ s) = μ.trim (t ∩ s), { rw h_eq_trim }, 
    rw [h_apply_eq_trim_apply, trim_eq_infi], simp only [le_infi_iff, restrict_apply],
    intros v h_subset h_meas_v,
    apply @infi_le_of_le ennreal _ _ _ _ (v ∪ sᶜ),
    repeat {apply @infi_le_of_le ennreal _ _ _ _ _},
    apply μ.mono, rw set.subset_def,
    simp only [set.mem_inter_eq, set.mem_union_eq, set.mem_compl_eq, and_imp],
    intros x h_in_v_or_not_s h_in_s, cases h_in_v_or_not_s with h_in_v h_in_not_s, apply h_in_v,
    exfalso, apply h_in_not_s h_in_s,
    apply is_measurable.union h_meas_v (is_measurable.compl h_meas),
    rw set.subset_def, intros x h_in_t,
    have h_subset_x := (set.subset_def.mp h_subset) x,
    rw [set.mem_inter_eq, and_imp] at h_subset_x,
    rw [set.mem_union_eq, set.mem_compl_eq],
    apply or.elim (classical.em (x ∈ s))  (λ h_in_v, or.inl (h_subset_x h_in_t h_in_v)) or.inr },
  { simp only [le_infi_iff, restrict_apply], intros u h_subset h_meas_u, apply μ.mono,
    simp only [set.inter_subset_right, set.subset_inter_iff, and_true],
    apply set.subset.trans (set.inter_subset_left t s) h_subset },
end

lemma of_function_apply {α : Type*} [measurable_space α]
  {g : set α → ennreal} (h_empty : g ∅ = 0) (s: set α):
  outer_measure.of_function g h_empty s = 
  (⨅ (f : ℕ → set α) (h : s ⊆ set.Union f), ∑' n, g (f n)) := rfl

/-- The value of the Infimum of a nonempty set of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of sets that 
covers that set, where a different measure can be used for each set in the cover. -/ 
lemma Inf_apply {α : Type*} [measurable_space α]
  {s : set (measure_theory.outer_measure α)} {t : set α} (h : s.nonempty):
  Inf s t = (⨅ (f : ℕ →  set α) (h : t ⊆ set.Union f), ∑' n, ⨅  (μ : outer_measure α) (h2 : μ ∈ s), μ (f n)) := 
begin
  rw set.nonempty_def at h, cases h with μ h, 
  rw [Inf_eq_of_function_Inf_gen, of_function_apply],
  apply le_antisymm; simp; intros f h_subset; apply @infi_le_of_le ennreal _ _ _ _ f;
  apply @infi_le_of_le ennreal _ _ _ _ h_subset; apply ennreal.tsum_le_tsum; intro n;
  rw Inf_gen_nonempty2 _ _ h; apply le_refl _,
end

/-- This proves that Inf and restrict commute for outer measures. -/
lemma restrict_Inf_eq_Inf_restrict {α : Type*} [measurable_space α]
  (s : set (measure_theory.outer_measure α)) {t : set α} (h_meas : is_measurable t) (h_nonempty : s.nonempty) :
  measure_theory.outer_measure.restrict t (Inf s) = Inf ((measure_theory.outer_measure.restrict t) '' s) := 
begin
  have h_nonempty_image:((measure_theory.outer_measure.restrict t) '' s).nonempty,
  { apply set.nonempty_image_iff.mpr h_nonempty },
  ext1 u, rw restrict_apply, 
  repeat {rw Inf_apply},
  apply le_antisymm; simp; intros f h_meas,
  { apply @infi_le_of_le ennreal _ _ _ _ (λ n, (f n) ∩ t),
    apply @infi_le_of_le ennreal _ _ _ _ _,
    apply ennreal.tsum_le_tsum, simp, intros n μ₁ μ₂ h_μ₂_in_s h_restrict_eq, subst μ₁,
    apply @infi_le_of_le ennreal _ _ _ _ μ₂,
    apply @infi_le_of_le ennreal _ _ _ _ h_μ₂_in_s,
    { simp [le_refl] },
    { rw set.subset_def, intros x h_x_in_union, rw set.mem_inter_eq at h_x_in_union,
      have h_exists := (set.mem_Union.mp ((set.subset_def.mp h_meas) x h_x_in_union.left)), cases h_exists with i h_x_in_f_i, 
      rw set.mem_Union, apply exists.intro i, rw set.mem_inter_eq, apply and.intro h_x_in_f_i h_x_in_union.right } },
  { apply @infi_le_of_le ennreal _ _ _ _ (λ n, (f n) ∪ tᶜ),
    apply @infi_le_of_le ennreal _ _ _ _ _,
    apply ennreal.tsum_le_tsum, simp, intros n μ h_nonempty,
    apply @infi_le_of_le ennreal _ _ _ _ (restrict t μ),
    apply @infi_le_of_le ennreal _ _ _ _ μ,
    apply @infi_le_of_le ennreal _ _ _ _ _,
    simp only [restrict_apply], apply μ.mono,
    { rw set.subset_def, simp only [and_imp, set.mem_inter_eq, set.mem_union_eq, set.mem_compl_eq],
      intros x h_in_f_n_or_notin_t h_x_in_t, cases h_in_f_n_or_notin_t with h_x_in_f_n h_x_notin_t,
      apply h_x_in_f_n, exfalso, apply h_x_notin_t, apply h_x_in_t },
    { simp [h_nonempty] },  
    { rw set.subset_def, intros x h_x_in_u,
      rw [set.mem_Union],
      have h_subset_x := (set.subset_def.mp h_meas) x,
      simp only [and_imp, set.mem_Union, set.mem_inter_eq] at h_subset_x,
      cases (classical.em (x ∈ t)) with h_x_in_t h_x_notin_t,
      have h_exists_i := h_subset_x h_x_in_u h_x_in_t, cases h_exists_i with i x_in_f_i,
      apply exists.intro i, apply (or.inl x_in_f_i),
      apply exists.intro 0,
      rw [set.mem_union_eq, set.mem_compl_eq],
      apply or.inr h_x_notin_t } },
  repeat {assumption},
end

end outer_measure

namespace measure

/--This lemma shows that `restrict` and `to_outer_measure` commute. Note that the LHS has a 
restrict on measures and the RHS has a restrict on outer measures. -/
lemma restrict_to_outer_measure_eq_to_outer_measure_restrict {α : Type*} [measurable_space α]
    {μ : measure α} {s : set α} (h : is_measurable s) :
    (μ.restrict s).to_outer_measure = measure_theory.outer_measure.restrict s (μ.to_outer_measure) :=
begin
  ext1 t,
  rw [outer_measure.restrict_apply, restrict, restrictₗ, coe_to_outer_measure, lift_linear,
    linear_map.coe_mk, ← outer_measure.measure_of_eq_coe, ← coe_to_outer_measure, 
    to_measure_to_outer_measure, outer_measure.restrict_trimmed_of_trimmed h, 
    outer_measure.measure_of_eq_coe, outer_measure.restrict_apply, coe_to_outer_measure],
  apply trimmed,
end

/--This lemma shows that `Inf` and `restrict` commute for measures. -/
lemma restrict_Inf_eq_Inf_restrict {α:Type*} [measurable_space α]
  (s : set (measure_theory.measure α)) {T : set α} (AX : s.nonempty) (A1 : is_measurable T) :
  (Inf s).restrict T = Inf ((λ μ:measure_theory.measure α, μ.restrict T) '' s) := 
begin
  ext1 s2 B1,
  have h_image_comm : (λ (x : measure_theory.measure α), (x.restrict T).to_outer_measure) =
    (λ (x : measure_theory.measure α), (measure_theory.outer_measure.restrict T) x.to_outer_measure),
  { ext1 x, rw restrict_to_outer_measure_eq_to_outer_measure_restrict A1 },
  rw [Inf_apply B1, restrict_apply B1, Inf_apply (is_measurable.inter B1 A1), set.image_image,
    h_image_comm, ← set.image_image _ to_outer_measure,
    ← outer_measure.restrict_Inf_eq_Inf_restrict _ A1,
    outer_measure.restrict_apply],
  apply set.nonempty_image_iff.mpr AX,
end

end measure

end measure_theory

/-
  This collection of theorems shows that 
  {S|is_measurable S ∧ μ.restrict S ≤ ν.restrict S} is a ring of sets.
 -/

lemma measure_theory.measure.restrict_apply_subset {α : Type*} [measurable_space α]
  (μ : measure_theory.measure α) {S T : set α} (h₁ : is_measurable S)
  (h₂ : S ⊆ T) : (μ.restrict T) S = μ S :=
begin
  rw measure_theory.measure.restrict_apply h₁,
  simp [set.inter_eq_self_of_subset_left, h₂],
end

lemma le_of_subset_of_restrict_le_restrict {α:Type*} [measurable_space α]
  {μ ν:measure_theory.measure α} {S T:set α}:
  T ⊆ S →
  (μ.restrict S) ≤ ν.restrict S →
  is_measurable S →
  is_measurable T →  μ T ≤ ν T :=
begin
  intros A3 A2 A1 A4,
  rw measure_theory.measure.le_iff at A2,
  have B3 := A2 T A4,
  rw measure_theory.measure.restrict_apply_subset μ A4 A3 at B3,
  rw measure_theory.measure.restrict_apply_subset ν A4 A3 at B3,
  apply B3,
end


lemma restrict_le_restrict_of_le_subset {α:Type*} [measurable_space α]
  {μ ν:measure_theory.measure α} {S:set α} (H:is_measurable S):
  (∀ T:set α, T ⊆ S → is_measurable T → μ T ≤ ν T) →
  (μ.restrict S) ≤ ν.restrict S :=
begin
  intros A1,
  rw measure_theory.measure.le_iff,
  intros s A2,
  repeat {rw measure_theory.measure.restrict_apply A2},
  apply A1,
  {simp},
  {simp [is_measurable.inter,H,A2]},
end

lemma restrict_le_restrict_of_restrict_le_restrict_of_subset {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X Y:set α}:
    μ.restrict X ≤ ν.restrict X →
    Y ⊆ X →
    is_measurable X →
    is_measurable Y →
    μ.restrict Y ≤ ν.restrict Y :=
begin
  intros A1 A2 A3 A4,
  rw measure_theory.measure.le_iff,
  intros S A5,
  rw measure_theory.measure.restrict_apply,
  rw measure_theory.measure.restrict_apply,
  have A6:S ∩ Y ⊆ X,
  {apply set.subset.trans _ A2, simp},
  apply le_of_subset_of_restrict_le_restrict A6 A1 A3,
  repeat {simp [is_measurable.inter,*]},
end

lemma restrict_le_restrict_union {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X Y:set α}:
    μ.restrict X ≤ ν.restrict X →
    μ.restrict Y ≤ ν.restrict Y →
    is_measurable X →
    is_measurable Y →
    μ.restrict (X ∪ Y) ≤ ν.restrict (X ∪ Y) :=
begin
  intros A1 A2 A3 A4,
  have A6:X ∪ (Y \ X) = X ∪ Y := set.union_diff_self,
  rw ← A6,
  have A7:disjoint X (Y \ X) := set.disjoint_diff,
  repeat {rw measure_theory.measure.restrict_union},
  apply measure_theory.measure.add_le_add A1 _,
  apply restrict_le_restrict_of_restrict_le_restrict_of_subset A2,
  apply set.diff_subset,
  repeat {simp [set.disjoint_diff, is_measurable.inter, is_measurable.diff,*]},
end

lemma set.directed_has_subset_of_monotone {α:Type*} {f:ℕ → set α}:
 monotone f → directed has_subset.subset f :=
begin
  intros A1,
  unfold directed,
  intros x y,
  apply exists.intro (max x y),
  split,
  {
    rw ← set.le_eq_subset,
    apply @A1 x (max x y),
    apply le_max_left,
  },
  {
    rw ← set.le_eq_subset,
    apply @A1 y (max x y),
    apply le_max_right,
  },
end

lemma restrict_le_restrict_m_Union {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) {f:ℕ → set α}:
    monotone f →
    (∀ n:ℕ, is_measurable (f n)) →
    (∀ n:ℕ, μ.restrict (f n) ≤ ν.restrict (f n)) → 
    (μ.restrict (set.Union f) ≤  ν.restrict (set.Union f)) :=
begin
  intros A1 A2 A3 S A5,
  rw measure_theory.measure.restrict_Union_apply_eq_supr,
  rw measure_theory.measure.restrict_Union_apply_eq_supr,
  rw supr_le_iff, 
  intro i,
  have B1:(μ.restrict (f i)) S ≤ (ν.restrict (f i)) S,
  {apply A3, apply A5},
  apply le_trans B1,
  
  apply @le_supr ennreal _ _,
  repeat {simp [set.directed_has_subset_of_monotone,*]}, 
end

--Used in radon-nikodym, but let's keep restrict lemmas together.
lemma measure_theory.measure.restrict_apply_self {α:Type*} [measurable_space α]
  (μ:measure_theory.measure α) {S:set α} (H:is_measurable S):
  (μ.restrict S) S = μ S :=
begin
  rw measure_theory.measure.restrict_apply H,
  simp,
end 

lemma nnreal.add_sub_add_eq_sub_add_sub {a b c d:nnreal} : c ≤ a → d ≤ b →
  a + b - (c + d) = (a - c) + (b - d) :=
begin
  intros A1 A2,
  have A3:c + d ≤ a + b,
  { apply add_le_add A1 A2 },
  repeat {rw ← nnreal.eq_iff <|> rw nnreal.coe_sub <|> rw nnreal.coe_add},
  repeat {assumption},
  linarith,
end

lemma ennreal.add_sub_add_eq_sub_add_sub {a b c d:ennreal}:c < ⊤ → d < ⊤ → 
    c ≤ a → d ≤ b →
    a + b - (c + d) = (a - c) + (b - d) :=
begin
  cases c;cases b;cases a;cases d;
  simp [ennreal.top_sub_coe, ennreal.none_eq_top, ennreal.some_eq_coe,
    ennreal.add_top, ← ennreal.coe_add, ← ennreal.coe_sub],
  apply nnreal.add_sub_add_eq_sub_add_sub,
end

lemma le_measurable_add {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) {X Y:set α}:
    μ X < ⊤ →
    μ Y < ⊤ →
    is_measurable X →
    is_measurable Y →
    μ X ≤ ν X →
    μ Y ≤ ν Y →
    disjoint X Y →
    ν (X ∪ Y) - μ (X ∪ Y) = (ν X - μ X) +  (ν Y - μ Y) :=
begin
  intros A1 A2 A3 A4 A5 A6 A7,
  repeat {rw measure_theory.measure_union A7 A3 A4},
  rw ennreal.add_sub_add_eq_sub_add_sub A1 A2 A5 A6,
end

lemma measure_theory.measure.le_of_restrict_le_restrict_self {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) {S:set α} (H:is_measurable S):
  (μ.restrict S) ≤ ν.restrict S  → μ S ≤  ν S :=
begin
  intro A1,
  apply le_of_subset_of_restrict_le_restrict (set.subset.refl S) A1 H H,
end

lemma restrict_le_restrict_add {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) {X Y:set α}:
    μ X < ⊤ →
    μ Y < ⊤ →
    is_measurable X →
    is_measurable Y →
    μ.restrict X ≤ ν.restrict X → 
    μ.restrict Y ≤ ν.restrict Y →
    disjoint X Y →
    ν (X ∪ Y) - μ (X ∪ Y) = (ν X - μ X) +  (ν Y - μ Y) :=
begin
  intros A1 A2 A3 A4 A5 A6 A7,
  apply le_measurable_add μ ν A1 A2 A3 A4 
      (measure_theory.measure.le_of_restrict_le_restrict_self _ _ A3 A5) 
      (measure_theory.measure.le_of_restrict_le_restrict_self _ _ A4 A6) A7,
end
