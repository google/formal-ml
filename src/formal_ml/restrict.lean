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

namespace measure_theory

namespace measure


lemma inter_add_inter_compl {α:Type*} [measurable_space α]
  (μ : measure α) (s t : set α)  (A2 : measurable_set s) (A1 : measurable_set t) :
  (μ (s ∩ t) + μ (s ∩ tᶜ)) = μ s :=
begin
  rw ← measure_union _
       (measurable_set.inter A2 A1) (measurable_set.inter A2 (measurable_set.compl A1)),  
  rw set.inter_union_compl,
  apply set.disjoint_of_subset (set.inter_subset_right s t) (set.inter_subset_right s tᶜ),
  apply @disjoint_compl_right (set α) t _,
end

lemma restrict_sub_eq_restrict_sub_restrict {Ω : Type*} [M : measurable_space Ω]
  (μ ν : measure Ω) {s : set Ω} (h_meas_s : measurable_set s) :
  (μ - ν).restrict s = (μ.restrict s) - (ν.restrict s) :=
begin
  repeat {rw sub_def},
  have h_nonempty : {d | μ ≤ d + ν}.nonempty,
  { apply @set.nonempty_of_mem _ _ μ, simp, intros t h_meas,
    apply le_add_right (le_refl (μ t)) },
  rw restrict_Inf_eq_Inf_restrict h_nonempty h_meas_s,
  have h_Inf_le_Inf : ∀ s' t' : set (measure Ω),
                      (∀ b ∈ t', ∃ a ∈ s', a ≤ b) → Inf s' ≤ Inf t',
  { intros s' t' h, 
    rw le_Inf_iff, intros b h_b_in_t', 
    have h_exists_a := h b h_b_in_t', cases h_exists_a with a h_a, 
    cases h_a with h_a_in_s' h_a_le_b,
    apply Inf_le_of_le h_a_in_s' h_a_le_b },  
  apply le_antisymm,
  { apply h_Inf_le_Inf,
    intros ν' h_ν'_in, simp at h_ν'_in, apply exists.intro (ν'.restrict s),
    split,
    { simp, apply exists.intro (ν' + (⊤ : measure_theory.measure Ω).restrict sᶜ),
      split,
      { rw [add_assoc, add_comm _ ν, ← add_assoc, measure_theory.measure.le_iff],
        intros t h_meas_t,
        have h_inter_inter_eq_inter : ∀ t' : set Ω , t ∩ t' ∩ t' = t ∩ t',
        { intro t', rw set.inter_eq_self_of_subset_left, apply set.inter_subset_right t t' },
        have h_meas_t_inter_s : measurable_set (t ∩ s) :=
        measurable_set.inter h_meas_t h_meas_s,
        rw [← inter_add_inter_compl μ t s h_meas_t h_meas_s,
            ← inter_add_inter_compl 
              (ν' + ν + (⊤ : measure Ω).restrict sᶜ) t s h_meas_t h_meas_s],
        apply add_le_add _ _; rw add_apply,
        { have h_restrict : ∀ μ₂ : measure Ω, μ₂ (t ∩ s) = μ₂.restrict s (t ∩ s),
          { intro μ₂, rw [restrict_apply h_meas_t_inter_s], 
            rw [(h_inter_inter_eq_inter s)] },
          apply le_add_right _,
          rw [add_apply, h_restrict μ, h_restrict ν], apply h_ν'_in _ h_meas_t_inter_s },
        cases (@set.eq_empty_or_nonempty _ (t ∩ sᶜ)) with h_inter_empty h_inter_nonempty,
        { simp [h_inter_empty] },
        { have h_meas_inter_compl := 
          measurable_set.inter h_meas_t (measurable_set.compl h_meas_s),
          rw [restrict_apply h_meas_inter_compl, h_inter_inter_eq_inter sᶜ],
          have h_mu_le_add_top : μ ≤ ν' + ν + ⊤,
          { rw add_comm,
            have h_le_top : μ ≤ ⊤ := le_top,
            apply (λ t₂ h_meas, le_add_right (h_le_top t₂ h_meas)) },
          apply h_mu_le_add_top _ h_meas_inter_compl } },
      { ext1 t h_meas_t,
        simp [restrict_apply h_meas_t,
              restrict_apply (measurable_set.inter h_meas_t h_meas_s),
              set.inter_assoc] } },
    { apply restrict_le_self } },
  { apply h_Inf_le_Inf,
    intros s h_s_in, cases h_s_in with t h_t, cases h_t with h_t_in h_t_eq, subst s,
    apply exists.intro (t.restrict s), split,
    { rw [set.mem_set_of_eq, ← restrict_add], 
      apply restrict_mono (set.subset.refl _) h_t_in },
    { apply le_refl _ } },
end

lemma restrict_apply_self {α : Type*} [measurable_space α]
  (μ : measure α) {s : set α} (h_meas_s : measurable_set s) :
  (μ.restrict s) s = μ s :=
begin
  rw [restrict_apply h_meas_s, set.inter_self],
end 

lemma sub_apply_eq_zero_of_restrict_le_restrict {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (s:set Ω) 
  (h_le : μ.restrict s ≤ ν.restrict s) (h_meas_s : measurable_set s) :
  (μ - ν) s = 0 :=
begin
  rw [← restrict_apply_self _ h_meas_s, restrict_sub_eq_restrict_sub_restrict,
      sub_eq_zero_of_le],
  repeat {simp [*]},
end

end measure

end measure_theory

def measure_theory.finite_measure_of_le {Ω:Type*} [M:measurable_space Ω] 
  (μ ν : measure_theory.measure Ω) [measure_theory.finite_measure ν] (H:μ ≤ ν):
  measure_theory.finite_measure μ :=
begin
  apply measure_theory.finite_measure.mk (lt_of_le_of_lt (H set.univ measurable_set.univ) _),
  apply measure_theory.measure_lt_top ν,
end 

def measure_theory.finite_measure_restrict {Ω:Type*} [M:measurable_space Ω] 
  (μ:measure_theory.measure Ω) [measure_theory.finite_measure μ] (S:set Ω):
  measure_theory.finite_measure (μ.restrict S) :=
begin
  have A1:= @measure_theory.measure.restrict_le_self Ω M μ S,
  apply measure_theory.finite_measure_of_le (μ.restrict S) μ A1,
end

--This works with EITHER ν or μ being finite, or even ν S < ⊤.
lemma jordan_decomposition_junior_apply {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S:set Ω) [AX:measure_theory.finite_measure ν]:
  (ν.restrict S ≤ μ.restrict S) → (measurable_set S) →
  (μ - ν) S = μ S - ν S :=
begin
  intros A1 B1,
  rw ← measure_theory.measure.restrict_apply_self _ B1,
  rw measure_theory.measure.restrict_sub_eq_restrict_sub_restrict _ _,
  rw @measure_theory.measure.sub_apply Ω _ _ _ S (measure_theory.finite_measure_restrict ν S) B1 A1,
  repeat {rw measure_theory.measure.restrict_apply_self},
  repeat {exact B1},
end

lemma measure_theory.measure.restrict_apply_subset {α : Type*} [measurable_space α]
  (μ : measure_theory.measure α) {S T : set α} (h₁ : measurable_set S)
  (h₂ : S ⊆ T) : (μ.restrict T) S = μ S :=
begin
  rw measure_theory.measure.restrict_apply h₁,
  simp [set.inter_eq_self_of_subset_left, h₂],
end

lemma le_of_subset_of_restrict_le_restrict {α:Type*} [measurable_space α]
  {μ ν:measure_theory.measure α} {S T:set α}:
  T ⊆ S →
  (μ.restrict S) ≤ ν.restrict S →
  measurable_set S →
  measurable_set T →  μ T ≤ ν T :=
begin
  intros A3 A2 A1 A4,
  rw measure_theory.measure.le_iff at A2,
  have B3 := A2 T A4,
  rw measure_theory.measure.restrict_apply_subset μ A4 A3 at B3,
  rw measure_theory.measure.restrict_apply_subset ν A4 A3 at B3,
  apply B3,
end

lemma restrict_le_restrict_of_restrict_le_restrict_of_subset {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X Y:set α}:
    μ.restrict X ≤ ν.restrict X →
    Y ⊆ X →
    measurable_set X →
    measurable_set Y →
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
  repeat {simp [measurable_set.inter,*]},
end


/--
  A jordan decomposition of subtraction.
 -/
lemma jordan_decomposition_nonneg_sub {Ω:Type*} [M:measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S T:set Ω) [A1:measure_theory.finite_measure μ]: 
    measurable_set T → measurable_set S → μ.restrict S ≤ ν.restrict S →
    ν.restrict Sᶜ ≤ μ.restrict Sᶜ →
    (ν - μ) T = ν (T ∩ S) - μ (T ∩ S) :=
begin
  intros A3 A2 A5 A6,
  rw ← measure_theory.measure.inter_add_inter_compl (ν - μ) _ _ A3 A2,
  rw jordan_decomposition_junior_apply ν μ (T ∩ S),
  rw measure_theory.measure.sub_apply_eq_zero_of_restrict_le_restrict ν μ (T ∩ Sᶜ),
  rw add_zero,
  apply @restrict_le_restrict_of_restrict_le_restrict_of_subset Ω M ν μ Sᶜ (T ∩ Sᶜ) A6,
  repeat {simp [A2, A3]},
  apply @restrict_le_restrict_of_restrict_le_restrict_of_subset Ω M μ ν S (T ∩ S) A5,
  repeat {simp [A2, A3]},
end

lemma restrict_le_restrict_of_le_subset {α:Type*} [measurable_space α]
  {μ ν:measure_theory.measure α} {S:set α} (H:measurable_set S):
  (∀ T:set α, T ⊆ S → measurable_set T → μ T ≤ ν T) →
  (μ.restrict S) ≤ ν.restrict S :=
begin
  intros A1,
  rw measure_theory.measure.le_iff,
  intros s A2,
  repeat {rw measure_theory.measure.restrict_apply A2},
  apply A1,
  {simp},
  {simp [measurable_set.inter,H,A2]},
end

lemma restrict_le_restrict_union {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X Y:set α}:
    μ.restrict X ≤ ν.restrict X →
    μ.restrict Y ≤ ν.restrict Y →
    measurable_set X →
    measurable_set Y →
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
  repeat {simp [set.disjoint_diff, measurable_set.inter, measurable_set.diff,*]},
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
    (∀ n:ℕ, measurable_set (f n)) →
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
    measurable_set X →
    measurable_set Y →
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
  (μ ν:measure_theory.measure α) {S:set α} (H:measurable_set S):
  (μ.restrict S) ≤ ν.restrict S  → μ S ≤  ν S :=
begin
  intro A1,
  apply le_of_subset_of_restrict_le_restrict (set.subset.refl S) A1 H H,
end

lemma restrict_le_restrict_add {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) {X Y:set α}:
    μ X < ⊤ →
    μ Y < ⊤ →
    measurable_set X →
    measurable_set Y →
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

