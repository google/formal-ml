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

import measure_theory.borel_space
import data.set.countable
import formal_ml.nnreal
import formal_ml.ennreal
import formal_ml.sum
import formal_ml.lattice
import formal_ml.measurable_space
import formal_ml.classical
import formal_ml.core
import formal_ml.characteristic
import data.equiv.list


lemma measure_theory.measure_unmeasurable {α:Type*} [M:measurable_space α] 
(μ:measure_theory.measure α)
(S:set α):
μ S = ⨅ (t : set α) (st : S ⊆ t) (ht : measurable_set t), μ t :=
begin
  have h1:μ S = μ.to_outer_measure.trim S,
  { rw μ.trimmed,  rw measure_theory.to_outer_measure_apply },
  rw measure_theory.outer_measure.trim_eq_infi at h1,
  apply h1,
end


lemma measure_theory.measurable_sequence {α:Type*} [M:measurable_space α] 
(μ:measure_theory.measure α)
(S:set α):
(μ S ≠ ⊤) →
∃ (f:ℕ → set α),
∀ n, measurable_set (f n) ∧ (S ⊆ f n) ∧ μ (f n) ≤ ((μ S) + (1)/((n:ennreal) + 1)) :=   
begin
  intros h1,
  
  have h2 : μ S = ⨅ (t : set α) (st : S ⊆ t) (ht : measurable_set t), μ t,
  { apply measure_theory.measure_unmeasurable },
  rw ←  ennreal.lt_top_iff_ne_top at h1,
  have h4 := h1,
 
   rw h2 at h1,
  have h:∀ (n:ℕ), ∃ (T:set α), measurable_set T ∧ (S ⊆ T) ∧ 
          μ T ≤ ((μ S) + (1)/((n:ennreal) + 1)),
  { intros n,
    have h3_4 : μ S + ((n:ennreal) + 1)⁻¹ < ⊤,
    { rw ennreal.add_lt_top,  split, apply h4,
      simp, apply ennreal.add_pos_of_pos, apply ennreal.zero_lt_one },
    have h3_1:0< (1)/((n:nnreal) + 1) := nnreal.unit_frac_pos n,
    have h3_2:= @ennreal.le_of_infi _ _ ((1)/((n:nnreal) + 1)) h1 h3_1,
    cases h3_2 with t h3_2,
    simp at h3_2,
    rw ← h2 at h3_2,
    have h3_5 : S ⊆ t,
    { apply ennreal.infi_prop_le_elim (S ⊆ t),
      apply lt_of_le_of_lt h3_2,
      apply h3_4, }, 
    rw infi_prop_def at h3_2,
    --apply h3_5,
    have h3_6 : measurable_set t,
    { apply ennreal.infi_prop_le_elim (measurable_set t),
      apply lt_of_le_of_lt h3_2,
      apply h3_4, }, 
    rw infi_prop_def at h3_2,
    apply exists.intro t,
    split,
    apply h3_6,
    split,
    apply h3_5,
    --simp, 
    have h3_7:1 / ((n:ennreal) + 1) = ((n:ennreal) + 1)⁻¹,
    { rw ennreal.one_div, },
    rw h3_7,
    apply h3_2,
    apply h3_6,
    apply h3_5 },
  rw classical.skolem at h,
  apply h,--sorry
end


lemma measure_theory.measurable_eq {α:Type*} [M:measurable_space α]
(μ:measure_theory.measure α) (S:set α):∃ T:set α, 
measurable_set T ∧ μ T = μ S ∧ S ⊆ T := 
begin
  have h1:μ S = μ.to_outer_measure.trim S,
  { rw μ.trimmed,  rw measure_theory.to_outer_measure_apply },
  rw measure_theory.outer_measure.trim_eq_infi at h1,
  --rw h1,
  have h2 : ((μ S) = (⊤:ennreal)) ∨ ((μ S) ≠ (⊤:ennreal)),
  { apply em },
  cases h2,
  { apply exists.intro set.univ, split,
    apply measurable_set.univ, split,
    rw h2, rw ← top_le_iff, 
    rw ← h2, apply measure_theory.measure_mono, simp, simp },
  { have h3 := measure_theory.measurable_sequence μ S h2,
    cases h3 with f h3,
    have h7:S ⊆ ⋂ (n:ℕ), f n,
    { rw set.subset_Inter_iff, intro n, apply (h3 n).right.left },
    apply exists.intro (⋂ n, f n),
    split,
    apply measurable_set.Inter,
    apply (λ n, (h3 n).left),
    split,
    apply le_antisymm,
    { apply ennreal.le_of_forall_pos_le_add,
      intros ε h4 h5,
      have h6 := nnreal.exists_unit_frac_lt_pos h4,
      cases h6 with n h6,
      apply @le_trans _ _ _ (μ (f n)),
      apply measure_theory.measure_mono, apply set.Inter_subset,
      --apply le_ _,
      apply le_trans ((h3 n).right.right),
      --apply ennreal.le_of_add_le_add_left,
      --apply h5,
      
      apply @add_le_add_left ennreal _ _, 
      apply le_of_lt _,
      
      rw ← ennreal.coe_one,
      have C8A1:(n:ennreal) = ((n:nnreal):ennreal),
      { simp },
      rw C8A1,
      rw ← ennreal.coe_add,
      rw ← ennreal.coe_div,
      rw ennreal.coe_lt_coe,
      apply h6,
      simp },
      apply measure_theory.measure_mono,
      apply h7,
      apply h7 },
end 

/--
  This is like measure_theory.measure_eq_inter_diff, but leverages measure_theory.le_to_outer_measure_caratheodory,  which could be considered an implementation detail.
 -/
lemma measure_theory.measure_eq_inter_diff' {α:Type*} [M:measurable_space α] 
  {μ:measure_theory.measure α} {s t:set α}:measurable_set t → μ s = μ (s ∩ t) + μ (s \ t) :=
begin
  intros A1,
  have A2:M ≤ μ.to_outer_measure.caratheodory := measure_theory.le_to_outer_measure_caratheodory μ,
  have A3:μ.to_outer_measure.caratheodory.measurable_set' t,
  {apply A2,apply A1},
  rw measure_theory.outer_measure.is_caratheodory_iff at A3,
  apply A3,
end  



