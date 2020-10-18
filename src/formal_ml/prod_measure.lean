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
import data.equiv.list


/--
  This is like measure_theory.measure_eq_inter_diff, but leverages measure_theory.le_to_outer_measure_caratheodory,
  which could be considered an implementation detail.
 -/
lemma measure_theory.measure_eq_inter_diff' {α:Type*} [M:measurable_space α] 
  {μ:measure_theory.measure α} {s t:set α}:is_measurable t → μ s = μ (s ∩ t) + μ (s \ t) :=
begin
  intros A1,
  have A2:M ≤ μ.to_outer_measure.caratheodory := measure_theory.le_to_outer_measure_caratheodory μ,
  have A3:μ.to_outer_measure.caratheodory.is_measurable' t,
  {apply A2,apply A1},
  rw measure_theory.outer_measure.is_caratheodory_iff at A3,
  apply A3,
end  

noncomputable def prod.outer_measure {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.outer_measure α) (μβ:measure_theory.outer_measure β):measure_theory.outer_measure (α × β) := 
  measure_theory.outer_measure.of_function
  (λ P:set (α × β), μα (prod.fst '' P) * μβ (prod.snd '' P))
begin
  simp,
end 

noncomputable def prod.measure {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.measure α) (μβ:measure_theory.measure β):measure_theory.measure (α × β) := 
  (prod.outer_measure μα.to_outer_measure μβ.to_outer_measure).to_measure 
begin
  unfold prod.measurable_space,
  simp,
  split;
  intros P A1;
  unfold measurable_space.comap at A1;
  cases A1 with s A1;
  cases A1 with A1 A2;
  subst P;
  apply measure_theory.outer_measure.of_function_caratheodory;
  simp,
  {intros t,
   have B1:μα (prod.fst '' t ∩ s) + μα (prod.fst '' t \ s) = μα (prod.fst '' t),
   {rw ← measure_theory.measure_eq_inter_diff', apply A1},
   rw ← B1,
   clear B1,
   rw right_distrib,
   apply @add_le_add ennreal _;apply ennreal.mul_le_mul;try {apply measure_theory.measure_mono};simp;rw set.subset_def;
   intros p B2;cases p;simp at B2;simp [B2];
   try {apply exists.intro p_snd,simp [B2]};
   {apply exists.intro p_fst,simp [B2]}},
  {intros t,
   have B1:μβ (prod.snd '' t ∩ s) + μβ (prod.snd '' t \ s) = μβ (prod.snd '' t),
   {rw ← measure_theory.measure_eq_inter_diff', apply A1},
   rw ← B1,
   clear B1,
   rw left_distrib,
   apply @add_le_add ennreal _;apply ennreal.mul_le_mul;try {apply measure_theory.measure_mono};simp;rw set.subset_def;
   intros p B2;cases p;simp at B2;simp [B2];
   try {apply exists.intro p_snd,simp [B2]};
   {apply exists.intro p_fst,simp [B2]}},
end

@[simp]
lemma set.prod_fst_image_of_prod {α:Type*} {β:Type*} (A:set α) (B:set β) (h:B.nonempty):(prod.fst '' (A.prod B)) = A :=
begin
  ext p;split;intros A1,
  simp at A1,simp [A1],
  simp [A1],
  apply h,
end

@[simp]
lemma set.prod_snd_image_of_prod {α:Type*} {β:Type*} (A:set α) (B:set β) (h:A.nonempty):(prod.snd '' (A.prod B)) = B :=
begin
  ext p;split;intros A1,
  simp at A1,simp [A1],
  simp [A1],
  apply h,
end

-- λ 
--#check (\lambda 
lemma prod.outer_measure.Inf_sum {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.outer_measure α) (μβ:measure_theory.outer_measure β) {P:set (α × β)}:
  prod.outer_measure μα μβ P = 
  ⨅ (f:ℕ → set α) (g:ℕ → set β) (h₁: P ⊆ ⋃ n, (f n).prod (g n)), ∑' n, μα (f n) * μβ (g n) :=
begin
  unfold prod.outer_measure measure_theory.outer_measure.of_function,
  rw ← measure_theory.outer_measure.measure_of_eq_coe,
  simp,
  apply le_antisymm,
  simp,
  intros f g B1,

  apply @infi_le_of_le ennreal  _ _ _ _ (λ (n:ℕ), (f n).prod (g n)),
  apply @infi_le_of_le ennreal  _ _ _ _ _,
  apply ennreal.tsum_le_tsum,
  intros a,
  --simp,
  cases (set.eq_empty_or_nonempty (f a)) with B2 B2,
  {simp [B2]},
  cases (set.eq_empty_or_nonempty (g a)) with B3 B3,
  {simp [B3]},
  {simp [B2,B3,le_refl]},
  --apply le_refl _,
  --apply @le_infi ennreal _ _,
  {simp [B1]},
  simp,
  intros h C1,
  apply @infi_le_of_le ennreal _ _ _ _ (λ n, prod.fst '' (h n)),
  apply @infi_le_of_le ennreal _ _ _ _ (λ n, prod.snd '' (h n)),
  apply @infi_le_of_le ennreal  _ _ _ _ _,
  simp,
  apply le_refl _,
  simp,
  apply @set.subset.trans (α × β) P (set.Union h) (⋃ (n : ℕ), (prod.fst '' h n).prod (prod.snd '' h n)) C1,
  apply set.Union_subset_Union,
  intro i,
  rw set.subset_def,
  intros a C2,cases a,simp,
  apply and.intro (exists.intro a_snd C2) (exists.intro a_fst C2),
end


/-
  If we can make this into an equality, we're home free. 
  See https://www.math.ucdavis.edu/~hunter/measure_theory/measure_notes_ch5.pdf
  Those notes focus on measurable sets. We could theoretically do the same. However,
  it would make the rest of the analysis much more complex.
  I wonder if using an "outer measure lower integral" would make this useful. 
-/
lemma prod.outer_measure.apply_prod_le {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.outer_measure α) (μβ:measure_theory.outer_measure β) {A:set α} {B:set β}:
  prod.outer_measure μα μβ (A.prod B) ≤ μα A * μβ B :=
begin
  rw prod.outer_measure.Inf_sum,
  {apply @infi_le_of_le ennreal _ _ _ _ (λ (n:ℕ), ite (n = 0) A ∅),
  apply @infi_le_of_le ennreal _ _ _ _ (λ (n:ℕ), ite (n = 0) B ∅),
  apply @infi_le_of_le ennreal _ _ _ _ _,
  rw tsum_eq_single 0,
  {simp [le_refl]},
  intros b' B1,
  simp [B1],
  apply ennreal.t2_space,
  rw set.subset_def,
  intros p B2,
  simp,
  apply exists.intro 0,
  {simp at B2,simp [B2]}},
end
#check measure_theory.outer_measure
/-
  This can be made into an equality once we fix the issues above.
-/
lemma prod.measure.apply_prod_le
{α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.measure α) (μβ:measure_theory.measure β) (A:set α) (B:set β):is_measurable A →
  is_measurable B → 
  (prod.measure μα μβ) (A.prod B) ≤ (μα A) * (μβ B)  :=
begin
  intros A1 A2,
  unfold prod.measure,
  rw ← measure_theory.to_outer_measure_apply,
  rw measure_theory.to_measure_to_outer_measure,
  rw measure_theory.outer_measure.trim_eq,
  apply prod.outer_measure.apply_prod_le,
  --refl,
  apply is_measurable.prod A1 A2,
end
