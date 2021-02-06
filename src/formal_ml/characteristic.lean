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



noncomputable def set.characteristic {α:Type*} (S:set α):α → ennreal := S.indicator (λ _, (1:ennreal))

@[simp]
lemma set.characteristic.of_mem {α:Type*} {S:set α} {a:α}:a∈ S → S.characteristic a = 1 :=
begin
  intros h,
  simp [set.characteristic, h], 
end

@[simp]
lemma set.characteristic.of_not_mem {α:Type*} {S:set α} {a:α}:a∉ S → S.characteristic a = 0 :=
begin
  intros h,
  simp [set.characteristic, h], 
end

--α → ennreal := S.indicator (λ _, (1:ennreal))


lemma set.characteristic.subset {α:Type*} {S T:set α} (h:S⊆ T):S.characteristic ≤ T.characteristic :=
begin
  intros a,
  cases classical.em (a ∈ S) with h1 h1; 
  cases classical.em (a ∈ T) with h2 h2; simp [h1, h2],
  { apply le_refl _ },
  apply h2,
  apply h,
  apply h1,
end

lemma set.characteristic.prod {α β:Type*} {A:set α} {B:set β} {a:α} {b:β}:
(A.prod B).characteristic (a, b) = (A.characteristic a) * (B.characteristic b) :=
begin
  cases classical.em (a ∈ A) with h1 h1; 
  cases classical.em (b ∈ B) with h2 h2; simp [h1, h2],
end

lemma set.characteristic.Union {α:Type*} {S:ℕ → set α}:
((⋃ (n:ℕ), S n).characteristic) ≤ (∑' (n:ℕ), (S n).characteristic) :=
begin
  intro x,
  rw ennreal.tsum_apply,
  cases classical.em (x ∈ (⋃ (n:ℕ), S n)) with h1 h1; simp [h1],
  simp at h1,
  cases h1 with i h1,
  have h2 : (S i).characteristic x = 1,
  { simp [h1] },
  rw ← h2,
  apply ennreal.le_tsum
end

lemma measure_theory.lintegral_characteristic {α:Type*} [Mα:measurable_space α]
(μ:measure_theory.measure α) (S:set α): measurable_set S →
  (∫⁻ (a : α), S.characteristic a ∂μ) = μ S := 
begin
  intros h,
  simp [set.characteristic],
  rw measure_theory.lintegral_indicator,
  simp,
  apply h,
end

lemma measurable.characteristic {α:Type*} [Mα:measurable_space α]
 (S:set α): measurable_set S →
  measurable (S.characteristic) := begin
  intros h,
  simp [set.characteristic],
  apply measurable.indicator,
  simp,
  apply h,
end

