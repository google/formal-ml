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
import formal_ml.classical


lemma with_density_le_with_density {Ω:Type*} {M:measurable_space Ω}
  {μ:measure_theory.measure Ω} {x y:Ω → ennreal} 
  {S:set Ω}:
  measurable_set S →
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


--TODO: Remove measurability?
lemma with_density_sup_of_le {Ω:Type*} {M:measurable_space Ω}
  {μ:measure_theory.measure Ω} {x y:Ω → ennreal} 
  {S:set Ω}:measurable x → measurable y →
  measurable_set S →
  (∀ ω ∈ S, x ω ≤ y ω) →  
  μ.with_density (x⊔y) S = μ.with_density y S :=
begin
  intros A1 A2 A3 A4,
  rw measure_theory.with_density_apply2' μ (x ⊔ y) S A3,
  rw measure_theory.with_density_apply2' μ y S A3,
  have A5:set.indicator S (x ⊔ y) = set.indicator S y,
  {
    apply funext,
    intro ω,
    cases (classical.em (ω∈ S)) with A5A A5A,
    {
      rw set.indicator_of_mem A5A,
      rw set.indicator_of_mem A5A,
      rw sup_apply,
      simp [A4 _ A5A],
    },
    {
      rw set.indicator_of_not_mem A5A,
      rw set.indicator_of_not_mem A5A,
    },
  },
  rw A5,
end


lemma measure_theory.measure.sup_le_apply {Ω:Type*}
  {M:measurable_space Ω}
  {μ ν m:measure_theory.measure Ω}
  {S:set Ω}:measurable_set S →
  (μ ≤ m) →
  (ν ≤ m) → 
  (μ ⊔ ν) S ≤ m S :=
begin
  intros A1 A2 A3,
  have A4:μ ⊔ ν ≤ m := 
      @sup_le (measure_theory.measure Ω) _ μ ν m A2 A3,
  apply A4,
  apply A1,
end
