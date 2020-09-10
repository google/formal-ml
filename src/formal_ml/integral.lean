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


noncomputable def measure_theory.measure.integral {α:Type*} [M:measurable_space α] (μ:measure_theory.measure α)
  (f:α → ennreal):ennreal :=
  @measure_theory.lintegral α M μ f

/-The integral is simply defined as the lower integral.
  Thus, it is simple to raise a bunch of theorems from there.
  This is just an example. -/
lemma integral_sum {α:Type*} {M:measurable_space α} {μ:measure_theory.measure α}
  (X Y:α  → ennreal):
  (measurable X) →
  (measurable Y) →
  measure_theory.measure.integral μ (X + Y) =
  measure_theory.measure.integral μ X +
  measure_theory.measure.integral μ Y
   :=
begin
  intros A1 A2,
  unfold measure_theory.measure.integral,
  apply measure_theory.lintegral_add,
  apply A1,
  apply A2,
end
