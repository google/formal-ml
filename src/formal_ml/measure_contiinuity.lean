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


def is_absolutely_continuous_wrt 
  {Ω:Type*} {M:measurable_space Ω} (μ ν:measure_theory.measure Ω):Prop :=
  ∀ A:set Ω, measurable_set A → (ν A = 0) → (μ A = 0)


lemma measure_zero_of_is_absolutely_continuous_wrt 
  {Ω:Type*} {M:measurable_space Ω} (μ ν:measure_theory.measure Ω) (A:set Ω):
  is_absolutely_continuous_wrt μ ν → 
  measurable_set A → (ν A = 0) → (μ A = 0) :=
begin
  intros A1 A2 A3,
  unfold is_absolutely_continuous_wrt at A1,
  apply A1 A A2 A3,
end


noncomputable def lebesgue_measure_on_borel := measure_theory.real.measure_space.volume


lemma lebesgue_measure_on_borel_def:
  lebesgue_measure_on_borel = measure_theory.real.measure_space.volume := rfl


lemma lebesgue_measure_on_borel_apply {S:set ℝ}:
  lebesgue_measure_on_borel S = measure_theory.lebesgue_outer S := rfl



def is_absolutely_continuous_wrt_lebesgue
  (μ:measure_theory.measure ℝ):Prop :=
  is_absolutely_continuous_wrt μ lebesgue_measure_on_borel

lemma prob_zero_of_is_absolute_continuous_wrt_lebesgue (μ:measure_theory.measure ℝ) (E:set ℝ):is_absolutely_continuous_wrt_lebesgue μ →
   measurable_set E →   
   measure_theory.lebesgue_outer E = 0 →
    μ E=0 :=
begin
  intros A1 A2 A3,
  apply measure_zero_of_is_absolutely_continuous_wrt μ lebesgue_measure_on_borel
  _ A1 A2,
  rw lebesgue_measure_on_borel_apply,
  apply A3,
end
