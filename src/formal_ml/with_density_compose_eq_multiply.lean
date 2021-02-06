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
import formal_ml.lattice
import formal_ml.rat

--import formal_ml.with_density_compose_eq_multiply_part_one
/-
  The simple way to think about a continuous random variable is as a
  continuous function (a density function). Formally, this is the Radon-Nikodym derivative.
  Using the operation with_density, one can transform this Radon-Nikodym derivative into
  a measure using measure_theory.with_density, which is provided in measure_theory.integration
  in mathlib. Specifically, one can write:
  μ.with_density f
  where μ is normally the Lebesgue measure on the real number line, and generate a probability
  measure for a continuous density function.

  In this file,
  measure_theory.with_density.compose_eq_multiply connects the integration (or expectation) of 
  a function with respect to the probability measure derived from the density function with the
  integral using the original base measure. So, if μ is again the base measure, f is the density
  function, and g is the function we want to take the expectation of, then:
  (μ.with_density f).integral g = μ.integral (f * g)

  This is the familiar connection that we use to integrate functions of real random variables on
  a regular basis.
 -/








------------------------Theorems of ennreal -------------------------------------------


--Unnecessary
lemma le_coe_ne_top {x:nnreal} {y:ennreal}:y≤(x:ennreal) → y≠ ⊤ :=
begin
  intro A1,
  have A2:(x:ennreal)< ⊤,
  {
    apply with_top.coe_lt_top,
  },
  have A3:y < ⊤,
  {
    apply lt_of_le_of_lt,
    apply A1,
    apply A2,
  },
  rw ← lt_top_iff_ne_top,
  apply A3,
end 

--Unnecessary
lemma upper_bounds_nnreal (s : set ennreal) {x:nnreal} {y:ennreal}: 
  (x:ennreal) ∈ upper_bounds s →  (y∈ s) →  y≠ ⊤:=
begin
  intros A1 A2,
  rw mem_upper_bounds at A1,
  have A3 := A1 y A2,
  apply le_coe_ne_top A3,
end


--Unnecessary
lemma upper_bounds_nnreal_fn {α:Type*} {f:α → ennreal} {x:nnreal}:
  (x:ennreal) ∈ upper_bounds (set.range f)  → (∃ g:α → nnreal,
  f = (λ a:α, (g a:ennreal))) :=
begin
  intro A1,
  let g:α → nnreal := λ a:α, ((f a).to_nnreal),
  begin
    have A2:g = λ a:α, ((f a).to_nnreal) := rfl,
    apply exists.intro g,
    rw A2,
    ext a,
    split;intro A3,
    {
      simp,
      simp at A3,
      rw A3,
      rw ennreal.to_nnreal_coe,
    },
    {
      simp,
      simp at A3,
      rw ← A3,
      symmetry,
      apply ennreal.coe_to_nnreal,
      apply upper_bounds_nnreal,
      apply A1,
      simp,
    },
  end
end




------ Measure theory --------------------------------------------------------------------------



--Used EVERYWHERE.
lemma measure.apply {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω)  (S:set Ω):
    μ S = μ.to_outer_measure.measure_of S :=
begin
  refl
end


--Use in hahn.lean
--TODO: Can this be replaced with measure_theory.lintegral_supr?
--Look more closely: this is using supr_apply, which means it is more 
--than just measure_theory.lintegral_supr.
lemma  measure_theory.lintegral_supr2 {α : Type*} 
    [N:measurable_space α]
    {μ:measure_theory.measure α}
     {f : ℕ → α → ennreal}:
    (∀ (n : ℕ), measurable (f n)) → 
    monotone f → 
    ((∫⁻ a:α,  (⨆ (n : ℕ), f n) a ∂ μ) = 
    ⨆ (n : ℕ), (∫⁻ a:α, (f n) a ∂ μ)) :=
begin
  intros A1 A2,
  have A3:(λ a, (⨆ (n : ℕ), f n a)) = (⨆ (n : ℕ), f n),
  {
    apply funext,
    intro a,
    rw supr_apply,
  },
  rw ← A3,
  apply measure_theory.lintegral_supr,
  apply A1,
  apply A2,
end


--Used in hahn.lean
lemma supr_indicator {Ω:Type*} (g:ℕ → Ω → ennreal) (S:set Ω):
     (set.indicator S (supr g)) =
     (⨆ (n : ℕ), (set.indicator S (g n))) :=
begin
  apply funext,
  intro ω,
  rw (@supr_apply Ω (λ ω:Ω, ennreal) ℕ _ (λ n:ℕ, set.indicator S (g n)) ),
  have A0:(λ (i : ℕ), (λ (n : ℕ), set.indicator S (g n)) i ω) =
      (λ (i : ℕ), set.indicator S (g i) ω),
  {
    apply funext,
    intro i,
    simp,
  },
  rw A0,
  have A1:ω ∈ S ∨ ω ∉ S ,
  {
    apply classical.em,
  },
  cases A1,
  {
    rw set.indicator_of_mem A1,
    have B1A:(λ (i : ℕ), set.indicator S (g i) ω) =
        (λ (i : ℕ), g i ω),
    {
      apply funext,
      intro i,
      rw set.indicator_of_mem A1,
    },
    rw B1A,
    rw supr_apply,
  },
  {
    rw set.indicator_of_not_mem A1,
    have B1A:(λ (i : ℕ), set.indicator S (g i) ω) = (λ (i:ℕ), 0),
    {
      apply funext,
      intro i,
      rw set.indicator_of_not_mem A1,
    },
    rw B1A,
    rw @supr_const ennreal ℕ _ _ 0,
  },
end

--Used all over.
--Prefer measure_theory.with_density_apply
lemma measure_theory.with_density_apply2' {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) (f:Ω → ennreal) (S:set Ω):(measurable_set S) →
    (μ.with_density f) S = (∫⁻ a:Ω, (set.indicator S f) a ∂ μ) :=
begin
  intro A1,
  rw measure_theory.with_density_apply f A1,
  rw measure_theory.lintegral_indicator,
  apply A1,
end

--Move to Radon-Nikodym (?)
lemma with_density.zero {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω):
    (μ.with_density 0) = 0 :=
begin
  apply measure_theory.measure.ext,
  intros S A1,
  rw measure_theory.with_density_apply2',
  {
    simp,
  },
  {
    apply A1,
  }
end
