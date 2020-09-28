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
import formal_ml.set
import formal_ml.measurable_space
import formal_ml.topological_space

/-
  The big question is how to introduce a measurable function over the reals.
  The topology over the reals is induced by a metric space, using absolute difference as a
  measure of distance. This metric space induces a topological_space.
  The measurable space is the borel space on top of this topological space.

  A key result is borel_eq_generate_from_of_subbasis. which shows that if a basis generates a
  second countable topology, it generates the borel space as well. For example, consider an
  arbitrary open sets on the real line. For any point x in the open set, there exists a real number
  e such that the open interval (x-e,x+e) is in the set. Moreover, there is a rational number p in
  the interval (x-e,x) and another in (x,x+e), implying x is in (p,q). If we take union of all the
  intervals (p,q) for each x in U, then we get U. So, the set of all open intervals with rational
  endpoints is a countable basis, implying the reals are a second order topology. It is also
  immediately obvious that any open set can be formed with a countable union for the reals.

  However, let's look at an arbitrary second countable topology. The generalization of Lindelöf's
  lemma shows that for a second countable topology, there is a set of open sets such that any open
  set is the countable union. For Munkres, the definition of second countable topology is that
  there exists a countable basis. The definition of basis from Munkres is that for every point is
  contained in at least one basis set, and for any element x in the intersection of two basis sets A
  and B, there is a basis set C containing x that is a subset of B and C.
  set, and to generate the topology, one considers arbitrary union of elements in the bases. Thus,
  any union of a subset of a countable set must be representable as a countable union. So, there
  is a countable union.

  The more interesting part of borel_eq_generate_from_of_subbasis is that ANY set that generates
  a second countable topology is a basis for the borel space. I am not exactly sure how this
  works: regardless, the theorem gives great insights into second countable topologies
  (especially, reals, nnreals, ennreals, et cetera) and borel
  measures.

  To start with, this implies that the cartesian product of the borel spaces is the same as the
  borel space of the cartesian product of the topologies (i.e. it commutes). So, results about
  continuous functions on two real variables (e.g., add, multiply, power) translate to
  measurable functions on measurable spaces.
-/


/-
  We begin with basic guarantees about intervals and measurable functions.
 -/
set_option pp.implicit true

lemma nnreal_measurable_space_def:nnreal.measurable_space = borel nnreal := rfl
lemma real_measurable_space_def:real.measurable_space = borel real := rfl
lemma ennreal_measurable_space_def:ennreal.measurable_space = borel ennreal := rfl

lemma borel_eq_generate_Iic (α:Type*)
  [topological_space α] [topological_space.second_countable_topology α]
  [linear_order α] [order_topology α] :
  borel α = measurable_space.generate_from (set.range set.Iic) :=
begin
  rw borel_eq_generate_Ioi α,
  apply le_antisymm,
  {
    rw measurable_space.generate_from_le_iff,
    rw set.subset_def,
    intros V A1,
    simp,
    simp at A1,
    cases A1 with y A1,
    subst V,
    rw ← set.compl_Iic,
    apply measurable_space.generate_measurable.compl,
    apply measurable_space.generate_measurable.basic,
    simp,
  },
  {
    rw measurable_space.generate_from_le_iff,
    rw set.subset_def,
    intros V A1,
    simp,
    simp at A1,
    cases A1 with y A1,
    subst V,
    rw ← set.compl_Ioi,
    apply measurable_space.generate_measurable.compl,
    apply measurable_space.generate_measurable.basic,
    simp,
  },
end


lemma is_measurable_intro_Iio (α β: Type*) [M:measurable_space α] [_inst_1 : topological_space β]
  [_inst_2 : @topological_space.second_countable_topology β _inst_1] [_inst_3 : linear_order β]
  [_inst_4 : @order_topology β _inst_1 (@partial_order.to_preorder β (@linear_order.to_partial_order β _inst_3))]
  (f:α → β):(∀ b:β, is_measurable (set.preimage f {y|y < b})) → 
            (@measurable α β M  (borel β) f) :=
begin
  intros A1,
  rw borel_eq_generate_Iio β,
  apply generate_from_measurable,
  refl,
  intros,
  cases H with z A2,
  subst B,
  unfold set.Iio,
  apply A1,
end

lemma is_nnreal_measurable_intro_Iio {α:Type*}
  [M:measurable_space α] (f:α → nnreal):
  (∀ x:nnreal, is_measurable (set.preimage f {y|y < x})) →
  (measurable f) :=
begin
  rw nnreal_measurable_space_def,
  apply is_measurable_intro_Iio,
end

lemma is_ennreal_measurable_intro_Iio {α:Type*}
  [M:measurable_space α] (f:α → ennreal):
  (∀ x:ennreal, is_measurable (set.preimage f {y|y < x})) →
  (measurable f) :=
begin
  rw ennreal_measurable_space_def,
  apply is_measurable_intro_Iio,
end


lemma is_real_measurable_intro_Iio {α:Type*}
  [M:measurable_space α] (f:α → real):
  (∀ x:real, is_measurable (set.preimage f {y|y < x})) →
  (measurable f) :=
begin
  rw real_measurable_space_def,
  apply is_measurable_intro_Iio,
end



lemma is_is_measurable_intro_Iio (β: Type*) [_inst_1 : topological_space β]
  [_inst_2 : @topological_space.second_countable_topology β _inst_1] [_inst_3 : linear_order β]
  [_inst_4 : @order_topology β _inst_1 (@partial_order.to_preorder β (@linear_order.to_partial_order β _inst_3))]
  (b:β):@is_measurable β (borel β) {y|y < b} :=
begin
  rw (@borel_eq_generate_Iio β _ _ _ _),
  apply measurable_space.is_measurable_generate_from,
  simp,
  unfold set.Iio,
  apply exists.intro b,
  refl,
end

lemma is_nnreal_is_measurable_intro_Iio (x:nnreal):
  (is_measurable {y|y < x}) :=
begin
  rw nnreal_measurable_space_def,
  apply is_is_measurable_intro_Iio,
end

lemma is_ennreal_is_measurable_intro_Iio (x:ennreal):
  (is_measurable {y|y < x}) :=
begin
  rw ennreal_measurable_space_def,
  apply is_is_measurable_intro_Iio,
end

lemma is_real_is_measurable_intro_Iio (x:real):
  (is_measurable {y|y < x}) :=
begin
  rw real_measurable_space_def,
  apply is_is_measurable_intro_Iio,
end

lemma is_is_measurable_intro_Ioi (β: Type*) [_inst_1 : topological_space β]
  [_inst_2 : @topological_space.second_countable_topology β _inst_1] [_inst_3 : linear_order β]
  [_inst_4 : @order_topology β _inst_1 (@partial_order.to_preorder β (@linear_order.to_partial_order β _inst_3))]
  (b:β):@is_measurable β (borel β) {y|b < y} :=
begin
  rw (@borel_eq_generate_Ioi β _ _ _ _),
  apply measurable_space.is_measurable_generate_from,
  simp,
  unfold set.Ioi,
  apply exists.intro b,
  refl,
end

lemma is_nnreal_is_measurable_intro_Ioi (x:nnreal):
  (is_measurable {y|x < y}) :=
begin
  rw nnreal_measurable_space_def,
  apply is_is_measurable_intro_Ioi,
end

lemma is_ennreal_is_measurable_intro_Ioi (x:ennreal):
  (is_measurable {y|x < y}) :=
begin
  rw ennreal_measurable_space_def,
  apply is_is_measurable_intro_Ioi,
end



lemma is_real_is_measurable_intro_Ioi (x:real):
  (is_measurable {y|x < y}) :=
begin
  rw real_measurable_space_def,
  apply is_is_measurable_intro_Ioi,
end




lemma is_measurable_intro_Ioi (α β: Type*) [M:measurable_space α] [_inst_1 : topological_space β]
  [_inst_2 : @topological_space.second_countable_topology β _inst_1] [_inst_3 : linear_order β]
  [_inst_4 : @order_topology β _inst_1 (@partial_order.to_preorder β (@linear_order.to_partial_order β _inst_3))]
  (f:α → β):(∀ b:β, is_measurable (set.preimage f {y|b<  y})) → 
            (@measurable α β M  (borel β) f) :=
begin
  intros A1,
  rw borel_eq_generate_Ioi β,
  apply generate_from_measurable,
  refl,
  intros,
  cases H with z A2,
  subst B,
  unfold set.Ioi,
  apply A1,
end

lemma is_nnreal_measurable_intro_Ioi {α:Type*}
  [M:measurable_space α] (f:α → nnreal):
  (∀ x:nnreal, is_measurable (set.preimage f {y|x < y})) →
  (measurable f) :=
begin
  rw nnreal_measurable_space_def,
  apply is_measurable_intro_Ioi,
end

lemma is_ennreal_measurable_intro_Ioi {α:Type*}
  [M:measurable_space α] (f:α → ennreal):
  (∀ x:ennreal, is_measurable (set.preimage f {y|x < y})) →
  (measurable f) :=
begin
  rw ennreal_measurable_space_def,
  apply is_measurable_intro_Ioi,
end

lemma is_real_measurable_intro_Ioi {α:Type*}
  [M:measurable_space α] (f:α → real):
  (∀ x:real, is_measurable (set.preimage f {y|x < y})) →
  (measurable f) :=
begin
  rw real_measurable_space_def,
  apply is_measurable_intro_Ioi,
end


lemma Iic_Iio_compl (β: Type*) [L : linear_order β] (x:β):{y:β|y ≤ x}ᶜ={y:β|x < y}  :=
begin
  intros,
  ext,split;intros A1,
  {
    simp,
    simp at A1,
    exact A1,
  },
  {
    simp,
    simp at A1,
    exact A1,
  }
end


lemma Iio_Ici_compl (β: Type*) [L : linear_order β] (x:β):{y:β|x < y}={y:β|y ≤ x}ᶜ :=
begin
  intros,
  ext,split;intros A1,
  {
    simp,
    simp at A1,
    exact A1,
  },
  {
    simp,
    simp at A1,
    exact A1,
  }
end

lemma Ioi_Ici_compl (β: Type*) [L : linear_order β] (x:β):{y:β|x ≤ y}={y:β|y < x}ᶜ :=
begin
  intros,
  ext,split;intros A1,
  {
    simp,
    simp at A1,
    exact A1,
  },
  {
    simp,
    simp at A1,
    exact A1,
  }
end

lemma is_measurable_intro_Iic (α β: Type*) [M:measurable_space α] [_inst_1 : topological_space β]
  [_inst_2 : @topological_space.second_countable_topology β _inst_1] [_inst_3 : linear_order β]
  [_inst_4 : @order_topology β _inst_1 (@partial_order.to_preorder β (@linear_order.to_partial_order β _inst_3))]
  (f:α → β):(∀ b:β, is_measurable (set.preimage f {y|y ≤ b})) → 
            (@measurable α β M  (borel β) f) :=
begin
  intros A1,
  apply is_measurable_intro_Ioi,
  intros x,
  rw ← Iic_Iio_compl,
  apply is_measurable.compl,
  apply A1,
end

lemma is_nnreal_measurable_intro_Iic {α:Type*}
  [M:measurable_space α] (f:α → nnreal):
  (∀ x:nnreal, is_measurable (set.preimage f {y|y ≤ x})) →
  (measurable f) :=
begin
  rw nnreal_measurable_space_def,
  apply is_measurable_intro_Iic,
end

lemma is_measurable_elim_Iio (α β: Type*) [M:measurable_space α] [_inst_1 : topological_space β]
  [_inst_2 : @topological_space.second_countable_topology β _inst_1] [_inst_3 : linear_order β]
  [_inst_4 : @order_topology β _inst_1 (@partial_order.to_preorder β (@linear_order.to_partial_order β _inst_3))]
  (f:α → β) (b:β):(@measurable α β M  (borel β) f) →
(is_measurable (set.preimage f {y|y < b})) :=
begin
  intros A1,
  apply @measurable_elim α β M (borel β),
  apply A1,
  rw borel_eq_generate_Iio β,
  apply measurable_space.is_measurable_generate_from,
  simp,
  apply exists.intro b,
  unfold set.Iio,
end

lemma is_nnreal_measurable_elim_Iio {α:Type*}
  [M:measurable_space α] (f:α → nnreal) (x:nnreal):
  (measurable f) →
  is_measurable (set.preimage f {y|y < x}) :=
begin
  rw nnreal_measurable_space_def,
  apply is_measurable_elim_Iio,
end

lemma is_measurable_elim_Iic (α β: Type*) [M:measurable_space α] [_inst_1 : topological_space β]
  [_inst_2 : @topological_space.second_countable_topology β _inst_1] [_inst_3 : linear_order β]
  [_inst_4 : @order_topology β _inst_1 (@partial_order.to_preorder β (@linear_order.to_partial_order β _inst_3))]
  (f:α → β) (b:β):(@measurable α β M  (borel β) f) →
(is_measurable (set.preimage f {y|y ≤ b})) :=
begin
  intro A1,
  apply @measurable_elim α β M (borel β),
  apply A1,
  rw borel_eq_generate_Ioi β,
  have A2:{y|y ≤ b}={y|b<y}ᶜ,
  {
     ext,split; intro A2A,
     {
       simp,
       simp at A2A,
       exact A2A,
     },
     {
       simp,
       simp at A2A,
       exact A2A,
     }
  },
  rw A2,
  apply is_measurable.compl,
  apply measurable_space.is_measurable_generate_from,
  simp,
  apply exists.intro b,
  refl,
end

lemma is_nnreal_measurable_elim_Iic {α:Type*}
  [M:measurable_space α] (f:α → nnreal) (x:nnreal):
  (measurable f) →
  (is_measurable (set.preimage f {y|y ≤ x})) :=
begin
  rw nnreal_measurable_space_def,
  apply is_measurable_elim_Iic,
end

lemma is_real_measurable_elim_Iic {α:Type*}
  [M:measurable_space α] (f:α → real) (x:real):
  (measurable f) →
  (is_measurable (set.preimage f {y|y ≤ x})) :=
begin
  rw real_measurable_space_def,
  apply is_measurable_elim_Iic,
end

/-
  Many more elimination rules can be added here.
  -/



lemma borel_def {α:Type*} [topological_space α]:(borel α) =
  measurable_space.generate_from {s : set α | is_open s} := rfl

lemma continuous_measurable {α β:Type*} [topological_space α] [topological_space β] (f:α → β):
continuous f →
@measurable α β (borel α) (borel β) f :=
begin
  intros A1,
  rw borel_def,
  rw borel_def,
  apply generate_from_measurable,
  {
    refl,
  },
  {
    intros,
    apply measurable_space.is_measurable_generate_from,
    unfold continuous at A1,
    apply A1,
    apply H,
  }
end


lemma borel_def_prod_second_countable {α β:Type*} [Tα:topological_space α]
  [Tβ:topological_space β]
  [SCα:topological_space.second_countable_topology α]
  [SCβ:topological_space.second_countable_topology β]
  :(@prod.measurable_space α β (borel α) (borel β)) =
   (@borel (α × β) (@prod.topological_space α β Tα Tβ)) :=
begin
  /- Note that the second countable property is required here. For instance the topology with
     a basis [x,y) is not second countable, and its product has a set that is open, but not
     coverable with a countable number of sets (e.g., the line y = -x). So, this would not work.

     The general idea is that since each topology has a countable basis the product topology
     has a countable basis as well.
    -/
  have A1:∃b:set (set α), set.countable b ∧ Tα = topological_space.generate_from b,
  {
    apply SCα.is_open_generated_countable,
  },
  cases A1 with basisα A1,
  cases A1 with A2 A3,
  rw (@borel_eq_generate_from_of_subbasis α basisα _ _ A3),
  have A4:∃b:set (set β), set.countable b ∧ Tβ = topological_space.generate_from b,
  {
    apply SCβ.is_open_generated_countable,
  },
  cases A4 with basisβ  A4,
  cases A4 with A5 A6,
  rw (@borel_eq_generate_from_of_subbasis β basisβ _ _ A6),
  rw prod_measurable_space_def,
  rw @borel_eq_generate_from_of_subbasis,
  rw A3,
  rw A6,
  rw prod_topological_space_def,
end



lemma continuous_measurable_binary {α β γ:Type*} [topological_space α] [topological_space β]
    [topological_space γ]
    [topological_space.second_countable_topology α]
    [topological_space.second_countable_topology β]
    (f:α × β → γ):
  continuous f → (@measurable (α × β) γ (@prod.measurable_space α β (borel α) (borel β)) (borel γ) f) :=
begin
  rw borel_def_prod_second_countable,
  apply continuous_measurable,
end


-- Note: there used to be theorems like this in mathlib, but they disappeared
lemma is_measurable_of_is_open {α:Type*} [topological_space α]
    (S:set α):is_open S → measurable_space.is_measurable' (borel α) S :=
begin
  rw borel_def,
  apply measurable_space.is_measurable_generate_from,
end

lemma is_measurable_of_is_closed {α:Type*} [topological_space α]
    (S:set α):is_closed S → measurable_space.is_measurable' (borel α) S :=
begin
  intro A1,
  unfold is_closed at A1,
  have A2:S = ((Sᶜ)ᶜ),
  {
    rw set.compl_compl,
  },
  rw A2,
  apply measurable_space.is_measurable_compl,
  apply is_measurable_of_is_open,
  apply A1,
end

lemma is_open_is_measurable_binary {α β:Type*} [topological_space α] [topological_space β]
    [topological_space.second_countable_topology α]
    [topological_space.second_countable_topology β]
    (S:set (α × β)):is_open S → measurable_space.is_measurable' (@prod.measurable_space α β (borel α) (borel β)) S :=
begin
  rw borel_def_prod_second_countable,
  apply is_measurable_of_is_open,
end

lemma is_closed_is_measurable_binary {α β:Type*} [topological_space α] [topological_space β]
    [topological_space.second_countable_topology α]
    [topological_space.second_countable_topology β]
    (S:set (α × β)):is_closed S → measurable_space.is_measurable' (@prod.measurable_space α β (borel α) (borel β)) S :=
begin
  rw borel_def_prod_second_countable,
  apply is_measurable_of_is_closed,
end



lemma SC_composition {Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} [Tβ:topological_space β] [CT:topological_space.second_countable_topology β]
  (f:Ω → β) (g:Ω → β) (h:β  → β → β):
  (@measurable Ω β MΩ (borel β) f) →
  (@measurable Ω β MΩ (borel β) g) →
  continuous2 h →
  @measurable Ω β MΩ (borel β) (λ ω:Ω, h (f ω) (g ω)) :=
begin
  intros A1 A2 A3,
  have A4:@measurable Ω (β × β) MΩ (@prod.measurable_space β β (borel β) (borel β)) (λ ω:Ω, prod.mk (f ω) (g ω)),
  {
    apply measurable_fun_product_measurable;assumption,
  },
  have A5:@measurable (β × β) β (@prod.measurable_space β β (borel β) (borel β)) (borel β) (λ p: (β × β), h (p.fst) (p.snd)),
  {
    rw continuous2_def at A3,
    apply continuous_measurable_binary,
    apply A3,
  },
  have A6:(λ ω:Ω, h (f ω) (g ω))=(λ p: (β × β), h (p.fst) (p.snd)) ∘ (λ ω:Ω, prod.mk (f ω) (g ω)),
  {
    simp,
  },
  rw A6,
  apply @compose_measurable_fun_measurable Ω (β × β)  β  MΩ (@prod.measurable_space β β (borel β) (borel β)) (borel β)  (λ p: (β × β), h (p.fst) (p.snd)) (λ ω:Ω, prod.mk (f ω) (g ω)) A5 A4,
end

lemma nnreal_composition {Ω:Type*} [MΩ:measurable_space Ω]
  (f:Ω → nnreal) (g:Ω → nnreal) (h:nnreal → nnreal → nnreal):
  measurable f →
  measurable g →
  continuous2 h →
  measurable (λ ω:Ω, h (f ω) (g ω)) :=
begin
  apply SC_composition,
end


lemma SC_sum_measurable {Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:add_monoid β} {TA:has_continuous_add β}
  (X Y:Ω → β):
  (@measurable _ _ _ (borel β) X) → 
  (@measurable _ _ _ (borel β) Y) →
  (@measurable _ _ _ (borel β) (λ ω:Ω, (X ω + Y ω))) :=
begin
  intros A1 A2,
  apply @SC_composition Ω MΩ β T SC X Y,
  apply A1,
  apply A2,
  apply TA.continuous_add,
end

lemma SC_neg_measurable {Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:add_group β} {TA:topological_add_group β}
  (X:Ω → β):
  (@measurable _ _ _ (borel β) X) → 
  (@measurable _ _ _ (borel β) (λ ω:Ω, (-X ω))) :=
begin
  intros A1,
  have A2:(λ (ω:Ω), -X ω)=has_neg.neg ∘ X := rfl,
  rw A2,
  apply @compose_measurable_fun_measurable Ω β β MΩ (borel β) (borel β),
  {
    apply continuous_measurable,
    apply topological_add_group.continuous_neg,
  },
  {
    apply A1,
  },
end

--const_measurable {Ω:Type*} [measurable_space Ω] {β:Type*} [measurable_space β] (c:β)
/-
∀ {α : Type u_1} {β : Type u_2} [_inst_1 : measurable_space α] [_inst_2 : measurable_space β] {a : α},
    @measurable β α _inst_2 _inst_1 (λ (b : β), a)
-/

def SC_sum_measurable_is_add_submonoid
{Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:add_monoid β} {TA:has_continuous_add β}:
  is_add_submonoid (@measurable Ω β MΩ (borel β)) := {
    zero_mem := @measurable_const β Ω (borel β) MΩ (0:β),
    add_mem := @SC_sum_measurable Ω MΩ β T SC CSR TA,
  }


def SC_sum_measurable_is_add_subgroup
{Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:add_group β} {TA:topological_add_group β}:
  is_add_subgroup (@measurable Ω β MΩ (borel β)) := {
    zero_mem := @measurable_const β Ω (borel β) MΩ (0:β),
    add_mem := @SC_sum_measurable Ω MΩ β T SC (add_group.to_add_monoid β) 
               (topological_add_group.to_has_continuous_add),
    neg_mem := @SC_neg_measurable Ω MΩ β T SC CSR TA,
  }

lemma SC_mul_measurable {Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:monoid β} {TA:has_continuous_mul β}
  (X Y:Ω → β):
  (@measurable _ _ _ (borel β) X) → (@measurable _ _ _ (borel β) Y) →
  (@measurable _ _ _ (borel β) (λ ω:Ω, (X ω * Y ω))) :=
begin
  intros A1 A2,
  apply @SC_composition Ω MΩ β T SC X Y,
  apply A1,
  apply A2,
  apply TA.continuous_mul,
end

def SC_mul_measurable_is_submonoid
{Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:monoid β} {TA:has_continuous_mul β}:
  is_submonoid (@measurable Ω β MΩ (borel β)) := {
    one_mem := @measurable_const β Ω (borel β) MΩ (1:β),
    mul_mem := @SC_mul_measurable Ω MΩ β T SC CSR TA,
  }



lemma nnreal_sum_measurable {Ω:Type*} [MΩ:measurable_space Ω] (X Y:Ω → nnreal):
  (measurable X) → (measurable Y) →
  measurable (λ ω:Ω, (X ω + Y ω)) :=
begin
  apply SC_sum_measurable,
  apply nnreal.topological_space.second_countable_topology,
  apply nnreal.topological_semiring.to_has_continuous_add,
end


lemma finset_sum_measurable {Ω β:Type*} [measurable_space Ω] [decidable_eq β]
  {γ:Type*} {T:topological_space γ} {SC:topological_space.second_countable_topology γ}
   {CSR:add_comm_monoid γ} {TA:has_continuous_add γ}
   (S:finset β) (X:β → Ω → γ):
  (∀ b:β, @measurable Ω  γ _  (borel γ) (X b)) →
  @measurable Ω γ _ (borel γ) (λ ω:Ω, S.sum (λ b:β, ((X b) ω))) :=
begin
  apply finset.induction_on S,
  {
    intros A1,
    simp,
    apply const_measurable,
  },
  {
    intros b T A2 A3 A4,
    -- A3,
    -- A4 B,
    have A5:(λ (ω : Ω), finset.sum (insert b T) (λ (b : β), X b ω)) =
    (λ (ω : Ω), (X b ω) + finset.sum T (λ (b : β), X b ω)),
    {
      ext,
      rw finset.sum_insert,
      exact A2,
    },
    rw A5,
    apply SC_sum_measurable,
    {
      apply SC,
    },
    {
      apply TA,
    },
    {
      apply A4,
    },
    {
      apply A3,
      exact A4,
    }
  }
end

lemma finset_sum_measurable_classical {Ω β:Type*} [MΩ:measurable_space Ω]
  {γ:Type*} {T:topological_space γ} {SC:topological_space.second_countable_topology γ}
   {CSR:add_comm_monoid γ} {TA:has_continuous_add γ}
   (S:finset β) (X:β → Ω → γ):
  (∀ b:β, @measurable  Ω γ _ (borel γ) (X b)) →
  @measurable Ω γ _ (borel γ) (λ ω:Ω, S.sum (λ b:β, ((X b) ω))) :=
begin
  have D:decidable_eq β,
  {
    apply classical.decidable_eq β,
  },
  apply @finset_sum_measurable Ω β MΩ D γ T SC CSR TA S X,
end


lemma nnreal_finset_sum_measurable {Ω β:Type*} [measurable_space Ω] [decidable_eq β] (S:finset β) (X:β → Ω → nnreal):
  (∀ b:β, measurable (X b)) →
  measurable (λ ω:Ω, S.sum (λ b:β, ((X b) ω))) :=
begin
  apply finset_sum_measurable,
  apply_instance,
  apply_instance,
end


lemma fintype_sum_measurable {Ω β:Type*} [F:fintype β] (X:β → Ω → nnreal) [M:measurable_space Ω]:
  (∀ b:β, measurable (X b)) →
  measurable (λ ω:Ω, F.elems.sum (λ b:β, ((X b) ω))) :=
begin
  have A1:decidable_eq β,
  {
    apply classical.decidable_eq,
  },
  apply @nnreal_finset_sum_measurable Ω β M A1,
end

lemma nnreal_fintype_sum_measurable {Ω β:Type*} [F:fintype β] (X:β → Ω → nnreal) [M:measurable_space Ω]:
  (∀ b:β, measurable (X b)) →
  measurable (λ ω:Ω, F.elems.sum (λ b:β, ((X b) ω))) :=
begin
  have A1:decidable_eq β,
  {
    apply classical.decidable_eq,
  },
  apply @nnreal_finset_sum_measurable Ω β M A1,
end


lemma nnreal_div_mul (x y:nnreal):(x/y = x * y⁻¹) :=
begin
  refl,
end



----------------Measurable Sets For Inequalities ---------------------------------------------------
-- These are basic results about order topologies.

lemma is_closed_le_alt {α:Type*} [T:topological_space α] [P:linear_order α]
   [OT:order_topology α]:is_closed {p:α × α|p.fst ≤ p.snd} :=
begin
  have A1:order_closed_topology α,
  {
    apply @order_topology.to_order_closed_topology,
  },
  apply A1.is_closed_le',
end

lemma is_measurable_of_le {α:Type*} [T:topological_space α]
      [SC:topological_space.second_countable_topology α] [P:linear_order α]
      [OT:order_topology α]:measurable_space.is_measurable' 
      (@prod.measurable_space α α (borel α) (borel α))
      {p:α × α|p.fst ≤ p.snd} :=
begin
  apply is_closed_is_measurable_binary,
  apply is_closed_le_alt,
end

lemma is_measurable_of_eq {α:Type*} [T:topological_space α]
      [SC:topological_space.second_countable_topology α]
      [T2:t2_space α]:measurable_space.is_measurable'
      (@prod.measurable_space α α (borel α) (borel α))
      {p:α × α|p.fst = p.snd} :=
begin
  apply is_closed_is_measurable_binary,
  apply is_closed_diagonal,
end
