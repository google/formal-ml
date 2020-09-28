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
import formal_ml.measurable_space
import formal_ml.probability_space
import formal_ml.real_measurable_space
import formal_ml.nnreal
import formal_ml.semiring
import topology.instances.real
import formal_ml.integral
import formal_ml.classical

/-
  This file should be vetted for results in borel_space.lean.

  borel_space also has a wealth of results about ennreal, including
  a proof that multiplication is measurable. This completes the story
  of ennreal measurable functions being a commutative semiring.
-/

------------- A measurable linear order ------------------------------------------------------------
/-
  Similar to topological semirings, a measurable linear order adds measurability onto a linear
  order.
-/
class measurable_linear_order (α:Type*) [M:measurable_space α]
  extends linear_order α :=
  (is_measurable_le:is_measurable {p:α × α|p.fst ≤ p.snd})
  (is_measurable_eq:is_measurable {p:α × α|p.fst = p.snd})


instance measurable_linear_order_to_has_measurable_eq (α:Type*) [M:measurable_space α]
  [L:measurable_linear_order α]:has_measurable_equality M := {
  is_measurable_eq := L.is_measurable_eq,
}

def measurable_linear_order_t2_sc {α:Type*} [T:topological_space α]
      [SC:topological_space.second_countable_topology α] [P:linear_order α]
      [OT:order_topology α] [T2:t2_space α]:@measurable_linear_order α (borel α) :=
      {
        is_measurable_le:=is_measurable_of_le,
        is_measurable_eq:=is_measurable_of_eq,
      }


noncomputable instance measurable_linear_order_nnreal:measurable_linear_order nnreal :=
  measurable_linear_order_t2_sc

noncomputable instance measurable_linear_order_real:measurable_linear_order real :=
  measurable_linear_order_t2_sc

noncomputable instance measurable_linear_order_ennreal:measurable_linear_order ennreal :=
  measurable_linear_order_t2_sc


lemma lt_iff_le_not_eq {α:Type*} [linear_order α] (a b:α):a < b ↔ a ≤ b ∧ (a ≠ b) :=
begin
  apply iff.trans,
  apply linear_order.lt_iff_le_not_le,
  split; intro A1,
  {
    split,
    apply A1.left,
    intro A2,
    apply A1.right,
    rw A2,
  },
  {
    split,
    apply A1.left,
    intro A2,
    apply A1.right,
    apply linear_order.le_antisymm,
    apply A1.left,
    apply A2,
  }
end

lemma measurable_linear_order.is_measurable_lt (α:Type*) [M:measurable_space α]
  [c:measurable_linear_order α]:measurable_space.is_measurable' (@prod.measurable_space α α M M) {p:α × α|p.fst < p.snd} :=
begin
  have A1:{p:α × α|p.fst < p.snd} = {p:α × α|p.fst ≤  p.snd} \ {p:α × α|p.fst = p.snd},
  {
    ext,
    simp,
    apply lt_iff_le_not_eq,
  },
  rw A1,
  apply is_measurable.diff,
  {
    apply measurable_linear_order.is_measurable_le,
  },
  {
    apply measurable_linear_order.is_measurable_eq
  }
end

lemma measurable_linear_order.is_measurable_le' (α:Type*) [M:measurable_space α]
  [MLO:measurable_linear_order α]:is_measurable {p:α × α|p.snd ≤ p.fst} :=
begin
  have A1:{p:α × α|p.snd ≤ p.fst} = {p:α × α|p.fst < p.snd}ᶜ,
  {
    ext p,
    split;intros A1A;simp;simp at A1A;apply A1A,
  }, 
  rw A1,
  apply is_measurable.compl,
  apply measurable_linear_order.is_measurable_lt,
end

---------------------------------------------------------------------------------------------------



section is_sub_semiring
universes u v

--def semiring.to_add_monoid {α:Type u} (semiring α):add_monoid α :=


def SC_sum_measurable_add_monoid
{Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:add_monoid β} {TA:has_continuous_add β}:
   add_monoid (measurable_fun MΩ (borel β)) :=
   @subtype.add_monoid (Ω → β) _ (@measurable Ω β MΩ (borel β))
   (@SC_sum_measurable_is_add_submonoid Ω MΩ β T SC CSR TA)

def SC_sum_measurable_add_comm_monoid
{Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:add_comm_monoid β} {TA:has_continuous_add β}:
   add_comm_monoid (measurable_fun MΩ (borel β)) :=
   @subtype.add_comm_monoid (Ω → β) _ (@measurable Ω β MΩ (borel β))
   (@SC_sum_measurable_is_add_submonoid Ω MΩ β T SC (add_comm_monoid.to_add_monoid β) TA)

def SC_sum_measurable_is_add_submonoid_from_semiring
{Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:semiring β} {TA:topological_semiring β}:
   is_add_submonoid (@measurable Ω β MΩ (borel β)) :=
   (@SC_sum_measurable_is_add_submonoid Ω MΩ β T SC (add_comm_monoid.to_add_monoid β)
   (topological_semiring.to_has_continuous_add))

def SC_sum_measurable_is_add_subgroup_from_ring
{Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:ring β} {TA:topological_ring β}:
   is_add_subgroup (@measurable Ω β MΩ (borel β)) :=
   (@SC_sum_measurable_is_add_subgroup Ω MΩ β T SC (add_comm_group.to_add_group β)
   (topological_ring.to_topological_add_group β))


def SC_mul_measurable_is_submonoid_from_semiring
  {Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:semiring β} {TA:topological_semiring β}:
   is_submonoid (@measurable Ω β MΩ (borel β)) :=
   (@SC_mul_measurable_is_submonoid Ω MΩ β T SC (monoid_with_zero.to_monoid β)
   (topological_semiring.to_has_continuous_mul))


def SC_measurable_semiring_is_sub_semiring
{Ω:Type u} [MΩ:measurable_space Ω]
  {β:Type v} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:semiring β} {TA:topological_semiring β}:
  is_sub_semiring (@measurable Ω β MΩ (borel β)) := {
    ..(@SC_sum_measurable_is_add_submonoid_from_semiring Ω MΩ β T SC _ TA),
    ..(@SC_mul_measurable_is_submonoid_from_semiring Ω MΩ β T SC _ TA),
  }

def SC_measurable_ring_is_subring
{Ω:Type u} [MΩ:measurable_space Ω]
  {β:Type v} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:ring β} {TA:topological_ring β}:
  is_subring (@measurable Ω β MΩ (borel β)) := {
    ..(@SC_sum_measurable_is_add_subgroup_from_ring Ω MΩ β T SC _ TA),
    ..(@SC_mul_measurable_is_submonoid_from_semiring Ω MΩ β T SC _ (topological_ring.to_topological_semiring β)),
  }

def SC_measurable_semiring
{Ω:Type u} [MΩ:measurable_space Ω]
  {β:Type v} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:semiring β} {TA:topological_semiring β}:
   semiring (measurable_fun MΩ (borel β)):=
   @subtype.semiring (Ω → β) _ (@measurable Ω β MΩ (borel β))
   (@SC_measurable_semiring_is_sub_semiring Ω MΩ β T SC CSR TA)


def SC_measurable_comm_semiring
  {Ω:Type u} [MΩ:measurable_space Ω]
  {β:Type v} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:comm_semiring β} {TA:topological_semiring β}:
   comm_semiring (measurable_fun MΩ (borel β)):=
   @subtype.comm_semiring (Ω → β) _ (@measurable Ω β MΩ (borel β))
   (@SC_measurable_semiring_is_sub_semiring Ω MΩ β T SC (comm_semiring.to_semiring β) TA)

def SC_measurable_comm_ring
  {Ω:Type u} [MΩ:measurable_space Ω]
  {β:Type v} {T:topological_space β} {SC:topological_space.second_countable_topology β}
   {CSR:comm_ring β} {TA:topological_ring β}:
   comm_ring (measurable_fun MΩ (borel β)):=
   @subtype.comm_ring (Ω → β) _ (@measurable Ω β MΩ (borel β))
   (@SC_measurable_ring_is_subring Ω MΩ β T SC (comm_ring.to_ring β) TA)

end is_sub_semiring

noncomputable instance nnreal_measurable_fun_comm_semiring {Ω:Type*} [MΩ:measurable_space Ω]:
  comm_semiring (measurable_fun MΩ (borel nnreal)):=
  @SC_measurable_comm_semiring Ω MΩ nnreal nnreal.topological_space
    nnreal.topological_space.second_countable_topology nnreal.comm_semiring
    nnreal.topological_semiring

noncomputable def real.topological_space:topological_space ℝ := infer_instance


noncomputable instance real_measurable_fun_comm_ring {Ω:Type*} [MΩ:measurable_space Ω]:
  comm_ring (measurable_fun MΩ (borel real)):=
  @SC_measurable_comm_ring Ω MΩ real real.topological_space
    real.topological_space.second_countable_topology real.comm_ring
    real.topological_ring


lemma nnreal_measurable_fun_zero_val_def {Ω:Type*} [MΩ:measurable_space Ω]:
  (0:MΩ →ₘ (borel nnreal)).val = 0 := rfl

lemma real_measurable_fun_zero_val_def {Ω:Type*} [MΩ:measurable_space Ω]:
  (0:MΩ →ₘ (borel real)).val = 0 := rfl


lemma nnreal_measurable_fun_add_val_def {Ω:Type*} [MΩ:measurable_space Ω] {a b:MΩ →ₘ (borel nnreal)}:
  (a + b).val = (a.val + b.val) := rfl

lemma real_measurable_fun_add_val_def {Ω:Type*} [MΩ:measurable_space Ω] {a b:MΩ →ₘ (borel real)}:
  (a + b).val = (a.val + b.val) := rfl

lemma nnreal_measurable_fun_one_val_def {Ω:Type*} [MΩ:measurable_space Ω]:
  (1:MΩ →ₘ (borel nnreal)).val = 1 := rfl

lemma real_measurable_fun_one_val_def {Ω:Type*} [MΩ:measurable_space Ω]:
  (1:MΩ →ₘ (borel real)).val = 1 := rfl

lemma nnreal_measurable_fun_mul_val_def {Ω:Type*} [MΩ:measurable_space Ω] {a b:MΩ →ₘ (borel nnreal)}:
  (a * b).val = (a.val * b.val) := rfl

lemma real_measurable_fun_mul_val_def {Ω:Type*} [MΩ:measurable_space Ω] {a b:MΩ →ₘ (borel real)}:
  (a * b).val = (a.val * b.val) := rfl

noncomputable instance nnreal_random_variable_comm_semiring {Ω:Type*}
  {p:probability_space Ω}:
  comm_semiring (random_variable p (borel nnreal)):=
  nnreal_measurable_fun_comm_semiring

noncomputable instance real_random_variable_comm_ring {Ω:Type*}
  {p:probability_space Ω}:
  comm_ring (random_variable p (borel real)):=
  real_measurable_fun_comm_ring


lemma nnreal_random_variable_add_val_def {Ω:Type*}
  {P:probability_space Ω} {a b:P →ᵣ (borel nnreal)}:
  (a + b).val = (a.val + b.val) := rfl

lemma real_random_variable_add_val_def {Ω:Type*}
  {P:probability_space Ω} {a b:P →ᵣ (borel real)}:
  (a + b).val = (a.val + b.val) := rfl


lemma nnreal_random_variable_mul_val_def {Ω:Type*}
  {P:probability_space Ω} {a b:P →ᵣ (borel nnreal)}:
  (a * b).val = (a.val * b.val) := rfl

lemma real_random_variable_mul_val_def {Ω:Type*}
  {P:probability_space Ω} {a b:P →ᵣ (borel nnreal)}:
  (a * b).val = (a.val * b.val) := rfl


lemma real_random_variable_neg_val_def {Ω:Type*}
  {P:probability_space Ω} {a:P →ᵣ (borel real)}:
  (-a).val = -(a.val) := rfl


--ennreal is not a topological semiring, because multiplication is not continuous,
--but it is measurable. Therefore, we must prove it is a submonoid directly.
def ennreal_measurable_is_submonoid
  {Ω:Type*} [MΩ:measurable_space Ω]:
   is_submonoid (@measurable Ω ennreal MΩ (borel ennreal)) := {
  one_mem :=@measurable_const ennreal Ω (borel ennreal) MΩ 1,
  mul_mem := 
  begin
    intros x y A1 A2,
    apply measurable.ennreal_mul A1 A2,

  end
}

--Should be able to use SC_sum_measurable_is_add_submonoid,
--but results in definitional inequalities in ennreal_measurable_is_sub_semiring.
def ennreal_measurable_is_add_submonoid
  {Ω:Type*} [MΩ:measurable_space Ω]:
   is_add_submonoid (@measurable Ω ennreal MΩ (borel ennreal)) := {
  zero_mem :=@measurable_const ennreal Ω (borel ennreal) MΩ 0,
  add_mem := 
  begin
    intros x y A1 A2,
    apply measurable.ennreal_add A1 A2,
  end
}


def ennreal_measurable_is_sub_semiring
{Ω:Type*} [MΩ:measurable_space Ω]:
  is_sub_semiring (@measurable Ω ennreal MΩ (borel ennreal)) := {
    ..(@ennreal_measurable_is_add_submonoid Ω MΩ),
    ..(@ennreal_measurable_is_submonoid Ω MΩ),
}


noncomputable instance ennreal_measurable_fun_comm_semiring {Ω:Type*} [MΩ:measurable_space Ω]:
  comm_semiring (measurable_fun MΩ (borel ennreal)):= 
  @subtype.comm_semiring (Ω → ennreal) _ (@measurable Ω ennreal MΩ (borel ennreal))
  (@ennreal_measurable_is_sub_semiring Ω MΩ)


noncomputable instance ennreal_random_variable_comm_semiring {Ω:Type*}
  {p:probability_space Ω}:
  comm_semiring (random_variable p (borel ennreal)):=
  ennreal_measurable_fun_comm_semiring

lemma ennreal_measurable_fun_zero_val_def {Ω:Type*} [MΩ:measurable_space Ω]:
  (0:MΩ →ₘ (borel ennreal)).val = 0 := rfl

lemma ennreal_measurable_fun_add_val_def {Ω:Type*} [MΩ:measurable_space Ω] {a b:MΩ →ₘ (borel ennreal)}:
  (a + b).val = (a.val + b.val) := rfl


--A test to see if + works.
lemma nnreal_commutes {Ω:Type*}
  {P:probability_space Ω} (A B:P →ᵣ (borel nnreal)):A + B = B + A :=
begin
  rw add_comm,
end

def measurable_set_le {β : Type*} [Mβ:measurable_space β] [L:measurable_linear_order β]
   :measurable_set (Mβ ×ₘ Mβ) := {
     val:={p:β × β|p.fst ≤ p.snd},
     property:=L.is_measurable_le,
   }

lemma measurable_set_le_val_def {β : Type*} [Mβ:measurable_space β] [L:measurable_linear_order β]:(@measurable_set_le β Mβ L).val = {p:β × β|p.fst ≤ p.snd} := rfl





lemma measurable_linear_order.is_measurable_lt' (α:Type*) [M:measurable_space α]
  [c:measurable_linear_order α]:measurable_space.is_measurable' (M ×ₘ M) {p:α × α|p.fst < p.snd} :=
begin
  apply measurable_linear_order.is_measurable_lt,
end

def measurable_set_lt {β : Type*} [Mβ:measurable_space β] [L:measurable_linear_order β]
   :measurable_set (Mβ ×ₘ Mβ) := {
     val:={p:β × β|p.fst < p.snd},
     property:=@measurable_linear_order.is_measurable_lt _ _ L,
   }


lemma event_eq_val_def {Ω : Type*} {P:probability_space Ω}
   {β : Type*} [Mβ:measurable_space β] [L:measurable_linear_order β]
   (X Y:P →ᵣ Mβ):(X =ᵣ Y).val = {a : Ω | X.val a = Y.val a} :=
begin
  rw rv_eq_val_def,
end

def event_lt
   {Ω : Type*} {P:probability_space Ω}
   {β : Type*} [Mβ:measurable_space β] [L:measurable_linear_order β]
   (X Y:P →ᵣ Mβ):event P := rv_event (X ×ᵣ Y) (measurable_set_lt)


/-
  Now, Pr[X <ᵣ  Y] is just what it looks like: the probability that X is less than Y.
  -/
infixr ` <ᵣ `:80 := event_lt

def event_le
   {Ω : Type*} {P:probability_space Ω}
   {β : Type*} [Mβ:measurable_space β] [L:measurable_linear_order β]
   (X Y:P →ᵣ Mβ):event P := rv_event (X ×ᵣ Y) (measurable_set_le)

infixr ` ≤ᵣ `:80 := event_le


lemma event_le_def 
   {Ω : Type*} {P:probability_space Ω}
   {β : Type*} [Mβ:measurable_space β] [L:measurable_linear_order β]
   (X Y:P →ᵣ Mβ):(X ≤ᵣ Y) = rv_event (X ×ᵣ Y) (measurable_set_le) := rfl

lemma event_le_val_def
   {Ω : Type*} {P:probability_space Ω}
   {β : Type*} [Mβ:measurable_space β] [L:measurable_linear_order β]
   (X Y:P →ᵣ Mβ):(X ≤ᵣ Y).val = {ω : Ω | X.val ω ≤ Y.val ω} :=
begin
  rw event_le_def,
  rw rv_event_val_def,
  rw prod_random_variable_val_def,
  rw measurable_set_le_val_def,
  simp,
end

noncomputable instance coe_measurable_fun_of_nnreal
      {Ω : Type*} {P:measurable_space Ω}
:has_coe nnreal (measurable_fun P (borel nnreal)) := {
  coe := const_measurable_fun
}

noncomputable instance coe_measurable_fun_of_real
      {Ω : Type*} {P:measurable_space Ω}
:has_coe real (measurable_fun P (borel real)) := {
  coe := const_measurable_fun
}



noncomputable instance coe_random_variable_of_nnreal
      {Ω : Type*} {P:probability_space Ω}
:has_coe nnreal (P →ᵣ borel nnreal) := {
  coe := const_random_variable
}

noncomputable instance coe_random_variable_of_real
      {Ω : Type*} {P:probability_space Ω}
:has_coe real (P →ᵣ borel real) := {
  coe := const_random_variable
}

lemma coe_random_variable_of_real_def {Ω : Type*} {P:probability_space Ω} {x:ℝ}:
  (x:P →ᵣ (borel ℝ)) = const_random_variable x := rfl

lemma coe_random_variable_of_real_val_def {Ω : Type*} {P:probability_space Ω} {x:ℝ}:
  (x:P →ᵣ (borel ℝ)).val = λ (ω:Ω), x := rfl


noncomputable def to_nnreal_rv {Ω : Type*}
    {P:probability_space Ω} (x:nnreal):(P →ᵣ borel nnreal) := x


lemma to_nnreal_rv_val_def {Ω : Type*}
    {P:probability_space Ω} (x:nnreal):(@to_nnreal_rv Ω P x).val = λ ω:Ω, x := rfl

noncomputable instance coe_measurable_fun_of_ennreal
      {Ω : Type*} [MΩ:measurable_space Ω]
:has_coe ennreal (measurable_fun MΩ (borel ennreal)) := {
  coe := const_measurable_fun
}

noncomputable instance coe_random_variable_of_ennreal
      {Ω : Type*} {P:probability_space Ω}
:has_coe ennreal (P →ᵣ borel ennreal) := {
  coe := const_random_variable
}

noncomputable def to_ennreal_rv {Ω : Type*}
    {P:probability_space Ω} (x:ennreal):(P →ᵣ borel ennreal) := x

def to_ennreal_rv_val_def {Ω : Type*}
    {P:probability_space Ω} (x:ennreal):
    (@to_ennreal_rv Ω P x).val = λ ω:Ω, x :=
begin
  rw to_ennreal_rv,
  refl,
end


noncomputable def expected_value_ennreal {α:Type*} {p:probability_space α}
  (X:p →ᵣ borel ennreal):ennreal :=
  measure_theory.measure.integral p.volume X.val


lemma nnreal_to_ennreal_measurable:measurable (λ x:nnreal, (x:ennreal)) :=
begin
  apply is_ennreal_measurable_intro_Iio,
  intro x,
  cases x,
  {
    simp,
  },
  {
    simp,
    apply is_nnreal_is_measurable_intro_Iio,
  }
end


def measurable2 {α β γ:Type*} [measurable_space α] [measurable_space β]
    [measurable_space γ] (f:α → β → γ):Prop :=
    measurable (λ p:α × β, f (p.fst) (p.snd))

lemma measurable2_def {α β γ:Type*} [measurable_space α] [measurable_space β]
    [measurable_space γ] (f:α → β → γ):measurable2 f =
    measurable (λ p:α × β, f (p.fst) (p.snd)) := rfl


lemma measurable2_composition {Ω:Type*} [MΩ:measurable_space Ω]
  {β:Type*} [Mβ:measurable_space β] 
  (f:Ω → β) (g:Ω → β) (h:β  → β → β):
  (measurable f) →
  (measurable g) →
  (measurable2 h) →
  measurable (λ ω:Ω, h (f ω) (g ω)) :=
begin
  intros A1 A2 A3,
  have A4:measurable (λ ω:Ω, prod.mk (f ω) (g ω)),
  {
    apply measurable_fun_product_measurable;assumption,
  },
  rw measurable2_def at A3,
  have A6:(λ ω:Ω, h (f ω) (g ω))=(λ p: (β × β), h (p.fst) (p.snd)) ∘ (λ ω:Ω, prod.mk (f ω) (g ω)),
  {
    simp,
  },
  rw A6,
  apply compose_measurable_fun_measurable (λ p: (β × β), h (p.fst) (p.snd)) (λ ω:Ω, prod.mk (f ω) (g ω)) A3 A4,
end


lemma measurable2_max:measurable2 (@max ℝ _) :=
begin
  rw measurable2_def,
  apply measurable.if,
  apply @measurable_linear_order.is_measurable_le' ℝ,
  apply fst_measurable,
  apply snd_measurable,
end

lemma abs_eq_max (x:ℝ):abs x = max x (-x) := rfl

lemma abs_eq_max_fn :(@abs ℝ _) = (λ x, max x (-x)) := 
begin
  ext,
  rw abs_eq_max,
end


lemma measurable_abs:measurable (@abs ℝ _) :=
begin
  rw abs_eq_max_fn,
  apply measurable2_composition  (@id ℝ) (@has_neg.neg ℝ _) (@max ℝ _), 
  {
    apply measurable_id,
  },
  {
    apply continuous_measurable,
    apply @topological_ring.continuous_neg ℝ _ _,
  },
  {
    apply measurable2_max,
  },
end


lemma of_real_of_nonpos {a:ℝ}:a ≤ 0 → (nnreal.of_real a = 0) :=
begin
  intro A1,
  apply subtype.eq,
  simp,
  apply A1,
end


lemma nnreal_lt {a:ℝ} {b:nnreal}:(b ≠ 0) → (nnreal.of_real a < b ↔ a < b.val)  :=
begin
  intro A1,
  split;intro A2,
  {
    have A3:0 ≤ a ∨ a < 0 := decidable.le_or_lt 0 a,
    cases A3,
    {
      rw ← nnreal.coe_lt_coe at A2,
      rw nnreal.coe_of_real _ A3 at A2,
      apply A2,
    },
    {
      apply lt_of_lt_of_le,
      apply A3,
      apply b.2,
    },
  },
  {
    have A3:0 ≤ a ∨ a < 0 := decidable.le_or_lt 0 a,
    cases A3,
    {
      rw ← nnreal.coe_lt_coe,
      rw nnreal.coe_of_real _ A3,
      apply A2,
    },
    {
      rw of_real_of_nonpos (le_of_lt A3),
     --apply lt_of_lt_of_le,
      --apply A3,
      --apply b.2,
      apply lt_of_le_of_ne,
      {
        apply bot_le,
      },
      {
        symmetry,
        apply A1,
      },
    },
  },
end

lemma nnreal_lt_set {b:nnreal}:(b ≠ 0) → {a:ℝ|nnreal.of_real a < b} =  {a:ℝ|a < b.val}  :=
begin
  intro A1,
  ext,
  simp,
  apply nnreal_lt A1,
end

lemma nnreal_lt_zero_set:{a : ℝ | nnreal.of_real a < 0} = ∅ :=
begin
  ext,
  simp,
end


lemma measurable_nnreal_of_real:measurable nnreal.of_real :=
begin
  apply is_nnreal_measurable_intro_Iio,
  intro x,
  simp,
  have A1:(x=0) ∨ (x≠ 0) := eq_or_ne, 
  cases A1,
  {
    rw A1,
    rw nnreal_lt_zero_set,
    apply is_measurable.empty,
  },
  {
    rw nnreal_lt_set A1,
    apply is_real_is_measurable_intro_Iio,
  },
end

noncomputable def nnreal_of_real_fun:measurable_fun (borel real) (borel nnreal) := {
  val := nnreal.of_real,
  property := measurable_nnreal_of_real,
}

lemma nnreal_of_real_fun_val_def:nnreal_of_real_fun.val = nnreal.of_real := rfl

noncomputable def real_abs_fun:measurable_fun (borel real) (borel real) := {
  val := (@abs ℝ _),
  property := measurable_abs,
}

lemma real_abs_fun_val_def:real_abs_fun.val = (@abs ℝ _) := rfl


noncomputable def measurable_fun_nnreal_of_measurable_fun_real {α:Type*} {Mα:measurable_space α} 
     (X:measurable_fun Mα (borel real)):measurable_fun Mα (borel nnreal) :=
  compose_measurable_fun nnreal_of_real_fun X

lemma measurable_fun_nnreal_of_measurable_fun_real_val_def {α:Type*} {Mα:measurable_space α} 
    (X:measurable_fun Mα (borel real)):
    (measurable_fun_nnreal_of_measurable_fun_real X).val = 
    (nnreal.of_real ∘ X.val) :=
begin
  unfold measurable_fun_nnreal_of_measurable_fun_real,
  rw compose_measurable_fun_val_def,
  rw nnreal_of_real_fun_val_def
end



def nnreal_to_ennreal_measurable_fun:measurable_fun (borel nnreal) (borel ennreal) := {
  val := (λ x:nnreal, (x:ennreal)),
  property := nnreal_to_ennreal_measurable,
}


noncomputable def nnreal_to_ennreal_random_variable {Ω:Type*}
  {p:probability_space Ω} (X:p →ᵣ borel nnreal):p →ᵣ borel ennreal :=
  nnreal_to_ennreal_measurable_fun ∘r X


lemma nnreal_to_ennreal_random_variable_val_def {Ω:Type*}
  {p:probability_space Ω} (X:p →ᵣ borel nnreal):
  (nnreal_to_ennreal_random_variable X).val = (λ (ω:Ω), ((X.val ω):ennreal)) :=
begin
  unfold nnreal_to_ennreal_random_variable,
  rw rv_compose_val_def,
  unfold nnreal_to_ennreal_measurable_fun,
end

noncomputable def expected_value_nnreal {Ω:Type*} {p:probability_space Ω}
  (X:p →ᵣ borel nnreal):ennreal :=
  @expected_value_ennreal Ω p (nnreal_to_ennreal_random_variable X)


class has_expectation (Ω α: Type*) (P:probability_space Ω) (M:measurable_space α) := (expectation : (P →ᵣ M) → ennreal)


notation `E[` X `]`:= has_expectation.expectation X

noncomputable instance has_expectation_nnreal {Ω:Type*} {P:probability_space Ω}:has_expectation Ω nnreal P (borel nnreal) := {
  expectation := @expected_value_nnreal Ω P
}


noncomputable instance has_expectation_ennreal {Ω:Type*} {P:probability_space Ω}:has_expectation Ω ennreal P (borel ennreal) := {
  expectation := @expected_value_ennreal Ω P
}


/-
  I haven't wrapped my head around measure_space yet.
  -/
def to_measure_space {Ω:Type*} (p:probability_space Ω):
    measure_theory.measure_space Ω := probability_space.to_measure_space


lemma expected_value_ennreal_def {Ω:Type*} {P:probability_space Ω}
  (X:P →ᵣ borel ennreal):E[X] = measure_theory.measure.integral (P.volume) (X.val) := rfl


lemma expected_value_ennreal_def2 {Ω:Type*} {P:probability_space Ω}
  (X:P →ᵣ borel ennreal):E[X] = measure_theory.lintegral P.volume(X.val) := rfl


lemma expected_value_nnreal_def {Ω:Type*} {P:probability_space Ω}
  (X:P →ᵣ borel nnreal):E[X] =   @expected_value_ennreal Ω P (nnreal_to_ennreal_random_variable X) := rfl

lemma expected_value_nnreal_def2 {Ω:Type*} {P:probability_space Ω}
  (X:P →ᵣ borel nnreal):E[X] =  measure_theory.lintegral P.volume 
    (λ (ω:Ω), ((X.val ω):ennreal)) := rfl

lemma expected_value_nnreal_def3 {Ω:Type*} {P:probability_space Ω}
  (X:P →ᵣ borel nnreal):E[X] = E[(nnreal_to_ennreal_random_variable X)] := rfl

lemma expected_value_nnreal_def4 {Ω:Type*} {P:probability_space Ω}
  (X:P →ᵣ borel nnreal):E[X] =   @expected_value_nnreal Ω P X := rfl




lemma expectation_add_ennreal {Ω:Type*} {p:probability_space Ω}
  (X Y:p →ᵣ borel ennreal):E[X + Y] = E[X] + E[Y] :=
begin
  repeat {rw expected_value_ennreal_def2},
  rw ennreal_measurable_fun_add_val_def,
  have A1:@measure_theory.lintegral Ω _ p.volume (X.val + Y.val)=
          (@measure_theory.lintegral Ω _ p.volume (λ a, X.val a + Y.val a)),
  {
    refl,
  },
  rw A1,
  rw @measure_theory.lintegral_add Ω (probability_space.to_measurable_space Ω) p.volume X.val Y.val,
  apply X.property,
  apply Y.property,
end


lemma decidable_subst (P Q:Prop):(P↔ Q) → decidable P → decidable Q :=
begin
  intros A1 A2,
  rw ← A1,
  apply A2,
end

lemma decidable_subst2 (P Q:Prop):(Q↔ P) → decidable P → decidable Q :=
begin
  intros A1 A2,
  rw A1,
  apply A2,
end


noncomputable def max_rv
  {α β:Type*}
  {P:probability_space α} {Mβ:measurable_space β}
  [L:measurable_linear_order β] [D:decidable_linear_order β]
  (X Y:random_variable P Mβ):random_variable P Mβ :=
    if_random_variable (X ≤ᵣ Y) (classical.decidable_pred (X ≤ᵣ Y).val) Y X


noncomputable def min_rv
  {α β:Type*}
  {P:probability_space α} {Mβ:measurable_space β}
  [L:measurable_linear_order β] [D:decidable_linear_order β]
  (X Y:random_variable P Mβ):random_variable P Mβ :=
    if_random_variable (X ≤ᵣ Y) (classical.decidable_pred (X ≤ᵣ Y).val) X Y




noncomputable def absolute_nnreal {Ω:Type*} {P:probability_space Ω} (X:random_variable P (borel ℝ)):random_variable P (borel nnreal) := 
  @measurable_fun_nnreal_of_measurable_fun_real Ω (probability_space.to_measurable_space Ω) (real_abs_fun ∘r X)

lemma absolute_nnreal_val_def {Ω:Type*} {P:probability_space Ω} (X:random_variable P (borel ℝ)):
    (absolute_nnreal X).val = nnreal.of_real ∘ (@abs ℝ _) ∘ X.val :=
begin
  unfold absolute_nnreal,
  rw measurable_fun_nnreal_of_measurable_fun_real_val_def,
  rw rv_compose_val_def,
  rw real_abs_fun_val_def,
end


noncomputable def pos_nnreal {Ω:Type*} {P:probability_space Ω} (X:random_variable P (borel ℝ)):random_variable P (borel nnreal) := 
  @measurable_fun_nnreal_of_measurable_fun_real Ω (probability_space.to_measurable_space Ω) X

lemma pos_nnreal_val_def {Ω:Type*} {P:probability_space Ω} (X:random_variable P (borel ℝ)):
    (pos_nnreal X).val = nnreal.of_real ∘ X.val :=
begin
  unfold pos_nnreal,
  rw measurable_fun_nnreal_of_measurable_fun_real_val_def,
end

noncomputable def neg_nnreal {Ω:Type*} {P:probability_space Ω} (X:random_variable P (borel ℝ)):random_variable P (borel nnreal) := 
  @measurable_fun_nnreal_of_measurable_fun_real Ω (probability_space.to_measurable_space Ω) (-X)

lemma neg_nnreal_val_def {Ω:Type*} {P:probability_space Ω} (X:random_variable P (borel ℝ)):
    (neg_nnreal X).val = nnreal.of_real ∘ (- X.val) :=
begin
  unfold neg_nnreal,
  rw measurable_fun_nnreal_of_measurable_fun_real_val_def,
  rw real_random_variable_neg_val_def,
end




noncomputable def absolute_expected_value_real {Ω:Type*} {P:probability_space Ω} (X:random_variable P (borel ℝ)):ennreal := 
    expected_value_nnreal  (absolute_nnreal X)



def expected_value_exists {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel real):Prop := (absolute_expected_value_real X) < ⊤ 



/- Calculate the expected value of a real random variable.
   If the absolute expected value is infinite, the result is undefined. -/
noncomputable def expected_value_real_raw {Ω:Type*} {P:probability_space Ω} (X:random_variable P (borel ℝ)):real := 
  ennreal.to_real (expected_value_nnreal (pos_nnreal X)) -
  (ennreal.to_real (expected_value_nnreal (neg_nnreal X)))


lemma absolute_nnreal_pos_nnreal_plus_neg_nnreal {Ω:Type*} {P:probability_space Ω} (X:random_variable P (borel ℝ)):
  (absolute_nnreal X) = (pos_nnreal X) + (neg_nnreal X) :=
begin
  apply subtype.eq,
  rw absolute_nnreal_val_def,
  rw nnreal_measurable_fun_add_val_def,
--  unfold absolute_nnreal pos_nnreal neg_nnreal,
  rw pos_nnreal_val_def,
  rw neg_nnreal_val_def,
  ext ω,
  simp,
  let x:ℝ := X.val ω,
  begin
    have A1:x = X.val ω:=rfl,
    rw ← random_variable_val_eq_coe,
    rw ← A1,
    have A2:x ≤ 0 ∨ (0 < x) := le_or_lt x 0,
    cases A2,
    {
      rw abs_of_nonpos,
      have A3:nnreal.of_real x = 0,
      {
        apply nnreal.of_real_of_nonpos A2,
      },
      rw A3,
      simp,
      apply A2,
    },
    {
      rw abs_of_pos A2,
      have A3:nnreal.of_real (-x) = 0,
      {
        apply nnreal.of_real_of_nonpos,
        apply le_of_lt,
        apply neg_lt_of_pos,
        apply A2,
      },
      {
        rw A3,
        simp,
      },
    },
  end
end

noncomputable def expected_value_real {Ω:Type*} {P:probability_space Ω} (X:random_variable P (borel ℝ)):real :=
    @ite (expected_value_exists X) (classical.prop_decidable (expected_value_exists X)) _ (expected_value_real_raw X) 0




/- Note that random variables do not necessarily have means or variances. In particular,
   the mean (or variance) may be infinite.
   TODO: make the calculation of the variance more explicit. Explicitly show that for any real
   or nnreal random variable, 0≤ (X ω - E[X]) * (X ω - E[x]) (on the extended real number line). -/
def has_mean {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel nnreal)
    (μ:nnreal):Prop := E[X] = μ


noncomputable def finite_mean {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel nnreal):nnreal 
  := ennreal.to_nnreal ( E[X] )

def has_variance {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel nnreal)
    {μ:nnreal} {H:has_mean X μ} {V:nnreal}:Prop := E[X * X] - μ * μ = V

lemma indicator_measurable {Ω:Type*} [measurable_space Ω]
  (E:set Ω) [D:decidable_pred E]: (is_measurable E) → measurable  (λ ω:Ω, if (ω ∈ E) then (1:nnreal) else (0:nnreal)) :=
begin
  intros A1,
  have A2:(λ ω:Ω, if (ω ∈ E) then (1:nnreal) else (0:nnreal)) = (λ ω:Ω, if (ω ∈ E) then ((λ x:Ω, (1:nnreal)) ω) else ((λ x:Ω, (0:nnreal)) ω)),
  {
    refl,
  },
  rw A2,
  apply measurable.if,
  {
    exact A1,
  },
  {
    apply const_measurable,
  },
  {
    apply const_measurable,
  }
end


def indicatorh {Ω : Type*} [MΩ:measurable_space Ω]
  (E:set Ω) [D:decidable_pred E] (H:is_measurable E):measurable_fun MΩ (borel nnreal) := {
    val := (λ ω:Ω, if (ω ∈ E) then (1:nnreal) else (0:nnreal)),
    property := @indicator_measurable Ω MΩ E D H,
  }

noncomputable def indicator {Ω : Type*} {MΩ:measurable_space Ω}
  (E:measurable_set MΩ):measurable_fun MΩ (borel nnreal) :=
  @indicatorh Ω MΩ E.val (classical.decidable_pred E.val) E.property


lemma indicator_val_def {Ω : Type*} {MΩ:measurable_space Ω}
  (E:measurable_set MΩ):(indicator E).val =
  (λ ω:Ω, @ite (ω ∈ E.val) (@classical.decidable_pred Ω E.val ω) nnreal (1:nnreal) (0:nnreal)) :=
begin
  refl,
end

noncomputable def indicator_rv {Ω : Type*} {P:probability_space Ω}
  (E:event P):random_variable P (borel nnreal) := indicator E


def finset_sum_measurable2 {Ω β:Type*} {MΩ:measurable_space Ω}
  {γ:Type*} {T:topological_space γ} {SC:topological_space.second_countable_topology γ}
   {CSR:add_comm_monoid γ} {TA:has_continuous_add γ}
   (S:finset β) (X:β → (measurable_fun MΩ (borel γ))):@measurable _ _ _ (borel γ) (λ ω:Ω, S.sum (λ b:β, ((X b).val ω))) :=
begin
  apply finset_sum_measurable_classical,
  {
    apply SC,
  },
  {
    apply TA,
  },
  {
    intro b,
    apply (X b).property,
  }
end

def finset_sum_measurable_fun {Ω β:Type*} {MΩ:measurable_space Ω}
  {γ:Type*} [T:topological_space γ] [SC:topological_space.second_countable_topology γ]
   [CSR:add_comm_monoid γ] [TA:has_continuous_add γ]
   (S:finset β) (X:β → (measurable_fun MΩ (borel γ))):measurable_fun MΩ (borel γ) := {
     val := (λ ω:Ω, S.sum (λ b:β, ((X b).val ω))),
     property := @finset_sum_measurable2 Ω β MΩ γ T SC CSR TA S X,
   }

lemma finset_sum_measurable_fun_val_def {Ω β:Type*} {MΩ:measurable_space Ω}
  {γ:Type*} [T:topological_space γ] [SC:topological_space.second_countable_topology γ]
   [CSR:add_comm_monoid γ] [TA:has_continuous_add γ]
   (S:finset β) (X:β → (measurable_fun MΩ (borel γ))):
  (finset_sum_measurable_fun S X).val = (λ ω:Ω, S.sum (λ b:β, ((X b).val ω))) :=
begin
  unfold finset_sum_measurable_fun,
end

noncomputable def count_finset {Ω β:Type*} {MΩ:measurable_space Ω}
  (S:finset β) (X:β → measurable_set MΩ):MΩ →ₘ borel nnreal :=
  finset_sum_measurable_fun S (λ b:β, indicator (X b))





lemma count_finset_val_def {Ω β:Type*} {MΩ:measurable_space Ω}
  (S:finset β) (X:β → measurable_set MΩ):(count_finset S X).val =
  λ ω:Ω, S.sum (λ (b : β), @ite (ω ∈ (X b).val) (@classical.decidable_pred Ω (X b).val ω) nnreal 1 0) :=
begin
  unfold count_finset,
  rw finset_sum_measurable_fun_val_def,
  ext ω,
  have A1:(λ (b : β), (indicator (X b)).val ω) =
    (λ b, @ite (ω ∈ (X b).val) (@classical.decidable_pred Ω (X b).val ω) nnreal 1 0),
  {
    ext,
    rw indicator_val_def,
  },
  rw A1,
end

noncomputable def count_finset_rv {Ω β:Type*} {P:probability_space Ω}
  (S:finset β) (X:β → event P):P →ᵣ borel nnreal :=
  count_finset S X

noncomputable def count {Ω β:Type*} {MΩ:measurable_space Ω}
  [F:fintype β] (X:β → measurable_set MΩ):MΩ →ₘ borel nnreal :=
  count_finset F.elems X

--Before going on, we need linearity of expectation.
--We have to either prove that the ennreal random variables are a commutative semiring, or
--just a commutative additive monoid.






---------- Lemmas that need a home -----------------------------------------------------------------
lemma supr_eq_max {α β:Type*} [complete_lattice α] {x:β} {f:β  → α}:
  (∀ y:β, f y ≤ f x)→  f x = supr f :=
begin
  intro A1,
  apply le_antisymm,
  {
    apply complete_lattice.le_Sup,
    simp,
  },
  {
    apply complete_lattice.Sup_le,
    intros b A2,
    simp at A2,
    cases A2 with y A3,
    rw ← A3,
    apply A1,
  }
end


lemma measure_theory_volume_def {Ω:Type*} {P:probability_space Ω} {S:set Ω}:@measure_theory.measure_space.volume Ω (to_measure_space P)  S =
  @measure_theory.measure_space.volume Ω (to_measure_space P) S := rfl

lemma measure_theory_volume_def2 {Ω:Type*}
  {P:probability_space Ω} {S:set Ω}:@measure_theory.measure_space.volume Ω (to_measure_space P)  S =
  P.volume.measure_of  S := rfl

lemma measure_theory_volume_def3 {Ω:Type*} {MΩ:measure_theory.measure_space Ω}
  {S:set Ω}:@measure_theory.measure_space.volume Ω MΩ S =
  @measure_theory.measure_space.volume Ω MΩ S := rfl

lemma measure_theory_volume_def4 {Ω:Type*} {MΩ:measure_theory.measure_space Ω}
  {S:set Ω}:@measure_theory.measure_space.volume Ω MΩ S =
  measure_theory.outer_measure.measure_of
  (@measure_theory.measure_space.volume Ω MΩ).to_outer_measure S := rfl


lemma univ_eq_empty_of_not_inhabited {Ω:Type*}:(¬(∃ x:Ω,true)) →
  (@set.univ Ω=∅) :=
begin
  intro A1,
  ext,split;intro A2,
  {
    exfalso,
    apply A1,
    apply exists.intro x,
    exact true.intro,
  },
  {
    exfalso,
    apply A2,
  }
end


lemma simple_func_const_cast_def {Ω:Type*} {MΩ:measurable_space Ω} (x:ennreal):
⇑(@measure_theory.simple_func.const Ω ennreal MΩ x)=λ ω:Ω, x := rfl

lemma simple_func_const_to_fun_def {Ω:Type*} {MΩ:measurable_space Ω} (x:ennreal):
(@measure_theory.simple_func.const Ω ennreal MΩ x).to_fun=λ ω:Ω, x := rfl

lemma simple_func_to_fun_eq_cast_def {Ω:Type*} {MΩ:measurable_space Ω}
(s:@measure_theory.simple_func Ω MΩ ennreal):s.to_fun = s := rfl



lemma outcome_space_inhabited {Ω:Type*}
  (P:probability_space Ω):(∃ x:Ω,true) :=
begin
  have A1:¬(∃ x:Ω,true) → false,
  {
    intro A1A,
    have A1B:(@set.univ Ω=∅),
    {
      apply univ_eq_empty_of_not_inhabited A1A,
    },
    have A1C:P.volume.measure_of (@set.univ Ω)=
            P.volume.measure_of (@has_emptyc.emptyc (set Ω) _),
    {
      rw A1B,
    },
    rw measure_theory.outer_measure.empty at A1C,
    rw probability_space.univ_one at A1C,
    simp at A1C,
    exact A1C,
  },
  apply classical.by_contradiction A1,
end

lemma outcome_space_nonempty {Ω:Type*}
  (P:probability_space Ω):nonempty Ω :=
begin
  have A1:(∃ x:Ω, true) := outcome_space_inhabited P,
  cases A1 with x A2,
  apply nonempty.intro x,
end

lemma integral_simple_func_const {Ω:Type*}
  {P:probability_space Ω}
  (x:ennreal):
 @measure_theory.simple_func.lintegral Ω
      (P.to_measurable_space)
      (@measure_theory.simple_func.const Ω ennreal (probability_space.to_measurable_space Ω) x) (P.to_measure_space.volume) = x :=
begin
  unfold measure_theory.simple_func.lintegral,
  have A1:(λ (x_1 : ennreal), x_1 *
  @measure_theory.measure_space.volume Ω (to_measure_space P) (⇑(measure_theory.simple_func.const Ω x) ⁻¹' {x_1}))
    = λ x_1:ennreal, if (x_1 = x) then x else 0,
  {
    ext x_1,
    rw measure_theory_volume_def2,
    rw simple_func_const_cast_def,

    have A1A:decidable (x_1 = x),
    {
      apply classical.decidable_eq ennreal x_1 x,
    },

    cases A1A,
    {
      rw if_neg A1A,
      have A1C:((λ (ω : Ω), x) ⁻¹' {x_1}) =∅,
      {
        ext ω,split;intros A1CA,
        {
          simp at A1CA,
          exfalso,
          apply A1A,
          rw A1CA,
        },
        {
          exfalso,
          apply A1CA,
        }
      },
      rw A1C,
      rw measure_theory.outer_measure.empty,
      simp,
    },
    {
      rw if_pos A1A,
      rw A1A,
      have A1C:((λ (ω : Ω), x) ⁻¹' {x}) =set.univ,
      {
        ext ω,split;intros A1CA;simp,
      },
      rw A1C,
      rw probability_space.univ_one,
      simp,
    },
  },
  rw A1,
  have A3:(@measure_theory.simple_func.range Ω ennreal
         (@measure_theory.measure_space.to_measurable_space Ω 
              (@to_measure_space Ω P))
         (@measure_theory.simple_func.const Ω ennreal
              (probability_space.to_measurable_space Ω) x)) = {x},
  {
    have A3X:nonempty Ω := outcome_space_nonempty P,
    apply @measure_theory.simple_func.range_const ennreal Ω
          (probability_space.to_measurable_space Ω) A3X x,
  },
  rw A3,
  simp,
end

lemma ge_refl {α : Type*} [preorder α] (a : α): a ≥ a :=
begin
  simp,
end

lemma simple_func_le_def {Ω:Type*} {MΩ:measurable_space Ω} {β:Type*}
  [preorder β] (a b:(@measure_theory.simple_func Ω MΩ β)):
  (a ≤ b) ↔ a.to_fun ≤ b.to_fun :=
begin
  refl,
end

lemma integral_simple_func_to_fun {Ω:Type*} {MΩ:measure_theory.measure_space Ω}
  (s:@measure_theory.simple_func Ω MΩ.to_measurable_space ennreal):
  @measure_theory.lintegral Ω MΩ.to_measurable_space MΩ.volume
      (@measure_theory.simple_func.to_fun Ω MΩ.to_measurable_space ennreal s) =
      s.lintegral MΩ.volume :=
begin
  rw simple_func_to_fun_eq_cast_def,
  rw measure_theory.simple_func.lintegral_eq_lintegral,
end


lemma to_ennreal_rv_val_eq_simple_func {Ω:Type*} {P:probability_space Ω}
  {x:ennreal}:(@to_ennreal_rv Ω P x).val =
  (@measure_theory.simple_func.const Ω ennreal (probability_space.to_measurable_space Ω) x).to_fun :=
begin
  rw to_ennreal_rv_val_def,
  rw simple_func_const_to_fun_def,
end


lemma ennreal_expectation_const {Ω:Type*} {P:probability_space Ω}
  {x:ennreal}:
  E[(@to_ennreal_rv Ω P x)] = (x:ennreal) :=
begin
  rw expected_value_ennreal_def2,
  rw to_ennreal_rv_val_eq_simple_func,
  rw integral_simple_func_to_fun,
  rw integral_simple_func_const,
end


lemma ennreal_expectation_zero {Ω:Type*} {P:probability_space Ω}:
  E[(0:P→ᵣ (borel ennreal))] = (0:ennreal) :=
begin
  --apply ennreal_expectation_const,
  rw expected_value_ennreal_def,
  have A1:(0:P→ᵣ (borel ennreal)).val=λ ω:Ω, 0,
  {
    apply @ennreal_measurable_fun_zero_val_def Ω (probability_space.to_measurable_space Ω),
  },
  rw A1,
  unfold measure_theory.measure.integral,
  rw measure_theory.lintegral_const,
  rw zero_mul,
end

lemma nnreal_zero_eq_ennreal_zero {Ω:Type*} {P:probability_space Ω}:
  (@nnreal_to_ennreal_random_variable Ω P (0:P→ᵣ (borel nnreal))) =
  (0:P→ᵣ (borel ennreal)) :=
begin
  apply subtype.eq,
  rw nnreal_to_ennreal_random_variable_val_def,
  refl,
end

lemma expectation_zero {Ω:Type*} {P:probability_space Ω}:
  E[(0:P→ᵣ (borel nnreal))] = (0:ennreal) :=
begin
  rw expected_value_nnreal_def3,
  rw nnreal_zero_eq_ennreal_zero,
  apply ennreal_expectation_zero,
end

lemma to_nnreal_rv_eq_to_ennreal_rv {Ω:Type*} {P:probability_space Ω}
  {x:nnreal}:
  (@nnreal_to_ennreal_random_variable Ω P (to_nnreal_rv x)) =
  (to_ennreal_rv (x:ennreal)) :=
begin
  apply subtype.eq,
  rw nnreal_to_ennreal_random_variable_val_def,
  refl,
end



lemma nnreal_expectation_const {Ω:Type*} {P:probability_space Ω}
  (x:nnreal):
  E[(@to_nnreal_rv Ω P x)] = (x:ennreal) :=
begin
  rw expected_value_nnreal_def3,
  rw to_nnreal_rv_eq_to_ennreal_rv,
  rw ennreal_expectation_const,
end


/-
lemma ennreal_expectation_prod {Ω:Type*} {P:probability_space Ω}
  (X Y:P →ᵣ (borel ennreal)):E[X * Y] = E[X] * E[Y]
-/

lemma finset_sum_measurable_fun_zero {Ω β:Type*} {P:probability_space Ω}
  (X:β → P →ᵣ (borel nnreal)):
  (finset_sum_measurable_fun ∅ (λ (b : β), (X b))) = (0:P→ᵣ (borel nnreal)) :=
begin
  unfold finset_sum_measurable_fun,
  simp,
  refl,
end


lemma finset_sum_measurable_fun_insert {Ω β:Type*} [decidable_eq β]
  {P:probability_space Ω}
  {a:β} {S:finset β} (X:β → P →ᵣ (borel nnreal)):(a∉ S) →
  (finset_sum_measurable_fun (insert a S) (λ (b : β), (X b))) =
  (X a) + (finset_sum_measurable_fun S (λ (b : β), (X b))) :=
begin
  intros A1,
  apply subtype.eq,
  rw finset_sum_measurable_fun_val_def,
  rw nnreal_measurable_fun_add_val_def,
  rw finset_sum_measurable_fun_val_def,
  ext ω,
  rw finset.sum_insert,
  refl,
  exact A1,
end


lemma lift_add_nnreal_random_variable {Ω:Type*} {p:probability_space Ω}
  (X Y:p →ᵣ borel nnreal):
  nnreal_to_ennreal_random_variable (X + Y) = (nnreal_to_ennreal_random_variable X) +
  (nnreal_to_ennreal_random_variable Y) :=
begin
  apply subtype.eq,
  rw ennreal_measurable_fun_add_val_def,
  rw nnreal_to_ennreal_random_variable_val_def,
  rw nnreal_to_ennreal_random_variable_val_def,
  rw nnreal_to_ennreal_random_variable_val_def,
  rw nnreal_measurable_fun_add_val_def,
  have A1:(λ (ω : Ω), (((X.val + Y.val) ω):ennreal))=(λ (ω : Ω), ((X.val ω):ennreal) + ((Y.val ω):ennreal)),
  {
    ext ω,
    simp,
  },
  rw A1,
  refl,
end

lemma expectation_add_nnreal {Ω:Type*} {p:probability_space Ω}
  (X Y:p →ᵣ borel nnreal):E[X + Y] = E[X] + E[Y] :=
begin
  rw expected_value_nnreal_def,
  rw lift_add_nnreal_random_variable,
  apply expectation_add_ennreal,
end

lemma finset_sum_measurable_fun_linear {Ω β:Type*} {P:probability_space Ω}
  (S:finset β) [D:decidable_eq β] (X:β → P →ᵣ (borel nnreal)):
  E[(finset_sum_measurable_fun S (λ (b : β), (X b)))] =
  finset.sum S (λ (k : β), E[X k]) :=
begin
  apply finset.induction_on S,
  {
    rw finset_sum_measurable_fun_zero,
    simp,
    rw expectation_zero,
  },
  {
    intros a s A1 A2,
    rw finset_sum_measurable_fun_insert,
    rw finset.sum_insert,
    rw expectation_add_nnreal,
    rw A2,
    exact A1,
    exact A1,
  }
end


noncomputable def ennreal.has_zero:has_zero ennreal := infer_instance

lemma indicator_eq_simple_func {Ω:Type*} {P:probability_space Ω}
  {S:event P}:
  (@nnreal_to_ennreal_random_variable Ω P (@indicator Ω (probability_space.to_measurable_space Ω) S)).val =
  (@measure_theory.simple_func.restrict Ω ennreal (probability_space.to_measurable_space Ω) ennreal.has_zero
  (@measure_theory.simple_func.const Ω ennreal (probability_space.to_measurable_space Ω) 1) S.val) :=
begin
  ext ω,
  rw nnreal_to_ennreal_random_variable_val_def,
  rw indicator_val_def,
  rw measure_theory.simple_func.restrict_apply,
  rw measure_theory.simple_func.const_apply,
  simp,
  apply S.property,
end

lemma restrict_univ {Ω:Type*} {MΩ:measurable_space Ω}
  (s:@measure_theory.simple_func Ω MΩ ennreal):
(@measure_theory.simple_func.restrict Ω ennreal MΩ ennreal.has_zero
         s
         (@set.univ Ω))=s :=
begin
  ext ω,
  simp,
end

lemma simple_func_preimage_empty_of_notin_range {Ω:Type*} {MΩ:measurable_space Ω}
  {f:@measure_theory.simple_func Ω MΩ ennreal}
  {x:ennreal}:(x∉ f.range) → ⇑f ⁻¹' {x}=∅ :=
begin
  intro A1,
  unfold measure_theory.simple_func.range at A1,
  ext ω,split;intro A2,
  {
    exfalso,
    apply A1,
    rw ← simple_func_to_fun_eq_cast_def at A2,
    simp,
    apply exists.intro ω,
    simp at A2,
    exact A2,
  },
  {
    exfalso,
    apply A2,
  }
end



lemma simple_func_integral_superset {Ω:Type*} {MΩ:measure_theory.measure_space Ω}
  {f:@measure_theory.simple_func Ω MΩ.to_measurable_space ennreal}
  {S:finset ennreal}:f.range ⊆ S →
  f.lintegral MΩ.volume = S.sum (λ x, x * measure_theory.measure_space.volume (f ⁻¹' {x})) :=
begin
  intro A1,
  unfold measure_theory.simple_func.lintegral,
  apply finset.sum_subset A1,
  intros x A2 A3,
  have A4:⇑f ⁻¹' {x}=∅,
  {
    apply simple_func_preimage_empty_of_notin_range A3,
  },
  rw A4,
  rw measure_theory_volume_def4,
  rw measure_theory.outer_measure.empty,
  simp,
end

lemma restrict_range_subseteq {Ω:Type*} {MΩ:measurable_space Ω}
  (s:@measure_theory.simple_func Ω MΩ ennreal)
  (S:measurable_set MΩ):
  (@measure_theory.simple_func.range Ω ennreal
         MΩ
         (@measure_theory.simple_func.restrict Ω ennreal MΩ ennreal.has_zero
            s
            (@subtype.val (set Ω) (@measurable_space.is_measurable' Ω MΩ) (S)))) ⊆
            {0} ∪ (s.range) :=
begin
  simp,
  rw finset.subset_iff,
  intros x A1,
  simp,
  simp at A1,
  cases A1 with ω A2,
  rw ← measurable_set_val_eq_coe at A2,
  rw @measure_theory.simple_func.restrict_apply Ω ennreal MΩ ennreal.has_zero s S.val
     S.property at A2,
  cases classical.em (ω ∈ S.val) with A3 A3,
  {
    right,
    apply exists.intro ω,
    rw if_pos at A2,
    exact A2,
    exact A3,
  },
  {
    left,
    rw if_neg at A2,
    rw A2,
    exact A3,
  }
end



lemma integral_simple_func_restrict_const {Ω:Type*} 
  {P:probability_space Ω} {S:event P}
  (x:ennreal):
  (x≠ 0) →
 (@measure_theory.simple_func.lintegral Ω
      (probability_space.to_measurable_space Ω)
        (@measure_theory.simple_func.restrict Ω ennreal (probability_space.to_measurable_space Ω) ennreal.has_zero
  (@measure_theory.simple_func.const Ω ennreal (probability_space.to_measurable_space Ω) x) S.val) 
   P.volume)
       = x * (P.volume.measure_of (S.val)) :=
begin
  intro AX,
  have A1:(λ (x_1 : ennreal), x_1 *
  @measure_theory.measure_space.volume Ω (to_measure_space P)
  (⇑(@measure_theory.simple_func.restrict Ω ennreal (probability_space.to_measurable_space Ω) ennreal.has_zero
  (@measure_theory.simple_func.const Ω ennreal (probability_space.to_measurable_space Ω) x) S.val) ⁻¹' {x_1}))
    = λ x_1:ennreal, if (x_1 = x) then x * (P.volume.measure_of S.val) else 0,
  {
    ext x_1,
    rw measure_theory_volume_def2,
    have A1X:decidable (x_1 = 0),
    {
      apply classical.decidable_eq ennreal x_1 0,
    },
    cases A1X,
    {
      rw measure_theory.simple_func.restrict_preimage,
      have A1A:decidable (x_1 = x),
      {
        apply classical.decidable_eq ennreal x_1 x,
      },
      cases A1A,
      {
        rw if_neg A1A,

        have A1C:⇑(@measure_theory.simple_func.const Ω ennreal (probability_space.to_measurable_space Ω) x) ⁻¹' {x_1} =∅,
        {
          ext ω,split;intros A1CA,
          {
            simp at A1CA,
            exfalso,
            apply A1A,
            rw A1CA,
          },
          {
            exfalso,
            apply A1CA,
          }
        },
        rw A1C,
        simp,
      },
      {
        rw if_pos A1A,
        rw A1A,
        have A1C:⇑(@measure_theory.simple_func.const Ω ennreal (probability_space.to_measurable_space Ω) x) ⁻¹' {x} =set.univ,
        {
          ext ω,split;intros A1CA;simp,
        },
        rw A1C,
        simp,

      },
      apply S.property,
      simp,
      intro A1D,
      apply A1X,
      rw A1D,
    },
    {
      rw A1X,
      simp,
      have A1E:¬ (0 = x),
      {
        intro A1E1,
        apply AX,
        rw A1E1,
      },
      rw if_neg,
      simp,
      intro A1E1,
      apply AX,
      rw A1E1,
    },
  },
  have B1:(@measure_theory.simple_func.range Ω ennreal
         (@measure_theory.measure_space.to_measurable_space Ω (@to_measure_space Ω P))
         (@measure_theory.simple_func.restrict Ω ennreal (probability_space.to_measurable_space Ω) ennreal.has_zero
            (@measure_theory.simple_func.const Ω ennreal (probability_space.to_measurable_space Ω) x)
            (@subtype.val (set Ω) (@measurable_space.is_measurable' Ω (probability_space.to_measurable_space Ω)) (S)))) ⊆
            {0,x},
  {
    apply set.subset.trans,
    apply restrict_range_subseteq,
    have B1A:nonempty Ω := outcome_space_nonempty P,
    rw @measure_theory.simple_func.range_const ennreal Ω (probability_space.to_measurable_space Ω) B1A x,
    simp,
  },
  rw @simple_func_integral_superset Ω (@to_measure_space Ω P)
         (@measure_theory.simple_func.restrict Ω ennreal (probability_space.to_measurable_space Ω) ennreal.has_zero
            (@measure_theory.simple_func.const Ω ennreal (probability_space.to_measurable_space Ω) x)
            (@subtype.val (set Ω) (@measurable_space.is_measurable' Ω (probability_space.to_measurable_space Ω)) (S)))
          {0,x} B1,
  rw A1,
  simp,
end


lemma indicator_expectation_set {Ω:Type*} {P:probability_space Ω}
  {S:event P}:E[(indicator S)] = (@event_prob Ω P S) :=
begin
  rw expected_value_nnreal_def3,
  rw expected_value_ennreal_def2,
  rw @indicator_eq_simple_func Ω P S,
  rw measure_theory.simple_func.lintegral_eq_lintegral,
  rw integral_simple_func_restrict_const,
  {
    simp,
    rw event_prob_def,
    rw ← event_val_eq_coe,
    refl,
  },
  apply one_ne_zero,
end

lemma indicator_expectation_event {Ω:Type*} {P:probability_space Ω}
  {S:event P}:E[(indicator S)] = Pr[S] :=
begin
  rw indicator_expectation_set,
end







---------- Unproven lemmas, all focusing on trying to get the PAC bound. ---------------------------



lemma ennreal_generate_from:(borel ennreal) = measurable_space.generate_from
  {s | ∃a, s = {b | a < b} ∨ s = {b | b < a}} :=
begin
  apply borel_eq_generate_from_of_subbasis,
  refl,
end


lemma generate_measurable_iff_is_measurable {Ω:Type*} (B:set (set Ω))
  (U:set Ω):
  measurable_space.generate_measurable B
  U ↔ @is_measurable Ω (measurable_space.generate_from B) U :=
begin
  unfold is_measurable,
  unfold measurable_space.generate_from,
end


lemma ennreal_is_measurable_of_generate_measurable (U:set ennreal):
  measurable_space.generate_measurable {s:set ennreal | ∃a, s = {b | a < b} ∨ s = {b | b < a}}
  U ↔ is_measurable U :=
begin
  have A1:is_measurable U = 
     @is_measurable ennreal (borel ennreal) U := rfl,
  rw A1,
  rw ennreal_generate_from,
  rw generate_measurable_iff_is_measurable,
end

lemma Iio_empty:@set.Iio ennreal _ 0 = ∅ :=
begin
  unfold set.Iio,
  simp,
end

lemma Ioi_empty:@set.Ioi ennreal _ ⊤ = ∅ :=
begin
  unfold set.Ioi,
  simp,
end

lemma Iio_in_ennreal_subbasis {t:ennreal}:
  (set.Iio t) ∈ {s:set ennreal| ∃a, s = {b | a < b} ∨ s = {b | b < a}} :=
begin
  simp,
  apply exists.intro t,
  right,
  refl,
end

lemma Ioi_in_ennreal_subbasis {t:ennreal}:
  (set.Ioi t) ∈ {s:set ennreal| ∃a, s = {b | a < b} ∨ s = {b | b < a}} :=
begin
  simp,
  apply exists.intro t,
  left,
  refl,
end


lemma Iic_compl_Ioi {α : Type*} [linear_order α] {a:α}:
  (set.Iic a)=(set.Ioi a)ᶜ :=
begin
  unfold set.Iic,
  unfold set.Ioi,
  ext,split;intro A1;simp;simp at A1;apply A1,
end


lemma Ici_compl_Iio {α : Type*} [linear_order α] {a:α}:
  (set.Ici a)=(set.Iio a)ᶜ :=
begin
  unfold set.Ici,
  unfold set.Iio,
  ext,split;intro A1;simp;simp at A1;apply A1,
end


lemma ennreal_is_measurable_Iic {a:ennreal}:is_measurable (set.Iic a) :=
begin
  rw ← ennreal_is_measurable_of_generate_measurable,
  have A1:(set.Iic a)=(set.Ioi a)ᶜ := Iic_compl_Ioi,
  rw A1,
  apply measurable_space.generate_measurable.compl,
  apply measurable_space.generate_measurable.basic,
  apply Ioi_in_ennreal_subbasis,
end

lemma ennreal_is_measurable_Iio {a:ennreal}:is_measurable (set.Iio a) :=
begin
  rw ← ennreal_is_measurable_of_generate_measurable,
  apply measurable_space.generate_measurable.basic,
  apply Iio_in_ennreal_subbasis,
end

lemma ennreal_is_measurable_Ici {a:ennreal}:is_measurable (set.Ici a) :=
begin
  rw ← ennreal_is_measurable_of_generate_measurable,
  have A1:(set.Ici a)=(set.Iio a)ᶜ := Ici_compl_Iio,
  rw A1,
  apply measurable_space.generate_measurable.compl,
  apply measurable_space.generate_measurable.basic,
  apply Iio_in_ennreal_subbasis,
end

lemma ennreal_is_measurable_Ioi {a:ennreal}:is_measurable (set.Ioi a) :=
begin
  rw ← ennreal_is_measurable_of_generate_measurable,
  apply measurable_space.generate_measurable.basic,
  apply Ioi_in_ennreal_subbasis,
end

lemma ennreal_measurable_introh (f:ennreal → ennreal):
  (∀ (y:ennreal),is_measurable (f  ⁻¹' (set.Iio y))) →
  (∀ (y:ennreal),is_measurable (f  ⁻¹' (set.Ioi y))) →
  measurable f :=
begin
  intros A1 A2,
  apply generate_from_measurable,
  symmetry,
  apply ennreal_generate_from,
  intros B A3,
  cases A3 with s A4,
  cases A4,
  {
    rw A4,
    apply A2,
  },
  {
    rw A4,
    apply A1,
  },
end


lemma ennreal_measurable_intro (f:ennreal → ennreal):
  (∀ (y:ennreal),y≠ 0 → is_measurable (f  ⁻¹' (set.Iio y))) →
  (∀ (y:ennreal),y≠ ⊤ → is_measurable (f  ⁻¹' (set.Ioi y))) →
  measurable f :=
begin
  intros A1 A2,
  apply ennreal_measurable_introh,
  {
    intro y,
    have A3:(y = 0) ∨ (y ≠ 0) := classical.em (y=0),
    cases A3,
    {
      rw A3,
      rw Iio_empty,
      simp,
    },
    {
      apply A1,
      apply A3,
    }
  },
  {
    intro y,
    have A3:(y = ⊤) ∨ (y ≠ ⊤) := classical.em (y=⊤),
    cases A3,
    {
      rw A3,
      rw Ioi_empty,
      simp,
    },
    {
      apply A2,
      apply A3,
    }
  },
end


lemma classical.double_negation_elimination {P:Prop}:¬ ¬ P → P :=
begin
  intro A1,
  have A2:P ∨ ¬ P := classical.em P,
  cases A2,
  {
    exact A2,
  },
  {
    exfalso,
    apply A1,
    exact A2,
  }
end

lemma subset_of_not_exists_in_diff {α:Type*} {S T:set α}:(¬ (∃ a:α, a∈ T \ S))
  → (T⊆ S) :=
begin
  intro A1,
  rw set.subset_def,
  have A2:∀ a:α, ¬ (a∈ T \ S) := forall_not_of_not_exists A1,
  intros x A3,
  have A4:x∉ T \ S := A2 x,
  simp at A4,
  apply A4 A3,
end


lemma in_notin_or_notin_in_or_eq {α:Type*} {S T:set α}:
    (∃ a:α, a∈ S \ T) ∨ (∃ a:α, a∈ T \ S) ∨ S = T :=
begin
  have A1:(∃ a:α, a∈ S \ T) ∨ ¬ (∃ a:α, a∈ S \ T),
  {
    apply classical.em,
  },
  have A2:(∃ a:α, a∈ T \ S) ∨ ¬ (∃ a:α, a∈ T \ S),
  {
    apply classical.em,
  },
  cases A1,
  {
    left,
    apply A1,
  },
  {
    cases A2,
    {
      right,left,
      apply A2,
    },
    right,right,
    apply set.subset.antisymm,
    {
       apply subset_of_not_exists_in_diff A1,
    },
    {
       apply subset_of_not_exists_in_diff A2,
    }
  },
end

lemma in_notin_or_notin_in_of_ne {α:Type*} {S T:set α}:S≠ T →
    ((∃ a:α, a∈ S \ T) ∨ (∃ a:α, a∈ T \ S)) :=
begin
  intros A1,
  have A2:((∃ a:α, a∈ S \ T) ∨ 
           (∃ a:α, a∈ T \ S) ∨ S = T )
   := in_notin_or_notin_in_or_eq,
  cases A2,
  {
    left,
    apply A2,
  },
  cases A2,
  {
    right,
    apply A2,
  },
  {
    exfalso,
    apply A1,
    apply A2,
  }
end


--Classical.
lemma exists_notin_of_ne_set_univ {α:Type*} {S:set α}:S ≠ set.univ → (∃ x, x∉ S) :=
begin
  intro A1,
  have A2:((∃ a:α, a∈ S \ set.univ) ∨ (∃ a:α, a∈ set.univ \ S)) :=in_notin_or_notin_in_of_ne A1,
  cases A2;cases A2 with a A3;simp at A3,
  {
    exfalso,
    apply A3,
  },
  {
    apply exists.intro a,
    exact A3,
  }
end


lemma false_of_le_of_lt {α:Type*} [linear_order α] {x y:α}:(x < y) → (y ≤ x) → false :=
begin
  intros A1 A2,
  apply not_le_of_lt A1,
  apply A2,
end


lemma ennreal_monotone_inv (f:ennreal → ennreal) (x y:ennreal):
  monotone f →
  f x < f y →
  x  < y  :=
begin
  intros A1 A2,
  apply classical.by_contradiction,
  intro A3,
  have A4:f y ≤ f x,
  {
    apply A1,
    apply le_of_not_lt A3,
  },
  apply false_of_le_of_lt A2 A4,
end

lemma ennreal_monotone_bound_le_Sup (f:ennreal → ennreal) (x' y:ennreal):
  monotone f →
  {x:ennreal|f x < y} ≠ set.univ →
  x'∈ {x:ennreal|f x < y} →
  x' ≤ Sup {x:ennreal|f x < y} :=
begin
  intros AX A1 A2,
  have A4:(bdd_above {x:ennreal|f x < y}),
  {
    unfold bdd_above,
    unfold upper_bounds,
    have A4A:(∃ z, z∉ {x:ennreal|f x < y}),
    {
      apply exists_notin_of_ne_set_univ,
      apply A1,
    },
    cases A4A with z A4B,
    apply exists.intro z,
    simp,
    simp at A4B,
    intros a A4C,
    apply @le_of_lt ennreal _ a z,
    apply ennreal_monotone_inv,
    unfold monotone at AX,
    apply AX,
    apply lt_of_lt_of_le,
    apply A4C,
    apply A4B,
  },
  apply le_cSup A4,
  exact A2,
end

lemma ennreal_monotone_bound_Inf_le (f:ennreal → ennreal) (x' y:ennreal):
  monotone f →
  {x:ennreal|y < f x} ≠ set.univ →
  x'∈ {x:ennreal|y < f x} →
  Inf {x:ennreal|y < f x} ≤ x' :=
begin
  intros AX A1 A2,
  have A4:(bdd_below {x:ennreal|y < f x}),
  {
    unfold bdd_below,
    unfold lower_bounds,
    have A4A:(∃ z, z∉ {x:ennreal|y < f x}),
    {
      apply exists_notin_of_ne_set_univ,
      apply A1,
    },
    cases A4A with z A4B,
    apply exists.intro z,
    simp,
    simp at A4B,
    intros a A4C,
    apply @le_of_lt ennreal _ z a,
    apply ennreal_monotone_inv,
    unfold monotone at AX,
    apply AX,
    apply lt_of_le_of_lt,
    apply A4B,
    apply A4C,
  },
  apply @cInf_le ennreal _ {x:ennreal|y < f x},
  apply A4,
  exact A2,
end

/-
  Given an order topology (which is also ???), a monotone function f is
  borel measurable.
  First, find the image of f.
  Given [0,y), find all x such that f x < y. If this is all x or none of x, then
  we are done. Otherwise, since the ennreal are a
  conditionally complete lattice, there exists a supremum on such x, we'll call x'.
  If f x' < y, then [0,x'] is the measurable set. If f x' = y, then for any x < x',
  f x < y, otherwise x' would be the supremum. Thus, [0,x') would be the open set.
  A similar proof works for the preimage of (y,∞].
-/
lemma ennreal_monotone_measurable (f:ennreal → ennreal):
  monotone f → measurable f :=
begin
  intro A1,
  apply ennreal_measurable_intro;intros y A2,
  {
    let S := {x:ennreal|f x < y},
    begin
      have B1:S = {x:ennreal|f x < y} := rfl,
      have C1:f ⁻¹' (set.Iio y) = S := rfl,
      rw C1,
      have B2:decidable (S=set.univ),
      {
        apply classical.prop_decidable,
      },
      have B3:S.nonempty ∨ (S=∅),
      {
        rw or.comm,
        apply set.eq_empty_or_nonempty,
      },
      have B4:decidable (y ≤ f (Sup S)),
      {
        apply classical.prop_decidable,
      },
      cases B2,
      cases B3,
      { -- ¬S = set.univ, ¬S = ∅ ⊢ is_measurable (f ⁻¹' set.Iio y)
        cases B4,
        {
          have B4A:f (Sup S) < y,
          begin
            apply lt_of_not_ge,
            apply B4,
          end,
          have B4B:S = set.Iic (Sup S),
          {
            rw B1,
            ext z,simp;split;intros B4BA,
            {
              apply ennreal_monotone_bound_le_Sup,
              exact A1,
              apply B2,
              apply B4BA,
            },
            {
              rw ← B1 at B4BA,
              have B4BB:f z ≤ f (Sup S),
              {
                apply A1,
                apply B4BA,
              },
              apply lt_of_le_of_lt,
              apply B4BB,
              apply B4A,
            }
          },
          rw B4B,
          apply ennreal_is_measurable_Iic,
        },
        {
          have B4A:S = set.Iio (Sup S),
          {
            ext,split;intro B4AB,
            {
              simp,
              apply lt_of_le_of_ne,
              {
                 apply ennreal_monotone_bound_le_Sup,
                 exact A1,
                 apply B2,
                 apply B4AB,
              },
              {
                intro B4AD,
                rw ← B4AD at B4,
                simp at B4AB,
                apply false_of_le_of_lt B4AB B4,
              },

            },
            {
              simp,
              simp at B4AB,
              apply classical.by_contradiction,
              intro D1,
              have D2:y≤ f x,
              {
                apply le_of_not_lt D1,
              },
              have D3:Sup S ≤ x,
              {
                apply cSup_le B3,
                intros b D3A,
                simp at D3A,
                have D3B:b < x,
                {
                  apply ennreal_monotone_inv,
                  apply A1,
                  apply lt_of_lt_of_le,
                  apply D3A,
                  apply D2,
                },
                apply le_of_lt D3B,
              },
              apply false_of_le_of_lt B4AB D3,
            }
          },
          rw B4A,
          apply ennreal_is_measurable_Iio,
        }
      },
      { -- S = ∅ ⊢ is_measurable (f ⁻¹' set.Iio y)
        rw B3,
        apply is_measurable.empty,
      },
      { -- S = set.univ ⊢ is_measurable (f ⁻¹' set.Iio y)
        rw B2,
        apply is_measurable.univ,
      },
    end
  },
  {
    let S := {x:ennreal|y < f x},
    begin
      have B1:S = {x:ennreal|y < f x} := rfl,
      have C1:f ⁻¹' (set.Ioi y) = S := rfl,
      rw C1,
      have B2:decidable (S=set.univ),
      {
        apply classical.prop_decidable,
      },
      have B3:S.nonempty ∨  (S=∅),
      {
        rw or.comm,
        apply set.eq_empty_or_nonempty,
      },
      have B4:decidable (f (Inf S)≤ y),
      {
        apply classical.prop_decidable,
      },
      cases B2,
      cases B3,
      { -- ¬S = set.univ,¬S = ∅ ⊢ is_measurable (f ⁻¹' set.Iio y)
        cases B4,
        {
          have B4A:y < f (Inf S),
          begin
            apply lt_of_not_ge,
            apply B4,
          end,
          have B4B:S = set.Ici (Inf S),
          {
            rw B1,
            ext z,simp;split;intros B4BA,
            {
              apply ennreal_monotone_bound_Inf_le,
              exact A1,
              apply B2,
              apply B4BA,
            },
            {
              rw ← B1 at B4BA,
              have B4BB:f (Inf S) ≤ f z,
              {
                apply A1,
                apply B4BA,
              },
              apply lt_of_lt_of_le,
              apply B4A,
              apply B4BB,
            }
          },
          rw B4B,
          apply ennreal_is_measurable_Ici,
        },
        {
          have B4A:S = set.Ioi (Inf S),
          {
            ext,split;intro B4AB,
            {
              simp,
              apply lt_of_le_of_ne,
              {
                 apply ennreal_monotone_bound_Inf_le,
                 exact A1,
                 apply B2,
                 apply B4AB,
              },
              {
                intro B4AD,
                rw B4AD at B4,
                simp at B4AB,
                apply false_of_le_of_lt B4AB B4,
              },

            },
            {
              simp,
              simp at B4AB,
              apply classical.by_contradiction,
              intro D1,
              have D2:f x ≤ y,
              {
                apply le_of_not_lt D1,
              },
              have D3:x ≤ Inf S,
              {
                apply le_cInf B3,
                intros b D3A,
                simp at D3A,
                have D3B:x < b,
                {
                  apply ennreal_monotone_inv,
                  apply A1,
                  apply lt_of_le_of_lt,
                  apply D2,
                  apply D3A,
                },
                apply le_of_lt D3B,
              },
              apply false_of_le_of_lt B4AB D3,
            }
          },
          rw B4A,
          apply ennreal_is_measurable_Ioi,
        }
      },
      { -- S = ∅ ⊢ is_measurable (f ⁻¹' set.Iio y)
        rw B3,
        apply is_measurable.empty,
      },
      { -- S = set.univ ⊢ is_measurable (f ⁻¹' set.Iio y)
        rw B2,
        apply is_measurable.univ,
      },
    end
  }
end



lemma ennreal_scalar_mul_monotone (k:ennreal):monotone (λ x, k * x) :=
begin
  apply ennreal.mul_left_mono,
end

/-
  WAIT: alternative proof. Scalar multiplication is monotone.
  Given an order topology (which is also ???), a monotone function f is
  borel measurable.
  First, find the image of f.
  Given [0,y), find all x such that f x < y. If this is all x or none of x, then
  we are done. Otherwise, since the ennreal are a
  conditionally complete lattice, there exists a supremum on such x, we'll call x'.
  If f x' < y, then [0,x'] is the measurable set. If f x' = y, then for any x < x',
  f x < y, otherwise x' would be the supremum. Thus, [0,x') would be the open set.
  A similar proof works for the preimage of (y,∞].


  This is the simplest way to prove that scalar multiplication is measurable.
  Basically, we can consider the preimage of sets of the form
  (x,∞] and [0,x), and prove that they are measurable.
  The preimage of [0,0) and (∞,∞] is ∅.
  1. If k = 0, then the preimage of [0,x) is set.univ. The preimage of (x,∞] is ∅.
  2. If k = ∞, then the preimage of [0,x) is {0}. The preimage of (x,∞] is (0,∞].
  3. Otherwise, the preimage of [0,x) is [0,x/k). The preimage of (x,∞] is (x/k,∞].
-/
lemma ennreal_scalar_mul_measurable (k:ennreal):measurable (λ x, k * x) :=
begin
  apply ennreal_monotone_measurable,
  apply ennreal.mul_left_mono,
end

--TODO: this represents a semi-module.
noncomputable def ennreal_scalar_measurable_fun (k:ennreal):(borel ennreal) →ₘ (borel ennreal) := {
  val := λ x, k * x,
  property := ennreal_scalar_mul_measurable k,
}

noncomputable def scalar_mul_measurable_fun {Ω:Type*} {MΩ:measurable_space Ω} (k:ennreal)
    (X:MΩ →ₘ (borel ennreal)):(MΩ →ₘ (borel ennreal)) :=
    (ennreal_scalar_measurable_fun k) ∘m X

noncomputable def scalar_mul_rv {Ω:Type*} {P:probability_space Ω}
    (k:ennreal) (X:P →ᵣ (borel ennreal)):(P →ᵣ (borel ennreal)) :=
    (ennreal_scalar_measurable_fun k) ∘r X

def scalar_mul_rv_val_def {Ω:Type*} {P:probability_space Ω}
    (k:ennreal) (X:P →ᵣ (borel ennreal)):
    (scalar_mul_rv k X).val = λ ω:Ω, k * (X.val ω) := rfl



lemma nnreal_scalar_mul_to_ennreal {Ω:Type*} (p:probability_space Ω)
   (k:nnreal) (X:random_variable p (borel nnreal)):
  nnreal_to_ennreal_random_variable ((to_nnreal_rv (k)) * X) = scalar_mul_rv (k:ennreal)
  (nnreal_to_ennreal_random_variable X) :=
begin
  apply subtype.eq,
  rw scalar_mul_rv_val_def,
  rw nnreal_to_ennreal_random_variable_val_def,
  rw nnreal_to_ennreal_random_variable_val_def,
  rw nnreal_random_variable_mul_val_def,
  rw to_nnreal_rv_val_def,
  simp,
end

lemma ennreal_scalar_expected_value {Ω:Type*} (p:probability_space Ω)
   (k:ennreal) (X:random_variable p (borel ennreal)):
   E[scalar_mul_rv k X] = k * E[X] :=
begin
  rw expected_value_ennreal_def,
  unfold measure_theory.measure.integral,
  rw scalar_mul_rv_val_def,
  rw measure_theory.lintegral_const_mul,
  rw expected_value_ennreal_def,
  unfold measure_theory.measure.integral,
  apply X.property
end


-----Our TWO TARGET LEMMAS--------------------------------------------------------------------------

/-
  Okay, here is the plan for this one, because solving this one the "right" way will take
  forever.
  1. First of all, we define a scalar multiplier on ennreal measurable functions and ennreal
  random variables.
  2. Then, we show how the cast to ennreal results in such a random variable.
  3. Then, we show how such the scalar multiplier yields a scalar multiplier on the
     expectation using measure_theory.lintegral_const_mul
-/
lemma scalar_expected_value {Ω:Type*} (p:probability_space Ω)
  (X:random_variable p (borel nnreal)) (k:nnreal):E[X * (to_nnreal_rv (k))] = E[X] * (k:ennreal) :=
begin
  rw mul_comm,
  rw mul_comm _ (k:ennreal),
  rw expected_value_nnreal_def,
  rw nnreal_scalar_mul_to_ennreal,
  apply ennreal_scalar_expected_value,
end

lemma linear_count_finset_rv {Ω β:Type*} {P:probability_space Ω}
  (S:finset β) (X:β → event P):E[count_finset_rv S X] = S.sum (λ k, (Pr[X k]:ennreal)) :=
begin
  unfold count_finset_rv,
  unfold count_finset,
  have A1:decidable_eq β := classical.decidable_eq β,
  rw @finset_sum_measurable_fun_linear Ω β P S A1,
  have A2:(λ (k : β), E[indicator (X k)])=(λ (k : β), ↑Pr[X k]),
  {
    ext k,
    rw indicator_expectation_event,
  },
  rw A2,
end

lemma pos_nnreal_and_neg_nnreal_of_expected_value_exists {Ω:Type*} {p:probability_space Ω} 
    (X:p →ᵣ borel real):(expected_value_exists X) → 
    E[pos_nnreal X] < ⊤ ∧ E[neg_nnreal X] < ⊤:=
begin
  unfold expected_value_exists,
  unfold absolute_expected_value_real,
  rw absolute_nnreal_pos_nnreal_plus_neg_nnreal,
  rw ← expected_value_nnreal_def4,
  rw expectation_add_nnreal,
  intro A1,
  rw with_top.add_lt_top at A1,
  apply A1,
end


lemma pos_nnreal_of_expected_value_exists {Ω:Type*} {p:probability_space Ω} 
    (X:p →ᵣ borel real):(expected_value_exists X) → 
    E[pos_nnreal X] < ⊤ :=
begin
  intro A1,
  have A2:E[pos_nnreal X] < ⊤ ∧ E[neg_nnreal X] < ⊤,
  {
    apply pos_nnreal_and_neg_nnreal_of_expected_value_exists,
    apply A1,
  },
  apply A2.left,
end


lemma neg_nnreal_of_expected_value_exists {Ω:Type*} {p:probability_space Ω} 
    (X:p →ᵣ borel real):(expected_value_exists X) → 
    E[neg_nnreal X] < ⊤ :=
begin
  intro A1,
  have A2:E[pos_nnreal X] < ⊤ ∧ E[neg_nnreal X] < ⊤,
  {
    apply pos_nnreal_and_neg_nnreal_of_expected_value_exists,
    apply A1,
  },
  apply A2.right,
end


noncomputable def real_CDF {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel real) (x:ℝ):nnreal :=
    Pr[X ≤ᵣ x]


-------------------------------Find a home for these theorems.--------------------------------

lemma pr_empty_zero {Ω α:Type*} {p:probability_space Ω} [M:measurable_space α] {X:p →ᵣ M}
 {E:@measurable_set α M}:E.val = ∅ → (X ∈ᵣ E ) =  @event_empty Ω p :=
begin
  intro A1,
  apply event.eq,
  rw rv_event_val_def,
  ext ω,
  rw A1,
  split;intros A2,
  {
    simp at A2,
    exfalso,
    apply A2,
  },
  {
    exfalso,
    apply A2,
  }
end

--Unused, except below.
lemma pr_empty_zero2 {Ω α:Type*} {p:probability_space Ω} [M:measurable_space α]
 {E:event p}:E = @event_empty Ω p → Pr[E] = 0 :=
begin
  intro A1,
  rw A1,
  rw Pr_event_empty,
end

--Unused.
lemma pr_empty_zero3 {Ω α:Type*} {p:probability_space Ω} [M:measurable_space α] {X:p →ᵣ M}
 {E:@measurable_set α M}:E.val = ∅ → Pr[X ∈ᵣ E ] = 0 :=
begin
  intro A1,
  apply @pr_empty_zero2 Ω α p M,
  apply pr_empty_zero,
  apply A1,
end

lemma set.disjoint_preimage
   {Ω α:Type*} 
   {X:Ω → α}
   {A B:set α}
  :
  (A ∩ B ⊆ ∅ ) →
  ((set.preimage X (A)) ∩ (set.preimage X (B)) ⊆ ∅ ) 
   :=
begin
  intros A1,
  rw set.subset_def,
  intros ω A2,
  exfalso,
  simp at A2,
  rw set.subset_def at A1,
  have A3 := A1 (X ω),
  apply A3,
  simp,
  apply A2,
end

lemma set.pairwise_disjoint_preimage
   {Ω α β:Type*}
   [decidable_eq β]
   {X:Ω → α}
   {f:β → set α}
  :
  (∀ (i j : β), i ≠ j → f i ∩ f j ⊆ ∅ ) →
  (∀ (i j : β), i ≠ j → (set.preimage X (f i)) ∩ (set.preimage X (f j)) ⊆ ∅ ) 
   :=
begin
  intros A1 i j A2,
  apply set.disjoint_preimage (A1 i j A2),
end


lemma measure_Union2
   {Ω α:Type*} {p:probability_space Ω} 
   {M:measurable_space α}
   {X:Ω → α}
   {f:ℕ → set α}
  :
   (measurable X) →
  (∀ (i j : ℕ), i ≠ j → f i ∩ f j ⊆ ∅ ) →
   (∀ n, is_measurable (f n)) →
   p.volume.measure_of (X ⁻¹' ⋃ (i : ℕ), f i)
   =∑' n:ℕ, p.volume.measure_of (X ⁻¹' f n)
   :=
begin
  intros A1 A2 A3,
  rw set.preimage_Union,
  apply @measure_theory.measure_Union Ω _ measure_theory.measure_space.volume ℕ _ (λ n:ℕ, (set.preimage X (f n))),
  apply set.pairwise_disjoint_preimage A2,
  intro i,
  apply measurable.preimage A1 (A3 i),
end



lemma induction_on_inter2
   {α:Type*} {M:measurable_space α}
   {S:set (set α)}
   {P:measurable_set M → Prop}:
   (M = measurable_space.generate_from S) →
   (∀ t₁ t₂:(set α), t₁ ∈ S →  t₂ ∈ S →
       set.nonempty (t₁ ∩ t₂) →
       t₁ ∩ t₂ ∈ S) → 
   (P ∅) →
   (∀ E:measurable_set M, P E → P (Eᶜ)) →
   (∀ (f : ℕ → measurable_set M),
    (∀ (i j : ℕ), i ≠ j → (measurable_inter (f i) (f j)).val ⊆ ∅) → 
   (∀ (i : ℕ), P (f i)) → P (measurable_Union f)) →
   (∀ E:measurable_set M, E.val ∈ S →  P E ) →
   (∀ E:measurable_set M, P E) :=
begin
  intros A1 A2 B1 B2 B3 A3,
  let P2 := λ T:set α, ∃ H:is_measurable T, P ⟨T, H⟩,
  begin
    have A4:P2 = λ T:set α, ∃ H:is_measurable T, P ⟨T, H⟩ := rfl,
    have A5:(∀ T:set α, is_measurable T → P2 T),
    {
      apply measurable_space.induction_on_inter,
      apply A1,
      apply A2,
      {
        rw A4,
        apply exists.intro is_measurable.empty,
        apply B1,
      },
      {
        intros T A5A,
        rw A4,
        have A5B:is_measurable T,
        {
          rw A1,
          apply measurable_space.generate_measurable.basic,
          apply A5A,
        },
        apply exists.intro A5B,
        apply A3,
        simp,
        apply A5A,
      },
      {
        intros T A5C,
        rw A4,
        intro A5D,
        cases A5D with A5E A5F,
        have A5G:= (is_measurable.compl A5E),
        apply exists.intro A5G,
        have A5H:(measurable_set.mk A5G)=(measurable_set.mk A5E)ᶜ,
        {
          unfold measurable_set.mk,
          apply subtype.eq,
          rw measurable_set_neg_def,
        },
        unfold measurable_set.mk at A5H,
        rw A5H,
        apply B2,
        apply A5F,
      },
      {
        intros f A5J A5K A5L,
        have A5M:is_measurable (⋃ (i:ℕ), f i),
        {
          apply is_measurable.Union,
          intro b,
          apply A5K,
        },
        rw A4,
        apply exists.intro A5M,
        let g := λ (i:ℕ), @measurable_set.mk α M (f i) (A5K i),
        let V := measurable_Union g,
        begin
          have A5N:g = λ (i:ℕ), @measurable_set.mk α M (f i) (A5K i) := rfl,
          have A5O:V = measurable_Union g := rfl,
          have A5P:@measurable_set.mk α M (⋃ (i:ℕ), f i) A5M = V,
          {
            apply subtype.eq,
            rw A5O,
            unfold measurable_set.mk,
            simp,
            rw ← measurable_set_val_eq_coe,
            rw measurable_Union_val_def,
            ext ω,split;intro A5PA;simp at A5PA;cases A5PA with i A5PA;simp;
            apply exists.intro i;have A5PB:f i = (g i).val := rfl,
            {
              rw ← measurable_set_val_eq_coe,
              rw ← A5PB,
              apply A5PA,
            },
            {
              rw A5PB,
              apply A5PA,
            },
          },
          unfold measurable_set.mk at A5P,
          rw A5P,
          rw A5O,
          apply B3,
          {
            intros i j A5Q,
            rw measurable_inter_val_def,
            have A5R:(g i).val = f i := rfl,
            have A5S:(g j).val = f j := rfl,
            rw A5R,
            rw A5S,
            apply A5J,
            apply A5Q,
          },
          {
            intro i,
            have A5T:=A5L i,
            rw A4 at A5T,
            cases A5T with A5U A5V,
            have A5W:g i = ⟨f i, A5U⟩ := rfl,
            rw A5W,
            apply A5V,
          },
        end
      },
    },
    intro E,
    cases E,
    have A6 := A5 E_val E_property,
    rw A4 at A6,
    cases A6 with A7 A8,
    have A9:(⟨E_val, E_property⟩:measurable_set M) = (⟨E_val, A7⟩:measurable_set M),
    {
      apply subtype.eq,
      refl,
    },
    rw A9,
    apply A8,
  end
end


lemma nnreal.sum_subst {β:Type*} [encodable β] {f g:β → nnreal}:(f = g) →
    (∑' (b:β), f b) = (∑' (b:β), g b) :=
begin
  intro A1,
  rw A1,
end


lemma random_variable_identical_generate_from
   {Ω α:Type*} {p:probability_space Ω}
   {M:measurable_space α}
   {S:set (set α)}
   {X Y:p →ᵣ M}:
   (M = measurable_space.generate_from S) →
   (∀ (t₁ t₂ : set α), t₁ ∈ S → t₂ ∈ S → set.nonempty (t₁ ∩ t₂) → t₁ ∩ t₂ ∈ S) →
   (∀ E:measurable_set M,  E.val ∈ S →  
       Pr[X ∈ᵣ E] = Pr[Y ∈ᵣ E]) →
   (∀ E:measurable_set M, 
       Pr[X ∈ᵣ E] = Pr[Y ∈ᵣ E]) :=
begin
  intros A1 A2,
  apply induction_on_inter2,
  {
    apply A1,
  },
  {
    apply A2,
  },
  {
     repeat {rw rv_event_empty},
  },
  {
     intros E A1,
     repeat {rw rv_event_compl},
     repeat {rw neg_eq_not},
     repeat {rw ← Pr_one_minus_eq_not},
     rw A1, 
  },
  {
    intros f A3 A4,
    repeat {rw rv_event_measurable_Union},
    repeat {rw measurable_Union_eq_any},
    repeat {rw Pr_eany_sum},
    rw nnreal.sum_subst,
    --rw @sum_subst ℕ _ (λ b:ℕ, Pr[X ∈ᵣ f b]),
    --sorry
    {
      ext i,
      rw A4 i,
    },
    apply set.pairwise_disjoint_preimage,
    {
      intros i j A5,
      have A6 := A3 i j A5,
      rw measurable_inter_val_def at A6,
      apply A6,
    },  
    apply set.pairwise_disjoint_preimage,
    {
      intros i j A5,
      have A6 := A3 i j A5,
      rw measurable_inter_val_def at A6,
      apply A6,
    },
  },
end

lemma random_variable_identical_generate_from2
   {Ω α:Type*} {p:probability_space Ω} 
   {M:measurable_space α}
   {S:set (set α)}
   {X Y:p →ᵣ M}:
   (M = measurable_space.generate_from S) →
   (∀ (t₁ t₂ : set α), t₁ ∈ S → t₂ ∈ S → set.nonempty (t₁ ∩ t₂) → t₁ ∩ t₂ ∈ S) → 
   (∀ E:measurable_set M,  E.val ∈ S →  
       Pr[X ∈ᵣ E] = Pr[Y ∈ᵣ E]) →
   @random_variable_identical Ω p α M X Y :=
begin
  intros AX A1 A2,
  unfold random_variable_identical,
  apply @random_variable_identical_generate_from Ω α p M S X Y AX A1 A2,
end

lemma generate_measurable_finite_union {α:Type*} {s:set (set α)} {f:ℕ → set α} {n:ℕ}:
  (∀ n:ℕ, (measurable_space.generate_measurable s (f n))) →
  measurable_space.generate_measurable s (set.sUnion (set.image f {i:ℕ|i < n})) :=
begin
  let g:= λ i:ℕ, if (i < n) then (f i) else ∅,
  begin
    intro A1,
    have A2:g = λ i:ℕ, if (i < n) then (f i) else ∅ := rfl,
    have A3:(⋃ j:ℕ, g j) = (set.sUnion (set.image f {i:ℕ|i < n})),
    {
      ext ω,split;intro A4,
      {
        simp at A4,
        cases A4 with i A4,
        rw A2 at A4,
        simp at A4,
        have A4A:i < n,
        {
          apply decidable.by_contradiction,
          intro A4A1,
          rw if_neg at A4,
          apply A4,
          apply A4A1,
        },
        rw if_pos at A4,
        simp,
        apply exists.intro i,
        split,
        {
          apply A4A,
        },
        {
          apply A4,
        },
        apply A4A,
      },
      {
        simp at A4,
        cases A4 with i A4,
        simp,
        apply exists.intro i,
        rw A2,
        simp,
        rw if_pos,
        apply A4.right,
        apply A4.left,
      },
    },    
    rw ← A3,
    apply measurable_space.generate_measurable.union,
    intro i,
    rw A2,
    simp,

    have A5:(i < n) ∨ ¬(i < n) := decidable.em (i < n),
    cases A5,
    {
      rw if_pos A5,
      apply A1,
    },
    {
      rw if_neg A5,
      apply measurable_space.generate_measurable.empty,      
    },
  end
end


lemma set_range_Iic_closed {t₁ t₂ : set ℝ}:
    t₁ ∈ set.range (@set.Iic  ℝ _)→
    t₂ ∈ set.range (@set.Iic  ℝ _) → 
    set.nonempty (t₁ ∩ t₂) → t₁ ∩ t₂ ∈ set.range (@set.Iic ℝ _):=
begin
  intros A1 A2 A3,
  simp at A1,
  cases A1 with y1 A1,
  simp at A2,
  cases A2 with y2 A2,
  subst t₁,
  subst t₂,
  rw set.Iic_inter_Iic,
  simp,
end


lemma set_Iic_eq_CDF {Ω:Type*} {p:probability_space Ω} {X:p →ᵣ borel real} {y:ℝ} 
   {E:measurable_set (borel ℝ)}:E.val = set.Iic y →
   (Pr[X ∈ᵣ E] = (real_CDF X y)) :=
begin
  intro A1,
  unfold real_CDF,
  rw ← ennreal.coe_eq_coe,
  repeat {
    rw event_prob_def
  },
  rw event_le_val_def,
  rw coe_random_variable_of_real_val_def,
  rw rv_event_val_def,
  rw A1,
  unfold set.Iic,
  simp,
end



--set_option pp.implicit true
lemma real.is_measurable_Iic (x:ℝ):is_measurable (set.Iic x) :=
begin
  rw real_measurable_space_def,
  apply is_measurable_Iic,
end

lemma real.is_measurable_Ioc (x y:ℝ):is_measurable (set.Ioc x y) :=
begin
  rw real_measurable_space_def,
  apply is_measurable_Ioc,
end



lemma real_CDF_identical {Ω:Type*} {p:probability_space Ω} 
    {X Y:p →ᵣ borel real}:
    ((real_CDF X) = (real_CDF Y)) → random_variable_identical X Y :=
begin
  intro A1,
  have A2:borel ℝ = measurable_space.generate_from (set.range set.Iic),
  {
    apply borel_eq_generate_Iic,
  },
  apply random_variable_identical_generate_from2 A2,
  apply set_range_Iic_closed,
  intros E A3,
  simp at A3,
  cases A3 with y A3,
  have A4:E.val = set.Iic y,
  {
    rw A3,
    rw measurable_set_val_eq_coe,
  },
  repeat {rw set_Iic_eq_CDF A4},
  rw A1,
end 


noncomputable def real_joint_CDF {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel real) (Y:p →ᵣ borel real) (x y:ℝ):nnreal :=
    Pr[(X ≤ᵣ x) ∧ₑ (Y ≤ᵣ y)]
 
def measurable_set.Iic (x:ℝ):measurable_set (borel ℝ) := {
  val := set.Iic x,
  property := real.is_measurable_Iic x,
}

def measurable_set.Ioc (x y:ℝ):measurable_set (borel ℝ) := {
  val := set.Ioc x y,
  property := real.is_measurable_Ioc x y,
}


lemma measurable_set.Iic_val_def {x:ℝ}:
  (measurable_set.Iic x).val = set.Iic x := rfl


lemma measurable_set.Ioc_val_def {x y:ℝ}:
  (measurable_set.Ioc x y).val = set.Ioc x y := rfl


noncomputable def real_joint_set (x y:ℝ):
    measurable_set ((borel real) ×ₘ (borel real)) :=
  prod_measurable_set (measurable_set.Iic x)
                      (measurable_set.Iic y)


lemma mem_real_measurable_set_Iic_def {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel real) (x:ℝ):X ∈ᵣ (measurable_set.Iic x) = X ≤ᵣ x :=
begin
  apply event.eq,
  rw rv_event_val_def,
  rw measurable_set.Iic_val_def,
  rw event_le_val_def,
  unfold set.Iic,
  simp,
  rw ← random_variable_val_eq_coe,
  rw ← random_variable_val_eq_coe,
  rw coe_random_variable_of_real_val_def,
end


lemma real_joint_CDF_alt {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel real) (Y:p →ᵣ borel real) (x y:ℝ):
    real_joint_CDF X Y x y = 
    Pr[(X ×ᵣ Y) ∈ᵣ real_joint_set x y] :=
begin
  unfold real_joint_set,
  rw mem_prod_random_variable_prod_measurable_set,
  unfold real_joint_CDF,
  repeat {rw mem_real_measurable_set_Iic_def},
end


lemma prod_set_Iic_eq_CDF {Ω:Type*} {p:probability_space Ω} 
   {X:p →ᵣ borel real} {x:ℝ} 
   {Y:p →ᵣ borel real} {y:ℝ} 
   {E:measurable_set (borel ℝ ×ₘ borel ℝ)}:
   E.val = set.prod (set.Iic x) (set.Iic y) →
   (Pr[(X ×ᵣ Y) ∈ᵣ E] = (real_joint_CDF X Y x y)) :=
begin
  intro A1,
  rw real_joint_CDF_alt,
  rw ← ennreal.coe_eq_coe,
  unfold real_joint_set,
  repeat {
    rw event_prob_def,
    rw rv_event_val_def
  },
  rw A1,
  rw prod_measurable_set_val_def,
  repeat {rw measurable_set.Iic_val_def},
end

lemma real.Iic_covers:set.sUnion (set.range (λ n:ℕ,set.Iic (n:ℝ))) = set.univ :=
begin
  ext x,split;intro A1,
  {
    apply set.mem_univ,
  },
  {
    simp,
    have A2 := exists_nat_gt x,
    cases A2 with i A2,
    apply exists.intro i,
    apply le_of_lt,
    apply A2,
  },
end

lemma set.mem_range_elim {α β:Type*} {f:α → β} {b:β}:
    b∈ set.range f →
    ∃ a:α, f a  = b :=
begin
  intro A1,
  simp at A1,
  apply A1,
end


lemma prod_borel_R_eq_Iic:
  (borel ℝ) ×ₘ (borel ℝ) = measurable_space.generate_from 
  {S|∃ x y:ℝ, S = set.prod (set.Iic x) (set.Iic y)} :=
begin
  repeat {rw borel_eq_generate_Iic},
  unfold prod_space,
  have A1:set.countable (set.range (λ n:ℕ,set.Iic (n:ℝ))),
  {
    apply set.countable_range,
  },
  have A2:(set.range (λ n:ℕ,set.Iic (n:ℝ))) ⊆ set.range set.Iic,
  {
    rw set.subset_def,
    intros S A2A,
    simp at A2A,
    simp,
    cases A2A with y A2A,
    apply exists.intro (y:ℝ),
    apply A2A,
  },
  have A3:set.sUnion (set.range (λ n:ℕ,set.Iic (n:ℝ))) = set.univ :=
    real.Iic_covers,
  rw @prod_measurable_space_def2 _ _ _ _ (set.range (λ n:ℕ,set.Iic (n:ℝ)))
  (set.range (λ n:ℕ,set.Iic (n:ℝ))) A1 A1 A2 A2 A3 A3,
  have A4:
      {U : set (ℝ × ℝ) | ∃ (A  ∈ set.range (@set.Iic ℝ _)),
       ∃ (B ∈ set.range (@set.Iic ℝ _)), 
        U = set.prod A B} =
    {S : set (ℝ × ℝ) | ∃ (x y : ℝ), S = 
         set.prod (@set.Iic ℝ _ x) (@set.Iic ℝ _ y)},
  {
    ext p;split;intro A4A;simp,
    {
      cases A4A with A A4A,
      cases A4A with A4A A4B,
      cases A4B with B A4B,
      cases A4B with A4B A4C,
      subst p,
      --cases A4A with x A4A,
      --unfold set.range at A4A,
      have A4D := @set.mem_range_elim (ℝ) (set ℝ) (set.Iic) A A4A,
      cases A4D with x A4D,
      apply exists.intro x,
      have A4E := @set.mem_range_elim (ℝ) (set ℝ) (set.Iic) B A4B,
      cases A4E with y A4E,
      apply exists.intro y,
      rw A4D,
      rw A4E,  
    },
    {
      simp at A4A,
      apply A4A,
    },
  },
  rw A4,
end

lemma prod_set_range_Iic_closed {t₁ t₂ : set (ℝ × ℝ)}:
    t₁ ∈ {S : set (ℝ × ℝ) | ∃ (x y : ℝ), S = set.prod (set.Iic x) (set.Iic y)} →
    t₂ ∈ {S : set (ℝ × ℝ) | ∃ (x y : ℝ), S = set.prod (set.Iic x) (set.Iic y)} →
    set.nonempty (t₁ ∩ t₂) →
    t₁ ∩ t₂ ∈ {S : set (ℝ × ℝ) | ∃ (x y : ℝ), S = set.prod (set.Iic x) (set.Iic y)} :=
begin
  intros A1 A2 A3,
  cases A1 with x1 A1,
  cases A1 with y1 A1,
  subst t₁,
  cases A2 with x2 A2,
  cases A2 with y2 A2,
  subst t₂,
  rw set.prod_inter_prod,
  repeat {rw set.Iic_inter_Iic},
  simp,
  apply exists.intro (x1 ⊓ x2),
  apply exists.intro (y1 ⊓ y2),
  refl,
end

lemma real_joint_CDF_identical {Ω:Type*} {p:probability_space Ω} 
    {X1 X2 Y1 Y2:p →ᵣ borel real}:
    ((real_joint_CDF X1 X2) = (real_joint_CDF Y1 Y2)) → 
    random_variable_identical (X1 ×ᵣ X2) (Y1 ×ᵣ Y2) :=
begin
  intro A1,
  have A2:= prod_borel_R_eq_Iic,
  apply random_variable_identical_generate_from2 A2,
  apply prod_set_range_Iic_closed,
  intros E A3,
  simp at A3,
  cases A3 with x A3,
  cases A3 with y A3,

  repeat {rw prod_set_Iic_eq_CDF A3},
  rw A1,
end 


lemma is_measurable.countable {S:set ℝ}:set.countable S → is_measurable S :=
begin
  intro A1,
  have A2:S = (set.sUnion (set.image singleton S)),
  {
    simp,
  },
  rw A2,
  apply is_measurable.sUnion,
  apply set.countable.image,
  apply A1,
  intro t,
  intro A3,
  simp at A3,
  cases A3 with x A3,
  cases A3 with A3 A4,
  subst t,
  apply is_measurable_singleton,
end


def measurable_set.of_countable (S:set ℝ) (H:set.countable S):measurable_set (borel ℝ) := {
  val := S,
  property := is_measurable.countable H,
}

def is_countable_support {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel ℝ) (S:set ℝ):Prop :=
 ∃ (H:set.countable S), Pr[X ∈ᵣ (measurable_set.of_countable S H)] = 1 

def is_discrete_random_variable {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel ℝ):Prop := ∃ (S:set ℝ), is_countable_support X S


def is_probability_mass_function {Ω:Type*} {p:probability_space Ω} (X:p →ᵣ borel ℝ) {S:set ℝ} (f:{x // x ∈ S} → nnreal):Prop := 
   (set.countable S) ∧
   (∀ E:measurable_set (borel ℝ), has_sum f (Pr[X∈ᵣ E]))




def is_absolutely_continuous_wrt 
  {Ω:Type*} {M:measurable_space Ω} (μ ν:measure_theory.measure Ω):Prop :=
  ∀ A:set Ω, is_measurable A → (ν A = 0) → (μ A = 0)

def measure_zero_of_is_absolutely_continuous_wrt 
  {Ω:Type*} {M:measurable_space Ω} (μ ν:measure_theory.measure Ω) (A:set Ω):
  is_absolutely_continuous_wrt μ ν → 
  is_measurable A → (ν A = 0) → (μ A = 0) :=
begin
  intros A1 A2 A3,
  unfold is_absolutely_continuous_wrt at A1,
  apply A1 A A2 A3,
end
