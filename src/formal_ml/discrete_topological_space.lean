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
import topology.basic
import topology.order
import topology.constructions
import topology.bases
import data.set.countable
import formal_ml.set

import topology.instances.nnreal
import topology.instances.ennreal
import formal_ml.topological_space
import formal_ml.nat
import formal_ml.int


/-
  This has several results related to the discrete topology (or bottom
  topology). In this topology, every set is open. In order to
  prove that every set is open, it is sufficient to prove every
  singleton set is open (see discrete_bottom_topological_space).
  Moreover, the discrete topologies on the naturals and the integers
  are also order topologies.
 -/
lemma topological_space.bot_is_open_def {α:Type*}:(@topological_space.is_open α ⊥) = (λ S:set α, true) := rfl


lemma topological_space.bot_is_open {α:Type*} {U:set α}:topological_space.is_open ⊥ U := 
begin
  rw topological_space.bot_is_open_def,
  apply true.intro,
end


lemma set.sUnion_of_element_singletons {α:Type*} {U:set α}:
    U = ⋃₀ {V:set α|∃ a∈ U, V={a}} :=
begin
      simp,
      ext,split;intros D1A,
      {
        simp,
        apply exists.intro {x},
        split,
        apply exists.intro x,
        split,
        apply D1A,
        refl,
        simp,
      },
      {
        simp at D1A,
        cases D1A with V D1A,
        cases D1A with D1A D1B,
        cases D1A with a D1A,
        cases D1A with D1A D1C,
        subst V,
        simp at D1B,
        subst x,
        apply D1A,
      },
end


lemma discrete_bottom_topological_space {α:Type*} {T:topological_space α}:(∀ a:α, @is_open α T {a}) →
    T = ⊥ :=
begin
  intro A1,
  ext U,split;intros B1,
  {
    apply topological_space.bot_is_open,
  },
  {
    rw @set.sUnion_of_element_singletons α U,
    apply is_open_sUnion,
    intros V D2,
    simp at D2,
    cases D2 with a D2,
    cases D2 with D2 D3,
    subst V,
    apply A1,
  },
end


instance nat.order_topology:order_topology ℕ  := 
begin
  apply order_topology.mk,
  have A1:nat.topological_space = ⊥ := rfl,
  symmetry,
  apply discrete_bottom_topological_space,
  intro a,
  unfold topological_space.generate_from topological_space.is_open is_open,
  cases a,
  {
    apply topological_space.generate_open.basic,
    simp,
    apply exists.intro 1,
    right,
    ext;split;intros B1;simp;simp at B1,
    {
      subst x,
       apply zero_lt_one,
    },
    {
     apply nat.zero_of_lt_one B1,
    },
  },
  {
    have C1:{a.succ}=set.Iio (a.succ.succ) ∩ set.Ioi a,
    {
      ext;split;intros C1A;simp;simp at C1A,
      {
        subst x,
        split,
        apply lt_succ,
        apply lt_succ,
      },
      {
        cases C1A with C1A C1B,
        apply le_antisymm,
        {
          apply nat.le_of_lt_succ C1A,
        },
        {
          rw nat.succ_le_iff,
          apply C1B,
        },
      },
    },
    rw C1,
    apply topological_space.generate_open.inter ,
    {
      apply topological_space.generate_open.basic,
      apply exists.intro (a.succ.succ),
      right,
      refl,
    },
    {
      apply topological_space.generate_open.basic,
      apply exists.intro (a),
      left,
      refl,
    },
  },
end


instance int.order_topology:order_topology int :=
begin
  apply order_topology.mk,
  symmetry,
  apply discrete_bottom_topological_space,
  intro a,
  have A1:{a} = set.Ioi a.pred ∩ set.Iio a.succ,
  {
    ext b,split;intros A1A;simp;simp at A1A,
    {
      subst b,
      split,
      apply int.pred_lt_self,
      apply int.lt_succ,
    },
    {
      cases A1A with A1A A1B,
      apply le_antisymm,
      rw int.lt_succ_iff at A1B,
      apply A1B,
      rw int.pred_lt_iff at A1A,
      apply A1A,
    },  
  },  
  rw A1,
  clear A1,
  apply topological_space.generate_open.inter ,
  {
    apply topological_space.generate_open.basic,
    apply exists.intro (a.pred),
    left,
    refl,
  },
  {
    apply topological_space.generate_open.basic,
    apply exists.intro (a.succ),
    right,
    refl,
  },
end




