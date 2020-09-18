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
--import formal_ml.set
import formal_ml.set
import formal_ml.topological_space




/-
  Establishes a topological basis for a topological_space T and a type α where:
  1. T is an order_topology
  2. α has a decidable_linear_order
  3. α has two distinct elements.



   that  Specifically, the goal of this file is to prove a topological
  basis for the extended reals (ennreal, or [0,∞]).

  A tricky part of a topological basis is that it must be closed under intersection. However, I
  am not entirely clear as to the value of this. Specifically, one benefit of a basis is to prove
  a function is continuous by considering the inverse of all sets. However, this adds a great
  deal of complexity, because (1) it introduces a bunch of open sets one has to take the inverse
  for and (2) it is sufficient to prove for sets of the form [0, a) and (a,∞] are open.

  The value of a topological basis is that you can use it to prove that something is not
  continuous. Thus, it is of particular importance to have a topological basis for ennreal,
  because in this way you can show that multiplication is discontinuous.

  Also, as far as I understand it, this theory can be lifted to an arbitrary order
  topology. Specifically, if you have a linear order, then you should be able to prove this.


  Some observations:

  1. The work below tries too hard to prove that the basis does not contain the empty set.
     This is harder than expected, because {b|b < 0} and {b|⊤ < b} are empty. However,
     embracing the empty set makes the problem easy. Specifically:
     Ioo a b ∩ Ioo c d = Ioo (max a c) (min b d)
     Ioo a b ∩ Ioi c = Ioo (max a c) b
     Ioo a b ∩ Iio c = Ioo a (min b c)
     Iio a ∩ Ioi b = Ioo b a
     Iio a ∩ Iio b = Iio (min a b)
     Ioi a ∩ Ioi b = Ioi (max a b)

  2. Also, the topological basis for the order topology is simply:
     {U:set ennreal|∃ a b, U = (set.Ioo a b)}∪ {s | ∃a, s = {b | a < b} ∨ s = {b | b < a}}

     There are introduction and elimination rules for the membership of Ioo, Iio, and Ioi.


-/




def order_topological_basis (α:Type*) [linear_order α]:set (set α) :=
  {U:set α|∃ a b, U = (set.Ioo a b)}∪
  {s | ∃a, s = {b | a < b} ∨ s = {b | b < a}}




lemma mem_order_topological_basis_intro_Ioo {α:Type*}
  [linear_order α] (a b:α):
  (set.Ioo a b) ∈ (order_topological_basis α)  :=
begin
  unfold order_topological_basis,
  left,
  apply exists.intro a,
  apply exists.intro b,
  refl,
end

lemma mem_order_topological_basis_intro_Ioi
  {α:Type*} [linear_order α] (a:α):
  set.Ioi a ∈ (order_topological_basis α) :=
begin
  unfold order_topological_basis,
  right,
  apply exists.intro a,
  left,
  refl,
end

lemma mem_order_topological_basis_intro_Iio
  {α:Type*} [linear_order α] (a:α):
  set.Iio a ∈ (order_topological_basis α) :=
begin
  unfold order_topological_basis,
  right,
  apply exists.intro a,
  right,
  refl,
end

def mem_order_topological_basis_def (α:Type*) [linear_order α] (U:set α):
  U ∈ (order_topological_basis α) ↔
  ((∃ (a b:α), U=(set.Ioo a b))∨ (∃ c:α,(U=(set.Ioi c))∨ (U=(set.Iio c)))) :=
begin
  refl,
end




lemma Ioo_inter_Ioo_eq_Ioo {α:Type*} [decidable_linear_order α] {a b c d:α}:
      set.Ioo a b ∩ set.Ioo c d = set.Ioo (max a c) (min b d) :=
begin
  unfold set.Ioo,
  ext,split;intro A1,
  {
    simp at A1,
    cases A1 with A2 A3,
    cases A2 with A4 A5,
    cases A3 with A6 A7,
    simp,
    apply (and.intro (and.intro A4 A6) (and.intro A5 A7)),
  },
  {
    simp at A1,
    cases A1 with A2 A3,
    cases A2 with A4 A5,
    cases A3 with A6 A7,
    simp,
    apply and.intro (and.intro A4 A6) (and.intro A5 A7),
  },
end

lemma Ioo_inter_Ioi_eq_Ioo {α:Type*} [decidable_linear_order α] {a b c:α}:
      set.Ioo a b ∩ set.Ioi c = set.Ioo (max a c) b :=
begin
  unfold set.Ioo,
  unfold set.Ioi,
  ext,split;intro A1,
  {
    simp at A1,
    cases A1 with A2 A3,
    cases A2 with A4 A5,
    simp,
    apply and.intro (and.intro A4 A3) A5,
  },
  {
    simp at A1,
    cases A1 with A2 A3,
    cases A2 with A4 A5,
    simp,
    apply and.intro (and.intro A4 A3) A5,
  }
end

lemma Ioi_inter_Iio_eq_Ioo {α:Type*} [decidable_linear_order α] {a b:α}:
      set.Ioi a ∩ set.Iio b = set.Ioo a b :=
begin
  unfold set.Ioi,
  unfold set.Ioo,
  refl,
end

lemma Ioo_inter_Iio_eq_Ioo {α:Type*} [decidable_linear_order α] {a b c:α}:
      set.Ioo a b ∩ set.Iio c = set.Ioo a (min b c) :=
begin
  unfold set.Ioo,
  unfold set.Iio,
  ext,split;intro A1,
  {
    simp at A1,
    cases A1 with A2 A3,
    cases A2 with A4 A5,
    simp,
    apply and.intro A4 (and.intro A5 A3),
  },
  {
    simp at A1,
    simp,
    apply and.intro (and.intro A1.left A1.right.left) A1.right.right,
  }
end

lemma Iio_inter_Iio_eq_Iio {α:Type*} [decidable_linear_order α] {a b:α}:
      set.Iio a ∩ set.Iio b = set.Iio (min a b) :=
begin
  unfold set.Iio,
  ext,split;intro A1,
  {
    simp at A1,
    simp,
    apply A1,
  },
  {
    simp at A1,
    simp,
    apply A1,
  }
end

lemma Ioi_inter_Ioi_eq_Ioi {α:Type*} [decidable_linear_order α] {a b:α}:
      set.Ioi a ∩ set.Ioi b = set.Ioi (max a b) :=
begin
  unfold set.Ioi,
  ext,split;intro A1,
  {
    simp at A1,
    simp,
    apply A1,
  },
  {
    simp at A1,
    simp,
    apply A1,
  }
end


lemma inter_order_topological_basis (α:Type*) [decidable_linear_order α] {U V:set α}:
   (U ∈ (order_topological_basis α)) →
   (V ∈ (order_topological_basis α)) →
   ((U ∩ V) ∈ (order_topological_basis α)) :=
begin
  intros A1 A2,
  rw mem_order_topological_basis_def at A1,
  rw mem_order_topological_basis_def at A2,
  cases A1,
  {
    cases A1 with a A1,
    cases A1 with b A1,
    subst U,
    cases A2,
    {
      cases A2 with c A2,
      cases A2 with d A2,
      subst V,
      rw Ioo_inter_Ioo_eq_Ioo,
      apply mem_order_topological_basis_intro_Ioo,
    },
    cases A2 with c A2,
    cases A2,
    {
      subst V,
      rw Ioo_inter_Ioi_eq_Ioo,
      apply mem_order_topological_basis_intro_Ioo,
    },
    {
      subst V,
      rw Ioo_inter_Iio_eq_Ioo,
      apply mem_order_topological_basis_intro_Ioo,
    },
  },
  cases A1 with c A1,
  cases A1,
  {
    subst U,
    cases A2,
    {
      cases A2 with a A2,
      cases A2 with b A2,
      subst V,
      rw set.inter_comm,
      rw Ioo_inter_Ioi_eq_Ioo,
      apply mem_order_topological_basis_intro_Ioo,
    },
    cases A2 with a A2,
    cases A2,
    {
      subst V,
      rw Ioi_inter_Ioi_eq_Ioi,
      apply mem_order_topological_basis_intro_Ioi,
    },
    {
      subst V,
      rw Ioi_inter_Iio_eq_Ioo,
      apply mem_order_topological_basis_intro_Ioo,
    }
  },
  {
    subst U,
    cases A2,
    {
      cases A2 with a A2,
      cases A2 with b A2,
      subst V,
      rw set.inter_comm,
      rw Ioo_inter_Iio_eq_Ioo,
      apply mem_order_topological_basis_intro_Ioo,
    },
    cases A2 with c A2,
    cases A2,
    {
      subst V,
      rw set.inter_comm,
      rw Ioi_inter_Iio_eq_Ioo,
      apply mem_order_topological_basis_intro_Ioo,
    },
    {
      subst V,
      rw Iio_inter_Iio_eq_Iio,
      apply mem_order_topological_basis_intro_Iio,
    },
  },
end






/-
  Note that the order topological basis is only a basis if there is at
  least two distinct elements of the type. A singleton set only has the
  universe and the empty set as open sets.
-/
lemma order_topological_basis_cover {α:Type*} [linear_order α] {a b:α}:
  (a<b)→
  ⋃₀ (order_topological_basis α) = set.univ :=
begin
  intro A0,
  ext;split;intro A1,
  {
    simp,
  },
  {
    clear A1,
    simp,
    have A2:(a < x ∨ x ≤ a) := lt_or_le a x,
    cases A2,
    {
      apply exists.intro (set.Ioi a),
      split,
      apply mem_order_topological_basis_intro_Ioi,
      apply A2,
    },
    {
      apply exists.intro (set.Iio b),
      split,
      apply mem_order_topological_basis_intro_Iio,
      apply lt_of_le_of_lt,
      exact A2,
      exact A0,
    }
  }
end


lemma generate_from_order_topological_basis {α:Type*} [decidable_linear_order α]
  [T:topological_space α]
  [X:order_topology α]:
  T =  @topological_space.generate_from α (order_topological_basis α) :=
begin
  rw X.topology_eq_generate_intervals,
  apply generate_from_eq_generate_from,
  {
    intros V A1,
    apply topological_space.generate_open.basic,
    simp at A1,
    cases A1 with a A1,
    cases A1,
    {
      subst V,
      apply mem_order_topological_basis_intro_Ioi,
    },
    {
      subst V,
      apply mem_order_topological_basis_intro_Iio,
    },
  },
  {
    intros V A1,
    rw mem_order_topological_basis_def at A1,
    cases A1,
    {
      cases A1 with a A1,
      cases A1 with b A1,
      rw ← Ioi_inter_Iio_eq_Ioo at A1,
      subst V,
      apply topological_space.generate_open.inter;apply topological_space.generate_open.basic,
      {
        apply exists.intro a,
        left,refl,
      },
      {
        apply exists.intro b,
        right,refl,
      }
    },
    cases A1 with c A1,
    apply topological_space.generate_open.basic,
    cases A1;subst V;apply exists.intro c,
    {
      left,refl,
    },
    {
      right,refl,
    },
  }
end



lemma is_topological_basis_order_topology {α:Type*} [decidable_linear_order α]
  [T:topological_space α]
  [X:order_topology α] {a b:α}:
  (a < b)→
  topological_space.is_topological_basis
  (order_topological_basis α) :=
begin
  intro A0,
  unfold topological_space.is_topological_basis,
  split,
  {
    intros t₁ A1 t₂ A2 x A3,
    apply exists.intro (t₁ ∩ t₂),
    split,
    {
      apply inter_order_topological_basis,
      apply A1,
      apply A2,
    },
    split,
    {
      exact A3,
    },
    {
      apply set.subset.refl,
    }
  },
  split,
  {
    apply order_topological_basis_cover A0,
  },
  {
    apply generate_from_order_topological_basis,
  }
end

lemma ennreal_is_topological_basis:
  topological_space.is_topological_basis
  (order_topological_basis ennreal) :=
begin
  have A1:(0:ennreal) < (1:ennreal) := canonically_ordered_semiring.zero_lt_one,
  apply is_topological_basis_order_topology A1,
end

/- In Munkres, Topology, Second Edition, page 84, they specify the basis of the order
   topology as above (modulo the empty set). However, if there is a singleton type,
   this is not the case.
  -/
lemma not_is_topological_basis_singleton {α:Type*} [decidable_linear_order α]
  [T:topological_space α]
  [X:order_topology α]
  [S:subsingleton α]
  {a:α}:
  ¬ (topological_space.is_topological_basis
  (order_topological_basis α)) :=
begin
  intro A1,
  unfold topological_space.is_topological_basis at A1,
  cases A1 with A2 A3,
  cases A3 with A4 A5,
  have A6:a∈ set.univ := set.mem_univ a,
  rw ← A4 at A6,
  cases A6 with V A7,
  cases A7 with A8 A9,
  rw mem_order_topological_basis_def at A8,
  cases A8,
  {
    cases A8 with b A8,
    have A10:b=a := subsingleton.elim b a,
    subst b,
    cases A8 with c A8,
    have A11:c=a := subsingleton.elim c a,
    subst c,
    subst V,
    apply (@set.left_mem_Ioo α _ a a).mp,
    exact A9,
  },
  cases A8 with c A8,
  have A12:c=a := subsingleton.elim c a,
  subst c,
  cases A8,
  {
    subst V,
    rw set.mem_Ioi at A9,
    apply lt_irrefl a A9,
  },
  {
    subst V,
    rw set.mem_Iio at A9,
    apply lt_irrefl a A9,
  },
end

namespace order_topology_counterexample

inductive ot_singleton:Type
| ot_element

lemma ot_singleton_subsingletonh (a b:ot_singleton):a = b :=
begin
  cases a,
  cases b,
  refl,
end

instance ot_singleton_subsingleton:subsingleton ot_singleton :=
  subsingleton.intro ot_singleton_subsingletonh


def ot_singleton_le (a b:ot_singleton):Prop := true

def ot_singleton_lt (a b:ot_singleton):Prop := false

instance ot_singleton_has_lt:has_lt ot_singleton := {
  lt := ot_singleton_lt,
}

instance ot_singleton_has_le:has_le ot_singleton := {
  le := ot_singleton_le,
}

lemma ot_singleton_le_true (a b:ot_singleton): a ≤ b = true :=
begin
  refl,
end

lemma ot_singleton_le_true2 (a b:ot_singleton): a ≤ b :=
begin
  rw ot_singleton_le_true,
  apply true.intro,
end

lemma ot_singleton_lt_false (a b:ot_singleton): a < b = false :=
begin
  refl,
end

lemma ot_singleton_lt_false2 (a b:ot_singleton): ¬ (a < b) :=
begin
  intro A1,
  rw ot_singleton_lt_false at A1,
  exact A1,
end

lemma ot_singleton_le_refl (a:ot_singleton):a ≤ a :=
begin
  apply ot_singleton_le_true2,
end

lemma ot_singleton_le_trans (a b c:ot_singleton):a ≤ b → b ≤ c → a ≤ c :=
begin
  intros A1 A2,
  apply ot_singleton_le_true2,
end

lemma ot_singleton_le_antisymm (a b:ot_singleton):a ≤ b → b ≤ a → a = b :=
begin
  intros A1 A2,
  apply subsingleton.elim,
end

lemma ot_singleton_le_total (a b:ot_singleton):a ≤ b ∨ b ≤ a :=
  or.inl (ot_singleton_le_true2 a b)


def ot_singleton_decidable_le:decidable_rel (ot_singleton_le) :=
begin
  unfold decidable_rel,
  intros a b,
  apply decidable.is_true (ot_singleton_le_true2 a b),
end


def ot_singleton_decidable_lt:decidable_rel (ot_singleton_lt) :=
begin
  unfold decidable_rel,
  intros a b,
  apply decidable.is_false (ot_singleton_lt_false2 a b),
end


lemma ot_singleton_lt_iff_le_not_le (a b:ot_singleton):a < b ↔ a ≤ b ∧ ¬b ≤ a :=
begin
  split;intro A1,
  {
    exfalso,
    apply ot_singleton_lt_false2 a b,
    exact A1,
  },
  {
    exfalso,
    cases A1 with A2 A3,
    apply A3,
    apply ot_singleton_le_true2,
  }
end

instance ot_singleton_decidable_linear_order:decidable_linear_order ot_singleton := {
   le := ot_singleton_le,
   lt := ot_singleton_lt,
   le_refl := ot_singleton_le_refl,
   le_trans := ot_singleton_le_trans,
   le_antisymm := ot_singleton_le_antisymm,
   lt_iff_le_not_le := ot_singleton_lt_iff_le_not_le,
   le_total := ot_singleton_le_total,
   decidable_le := ot_singleton_decidable_le,
   decidable_lt := ot_singleton_decidable_lt,
}


lemma not_is_topological_basis_ot_singleton
  [T:topological_space ot_singleton]
  [X:order_topology ot_singleton]:
  ¬ (topological_space.is_topological_basis
  (order_topological_basis ot_singleton)) :=
begin
  apply not_is_topological_basis_singleton,
  apply ot_singleton.ot_element,
end
end order_topology_counterexample
