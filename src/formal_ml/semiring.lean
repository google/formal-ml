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
import group_theory.subgroup
--import algebra.pi_instances
import deprecated.submonoid
import group_theory.submonoid
import algebra.ring.pi
import tactic.subtype_instance
import data.equiv.ring

/-
  Code to handle subtypes and functions of semirings and commutative semirings.

  There is work on rings, but not semirings.
  In particular, the (measurable functions/random variables) over (nnreal/ennreal) are commutative
  semirings, but both don't have a concept of opposite (so are not rings).
-/

/-
  A sub-semiring is a subtype of a semiring that has 0, 1, and is closed under multiplication and
  addition.

  Note: is_add_submonoid is deprecated, as is is_submonoid.
-/
class is_sub_semiring {R:Type*} [semiring R]
(S : set R) extends is_add_submonoid S, is_submonoid S : Prop.

--Likely defined elsewhere.
lemma set.subtype_coe {R:Type*} {S:set R} {a b: S}:a = b ↔ (a:R) = (b:R) :=
begin
  split;intros A1,
  {
    subst a,
  },
  {
    apply subtype.eq,
    apply A1,
  },
end

--This could be written better: however, should figure out the fate of the deprecated
--is_add_submonoid and is_submonoid first.
instance subtype.semiring {R:Type*} [semiring R] {S : set R} [is_sub_semiring S] : semiring S := {
  zero_mul :=
  begin
    intro a,
    rw set.subtype_coe,
    apply zero_mul,
  end,
  mul_zero :=
  begin
    intro a,
    rw set.subtype_coe,
    apply mul_zero,
  end,
  left_distrib :=
  begin
    intros a b c,
    rw set.subtype_coe,
    apply left_distrib,
  end,
  right_distrib :=
  begin
    intros a b c,
    rw set.subtype_coe,
    apply right_distrib,
  end,
  .. subtype.add_comm_monoid,
  .. subtype.monoid
}
--by subtype_instance



instance subtype.comm_semiring {R:Type*} [comm_semiring R]
  {S : set R} [is_sub_semiring S] : comm_semiring S := {
  mul_comm :=
  begin
    intros a b,
    rw set.subtype_coe,
    apply mul_comm,
  end
  ..subtype.semiring
}




/- 
   If you have an homomorphic injection into a group or ring,
   the properties can carry backwards across it. 
   Note that these theorems assume that we have already defined all of the operations.
   For example, we can define a very specific implementation of ℤ_{2^32}, and then show
   that the operations map to fin (2^32), and are thus a commutative ring.

   Another approach would be to specify an injection, and then use this to define the
   operations. These two approaches can be blended: some operations can be explicitly defined,
   and some inferred from the injection.
-/ 
lemma add_comm_of_is_add_hom {α β:Type*} [H1:has_add α] [H2:has_add β] (f:α → β):(is_add_hom f)
  → (function.injective f) →
  (∀ b1 b2:β, b1 + b2 = b2 + b1) → (∀ a1 a2:α,  a1  +  a2=  a2  + a1)  :=
begin
  intros A1 A2 A3 a1 a2,
  apply A2,
  apply eq.trans,
  apply A1.map_add,
  apply eq.trans,
  apply A3,
  symmetry,
  apply A1.map_add,
end

lemma mul_comm_of_is_mul_hom {α β:Type*} [H1:has_mul α] [H2:has_mul β] (f:α → β):(is_mul_hom f)
  → (function.injective f) →
  (∀ b1 b2:β, b1 * b2 = b2 * b1) → (∀ a1 a2:α,  a1  *  a2=  a2 * a1)  :=
begin
  intros A1 A2 A3 a1 a2,
  apply A2,
  apply eq.trans,
  apply A1.map_mul,
  apply eq.trans,
  apply A3,
  symmetry,
  apply A1.map_mul,
end

lemma add_assoc_of_is_add_hom {α β:Type*} [H1:has_add α] [H2:has_add β] (f:α → β):(is_add_hom f)
  → (function.injective f) →
  (∀ b1 b2 b3: β, b1 + b2 + b3= b1 + (b2 + b3)) → (∀ a1 a2 a3:α,  a1  +  a2+ a3=  a1 + (a2 + a3))  :=
begin
  intros A1 A2 A3 a1 a2 a3,
  apply A2,
  apply eq.trans,
  apply A1.map_add,
  rw A1.map_add,
  rw A1.map_add,
  rw A1.map_add,
  apply A3,
end

lemma mul_assoc_of_is_mul_hom {α β:Type*} [H1:has_mul α] [H2:has_mul β] (f:α → β):(is_mul_hom f)
  → (function.injective f) →
  (∀ b1 b2 b3: β, b1 * b2 * b3= b1 * (b2 * b3)) → (
   ∀ a1 a2 a3:α,  a1  *  a2 * a3=  a1 * (a2 * a3))  :=
begin
  intros A1 A2 A3 a1 a2 a3,
  apply A2,
  apply eq.trans,
  apply A1.map_mul,
  rw A1.map_mul,
  rw A1.map_mul,
  rw A1.map_mul,
  apply A3,
end


set_option pp.implicit true

lemma one_mul_of_is_mul_hom {α β:Type*} [HMα:has_mul α] [HZα:has_one α] [HMβ:monoid β] (f:α → β):(is_mul_hom f)
  → (function.injective f) →
   (f 1 = 1) →
   (∀ a:α,  1 * a = a) :=
begin
  intros A1 A2 A3 a,
  apply A2,
  rw A1.map_mul,
  rw A3,
  apply monoid.one_mul (f a), 
end

lemma zero_mul_of_is_mul_hom {α β:Type*} [HMα:has_mul α] [HZα:has_zero α] [Rβ:semiring β] (f:α → β):(is_mul_hom f)
  → (function.injective f) →
   (f 0 = 0) →
   (∀ a:α,  0 * a = 0) :=
begin
  intros A1 A2 A3 a,
  apply A2,
  rw A1.map_mul,
  rw A3,
  apply semiring.zero_mul (f a), 
end

lemma mul_one_of_is_mul_hom {α β:Type*} [HMα:has_mul α] [HZα:has_one α] [HMβ:monoid β] (f:α → β):(is_mul_hom f)
  → (function.injective f) →
   (f 1 = 1) →
   (∀ a:α,  a * 1 = a) :=
begin
  intros A1 A2 A3 a,
  apply A2,
  rw A1.map_mul,
  rw A3,
  apply monoid.mul_one (f a), 
end

lemma mul_zero_of_is_mul_hom {α β:Type*} [HMα:has_mul α] [HZα:has_zero α] [Rβ:semiring β] (f:α → β):(is_mul_hom f)
  → (function.injective f) →
   (f 0 = 0) →
   (∀ a:α,  a * 0 = 0) :=
begin
  intros A1 A2 A3 a,
  apply A2,
  rw A1.map_mul,
  rw A3,
  apply semiring.mul_zero (f a), 
end

lemma zero_add_of_is_add_hom {α β:Type*} [HMα:has_add α] [HZα:has_zero α] [HMβ:add_monoid β] (f:α → β):(is_add_hom f)
  → (function.injective f) →
   (f 0 = 0) →
   (∀ a:α,  0 + a = a) :=
begin
  intros A1 A2 A3 a,
  apply A2,
  rw A1.map_add,
  rw A3,
  apply add_monoid.zero_add (f a), 
end

lemma add_zero_of_is_add_hom {α β:Type*} [HMα:has_add α] [HZα:has_zero α] [HMβ:add_monoid β] (f:α → β):(is_add_hom f)
  → (function.injective f) →
   (f 0 = 0) →
   (∀ a:α,  a + 0 = a) :=
begin
  intros A1 A2 A3 a,
  apply A2,
  rw A1.map_add,
  rw A3,
  apply add_monoid.add_zero (f a), 
end

def monoid_of_is_mul_hom {α β:Type*} [HMα:has_mul α] [HOα:has_one α] [Mβ:monoid β] (f:α → β) 
    (IMH:is_mul_hom f) (I:function.injective f) (HOM:f 1 = 1):monoid α := {
  mul := HMα.mul,
  one := HOα.one,
  mul_one := @mul_one_of_is_mul_hom α β HMα HOα Mβ f IMH I HOM,
  one_mul := @one_mul_of_is_mul_hom α β HMα HOα Mβ f IMH I HOM,
  mul_assoc := @mul_assoc_of_is_mul_hom α β HMα _ f IMH I monoid.mul_assoc,
}

def comm_monoid_of_is_mul_hom {α β:Type*} [HMα:has_mul α] [HOα:has_one α] [Mβ:comm_monoid β] (f:α → β) 
    (IMH:is_mul_hom f) (I:function.injective f) (HOM:f 1 = 1):comm_monoid α := {
  mul_comm := @mul_comm_of_is_mul_hom α β HMα _ f IMH I comm_monoid.mul_comm,
  ..(monoid_of_is_mul_hom f IMH I HOM),
}

def add_monoid_of_is_add_hom {α β:Type*} [HAα:has_add α] [HZα:has_zero α] [AMβ:add_monoid β] (f:α → β) 
    (IAH:is_add_hom f) (I:function.injective f) (HZM:f 0 = 0):add_monoid α := {
  add := HAα.add,
  zero := HZα.zero,
  add_zero := @add_zero_of_is_add_hom α β HAα HZα AMβ f IAH I HZM,
  zero_add := @zero_add_of_is_add_hom α β HAα HZα AMβ f IAH I HZM,
  add_assoc := @add_assoc_of_is_add_hom α β HAα _ f IAH I add_monoid.add_assoc,
}

class is_neg_hom {α β : Type*} [has_neg α] [has_neg β] (f : α → β) : Prop :=
(map_neg : ∀ x, f (-x) =  -(f x))


lemma add_left_neg_of_is_hom {α β:Type*} [HAα:has_add α] [HNα:has_neg α] [HZα:has_zero α] [AMβ:add_group β] (f:α → β): 
    (is_add_hom f)→ (is_neg_hom f)→ (function.injective f)→ (f 0 = 0) →
(∀ x:β, (-x) + x = 0 )→ 
(∀ x:α, (-x) + x = 0 ) :=
begin
  intros A1 A2 A3 A4 A5 x,
  apply A3,
  rw A1.map_add,
  rw A2.map_neg,
  rw A4,
  apply A5,
end


def add_group_of_is_hom {α β:Type*} [HAα:has_add α] [HNα:has_neg α] [HZα:has_zero α] [AMβ:add_group β] (f:α → β) 
    (IAH:is_add_hom f) (INH:is_neg_hom f) (I:function.injective f) (HZM:f 0 = 0):add_group α := {
  neg := HNα.neg,
  add_left_neg := @add_left_neg_of_is_hom α β HAα HNα HZα AMβ f IAH INH I HZM AMβ.add_left_neg,
  ..(add_monoid_of_is_add_hom f IAH I HZM),
}

def add_comm_group_of_is_hom {α β:Type*} [HAα:has_add α] [HNα:has_neg α] [HZα:has_zero α] [AMβ:add_comm_group β] (f:α → β) 
    (IAH:is_add_hom f) (INH:is_neg_hom f) (I:function.injective f) (HZM:f 0 = 0):add_comm_group α := {
  add_comm := @add_comm_of_is_add_hom α β _ _ f IAH I AMβ.add_comm,
  ..(add_group_of_is_hom f IAH INH I HZM),
}


def add_comm_monoid_of_is_add_hom {α β:Type*} [HAα:has_add α] [HZα:has_zero α] [AMβ:add_comm_monoid β] (f:α → β) 
    (IAH:is_add_hom f) (I:function.injective f) (HZM:f 0 = 0):add_comm_monoid α := {
  add_comm := @add_comm_of_is_add_hom α β HAα _ f IAH I add_comm_monoid.add_comm,
  ..(add_monoid_of_is_add_hom f IAH I HZM),
}


lemma left_distrib_of_is_hom {α β:Type*} [HAα:has_add α] [HMα:has_mul α] [Rβ:distrib β] (f:α → β):
   (is_add_hom f) → 
   (is_mul_hom f) →
   (function.injective f) →
   (∀ a b c:α,  a * (b + c) = a * b + a * c) :=
begin
  intros A1 A2 A3 a b c,
  apply A3,
  rw A1.map_add,
  rw A2.map_mul,
  rw A1.map_add,
  rw A2.map_mul,
  rw A2.map_mul,
  apply distrib.left_distrib,
end

lemma right_distrib_of_is_hom {α β:Type*} [HAα:has_add α] [HMα:has_mul α] [Rβ:distrib β] (f:α → β):
   (is_add_hom f) → 
   (is_mul_hom f) →
   (function.injective f) →
   (∀ a b c:α,  (a + b)  * c = a * c + b * c) :=
begin
  intros A1 A2 A3 a b c,
  apply A3,
  rw A1.map_add,
  rw A2.map_mul,
  rw A1.map_add,
  rw A2.map_mul,
  rw A2.map_mul,
  apply distrib.right_distrib,
end

def distrib_of_is_hom {α β:Type*} [HAα:has_add α] [HMα:has_mul α] [Dβ:distrib β] (f:α → β)
   (IAH:is_add_hom f) 
   (IMH:is_mul_hom f)
   (I:function.injective f):distrib α := {
  mul := HMα.mul,
  add := HAα.add,
  left_distrib := @left_distrib_of_is_hom 
      α β HAα HMα Dβ  f IAH IMH I,
  right_distrib := @right_distrib_of_is_hom α β 
      HAα HMα Dβ f IAH IMH I,
}

def semiring_of_is_hom {α β:Type*} [HAα:has_add α] [HZα:has_zero α] [HMα:has_mul α] [HOα:has_one α] [SRβ:semiring β] (f:α → β)
   (IAH:is_add_hom f) 
   (IMH:is_mul_hom f)
   (I:function.injective f)
   (HZM:f 0 = 0)
   (HOM:f 1 = 1):semiring α := {
  zero_mul := @zero_mul_of_is_mul_hom α β _ _ _ f IMH I HZM,
  mul_zero := @mul_zero_of_is_mul_hom α β _ _ _ f IMH I HZM,

  ..(add_comm_monoid_of_is_add_hom f IAH I HZM),
  ..(monoid_of_is_mul_hom f IMH I HOM),
  ..(distrib_of_is_hom f IAH IMH I),
}


def ring_of_is_hom {α β:Type*} [HAα:has_add α] [HNα:has_neg α] [HZα:has_zero α] [HMα:has_mul α] [HOα:has_one α] [SRβ:ring β] (f:α → β)
   (IAH:is_add_hom f) 
   (IMH:is_mul_hom f)
   (INH:is_neg_hom f)
   (I:function.injective f)
   (HZM:f 0 = 0)
   (HOM:f 1 = 1):ring α := {
  ..(semiring_of_is_hom f IAH IMH I HZM HOM),
  ..(add_group_of_is_hom f IAH INH I HZM),
}

def comm_ring_of_is_hom {α β:Type*} [HAα:has_add α] [HNα:has_neg α] [HZα:has_zero α] [HMα:has_mul α] [HOα:has_one α] [CRβ:comm_ring β] (f:α → β)
   (IAH:is_add_hom f) 
   (IMH:is_mul_hom f)
   (INH:is_neg_hom f)
   (I:function.injective f)
   (HZM:f 0 = 0)
   (HOM:f 1 = 1):comm_ring α := {
  mul_comm := (@mul_comm_of_is_mul_hom α β _ _ f IMH I CRβ.mul_comm),
  ..(ring_of_is_hom f IAH IMH INH I HZM HOM),
}

/-
  This represents an alternative: if there exists a surjective homomorphism to a type from a ring or group,
  then the codomain is a ring or group.
-/

lemma add_comm_of_is_add_hom_of_sur {α β:Type*} [H1:has_add α] [H2:has_add β] (f:α → β):(is_add_hom f)
  → (function.surjective f) →
  (∀ a1 a2:α, a1 + a2 = a2 + a1)  →
  (∀ b1 b2:β, b1 + b2 = b2 + b1)   :=
begin
  intros A1 A2 A3 b1 b2,
  have A4:∃a1, f a1 = b1 := A2 b1,
  cases A4 with a1 A5,
  have A6:∃a2, f a2  = b2 := A2 b2,
  cases A6 with a2 A7,
  rw ← A5,
  rw ← A7,
  rw ← A1.map_add,
  rw ← A1.map_add,
  rw A3 a1 a2,
end

lemma mul_comm_of_is_mul_hom_of_sur {α β:Type*} [H1:has_mul α] [H2:has_mul β] (f:α → β):(is_mul_hom f)
  → (function.surjective f) →
  (∀ a1 a2:α, a1 * a2 = a2 * a1)  →
  (∀ b1 b2:β, b1 * b2 = b2 * b1)   :=
begin
  intros A1 A2 A3 b1 b2,
  have A4:∃a1, f a1 = b1 := A2 b1,
  cases A4 with a1 A5,
  have A6:∃a2, f a2  = b2 := A2 b2,
  cases A6 with a2 A7,
  rw ← A5,
  rw ← A7,
  rw ← A1.map_mul,
  rw ← A1.map_mul,
  rw A3 a1 a2,
end

lemma add_assoc_of_is_add_hom_of_sur {α β:Type*} [H1:has_add α] [H2:has_add β] (f:α → β):(is_add_hom f)
  → (function.surjective f) →
  (∀ a1 a2 a3:α, a1 + a2 + a3 = a1 + (a2 + a3))  →
  (∀ b1 b2 b3:β, b1 + b2 + b3 = b1 + (b2 + b3))   :=
begin
  intros A1 A2 A3 b1 b2 b3,
  have A4:∃a1, f a1 = b1 := A2 b1,
  cases A4 with a1 A5,
  have A6:∃a2, f a2  = b2 := A2 b2,
  cases A6 with a2 A7,
  have A8:∃a3, f a3  = b3 := A2 b3,
  cases A8 with a3 A9,
  rw ← A5,
  rw ← A7,
  rw ← A9,
  rw ← A1.map_add,
  rw ← A1.map_add,
  rw ← A1.map_add,
  rw ← A1.map_add,
  rw A3 a1 a2 a3,
end


lemma mul_assoc_of_is_mul_hom_of_sur {α β:Type*} [H1:has_mul α] [H2:has_mul β] (f:α → β):(is_mul_hom f)
  → (function.surjective f) →
  (∀ a1 a2 a3:α, a1 * a2 * a3 = a1 * (a2 * a3))  →
  (∀ b1 b2 b3:β, b1 * b2 * b3 = b1 * (b2 * b3))   :=
begin
  intros A1 A2 A3 b1 b2 b3,
  have A4:∃a1, f a1 = b1 := A2 b1,
  cases A4 with a1 A5,
  have A6:∃a2, f a2  = b2 := A2 b2,
  cases A6 with a2 A7,
  have A8:∃a3, f a3  = b3 := A2 b3,
  cases A8 with a3 A9,
  rw ← A5,
  rw ← A7,
  rw ← A9,
  rw ← A1.map_mul,
  rw ← A1.map_mul,
  rw ← A1.map_mul,
  rw ← A1.map_mul,
  rw A3 a1 a2 a3,
end


lemma add_zero_of_is_add_hom_of_sur {α β:Type*} [HAα:has_add α] [HZα:has_zero α] [HAβ:has_add β] [HZβ:has_zero β] (f:α → β):(is_add_hom f)
  → (function.surjective f) →
  (f 0 = 0) → 
  (∀ a:α, a + 0 = a)  →
  (∀ b:β, b + 0 = b) :=
begin
  intros A1 A2 A3 A4 b,
  have A5:∃a, f a = b := A2 b,
  cases A5 with a A6,
  rw ← A6,
  rw ← A3,
  rw ← A1.map_add,
  rw A4 a,
end


lemma mul_one_of_is_mul_hom_of_sur {α β:Type*} [HAα:has_mul α] [HZα:has_one α] [HAβ:has_mul β] [HZβ:has_one β] (f:α → β):(is_mul_hom f)
  → (function.surjective f) →
  (f 1 = 1) → 
  (∀ a:α, a * 1 = a)  →
  (∀ b:β, b * 1 = b) :=
begin
  intros A1 A2 A3 A4 b,
  have A5:∃a, f a = b := A2 b,
  cases A5 with a A6,
  rw ← A6,
  rw ← A3,
  rw ← A1.map_mul,
  rw A4 a,
end


lemma mul_zero_of_is_mul_hom_of_sur {α β:Type*} [HAα:has_mul α] [HZα:has_zero α] [HAβ:has_mul β] [HZβ:has_zero β] (f:α → β):(is_mul_hom f)
  → (function.surjective f) →
  (f 0 = 0) → 
  (∀ a:α, a * 0 = 0)  →
  (∀ b:β, b * 0 = 0) :=
begin
  intros A1 A2 A3 A4 b,
  have A5:∃a, f a = b := A2 b,
  cases A5 with a A6,
  rw ← A6,
  rw ← A3,
  rw ← A1.map_mul,
  rw A4 a,
end

lemma zero_add_of_is_add_hom_of_sur {α β:Type*} [HAα:has_add α] [HZα:has_zero α] [HAβ:has_add β] [HZβ:has_zero β] (f:α → β):(is_add_hom f)
  → (function.surjective f) →
  (f 0 = 0) → 
  (∀ a:α, 0 + a = a)  →
  (∀ b:β, 0 + b = b) :=
begin
  intros A1 A2 A3 A4 b,
  have A5:∃a, f a = b := A2 b,
  cases A5 with a A6,
  rw ← A6,
  rw ← A3,
  rw ← A1.map_add,
  rw A4 a,
end

lemma one_mul_of_is_mul_hom_of_sur {α β:Type*} [HAα:has_mul α] [HZα:has_one α] [HAβ:has_mul β] [HZβ:has_one β] (f:α → β):(is_mul_hom f)
  → (function.surjective f) →
  (f 1 = 1) → 
  (∀ a:α, 1 * a = a)  →
  (∀ b:β, 1 * b = b) :=
begin
  intros A1 A2 A3 A4 b,
  have A5:∃a, f a = b := A2 b,
  cases A5 with a A6,
  rw ← A6,
  rw ← A3,
  rw ← A1.map_mul,
  rw A4 a,
end

lemma zero_mul_of_is_mul_hom_of_sur {α β:Type*} [HAα:has_mul α] [HZα:has_zero α] [HAβ:has_mul β] [HZβ:has_zero β] (f:α → β):(is_mul_hom f)
  → (function.surjective f) →
  (f 0 = 0) → 
  (∀ a:α, 0 * a = 0)  →
  (∀ b:β, 0 * b = 0) :=
begin
  intros A1 A2 A3 A4 b,
  have A5:∃a, f a = b := A2 b,
  cases A5 with a A6,
  rw ← A6,
  rw ← A3,
  rw ← A1.map_mul,
  rw A4 a,
end


lemma add_semigroup_of_is_add_hom_of_sur {α β:Type*} [AM:add_semigroup α] [HAβ:has_add β] (f:α → β) (IAH:is_add_hom f)
  (S:function.surjective f):add_semigroup β := {
  add := HAβ.add,
  add_assoc := @add_assoc_of_is_add_hom_of_sur α β _ HAβ f IAH S (@add_semigroup.add_assoc α AM),
}


set_option pp.implicit true
lemma add_monoid_of_is_add_hom_of_sur {α β:Type*} [AM:add_monoid α] [HAβ:has_add β] [HZβ:has_zero β] (f:α → β) (IAH:is_add_hom f)
  (S:function.surjective f) (HMZ:f 0 = 0):add_monoid β := {
  zero := HZβ.zero,
  add := HAβ.add,
  zero_add := @zero_add_of_is_add_hom_of_sur α β _ _ HAβ HZβ f IAH S HMZ add_monoid.zero_add,
  add_zero := @add_zero_of_is_add_hom_of_sur α β _ _ HAβ HZβ f IAH S HMZ (@add_monoid.add_zero α AM),
  add_assoc := @add_assoc_of_is_add_hom_of_sur α β _ HAβ f IAH S (@add_monoid.add_assoc α AM),
}


lemma semigroup_of_is_mul_hom_of_sur {α β:Type*} [AM:semigroup α] [HMβ:has_mul β] (f:α → β) (IAH:is_mul_hom f)
  (S:function.surjective f):semigroup β := {
  mul := HMβ.mul,
  mul_assoc := @mul_assoc_of_is_mul_hom_of_sur α β _ HMβ f IAH S (@semigroup.mul_assoc α AM),
}

lemma monoid_of_is_mul_hom_of_sur {α β:Type*} [M:monoid α] [HMβ:has_mul β] [HOβ:has_one β] (f:α → β) (IMH:is_mul_hom f)
  (S:function.surjective f) (HMO:f 1 = 1):monoid β := {
  one := HOβ.one,
  mul := HMβ.mul,
  one_mul := @one_mul_of_is_mul_hom_of_sur α β _ _ HMβ HOβ f IMH S HMO monoid.one_mul,
  mul_one := @mul_one_of_is_mul_hom_of_sur α β _ _ HMβ HOβ f IMH S HMO (@monoid.mul_one α M),
  mul_assoc := @mul_assoc_of_is_mul_hom_of_sur α β _ HMβ f IMH S (@monoid.mul_assoc α M),
}

lemma comm_monoid_of_is_mul_hom_of_sur {α β:Type*} [M:comm_monoid α] [HMβ:has_mul β] [HOβ:has_one β] (f:α → β) (IMH:is_mul_hom f)
  (S:function.surjective f) (HMO:f 1 = 1):comm_monoid β := {
  mul := HMβ.mul,
  mul_comm := @mul_comm_of_is_mul_hom_of_sur α β _ _ f IMH S comm_monoid.mul_comm,
  one := HOβ.one,
  one_mul := @one_mul_of_is_mul_hom_of_sur α β _ _ HMβ HOβ f IMH S HMO monoid.one_mul,
  mul_one := @mul_one_of_is_mul_hom_of_sur α β _ _ HMβ HOβ f IMH S HMO (@comm_monoid.mul_one α M),
  mul_assoc := @mul_assoc_of_is_mul_hom_of_sur α β _ HMβ f IMH S (@comm_monoid.mul_assoc α M),
}

lemma add_left_neg_of_is_hom_of_sur {α β:Type*} [AGα:add_group α] [HAβ:has_add β] [HNβ:has_neg β] [HZβ:has_zero β] (f:α → β): 
    (is_add_hom f)→ (is_neg_hom f)→ (function.surjective f)→ (f 0 = 0) →
(∀ x:α, (-x) + x = 0 )→ 
(∀ x:β, (-x) + x = 0 ) :=
begin
  intros A1 A2 A3 A4 A5 x,
  cases (A3 x) with a A6,
  rw ← A6,
  rw ← A2.map_neg,
  rw ← A1.map_add,
  rw ← A4,
  rw A5,
end


def add_group_of_is_hom_of_sur {α β:Type*} [AGα:add_group α] [HAβ:has_add β] [HNβ:has_neg β] [HZβ:has_zero β] (f:α → β) 
    (IAH:is_add_hom f) (INH:is_neg_hom f) (S:function.surjective f) (HMZ:f 0 = 0):add_group β := {
  neg := HNβ.neg,
  zero := HZβ.zero,
  add := HAβ.add,
  add_left_neg := @add_left_neg_of_is_hom_of_sur α β _ _ _ _ f IAH INH S HMZ AGα.add_left_neg,
  add_assoc := @add_assoc_of_is_add_hom_of_sur α β _ HAβ f IAH S (@add_monoid.add_assoc α _),
  add_zero := @add_zero_of_is_add_hom_of_sur α β _ _ HAβ HZβ f IAH S HMZ (@add_monoid.add_zero α _),
  zero_add := @zero_add_of_is_add_hom_of_sur α β _ _ HAβ HZβ f IAH S HMZ add_monoid.zero_add,
  ..(add_monoid_of_is_add_hom_of_sur f IAH S HMZ),
}

def add_comm_group_of_is_hom_of_sur {α β:Type*} [ACGα:add_comm_group α] [HAβ:has_add β] [HNβ:has_neg β] [HZβ:has_zero β] (f:α → β) 
    (IAH:is_add_hom f) (INH:is_neg_hom f) (I:function.surjective f) (HZM:f 0 = 0):add_comm_group β := {
  add := HAβ.add,
  add_comm := @add_comm_of_is_add_hom_of_sur α β _ _ f IAH I ACGα.add_comm,
  ..(add_group_of_is_hom_of_sur f IAH INH I HZM),
}


def add_comm_monoid_of_is_add_hom_of_sur {α β:Type*} [HAβ:has_add β] [HZβ:has_zero β] [ACMα:add_comm_monoid α] (f:α → β) 
    (IAH:is_add_hom f) (S:function.surjective f) (HZM:f 0 = 0):add_comm_monoid β := {
  add := HAβ.add,
  zero := HZβ.zero,
  add_comm := @add_comm_of_is_add_hom_of_sur α β _ _ f IAH S add_comm_monoid.add_comm,
  add_assoc := @add_assoc_of_is_add_hom_of_sur α β _ HAβ f IAH S (@add_monoid.add_assoc α _),
  add_zero := @add_zero_of_is_add_hom_of_sur α β _ _ HAβ HZβ f IAH S HZM (@add_monoid.add_zero α _),
  zero_add := @zero_add_of_is_add_hom_of_sur α β _ _ HAβ HZβ f IAH S HZM (@add_monoid.zero_add α _),
}

lemma left_distrib_of_is_hom_of_sur {α β:Type*} [Rα:distrib α] [HAβ:has_add β] [HMβ:has_mul β] (f:α → β):
   (is_add_hom f) → 
   (is_mul_hom f) →
   (function.surjective f) →
   (∀ a b c:β,  a * (b + c) = a * b + a * c) :=
begin
  intros A1 A2 A3 a b c,
  cases (A3 a) with a2 A4,
  cases (A3 b) with b2 A5,
  cases (A3 c) with c2 A6,
  rw ← A4,
  rw ← A5,
  rw ← A6,
  rw ← A2.map_mul,
  rw ← A1.map_add,
  rw ← A2.map_mul,
  rw ← A2.map_mul,
  rw ← A1.map_add,
  rw distrib.left_distrib,
  refl,
end

lemma right_distrib_of_is_hom_of_sur {α β:Type*} [Rα:distrib α] [HAβ:has_add β] [HMβ:has_mul β] (f:α → β):
   (is_add_hom f) → 
   (is_mul_hom f) →
   (function.surjective f) →
   (∀ a b c:β,  (a + b)  * c = a * c + b * c) :=
begin
  intros A1 A2 A3 a b c,
  cases (A3 a) with a2 A4,
  cases (A3 b) with b2 A5,
  cases (A3 c) with c2 A6,
  rw ← A4,
  rw ← A5,
  rw ← A6,
  rw ← A2.map_mul,
  rw ← A1.map_add,
  rw ← A2.map_mul,
  rw ← A2.map_mul,
  rw ← A1.map_add,
  rw distrib.right_distrib,
  refl,
end

def distrib_of_is_hom_of_sur {α β:Type*} [Dα:distrib α] [HAβ:has_add β] [HMβ:has_mul β] (f:α → β)
   (IAH:is_add_hom f) 
   (IMH:is_mul_hom f)
   (S:function.surjective f):distrib β := {
  mul := HMβ.mul,
  add := HAβ.add,
  left_distrib := @left_distrib_of_is_hom_of_sur α β _ _ _ f IAH IMH S,
  right_distrib := @right_distrib_of_is_hom_of_sur α β _ _ _ f IAH IMH S,
}




def comm_semiring_of_is_hom_of_sur {α β:Type*} [CRα:comm_semiring α] [HAβ:has_add β] [HZβ:has_zero β] [HOβ:has_one β] [HMβ:has_mul β] (f:α → β) 
    (IAH:is_add_hom f) (IMH:is_mul_hom f) (S:function.surjective f) (HZM:f 0 = 0) (HOM:f 1 = 1):comm_semiring β := {
  add := HAβ.add,
  mul := HMβ.mul,
  --add_comm := add_comm_of_is_add_hom_of_sur f IAH S CRα.add_comm,
  left_distrib := @left_distrib_of_is_hom_of_sur α β _ _ _ f IAH IMH S,
  right_distrib := @right_distrib_of_is_hom_of_sur α β _ _ _ f IAH IMH S,
  mul_comm := @mul_comm_of_is_mul_hom_of_sur α β _ _ f IMH S comm_monoid.mul_comm,
  one := HOβ.one,
  one_mul := @one_mul_of_is_mul_hom_of_sur α β _ _ HMβ HOβ f IMH S HOM monoid.one_mul,
  mul_one := @mul_one_of_is_mul_hom_of_sur α β _ _ HMβ HOβ f IMH S HOM (@comm_monoid.mul_one α _),
  mul_assoc := @mul_assoc_of_is_mul_hom_of_sur α β _ HMβ f IMH S (@comm_monoid.mul_assoc α _),
  zero_mul := @zero_mul_of_is_mul_hom_of_sur α β _ _ HMβ HZβ f IMH S HZM (@comm_semiring.zero_mul α _),
  mul_zero := @mul_zero_of_is_mul_hom_of_sur α β _ _ HMβ HZβ f IMH S HZM (@comm_semiring.mul_zero α _),
  ..(add_comm_monoid_of_is_add_hom_of_sur f IAH S HZM),
}

def comm_ring_of_is_hom_of_sur {α β:Type*} [CRα:comm_ring α] [HAβ:has_add β] [HZβ:has_zero β] [HOβ:has_one β] [HNβ:has_neg β] [HMβ:has_mul β] (f:α → β) 
    (IAH:is_add_hom f) (INH:is_neg_hom f) (IMH:is_mul_hom f) (S:function.surjective f) (HZM:f 0 = 0) (HOM:f 1 = 1):comm_ring β := {
  add := HAβ.add,
  mul := HMβ.mul,
  --add_comm := add_comm_of_is_add_hom_of_sur f IAH S CRα.add_comm,
  left_distrib := @left_distrib_of_is_hom_of_sur α β _ _ _ f IAH IMH S,
  right_distrib := @right_distrib_of_is_hom_of_sur α β _ _ _ f IAH IMH S,
  mul_comm := @mul_comm_of_is_mul_hom_of_sur α β _ _ f IMH S comm_monoid.mul_comm,
  one := HOβ.one,
  one_mul := @one_mul_of_is_mul_hom_of_sur α β _ _ HMβ HOβ f IMH S HOM monoid.one_mul,
  mul_one := @mul_one_of_is_mul_hom_of_sur α β _ _ HMβ HOβ f IMH S HOM (@comm_monoid.mul_one α _),
  mul_assoc := @mul_assoc_of_is_mul_hom_of_sur α β _ HMβ f IMH S (@comm_monoid.mul_assoc α _),
  ..(add_comm_group_of_is_hom_of_sur f IAH INH S HZM),
}

/-
  In hindsight, these injective homomorphisms are all that is needed. We could rewrite some of the proofs below
  to leverage the proofs above.
-/

lemma equiv_flip {α β:Type*} {E:equiv α β} {a:α} {b:β}:
(E.to_fun a = b) ↔ (E.inv_fun b = a) :=
begin
  split;intros A1;rw ← A1,
  {
    rw E.left_inv,
  },
  {
    rw E.right_inv,
  },
end

lemma equiv_rev_to_fun {α β:Type*} {E:equiv α β} {a:α} {b:β}:
(E.to_fun a = b) → (E.symm.to_fun b = a) :=
begin
  intro A0,
  have A1:E.to_fun = E.symm.inv_fun := rfl,
  have A2:E.symm.inv_fun a = b,
  {
    rw ← A1,
    apply A0,
  },
  rw ← equiv_flip at A2,
  apply A2,
end


lemma mul_equiv_rev_to_fun {α β:Type*} [has_mul α] [has_mul β] {E:mul_equiv α β} {a:α} {b:β}:
(E.to_fun a = b) → (E.symm.to_fun b = a) :=
begin
  have A1:E.to_fun = E.to_equiv.to_fun := rfl,
  have A2:E.symm.to_fun = E.symm.to_equiv.to_fun := rfl,
  rw A1,
  rw A2,
  have A3:E.symm.to_equiv = E.to_equiv.symm := rfl,
  rw A3,
  apply equiv_rev_to_fun,
end


lemma mul_assoc_equiv {α β:Type*} [semigroup α] [has_mul β] 
  {E:mul_equiv α β}(a b c:β) :a * b * c = a * (b * c) :=
begin
  have A1:(E.to_fun (E.inv_fun a)) = a := E.right_inv a,
  have A2:(E.to_fun (E.inv_fun b)) = b := E.right_inv b,
  have A3:(E.to_fun (E.inv_fun c)) = c := E.right_inv c,
  rw ← A1,
  rw ← A2,
  rw ← A3,
  rw ← E.map_mul',
  rw ← E.map_mul',
  rw mul_assoc,
  rw ← E.map_mul',
  rw ← E.map_mul',
end


/-
  Note that we must explicitly identify the that one maps to one,
  because before we say a class is a monoid, we can label anything 1.
-/
lemma one_mul_equiv {α β:Type*} [monoid α] [has_mul β] [has_one β]
{E:mul_equiv α β} (H:E.to_fun 1 = 1) (b:β):1 * b = b :=
begin
  have A1:(E.to_fun (E.inv_fun b)) = b := E.right_inv b,
  have A2:(E.to_fun 1) * E.to_fun (E.inv_fun b) = b,
  {
    rw ← E.map_mul',
    rw one_mul,
    rw E.right_inv,
  },
  rw H at A2,
  rw A1 at A2,
  apply A2,
end

lemma one_mul_equiv_rev {α β:Type*} [monoid β] [has_mul α] [has_one α]
{E:mul_equiv α β} (H:E.to_fun 1 = 1) (b:α):1 * b = b :=
  @one_mul_equiv β α _ _ _ E.symm (@mul_equiv_rev_to_fun α β _ _ E 1 1 H) b


lemma mul_one_equiv {α β:Type*} [monoid α] [has_mul β] [has_one β]
{E:mul_equiv α β} (H:E.to_fun 1 = 1) (b:β):b * 1 = b :=
begin
  have A1:(E.to_fun (E.inv_fun b)) = b := E.right_inv b,
  have A2:E.to_fun (E.inv_fun b) * (E.to_fun 1) = b,
  {
    rw ← E.map_mul',
    rw mul_one,
    rw E.right_inv,
  },
  rw H at A2,
  rw A1 at A2,
  apply A2,
end


lemma mul_one_equiv_rev {α β:Type*} [monoid β] [has_mul α] [has_one α]
{E:mul_equiv α β} (H:E.to_fun 1 = 1) (b:α):b * 1 = b :=
  @mul_one_equiv β α _ _ _ E.symm (@mul_equiv_rev_to_fun α β _ _ E 1 1 H) b


--Create a monoid through an equivalence relation.
def monoid_equiv {α β:Type*} [Mα:monoid α] [HMβ:has_mul β] [HOβ:has_one β]
{E:mul_equiv α β} (H:E.to_fun 1 = 1):monoid β := {
  mul:=HMβ.mul,
  one:=HOβ.one,
  mul_one:=@mul_one_equiv α β Mα HMβ HOβ E H,
  one_mul:=@one_mul_equiv α β Mα HMβ HOβ E H,
  mul_assoc:=@mul_assoc_equiv α β (monoid.to_semigroup α) HMβ E,
}

def monoid_equiv_rev {α β:Type*} [Mβ:monoid β] [HMα:has_mul α] [HOα:has_one α]
{E:mul_equiv α β} (H:E.to_fun 1 = 1):monoid α := {
  mul:=HMα.mul,
  one:=HOα.one,
  mul_one:=@mul_one_equiv_rev α β Mβ HMα HOα E H,
  one_mul:=@one_mul_equiv_rev α β Mβ HMα HOα E H,
  mul_assoc:=@mul_assoc_equiv β α _ HMα E.symm,
}


lemma add_assoc_equiv {α β:Type*} [add_semigroup α] [has_add β] 
  {E:add_equiv α β}(a b c:β) :a + b + c = a + (b + c) :=
begin
  have A1:(E.to_fun (E.inv_fun a)) = a := E.right_inv a,
  have A2:(E.to_fun (E.inv_fun b)) = b := E.right_inv b,
  have A3:(E.to_fun (E.inv_fun c)) = c := E.right_inv c,
  rw ← A1,
  rw ← A2,
  rw ← A3,
  rw ← E.map_add',
  rw ← E.map_add',
  rw add_assoc,
  rw ← E.map_add',
  rw ← E.map_add',
end

lemma add_equiv_rev_to_fun {α β:Type*} [has_add α] [has_add β] {E:add_equiv α β} {a:α} {b:β}:
(E.to_fun a = b) → (E.symm.to_fun b = a) :=
begin
  have A1:E.to_fun = E.to_equiv.to_fun := rfl,
  have A2:E.symm.to_fun = E.symm.to_equiv.to_fun := rfl,
  rw A1,
  rw A2,
  have A3:E.symm.to_equiv = E.to_equiv.symm := rfl,
  rw A3,
  apply equiv_rev_to_fun,
end

lemma zero_add_equiv {α β:Type*} [add_monoid α] [has_add β] [has_zero β]
{E:add_equiv α β} (H:E.to_fun 0 = 0) (b:β):0 + b = b :=
begin
  have A1:(E.to_fun (E.inv_fun b)) = b := E.right_inv b,
  have A2:(E.to_fun 0) + E.to_fun (E.inv_fun b) = b,
  {
    rw ← E.map_add',
    rw zero_add,
    rw E.right_inv,
  },
  rw H at A2,
  rw A1 at A2,
  apply A2,
end

lemma zero_add_equiv_rev {α β:Type*} [add_monoid β] [has_add α] [has_zero α]
{E:add_equiv α β} (H:E.to_fun 0 = 0) (b:α):0 + b = b :=
  @zero_add_equiv β α _ _ _ E.symm (@add_equiv_rev_to_fun α β _ _ E 0 0 H) b

lemma add_zero_equiv {α β:Type*} [add_monoid α] [has_add β] [has_zero β]
{E:add_equiv α β} (H:E.to_fun 0 = 0) (b:β):b + 0 = b :=
begin
  have A1:(E.to_fun (E.inv_fun b)) = b := E.right_inv b,
  have A2:E.to_fun (E.inv_fun b) + (E.to_fun 0) = b,
  {
    rw ← E.map_add',
    rw add_zero,
    rw E.right_inv,
  },
  rw H at A2,
  rw A1 at A2,
  apply A2,
end

lemma add_zero_equiv_rev {α β:Type*} [add_monoid β] [has_add α] [has_zero α]
{E:add_equiv α β} (H:E.to_fun 0 = 0) (b:α):b + 0 = b :=
  @add_zero_equiv β α _ _ _ E.symm (@add_equiv_rev_to_fun α β _ _ E 0 0 H) b



--Create a monoid through an equivalence relation.
def add_monoid_equiv {α β:Type*} [Mα:add_monoid α] [HAβ:has_add β] [HZβ:has_zero β]
{E:add_equiv α β} (H:E.to_fun 0 = 0):add_monoid β := {
  add:=HAβ.add,
  zero:=HZβ.zero,
  add_zero:=@add_zero_equiv α β Mα HAβ HZβ E H,
  zero_add:=@zero_add_equiv α β Mα HAβ HZβ E H,
  add_assoc:=@add_assoc_equiv α β (add_monoid.to_add_semigroup α) HAβ E,
}

def add_monoid_equiv_rev {α β:Type*} [Mβ:add_monoid β] [HAα:has_add α] [HZα:has_zero α]
{E:add_equiv α β} (H:E.to_fun 0 = 0):add_monoid α :=
  @add_monoid_equiv β α Mβ HAα HZα E.symm (@add_equiv_rev_to_fun α β _ _ E 0 0 H)


lemma add_comm_equiv {α β:Type*} [add_comm_monoid α] [has_add β] [has_zero β]
{E:add_equiv α β} (a b:β):a + b = b + a :=
begin
  rw ← E.right_inv a,
  rw ← E.right_inv b,
  rw ← E.map_add',
  rw ← E.map_add',
  rw add_comm,
end

def add_comm_monoid_equiv {α β:Type*} [Mα:add_comm_monoid α] [HAβ:has_add β] [HZβ:has_zero β]
{E:add_equiv α β} (H:E.to_fun 0 = 0):add_comm_monoid β := {
  add:=HAβ.add,
  zero:=HZβ.zero,
  add_zero:=@add_zero_equiv α β _ HAβ HZβ E H,
  zero_add:=@zero_add_equiv α β _ HAβ HZβ E H,
  add_assoc:=@add_assoc_equiv α β _ HAβ E,
  add_comm:=@add_comm_equiv α β _ HAβ HZβ E,
}

def add_comm_monoid_equiv_rev {α β:Type*} [Mβ:add_comm_monoid β] [HAα:has_add α] [HZα:has_zero α]
{E:add_equiv α β} (H:E.to_fun 0 = 0):add_comm_monoid α :=
  @add_comm_monoid_equiv β α Mβ HAα HZα E.symm (@add_equiv_rev_to_fun α β _ _ E 0 0 H)


lemma mul_comm_equiv {α β:Type*} [comm_semigroup α] [has_mul β]
{E:mul_equiv α β} (a b:β):a * b = b * a :=
begin
  rw ← E.right_inv a,
  rw ← E.right_inv b,
  rw ← E.map_mul',
  rw ← E.map_mul',
  rw mul_comm,
end


lemma mul_zero_equiv {α β:Type*} [Mα:semiring α] [HZβ:has_zero β]
  [HMβ:has_mul β] {E:mul_equiv α β} (MZ:E.to_fun 0 = 0)
  (b:β):b * 0 = 0 :=
begin
  have A1:(E.to_fun (E.inv_fun b)) * (E.to_fun 0) = 0,
  {
    rw ← E.map_mul',
    rw mul_zero,
    rw MZ,    
  },
  rw (E.right_inv b) at A1,
  rw MZ at A1,
  apply A1,
end


lemma left_distrib_equiv {α β:Type*} [Mα:semiring α] [HAβ:has_add β]
  [HMβ:has_mul β] {E:ring_equiv α β}
  (a b c:β):a * (b + c) = a * b + a * c :=
begin
  rw ← E.right_inv a,
  rw ← E.right_inv b,
  rw ← E.right_inv c,
  rw ← E.map_add',
  rw ← E.map_mul',
  rw ← E.map_mul',
  rw ← E.map_mul',
  rw ← E.map_add',
  rw left_distrib,
end


lemma right_distrib_equiv {α β:Type*} [Mα:semiring α] [HAβ:has_add β]
  [HMβ:has_mul β] {E:ring_equiv α β}
  (a b c:β):(a + b) * c = a * c + b * c :=
begin
  rw ← E.right_inv a,
  rw ← E.right_inv b,
  rw ← E.right_inv c,
  rw ← E.map_add',
  rw ← E.map_mul',
  rw ← E.map_mul',
  rw ← E.map_mul',
  rw ← E.map_add',
  rw right_distrib,
end

lemma zero_mul_equiv {α β:Type*} [Mα:semiring α] [HZβ:has_zero β]
  [HMβ:has_mul β] {E:mul_equiv α β} (MZ:E.to_fun 0 = 0)
  (b:β):0 * b = 0 :=
begin
  have A1:(E.to_fun 0) * (E.to_fun (E.inv_fun b)) = 0,
  {
    rw ← E.map_mul',
    rw zero_mul,
    rw MZ,
  },
  rw (E.right_inv b) at A1,
  rw MZ at A1,
  apply A1,
end


def semiring_equiv {α β:Type*} [Mα:semiring α] [HAβ:has_add β] [HZβ:has_zero β]
  [HMβ:has_mul β] [HOβ:has_one β] {E:ring_equiv α β} (MZ:E.to_fun 0 = 0)
  (MO:E.to_fun 1 = 1):semiring β := {
  add:=HAβ.add,
  zero:=HZβ.zero,
  mul:=HMβ.mul,
  one:=HOβ.one,
  add_zero:=@add_zero_equiv α β (add_comm_monoid.to_add_monoid α) HAβ HZβ E MZ,
  zero_add:=@zero_add_equiv α β (add_comm_monoid.to_add_monoid α) HAβ HZβ E MZ,
  add_assoc:=@add_assoc_equiv α β _ HAβ E,
  mul_one:=@mul_one_equiv α β _ HMβ HOβ E MO,
  one_mul:=@one_mul_equiv α β _ HMβ HOβ E MO,
  mul_assoc:=@mul_assoc_equiv α β (monoid.to_semigroup α) HMβ E,
  zero_mul:=@zero_mul_equiv α β Mα HZβ HMβ (E.to_mul_equiv) MZ,
  add_comm:=@add_comm_equiv α β _ HAβ HZβ E,
  mul_zero:=@mul_zero_equiv α β Mα HZβ HMβ (E.to_mul_equiv) MZ,
  left_distrib:=@left_distrib_equiv α β Mα HAβ HMβ E,
  right_distrib:=@right_distrib_equiv α β Mα HAβ HMβ E,
}

def comm_semiring_equiv {α β:Type*} [Mα:comm_semiring α] [HAβ:has_add β] [HZβ:has_zero β]
  [HMβ:has_mul β] [HOβ:has_one β] {E:ring_equiv α β} (MZ:E.to_fun 0 = 0)
  (MO:E.to_fun 1 = 1):comm_semiring β := {
  mul_comm:=@mul_comm_equiv α β _ HMβ E,
  ..(@semiring_equiv α β _ HAβ HZβ HMβ HOβ E MZ MO),
}

lemma ring_equiv_rev_to_fun {α β:Type*} [has_add α] [has_add β] [has_mul α] [has_mul β] {E:ring_equiv α β} {a:α} {b:β}:
(E.to_fun a = b) → (E.symm.to_fun b = a) :=
begin
  have A1:E.to_fun = E.to_equiv.to_fun := rfl,
  have A2:E.symm.to_fun = E.symm.to_equiv.to_fun := rfl,
  rw A1,
  rw A2,
  have A3:E.symm.to_equiv = E.to_equiv.symm := rfl,
  rw A3,
  apply equiv_rev_to_fun,
end

def semiring_equiv_rev {α β:Type*} [Mβ:semiring β] [HAα:has_add α] [HZα:has_zero α] 
    [HMα:has_mul α] [HOα:has_one α] {E:ring_equiv α β} (HZ:E.to_fun 0 = 0) (HO:E.to_fun 1 = 1):semiring α :=
    @semiring_equiv β α Mβ HAα HZα HMα HOα E.symm (@ring_equiv_rev_to_fun α β _ _ _ _ E 0 0 HZ) (@ring_equiv_rev_to_fun α β _ _ _ _ E 1 1 HO)

def comm_semiring_equiv_rev {α β:Type*} [Mβ:comm_semiring β] [HAα:has_add α] [HZα:has_zero α] 
    [HMα:has_mul α] [HOα:has_one α] {E:ring_equiv α β} (HZ:E.to_fun 0 = 0) (HO:E.to_fun 1 = 1):comm_semiring α :=
    @comm_semiring_equiv β α Mβ HAα HZα HMα HOα E.symm (@ring_equiv_rev_to_fun α β _ _ _ _ E 0 0 HZ) (@ring_equiv_rev_to_fun α β _ _ _ _ E 1 1 HO)
