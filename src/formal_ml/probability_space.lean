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
import formal_ml.nnreal
import formal_ml.sum
import formal_ml.measurable_space
import formal_ml.classical

----------------------------------------------------------------------------------------------------


/-
  A probability measure is a non-negative measure that sums to one over the universe.
  This is no longer used. In Wikipedia, a probability measure is defined to be over a probability
  space, which would make this of limited value.
-/
structure probability_measure (α : Type*) [measurable_space α] extends measure_theory.measure α :=
  (univ_one:measure_of (set.univ) = 1)


class probability_space (α: Type*) extends measure_theory.measure_space α :=
  (univ_one:volume.measure_of (set.univ) = 1) 


instance probability_space.to_measurable_space (α:Type*) [probability_space α]:measurable_space α :=
  measure_theory.measure_space.to_measurable_space

--instance probability_space_to_measurable_space {α:Type*} [

/-
  In measure theory (and specifically, in probability theory), not all sets of outcomes have
  probabilities that can be measured. We represent those that can be measured as measurable
  sets.
-/
def measurable_set {α:Type*} (M:measurable_space α):Type* := subtype (M.is_measurable)

def measurable_set.mk {α:Type*} {M:measurable_space α} {S:set α} (H:is_measurable S):measurable_set M := ⟨S, H⟩

lemma measurable_set_val_eq_coe {Ω:Type*} {P:measurable_space Ω}  
  (X:measurable_set P):X.val = 
  (@coe (subtype (@is_measurable Ω _)) (set Ω) _ X) :=
begin
  refl
end

/-
  A measurable set on a measurable space that has a probability measure is called an event.
-/
def event {Ω:Type*} (M:probability_space Ω):Type* := measurable_set (probability_space.to_measurable_space Ω)

lemma event_val_eq_coe {Ω:Type*} {P:probability_space Ω}  
  (X:event P):X.val = 
  (@coe (subtype (@is_measurable Ω _)) (set Ω) _ X) :=
begin
  refl
end


lemma event.eq {Ω:Type*} {P:probability_space Ω} (A B:event P):
A.val = B.val → A = B :=
begin
  intro A1,
  apply subtype.eq,
  exact A1
end

def event_mem {Ω:Type*} [P:probability_space Ω] (a:Ω) (E:event P):Prop :=
  a∈ E.val


instance {Ω:Type*} [P:probability_space Ω]:has_mem Ω (event P) := {
  mem := event_mem
}



lemma prob_le_1 {Ω:Type*} {P:probability_space Ω} (S:set Ω):
  P.volume.measure_of S ≤ 1 :=
begin
  have A1:P.volume.measure_of set.univ = 1,
  {
    apply P.univ_one,
  },
  have A2:S ⊆ set.univ,
  {
    simp,
  },
  have A3:P.volume.measure_of S ≤ P.volume.measure_of set.univ,
  {
    apply P.volume.mono,
    apply A2,
  },
  rw A1 at A3,
  exact A3,
end


/-
  There are a lot of long proofs here, but this one seems particularly roundabout.
-/
lemma prob_not_infinite {Ω:Type*} {P:probability_space Ω} (S:set Ω):
  (P.volume.measure_of S) ≠ ⊤ :=
begin
  have A1:P.volume.measure_of S ≤ 1,
  {
     apply prob_le_1,
  },
  intro A2,
  rw A2 at A1,
  have A3:(1:ennreal)=⊤,
  {
    apply complete_linear_order.le_antisymm,
    {
      apply (ennreal.complete_linear_order.le_top),
    },
    {
      apply A1,
    }
  },
  have A4:(1:ennreal) ≠ (⊤:ennreal),
  {
    apply ennreal.one_ne_top,
  },
  rw A3 at A4,
  apply A4,
  refl,
end

lemma prob_nnreal {Ω:Type*} {P:probability_space Ω} (S:set Ω):
   ↑((P.volume.measure_of S).to_nnreal) = P.volume.measure_of S :=
begin
  apply ennreal.coe_to_nnreal,
  apply prob_not_infinite,
end

def event_prob {Ω:Type*} {P:probability_space Ω} (E:event P):nnreal :=
  (P.volume.measure_of E.val).to_nnreal

notation `Pr[`E`]` := event_prob E

lemma event_prob_def {Ω:Type*} {p:probability_space Ω} (E:event p):
  ↑(Pr[E]) = (p.volume.measure_of E.val):=
begin
  unfold event_prob,
  apply prob_nnreal,
end


lemma to_nnreal_almost_monotonic (a b:ennreal):(a≠ ⊤)→(b≠⊤)→(a ≤ b)→ (a.to_nnreal ≤ b.to_nnreal) :=
begin
  intros A1 A2 A3,
  have A4:↑(a.to_nnreal)=a,
  {
    apply ennreal.coe_to_nnreal,
    apply A1,
  },
  have A5:↑(b.to_nnreal)=b,
  {
    apply ennreal.coe_to_nnreal,
    apply A2,
  },
  rw ← A4 at A3,
  rw ← A5 at A3,
  simp at A3,
  apply A3,
end

lemma to_ennreal_monotonic (a b:nnreal):(a ≤ b)→ ((a:ennreal) ≤ (b:ennreal)) :=
begin
  intro A1,
  simp,
  apply A1,
end

-- See ennreal.add_eq_top
lemma add_finite (a b:ennreal):(a≠ ⊤) → (b≠ ⊤) → (a + b≠ ⊤) :=
begin
  intros A1 A2 A3,
  rw ennreal.add_eq_top at A3,
  cases A3,
  {
    apply A1,
    apply A3,
  },
  {
    apply A2,
    apply A3,
  }
end


lemma event_prob_mono1 {Ω:Type*} {p:probability_space Ω} (E F:event p):
  p.volume.measure_of E.val ≤ p.volume.measure_of F.val →
  Pr[E] ≤ Pr[F] :=
begin
  unfold event_prob,
  intro A1,
  apply to_nnreal_almost_monotonic,
  apply prob_not_infinite,
  apply prob_not_infinite,
  apply A1,
end


lemma event_prob_mono2 {Ω:Type*} {p:probability_space Ω} (E F:event p):
  (E.val ⊆ F.val) →
  Pr[E] ≤ Pr[F] :=
begin
  intro A1,
  apply event_prob_mono1,
  apply p.volume.mono,
  apply A1,
end

def event_univ {Ω:Type*} {p:probability_space Ω}:event p := {
  val := set.univ,
  property := is_measurable.univ,
}

lemma event_univ_val_def {Ω:Type*} {p:probability_space Ω}:
  (@event_univ Ω p).val = set.univ :=
begin
  unfold event_univ,
end


lemma Pr_event_univ {Ω:Type*} {p:probability_space Ω}:
  Pr[@event_univ Ω p] = 1 :=
begin
  have A1:↑(Pr[@event_univ Ω p]) = (1:ennreal),
  {
    rw event_prob_def,
    apply p.univ_one,
  },
  simp at A1,
  apply A1
end

lemma Pr_event_le_1 {Ω:Type*} {p:probability_space Ω} {E:event p}:
  Pr[E] ≤ 1 :=
begin
  have A1:Pr[E] ≤ Pr[@event_univ Ω p],
  {
    apply event_prob_mono2,
    rw event_univ_val_def,
    rw set.subset_def,
    intros x A1A,
    simp,
  },
  rw Pr_event_univ at A1,
  apply A1,
end

def measurable_set_empty {Ω:Type*} {p:measurable_space Ω}:measurable_set p := {
  val := ∅,
  property := is_measurable.empty,
}

instance has_emptyc_measurable_set {Ω:Type*} {M:measurable_space Ω}:has_emptyc (measurable_set M) := ⟨ @measurable_set_empty Ω M ⟩



def event_empty {Ω:Type*} {p:probability_space Ω}:event p := 
  @measurable_set_empty Ω (probability_space.to_measurable_space Ω)

instance has_emptyc_event {Ω:Type*} {P:probability_space Ω}:has_emptyc (event P) := 
    ⟨ @event_empty Ω P ⟩

lemma has_emptyc_emptyc_event {Ω:Type*} {P:probability_space Ω}:
  ∅ = (@event_empty Ω P) :=  rfl


lemma event_empty_val_def {Ω:Type*} {p:probability_space Ω}:
  (@event_empty Ω p).val = ∅  := rfl

lemma event_empty_val_def2 {Ω:Type*} {p:probability_space Ω}:
  (@has_emptyc.emptyc (event p) _).val = ∅  :=  rfl


lemma Pr_event_empty {Ω:Type*} {p:probability_space Ω}:
  Pr[@event_empty Ω p] = 0 :=
begin
  have A1:↑(Pr[@event_empty Ω p]) = (0:ennreal),
  {
    rw event_prob_def,
    apply p.volume.empty,
  },
  simp at A1,
  apply A1
end


/-Since Pr[E] is a nnreal, this establishes that the probability is in the interval [0,1] -/
lemma event_prob_le_1 {Ω:Type*} {p:probability_space Ω} {E:event p}:
  Pr[E] ≤ 1 :=
begin
  have A1:Pr[@event_univ Ω p] = 1,
  {
    apply Pr_event_univ,
  },
  rw ← A1,
  apply event_prob_mono2,
  rw event_univ_val_def,
  simp,
end

def event_const {Ω:Type*} {p:probability_space Ω} (P:Prop):event p := {
  val := {ω:Ω|P},
  property := is_measurable.const P,
}

lemma event_const_val_def {Ω:Type*} {p:probability_space Ω} (P:Prop):
  (@event_const _ p P).val={ω:Ω|P} := rfl

lemma event_const_true_eq_univ {Ω:Type*} {p:probability_space Ω} (P:Prop):P →
(@event_const _ p P)=event_univ :=
begin
  intro A1,
  apply event.eq,
  rw event_univ_val_def,
  rw event_const_val_def,
  ext ω,split;intro A2,
  {
     simp,
  },
  {
     simp,
     exact A1,
  }
end

lemma event_const_false_eq_empty {Ω:Type*} {p:probability_space Ω} (P:Prop):¬P →
(@event_const _ p P)=event_empty :=
begin
  intro A1,
  apply event.eq,
  rw event_empty_val_def,
  rw event_const_val_def,
  ext ω,split;intro A2,
  {
     simp,
     apply A1,
     apply A2,
  },
  {
     simp,
     exfalso,
     apply A2,
  }
end

lemma Pr_event_const_true {Ω:Type*} {p:probability_space Ω} (P:Prop):P →
Pr[(@event_const _ p P)]=1 :=
begin
  intro A1,
  rw event_const_true_eq_univ,
  apply Pr_event_univ,
  exact A1,
end

lemma Pr_event_const_false {Ω:Type*} {p:probability_space Ω} (P:Prop):¬P →
Pr[(@event_const _ p P)]=0 :=
begin
  intro A1,
  rw event_const_false_eq_empty,
  apply Pr_event_empty,
  exact A1,
end



--The and of two events.


def measurable_inter {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set p):measurable_set p := {
  val:=A.val ∩ B.val,
  property := is_measurable.inter A.property B.property,
}

lemma measurable_inter_val_def {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set p):
  (measurable_inter A B).val= A.val ∩ B.val := rfl


def eand {Ω:Type*} {p:probability_space Ω} (A B:event p):event p := 
  measurable_inter A B

/-{
  val:=A.val ∩ B.val,
  property := is_measurable.inter A.property B.property,
}-/

infixr `∧ₑ`:100 := eand

lemma eand_val_def {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∧ₑ B).val = A.val ∩ B.val :=
begin
  refl,
end

lemma eand_comm {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∧ₑ B) = (B ∧ₑ A) :=
begin
  apply event.eq,
  rw eand_val_def,
  rw eand_val_def,
  apply set.inter_comm,
end

lemma eand_eq_self_of_subset_left {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A.val ⊆ B.val) →
  (A ∧ₑ B) = A :=
begin
  intro A1,
  apply event.eq,
  rw eand_val_def,
  apply set.inter_eq_self_of_subset_left,
  exact A1,
end

lemma eand_eq_self_of_subset_right {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (B.val ⊆ A.val) →
  (A ∧ₑ B) = B :=
begin
  intro A1,
  rw eand_comm,
  apply eand_eq_self_of_subset_left,
  exact A1,
end


lemma Pr_eand_le_left {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∧ₑ B]≤ Pr[A] :=
begin
  apply event_prob_mono2,
  rw eand_val_def,
  apply set.inter_subset_left,
end


lemma Pr_eand_le_right {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∧ₑ B]≤ Pr[B] :=
begin
  rw eand_comm,
  apply Pr_eand_le_left,
end


lemma Pr_eand_le_min {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∧ₑ B]≤ min Pr[A]  Pr[B] :=
begin
  apply le_min,
  {
    apply Pr_eand_le_left,
  },
  {
    apply Pr_eand_le_right,
  }
end


def measurable_union {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set p):measurable_set p := {
  val:=A.val ∪  B.val,
  property := is_measurable.union A.property B.property,
}

lemma measurable_union_val_def {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set p):
  (measurable_union A B).val=A.val ∪ B.val := rfl


def eor {Ω:Type*} {p:probability_space Ω} (A B:event p):event p := measurable_union A B
/-{
  val:=A.val ∪  B.val,
  property := is_measurable.union A.property B.property,
}-/

infixr `∨ₑ`:100 := eor

lemma eor_val_def {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∨ₑ B).val = A.val ∪ B.val :=
begin
  refl,
end

lemma eor_comm {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∨ₑ B) = (B ∨ₑ A) :=
begin
  apply event.eq,
  rw eor_val_def,
  rw eor_val_def,
  apply set.union_comm,
end


lemma Pr_le_eor_left {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A] ≤ Pr[A ∨ₑ B] :=
begin
  apply event_prob_mono2,
  rw eor_val_def,
  apply set.subset_union_left,
end

lemma Pr_le_eor_right {Ω:Type*} {p:probability_space Ω} (A B:event p):
   Pr[B] ≤ Pr[A ∨ₑ B] :=
begin
  rw eor_comm,
  apply Pr_le_eor_left,
end

lemma Pr_le_eor_sum {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∨ₑ B]≤ Pr[A] + Pr[B] :=
begin
  have A1:↑(Pr[A ∨ₑ B])≤ (Pr[A]:ennreal) + (Pr[B]:ennreal),
  {
    rw event_prob_def,
    rw event_prob_def,
    rw event_prob_def,
    rw eor_val_def,
    apply measure_theory.outer_measure.union,
  },
  have A2:↑(Pr[A ∨ₑ B])≤ ((Pr[A] + Pr[B]):ennreal) → Pr[A ∨ₑ B]≤ Pr[A] + Pr[B],
  {
    apply to_nnreal_almost_monotonic,
    {
      rw event_prob_def,
      apply prob_not_infinite,
    },
    {
      apply add_finite,
      rw event_prob_def,
      apply prob_not_infinite,
      rw event_prob_def,
      apply prob_not_infinite,
    }
  },
  apply A2,
  apply A1,
end


lemma Pr_disjoint_eor {Ω:Type*} {p:probability_space Ω} (A B:event p):
  disjoint A.val B.val →
  Pr[A ∨ₑ B] =  Pr[A] + Pr[B] :=
begin
  intro A1,
  have A2:↑(Pr[A ∨ₑ B])= (Pr[A]:ennreal) + (Pr[B]:ennreal),
  {
    rw event_prob_def,
    rw event_prob_def,
    rw event_prob_def,
    rw eor_val_def,

    apply measure_theory.measure_union,
    apply A1,
    apply A.property,
    apply B.property,
  },
  have A3:((Pr[A ∨ₑ B]):ennreal).to_nnreal= ((Pr[A]:ennreal) + (Pr[B]:ennreal)).to_nnreal,
  {
    rw A2,
  },
  simp at A3,
  apply A3,
end

def enot {Ω:Type*} {p:probability_space Ω} (A:event p):event p := {
  val:=(A).valᶜ,
  property := is_measurable.compl A.property,
}

prefix `¬ₑ` :100 := enot

lemma enot_val_def {Ω:Type*} {p:probability_space Ω} (A:event p):
  (¬ₑ A).val = (A.val)ᶜ :=
begin
  refl,
end

/-
  Double negation elimination. However, it is hard to avoid in measure theory.
-/
lemma enot_enot_eq_self {Ω:Type*} {p:probability_space Ω} (A:event p):
  (¬ₑ (¬ₑ A)) = (A) :=
begin
  apply event.eq,
  rw enot_val_def,
  rw enot_val_def,
  ext ω,
  have A1:decidable (ω ∈ A.val),
  {
    apply classical.prop_decidable,
  },
  split;intro A2,
  {
    cases A1,
    {
      exfalso,
      apply A2,
      apply A1,
    },
    {
      exact A1,
    }
  },
  {
    intro A3,
    apply A3,
    exact A2,
  }
end



lemma em_event {Ω:Type*} {p:probability_space Ω} (A:event p):
    A ∨ₑ (¬ₑ A)=event_univ :=
begin
  apply event.eq,
  rw event_univ_val_def,
  rw eor_val_def,
  rw enot_val_def,
  rw set.union_compl_self,
end


lemma Pr_add_enot_eq_1 {Ω:Type*} {p:probability_space Ω} (A:event p):
  Pr[A] + Pr[¬ₑ A] = 1 :=
begin
  have A1:disjoint (A.val) (enot A).val,
  {
    unfold disjoint,
    rw enot_val_def,
    simp,
  },
  have A2:A∨ₑ (¬ₑ A) = event_univ,
  {
    apply em_event,
  },
  have A3:Pr[A∨ₑ (¬ₑ A)] = Pr[event_univ],
  {
    rw A2,
  },
  rw Pr_event_univ at A3,
  rw Pr_disjoint_eor at A3,
  apply A3,
  apply A1,
end

lemma Pr_one_minus_eq_not {Ω:Type*} {p:probability_space Ω} (A:event p):
  1 - Pr[A] = Pr[¬ₑ A] :=
begin
  apply nnreal_add_sub_left,
  apply Pr_add_enot_eq_1,
end


lemma Pr_one_minus_not_eq {Ω:Type*} {p:probability_space Ω} (A:event p):
  1 - Pr[enot A] = Pr[A] :=
begin
  apply nnreal_add_sub_right,
  apply Pr_add_enot_eq_1,
end

lemma em_event_cond {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∧ₑ B) ∨ₑ (A ∧ₑ ¬ₑ B) = A :=
begin
  apply event.eq,
  rw eor_val_def,
  rw eand_val_def,
  rw eand_val_def,
  apply set.union_inter_compl,
end

lemma Pr_em {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∧ₑ B] + Pr[A ∧ₑ ¬ₑ B] = Pr[A] :=
begin
  rw ← Pr_disjoint_eor,
  { --Pr[(A∧ₑ B)∨ₑ A∧ₑ ¬ₑ B] = Pr[A]
    rw em_event_cond,
  },
  { --disjoint ((A∧ₑ B).val) ((A∧ₑ ¬ₑ B).val)
    rw eand_val_def,
    rw eand_val_def,
    rw enot_val_def,
    apply set.disjoint_inter_compl,
  }
end

lemma Pr_diff {Ω:Type*} {p:probability_space Ω} (A B:event p):
    A.val ⊆ B.val →
    Pr[B ∧ₑ ¬ₑ A] = Pr[B] - Pr[A] :=
begin
  intro A1,
  have A2:Pr[B ∧ₑ A] + Pr[B ∧ₑ ¬ₑ A] = Pr[B],
  {
    apply Pr_em,
  },
  have A3:B ∧ₑ A = A,
  {
    apply eand_eq_self_of_subset_right,
    apply A1,
  },
  rw A3 at A2,
  symmetry,
  apply nnreal_add_sub_left,
  exact A2,
end


def event_eqv {Ω:Type*} {p:probability_space Ω} (A B:event p):event p :=
    (A ∧ₑ B) ∨ₑ ((¬ₑ A) ∧ₑ (¬ₑ B))

infixr `=ₑ`:100 := event_eqv

/-
-- Should prove this.
lemma Pr_eor_eq_minus_eand {Ω:Type*} [ Ω] {p:probability_space Ω} (A B:event p):
  Pr[A ∨ₑ B] =  Pr[A] + Pr[B] - Pr[A ∧ₑ B]
-/

def eall {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event p):event p := {
  val:=(⋂ b:β, (A b).val),
  property := is_measurable.Inter (λ b:β, (A b).property),
}

lemma eall_val_def {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event p):
  (eall A).val = (⋂ b:β, (A b).val) := rfl

def eall_prop {Ω β:Type*} {p:probability_space Ω} [E:encodable β]
  (P:β → Prop) [D:decidable_pred P]
  (A:β → event p):event p := @eall _ _ _ (@encodable.subtype β P E D) (λ (b:(subtype P)), A (b.val) )

def to_set_of_sets {Ω:Type*} {p:probability_space Ω} (A:set (event p)):set (set Ω) :=
  (set.image (λ a:event p, a.val) A)

lemma all_measurable_to_set_of_sets {Ω:Type*} {p:probability_space Ω} (A:set (event p))
  (a∈ (to_set_of_sets A)):is_measurable a :=
begin
  unfold to_set_of_sets at H,
  simp at H,
  cases H with x H,
  cases H with A1 A2,
  subst a,
  exact x.property,
end

lemma countable_to_set_of_sets {Ω:Type*} {p:probability_space Ω} {A:set (event p)}:
  (set.countable A)→ (set.countable (to_set_of_sets A)) :=
begin
  unfold to_set_of_sets,
  intro A1,
  apply set.countable.image,
  apply A1,
end

def eall_set {Ω:Type*} {p:probability_space Ω} (A:set (event p)) (cA:set.countable A):event p:=
{
  val:=set.sInter (to_set_of_sets A),
  property:=is_measurable.sInter (countable_to_set_of_sets cA) (all_measurable_to_set_of_sets A),
}



def eall_finset_val {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event p):set Ω :=  ⋂ s∈ S, (A s).val


lemma eall_finset_val_measurable {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event p):is_measurable (eall_finset_val S A) :=
begin
  unfold eall_finset_val,
  apply finset_inter_measurable,
  intros,
  apply (A t).property,
end

--

def eall_finset {Ω β:Type*} {p:probability_space Ω}
  (S:finset β)
  (A:β → event p):event p := {
    val:=eall_finset_val S A,
    property:=eall_finset_val_measurable S A,
  }

lemma eall_finset_val_def {Ω β:Type*} {p:probability_space Ω}
  (S:finset β) (A:β → event p):(eall_finset S A).val = ⋂ s∈ S, (A s).val := rfl



--If we could state forall for events, that would be great!
--notation `∀r` binders `, ` r:(scoped f, eall_finset f) := r


def eall_fintype {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event p):event p := eall_finset F.elems A
lemma eall_fintype_val_def {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event p):(eall_fintype F A).val = ⋂ (s:β), (A s).val :=
begin
  unfold eall_fintype,
  rw eall_finset_val_def,
  {
    ext,split;intro A1;simp at A1;simp,
    {
      intro i,
      apply A1,
      apply F.complete,
    },
    {
      intros i A2,
      apply A1,
    }
  }
end

def measurable_Union {Ω β:Type*} {p:measurable_space Ω} [encodable β] (A:β → measurable_set p):
  measurable_set p := {
  val:=(⋃ b:β, (A b).val),
  property := is_measurable.Union (λ b:β, (A b).property),
}

lemma measurable_Union_val_def {Ω β:Type*} {p:measurable_space Ω} [E:encodable β] 
    (A:β → measurable_set p):
    (@measurable_Union Ω β p E A).val = (⋃ b:β, (A b).val) := rfl




def eany {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event p):event p := 
  measurable_Union A

lemma measurable_Union_eq_any {Ω β:Type*} 
    {p:probability_space Ω} [E:encodable β] (A:β → event p):
    measurable_Union A = eany A := rfl


lemma sum_subst {β:Type*} [encodable β] {f g:β → ennreal}:(f = g) →
    (tsum f) = (tsum g) :=
begin
  intro A1,
  rw A1,
end


lemma Pr_measurable_Union_sum_dummy {Ω β:Type*} [M:probability_space Ω]
    --{m:measure_theory.measure Ω}
    [E:encodable β]  
    (A:β → set Ω):(∀ (i j:β), i ≠ j → 
    (A i ∩ A j = ∅))→
    (∀ i, is_measurable (A i)) →
    ((@measure_theory.measure_space.volume Ω (probability_space.to_measure_space)) (⋃ (n:β), A n)) = 
    (∑' (i:β), (@measure_theory.measure_space.volume Ω (probability_space.to_measure_space)) (A i)) :=
begin
  intros A1 A3,
  rw measure_theory.measure_Union,
  {
    intros i j A2,
    simp,
    --have A3 := A1 i j A2,
    unfold disjoint function.on_fun,
    simp,
    rw subset_empty_iff,
    apply A1 i j A2,
  },
  {
    apply A3,
  },
end

lemma measure_eq_measure {Ω:Type*} [P:probability_space Ω] {S:set Ω}:
  measure_theory.measure_space.volume.to_outer_measure.measure_of S =
  (@measure_theory.measure_space.volume Ω (probability_space.to_measure_space)) S := rfl


lemma eany_val_def {Ω β:Type*} {p:probability_space Ω} [encodable β]
  (A:β → event p):(eany A).val=(⋃ b:β, (A b).val) := rfl

def eany_finset_val {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event p):set Ω :=  ⋃ s∈ S, (A s).val



lemma eany_finset_val_measurable {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event p):is_measurable (eany_finset_val S A) :=
begin
  unfold eany_finset_val,
  apply finset_union_measurable,
  intros,
  apply (A t).property,
end

def eany_finset {Ω β:Type*} {p:probability_space Ω}
  (S:finset β)
  (A:β → event p):event p := {
    val:=eany_finset_val S A,
    property:=eany_finset_val_measurable S A,
  }

lemma eany_finset_val_def {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event p):(eany_finset S A).val = ⋃ s∈ S, (A s).val := rfl


/-lemma eany_finset_insert_val {Ω β:Type*} {p:probability_space Ω} [decidable_eq β] (S:finset β) {a:β}
  (A:β → event p): 
--  (⋃ s∈  (insert a S), (A s).val) = 
--  ((A a).val ) ∪ (⋃ s∈ S,(A s).val) :=
  (eany_finset (insert a S) A).val = ((A a).val ) ∪ (⋃ s∈ S,(A s).val) :=
begin
  simp,
end-/

def eany_fintype {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event p):event p := eany_finset F.elems A


lemma eany_finset_empty {Ω β:Type*} {p:probability_space Ω}
  (A:β → event p):eany_finset ∅ A = event_empty :=
begin
  apply event.eq,
  rw eany_finset_val_def,
  rw event_empty_val_def,
  simp,
end


lemma eany_finset_insert {Ω β:Type*} [D:decidable_eq β] {p:probability_space Ω}
  {S:finset β} {A:β → event p} {a:β}:
  eany_finset (insert a S) A = (A a) ∨ₑ eany_finset S A  :=
begin
  apply event.eq,
  rw eany_finset_val_def,
  rw eor_val_def,
  rw eany_finset_val_def,
  ext ω,split;intros A2;simp;simp at A2;apply A2,
end

lemma eany_finset_bound {Ω β:Type*} [D:decidable_eq β]
  {p:probability_space Ω}
  (S:finset β) (A:β → event p):Pr[eany_finset S A] ≤ finset.sum S (λ a:β, Pr[A a]) :=
begin
  apply finset.induction_on S,
  {
    simp,
    rw eany_finset_empty,
    apply Pr_event_empty,
  },
  {
    intros a S2 A1 A2,
    rw finset.sum_insert A1,
    rw eany_finset_insert,
    apply le_trans,
    apply Pr_le_eor_sum,
    apply add_le_add_left,
    apply A2,
  }
end


lemma eany_fintype_bound {Ω β:Type*} [D:decidable_eq β] {p:probability_space Ω}
  (F:fintype β) (A:β → event p):Pr[eany_fintype F A] ≤  ∑' a:β, Pr[A a] :=
begin
  unfold eany_fintype,
  rw tsum_fintype,
  apply eany_finset_bound,
end


lemma eany_fintype_bound2 {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event p) (k:nnreal):
  (∀ a:β, Pr[A a]≤ k) →
  Pr[eany_fintype F A] ≤ (fintype.card β) * k :=
begin
  intro A1,
  have A2:decidable_eq β := classical.decidable_eq β,

  apply le_trans,
  apply @eany_fintype_bound Ω β A2,
  rw tsum_fintype,
  unfold fintype.card,
  apply @finset_sum_le_const β A2,
  intros s A3,
  apply A1,
end


def independent_event_pair {Ω:Type*} {p:probability_space Ω} (A B:event p):Prop :=
  --(event_prob (eand A B)) = (event_prob A) * (event_prob B)
  Pr[ A ∧ₑ B] = Pr[A] * Pr[B]


def independent_events {Ω β:Type*} {p:probability_space Ω} [fintype β]
  (A:β → event p):Prop :=
  ∀ (S:finset β), (finset.prod S (λ b, Pr[A b])) = Pr[eall_finset S A]

def events_IID {Ω β:Type*} {p:probability_space Ω} [fintype β]
  (A:β → event p):Prop :=
  independent_events A ∧ (∀ x y:β, Pr[A x] = Pr[A y])

lemma events_IID_pow {α : Type*} {p : probability_space α} {β : Type*}
  [F:fintype β] [I:inhabited β] (A:β → event p) (S:finset β):
  events_IID A → Pr[eall_finset S A] = Pr[A I.default]^(S.card) :=
begin
  intros A1,
  unfold events_IID at A1,
  cases A1 with A2 A3,
  unfold independent_events at A2,
  have A4:(finset.prod S (λ b, Pr[A b])) = Pr[eall_finset S A],
  {
    apply A2,
  },
  rw ← A4,
  have A5:(λ (b : β), Pr[A b]) = (λ (b:β), Pr[A (inhabited.default β)]),
  {
    ext b,
    rw A3,
  },
  rw A5,
  apply finset.prod_const,
end


def measurable_fun {α:Type*}  {β:Type*} (Mα:measurable_space α) (Mβ:measurable_space β):Type*
    := subtype (@measurable α β _ _)

def random_variable {α:Type*} (p:probability_space α) {β:Type*}
  (Mβ:measurable_space β):Type* := measurable_fun (probability_space.to_measurable_space α) Mβ

infixr  ` →m `:80 := measurable_fun
infixr  ` →r `:80 := random_variable


lemma random_variable_val_eq_coe {Ω α:Type*} {P:probability_space Ω} {M:measurable_space α}  
  (X:P →r M):X.val = 
  (@coe (subtype (@measurable Ω α _ _)) (Ω → α) _ X) :=
begin
  refl
end




lemma measurable_set_preimageh {α:Type*}  {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β]
  (f:measurable_fun Mα Mβ) (S:measurable_set Mβ):is_measurable (set.preimage (f.val) (S.val)) :=
begin
  apply measurable_elim,
  apply f.property,
  apply S.property
end

def measurable_set_preimage {α:Type*}  {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β]
  (f:measurable_fun Mα Mβ) (S:measurable_set Mβ):measurable_set Mα := {
    val:= (set.preimage (f.val) (S.val)),
    property:=measurable_set_preimageh f S,
}



def rv_event {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X:random_variable p Mβ) (S:measurable_set Mβ):event p :=
   measurable_set_preimage X S


infixr ` ∈r `:80 := rv_event


lemma rv_event_val_def {α:Type*} {p : probability_space α} {β : Type*}
  [Mβ : measurable_space β] (X:p →r Mβ) (S:measurable_set Mβ):(X ∈r S).val = {a:α|X.val a ∈ S.val} :=
begin
  refl
end


lemma rv_event_empty {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X:random_variable p Mβ):X ∈r ∅ = ∅ :=
begin
  apply event.eq,
  rw rv_event_val_def,
  rw event_empty_val_def2,
  ext ω;split;intros A1,
  {
    exfalso,
    simp at A1,
    apply A1,
  },
  {
    exfalso,
    apply A1,
  },
end

lemma rv_event_measurable_union {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X:random_variable p Mβ) 
  {A B:measurable_set Mβ}:X ∈r (measurable_union A B) = (X ∈r A) ∨ₑ (X∈r B) :=
begin
  apply event.eq,
  repeat {rw rv_event_val_def},
  rw eor_val_def,
  repeat {rw rv_event_val_def},
  rw measurable_union_val_def,
  ext ω;split;intros A1;simp;simp at A1;apply A1
end

lemma rv_event_val_def' {α:Type*} {p : probability_space α} {β : Type*}
  [Mβ : measurable_space β] (X:p →r Mβ) (S:measurable_set Mβ) {ω:α}:
  (ω ∈ ((X ∈r S)))↔ (X.val ω ∈ S.val) :=
begin
  refl
end


lemma set.mem_Prop_def {α:Type*} {P:α → Prop} {a:α}:
    (a ∈ {a':α|P a'} )= P a := rfl


lemma rv_event_measurable_Union {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] {γ:Type*} [E:encodable γ] (X:random_variable p Mβ) 
  {f:γ → measurable_set Mβ}:X ∈r (measurable_Union f) = 
  measurable_Union (λ i, X ∈r (f i)) :=
begin
  apply event.eq,
  ext ω,
  rw rv_event_val_def,
  rw measurable_Union_val_def,
  rw measurable_Union_val_def,
  split;intro A1,
  {
    rw set.mem_Prop_def at A1,
    rw set.mem_Union,
    rw set.mem_Union at A1,
    cases A1 with i A1,
    apply exists.intro i,
    rw @rv_event_val_def α p β Mβ X (f i),
    rw set.mem_Prop_def,
    apply A1,
  },
  {
    rw set.mem_Prop_def,
    rw set.mem_Union,
    rw set.mem_Union at A1,
    cases A1 with i A1,
    rw @rv_event_val_def α p β Mβ X (f i) at A1,
    apply exists.intro i,
    apply A1,
  },
end



instance measurable_set_has_compl {α:Type*} [M:measurable_space α]:has_compl (@measurable_set α M) := {
  compl := λ E, ⟨ E.valᶜ, is_measurable.compl E.property⟩,
}

instance measurable_set_subtype_has_neg {α:Type*} [M:measurable_space α]:has_neg (subtype (@is_measurable α M)) := {
  neg := λ E, ⟨ E.valᶜ, is_measurable.compl E.property⟩,
}

lemma measurable_set_neg_def {α:Type*} [M:measurable_space α] {E:@measurable_set α M}:
    Eᶜ = ⟨ E.valᶜ, is_measurable.compl E.property⟩ :=rfl

lemma measurable_set_neg_val_def {α:Type*} [M:measurable_space α] {E:@measurable_set α M}:
    (Eᶜ).val = (E.val)ᶜ  :=rfl


instance event_has_compl {α:Type*} [M:probability_space α]:has_compl (@event α M) := {
  compl := λ E, ⟨E.valᶜ, is_measurable.compl E.property⟩,
}

lemma event_neg_def {α:Type*} [M:probability_space α] {E:@event α M}:
    Eᶜ = ⟨ E.valᶜ, is_measurable.compl E.property⟩ :=rfl

lemma event_neg_val_def {α:Type*} [M:probability_space α] {E:@event α M}:
    (Eᶜ).val = (E.val)ᶜ := rfl



lemma event_simp_def {α:Type*} [p:probability_space α] {X:set α} {H:is_measurable X}:
  (subtype.mk X H).val = X := rfl

lemma measurable_set_simp_def {α:Type*} [p:measurable_space α] {X:set α} {H:is_measurable X}:
  (subtype.mk X H).val = X := rfl

lemma pr_comp_event {Ω:Type*} {p:probability_space Ω} {X:p →r borel real}
 {E:@measurable_set ℝ (borel ℝ)}:
 (X ∈r (Eᶜ)) = (X ∈r E)ᶜ :=
begin
  apply event.eq,
  rw event_neg_def,
  rw rv_event_val_def,
  rw @event_simp_def Ω p ,
  rw rv_event_val_def,
  rw measurable_set_neg_def,
  rw @measurable_set_simp_def ℝ (borel ℝ),  
  ext ω,
  simp,
end

--ᶜ
lemma rv_event_compl {Ω:Type*} {MΩ:probability_space Ω} {β:Type*} [Mβ:measurable_space β]
  (X:MΩ →r Mβ) (S:measurable_set Mβ):(X ∈r (Sᶜ)) = (rv_event X S)ᶜ :=
begin
  apply event.eq,
  rw event_neg_val_def,
  rw rv_event_val_def,
  rw measurable_set_neg_val_def,
  rw rv_event_val_def,
  simp,
  refl,
end

lemma neg_eq_not {Ω:Type*} {p:probability_space Ω} (A:event p):
  Aᶜ = ¬ₑ A :=
begin
  apply event.eq,
  rw event_neg_val_def,
  rw enot_val_def,
end

def random_variable_identical {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X Y:random_variable p Mβ):Prop :=
  ∀ (S:measurable_set Mβ), Pr[X ∈r S] = Pr[Y ∈r S]

def random_variable_independent_pair {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X Y:random_variable p Mβ):Prop :=
  ∀ (S T:measurable_set Mβ), independent_event_pair (X ∈r S) (Y ∈r T)

def random_variable_independent {α:Type*} {p:probability_space α} {β:Type*}
  [fintype β]
  {γ:β → Type*} [Mγ:Π b, measurable_space (γ b)] (X:Π b, random_variable p (Mγ b)):Prop :=
  ∀ (S:Π b, measurable_set (Mγ b)), independent_events (λ b:β, ((X b) ∈r (S b)))

def random_variables_IID {α:Type*} {p:probability_space α} {β:Type*}
  [fintype β]
  {γ:Type*} [Mγ:measurable_space γ] (X:β → random_variable p Mγ):Prop :=
  random_variable_independent X ∧
  ∀ (i j:β), random_variable_identical (X i) (X j)


/- There are a lot of types where everything is measurable. This is equivalent to ⊤. -/
class top_measurable (α:Type*) extends measurable_space α :=
  (all_measurable:∀ S:set α,is_measurable S)

instance bool_top_measurable:top_measurable bool := {
  all_measurable:=@measurable_space.is_measurable_top bool,
  ..bool.measurable_space
}

instance int_top_measurable:top_measurable ℤ := {
  all_measurable:=@measurable_space.is_measurable_top ℤ,
  ..int.measurable_space
}

/-
  In a top measurable space (e.g. bool, ℕ, ℤ, et cetera),
  everything is measurable. So, we can make an event from everything.
-/
def measurable_set_top {β:Type*} [M:top_measurable β] (S:set β):
    (@measurable_set β M.to_measurable_space) := {
  val := S,
  property := top_measurable.all_measurable S,
}

def rv_top_event {α:Type*} {p:probability_space α}
 {β:Type*} [Mβ:top_measurable β]
  (X:random_variable p Mβ.to_measurable_space) (S:set β):event p :=
  rv_event X (measurable_set_top S)

--To apply this directly to a set, it has to be top measurable.
infixr ` ∈t `:80 := rv_top_event

lemma rv_top_event_val_def  {α:Type*} {p:probability_space α}
 {β:Type*} [Mβ:top_measurable β]
  (X:random_variable p Mβ.to_measurable_space) (S:set β):
  (rv_top_event X S).val = {a:α|X.val a ∈ S} := rfl


/-
  For encodable types where every event is measurable (bool, ℤ, ℕ, et cetera),
  one can define equality of two random variables as an event.
-/
def rv_eq {α:Type*} {p:probability_space α} {β:Type*}
  [encodable β] [Mβ:top_measurable β] (X Y:random_variable p Mβ.to_measurable_space):event p :=
  eany (λ b:β,  (X ∈t {b}) ∧ₑ (Y ∈t {b}))


lemma rv_eq_val_def {α:Type*} {p : probability_space α} {β : Type*}
  [encodable β] [Mβ : top_measurable β] (X Y:p →r Mβ.to_measurable_space):
  (rv_eq X Y).val = {a:α| X.val a = Y.val a} :=
begin
  unfold rv_eq,
  rw eany_val_def,
  ext ω,
  --simp,
  split;intros A1,
  {
    rw set.mem_Union at A1,
    rw set.mem_Prop_def,
    cases A1 with i A2,
    rw eand_val_def at A2,
    rw rv_top_event_val_def at A2,
    rw rv_top_event_val_def at A2,
    cases A2 with A3 A4,
    rw set.mem_Prop_def at A3,
    rw set.mem_singleton_iff at A3,
    rw set.mem_Prop_def at A4,
    rw set.mem_singleton_iff at A4,
    rw A3,
    rw A4,
  },
  {
    rw set.mem_Prop_def at A1,
    rw set.mem_Union,
    apply exists.intro (X.val ω),
    rw eand_val_def,
    rw rv_top_event_val_def,
    rw rv_top_event_val_def,
    apply set.mem_inter,
    simp,
    rw A1,
    simp,
  }
end

def rv_ne {α:Type*} {p:probability_space α} {β:Type*}
  [encodable β] [Mβ:top_measurable β] (X Y:random_variable p Mβ.to_measurable_space):event p :=
  ¬ₑ (rv_eq X Y)

lemma rv_ne_val_def {α:Type*} {p : probability_space α} {β : Type*}
  [encodable β] [Mβ : top_measurable β] (X Y:p →r Mβ.to_measurable_space):
  (rv_ne X Y).val = {a:α| X.val a ≠ Y.val a} :=
begin
  unfold rv_ne,
  rw enot_val_def,
  rw rv_eq_val_def,
  refl,
end



lemma compose_measurable_fun_measurable2 {α β γ:Type*}
  [Mα:measurable_space α] [Mβ:measurable_space β] [Mγ:measurable_space γ]
  (X:measurable_fun Mβ Mγ) (Y:measurable_fun Mα Mβ):measurable (X.val ∘ Y.val) :=
begin
  apply measurable_intro,
  intros,
  have A1:(X.val ∘ Y.val ⁻¹' B)=(Y.val ⁻¹' (X.val ⁻¹' B)),
  {
    refl,
  },
  rw A1,
  apply measurable_elim Y.val _ Y.property,
  apply measurable_elim X.val _ X.property,
  apply a
end


def compose_measurable_fun {α β γ:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β} {Mγ:measurable_space γ}
  (X:measurable_fun Mβ Mγ) (Y:measurable_fun Mα Mβ):(measurable_fun Mα Mγ) := {
    val := X.val ∘ Y.val,
    property := compose_measurable_fun_measurable2 X Y
  }




infixr  ` ∘m `:80 := compose_measurable_fun

lemma compose_measurable_fun_val_def {Ω : Type*} {β : Type*} {γ : Type*}
  [MΩ : measurable_space Ω] [Mβ : measurable_space β]
  [Mγ : measurable_space γ] (Y:Mβ →m Mγ) (X:MΩ →m Mβ):
  (Y ∘m X).val = (λ ω:Ω, Y.val (X.val ω)) :=
begin
  refl
end



/-
Delete if doesn't cause errors.
def rv_compose {α β γ:Type*}
  [Mα:measurable_space α] [Mβ:measurable_space β] [Mγ:measurable_space γ] {p:probability_space α}
  (X:measurable_fun Mβ Mγ) (Y:random_variable p Mβ):random_variable p Mγ :=
  compose_measurable_fun X Y



def rv_composeM {α : Type*} {β : Type*} {γ : Type*} [Mα : measurable_space α]
  (p : probability_space α) (Mβ : measurable_space β)
  (Mγ : measurable_space γ) (X:measurable_fun Mβ Mγ) (Y:random_variable p Mβ):random_variable p Mγ :=
  rv_compose X Y
 -/
-- Used to be rv_composeM2
def rv_compose {α : Type*} {β : Type*} {γ : Type*}
  {p : probability_space α} {Mβ : measurable_space β}
  {Mγ : measurable_space γ} (X:measurable_fun Mβ Mγ) (Y:random_variable p Mβ):random_variable p Mγ :=
  compose_measurable_fun X Y

--  rv_compose X Y

infixr  ` ∘r `:80 := rv_compose

lemma rv_compose_val_def {Ω : Type*} {β : Type*} {γ : Type*}
  [Mβ : measurable_space β]
  [Mγ : measurable_space γ] {p : probability_space Ω} (Y:Mβ →m Mγ) (X:p →r Mβ):
  (Y ∘r X).val = (λ ω:Ω, Y.val (X.val ω)) :=
begin
  refl
end





def prod_space {α β:Type*} (Mα:measurable_space α) (Mβ:measurable_space β):=(@prod.measurable_space α β Mα Mβ)

infixr  ` ×m `:80 := prod_space


def mf_fst {α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}:measurable_fun
    (Mα ×m Mβ) Mα := {
    val:= (λ x:(α × β), x.fst),
    property := fst_measurable,
  }

def mf_snd {α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}:measurable_fun (prod_space Mα Mβ) Mβ := {
    val:= (λ x:(α × β), x.snd),
    property := snd_measurable,
  }

/-
 {Ω : Type u_1} [_inst_1 : measurable_space Ω] {β : Type u_2} [_inst_2 : measurable_space β] (c : β),
    measurable (λ (ω : Ω), c)
-/
def const_measurable_fun {Ω : Type*} [MΩ : measurable_space Ω] {β : Type*}
   [Mβ : measurable_space β] (c : β):MΩ →m Mβ := {
     val := (λ (ω : Ω), c),
     property := const_measurable c,
   }

lemma const_measurable_fun_val_def {Ω : Type*} [MΩ : measurable_space Ω] {β : Type*}
   [Mβ : measurable_space β] (c : β):(const_measurable_fun c).val = (λ (ω : Ω), c) := rfl

def const_random_variable {Ω : Type*} {P:probability_space Ω}
   {β : Type*}
   [Mβ : measurable_space β] (c : β):P →r Mβ := const_measurable_fun c


def prod_measurable_fun
{α β γ:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β} {Mγ:measurable_space γ}
  (X:measurable_fun Mα Mβ) (Y:measurable_fun Mα Mγ):measurable_fun Mα (Mβ ×m Mγ) := {
    val := (λ a:α, prod.mk (X.val a) (Y.val a)),
    property := measurable_fun_product_measurable X.val Y.val X.property Y.property,
  }

lemma prod_measurable_fun_val_def {Ω : Type*} {β : Type*} {γ : Type*} {MΩ : measurable_space Ω}
  {Mβ : measurable_space β} {Mγ : measurable_space γ} {X:MΩ  →m Mβ}
  {Y:MΩ  →m Mγ}: (prod_measurable_fun X Y).val = λ ω:Ω, prod.mk (X.val ω) (Y.val ω) :=
begin
  refl
end

def prod_random_variable
{α β γ:Type*}
  {P:probability_space α} {Mβ:measurable_space β} {Mγ:measurable_space γ}
  (X:random_variable P Mβ) (Y:random_variable P Mγ):random_variable P (Mβ ×m Mγ) :=
  prod_measurable_fun X Y

infixr  ` ×r `:80 := prod_random_variable


lemma prod_random_variable_val_def {Ω : Type*} {β : Type*} {γ : Type*}
  {P : probability_space Ω} {Mβ : measurable_space β} {Mγ : measurable_space γ} {X:P →r Mβ}
  {Y:P →r Mγ}: (X ×r Y).val = λ ω:Ω, prod.mk (X.val ω) (Y.val ω) :=
begin
  refl
end


def prod_measurable_set {β : Type*} {γ : Type*}
  {Mβ : measurable_space β} 
  {Mγ : measurable_space γ} 
  (X:measurable_set Mβ) (Y:measurable_set Mγ):measurable_set (Mβ ×m Mγ) := {
  val := (set.prod X.val Y.val),
  property := is_measurable_prod' X.property Y.property
}

lemma prod_measurable_set_val_def {β : Type*} {γ : Type*}
  {Mβ : measurable_space β} 
  {Mγ : measurable_space γ} 
  (X:measurable_set Mβ) (Y:measurable_set Mγ):
  (prod_measurable_set X Y).val = set.prod X.val Y.val := rfl


lemma union_func_eq_sUnion_image {α β:Type*}
  [Tβ:measurable_space β] {A:set α} {f:α → set β}:
  (⋃ a∈ A, f a)=set.sUnion (@set.image α (set β) f A) :=
begin
  simp,
end


lemma is_measurable_countable_union_func {α β:Type*}
  [Tβ:measurable_space β] {A:set α} {f:α → set β}:
  set.countable A →
  (∀ a∈ A, is_measurable (f a)) →
  is_measurable (⋃ a∈ A, f a) :=
begin
  intros A1 A2,
  rw union_func_eq_sUnion_image,
  apply is_measurable.sUnion,
  {
    apply set.countable.image,
    apply A1,
  },
  intros t A4,
  cases A4 with a A5,
  cases A5 with A6 A7,
  subst t,
  apply A2,
  apply A6,
end


-- cf set.prod_singleton_singleton
lemma singleton_prod {α β:Type*} {ab:α × β}:{ab} = (@set.prod α β {ab.fst} {ab.snd}) :=
begin
  simp,
end

lemma top_measurable_prodh {α β:Type*} [encodable α] [encodable β]
  [Tα:top_measurable α] [Tβ:top_measurable β] (U:set (α × β)):
  is_measurable U :=
begin
  have A2:encodable (α × β):= encodable.prod,
  have A3:set.countable U := set.countable_encodable U,
  have A4:(⋃ a∈U,{a}) = U,
  {
    simp
  },
  rw ← A4,
  apply is_measurable_countable_union_func A3,
  intros ab A5,
  rw singleton_prod,
  apply is_measurable.prod,
  {
    apply top_measurable.all_measurable,
  },
  {
    apply top_measurable.all_measurable,
  },
end


instance top_measurable_prod {α β:Type*} [encodable α] [encodable β]
  [Tα:top_measurable α] [Tβ:top_measurable β]:top_measurable (α × β) := {
     all_measurable := top_measurable_prodh,
  }




def if_measurable_fun
{α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}
  (E:measurable_set Mα) (D:decidable_pred E.val)
  (X:measurable_fun Mα Mβ) (Y:measurable_fun Mα Mβ):measurable_fun Mα Mβ :={
    val := λ a:α, if (E.val a) then (X.val a) else (Y.val a),
    property := measurable.if E.property X.property Y.property,
  }

def if_random_variable
{α β:Type*}
  {P:probability_space α} {Mβ:measurable_space β}
  (E:event P) (D:decidable_pred E.val)
  (X:random_variable P Mβ) (Y:random_variable P Mβ):random_variable P Mβ :=
  if_measurable_fun E D X Y

lemma rv_event_IID {α : Type*} {p : probability_space α} {β : Type*}
  [fintype β] {γ : Type*} [Mγ : measurable_space γ] (X:β → p →r Mγ) (S:measurable_set Mγ):
  random_variables_IID X  → events_IID (λ b:β, (X b) ∈r S) :=
begin
  intro A1,
  unfold random_variables_IID at A1,
  cases A1 with A2 A3,
  unfold random_variable_independent at A2,
  unfold random_variable_identical at A3,
  split,
  {
    apply A2,
  },
  {
    intros i j,
    simp,
    apply A3,
  }
end

lemma measurable_set_preimage_val_def {α:Type*}  {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β]
  (f:measurable_fun Mα Mβ) (S:measurable_set Mβ):
  (measurable_set_preimage f S).val = (set.preimage (f.val) (S.val)) := rfl

lemma compose_measurable_fun_measurable_set {Ω : Type*} {β : Type*} {γ : Type*}
  [MΩ : measurable_space Ω] [Mβ : measurable_space β]
  [Mγ : measurable_space γ] (Y:Mβ →m Mγ) (X:MΩ →m Mβ) (S:measurable_set Mγ):
  measurable_set_preimage (Y ∘m X) S = measurable_set_preimage X (measurable_set_preimage Y S) :=
begin
  apply subtype.eq,
  rw measurable_set_preimage_val_def,
  rw measurable_set_preimage_val_def,
  rw measurable_set_preimage_val_def,
  rw compose_measurable_fun_val_def,
  refl,
end

lemma rv_compose_measurable_set  {α : Type*} {β : Type*} {γ : Type*}
  {p : probability_space α} {Mβ : measurable_space β}
  {Mγ : measurable_space γ} (X:measurable_fun Mβ Mγ) (Y:random_variable p Mβ) (S:measurable_set Mγ):
  (X ∘r Y) ∈r S = (Y ∈r (measurable_set_preimage X S)) :=
begin
  apply compose_measurable_fun_measurable_set,
end

lemma compose_independent {α:Type*} {p:probability_space α} {β:Type*}
  [fintype β]
  {γ:Type*} [Mγ:measurable_space γ]
  {κ:Type*} [Mκ:measurable_space κ] (X:β → random_variable p Mγ) (Y:Mγ →m  Mκ):
  random_variable_independent X → random_variable_independent (λ b:β, Y ∘r (X b)) :=
begin
  unfold random_variable_independent,
  intros A1 S T,
  unfold independent_events,
  have A2:(λ (b : β), Pr[(Y ∘r X b) ∈r S b]) =
      (λ (b : β), Pr[(X b) ∈r (measurable_set_preimage Y (S b))]),
  {
    ext b,
    rw rv_compose_measurable_set,
  },
  rw A2,
  have A3:(λ (b : β), (Y ∘r X b) ∈r S b) =
      (λ (b : β), (X b) ∈r (measurable_set_preimage Y (S b))),
  {
    ext b,
    rw rv_compose_measurable_set,
  },
  rw A3,
  apply A1,
end


lemma compose_identical {α:Type*} {p:probability_space α}
  {γ:Type*} [Mγ:measurable_space γ]
  {κ:Type*} [Mκ:measurable_space κ] (X₁ X₂:random_variable p Mγ) (Y:Mγ →m  Mκ):
  random_variable_identical X₁ X₂ → random_variable_identical (Y ∘r X₁) (Y ∘r X₂)  :=
begin
  unfold random_variable_identical,
  intro A1,
  intros S,
  rw rv_compose_measurable_set,
  rw rv_compose_measurable_set,
  apply A1,
end

lemma compose_IID {α:Type*} {p:probability_space α} {β:Type*}
  [fintype β]
  {γ:Type*} [Mγ:measurable_space γ]
  {κ:Type*} [Mκ:measurable_space κ] (X:β → random_variable p Mγ) (Y:Mγ →m  Mκ):
  random_variables_IID X → random_variables_IID (λ b:β, Y ∘r (X b)) :=
begin
  unfold random_variables_IID,
  intro A1,
  cases A1 with A2 A3,
  split,
  {
    apply compose_independent,
    apply A2,
  },
  {
    intros i j,
    apply compose_identical,
    apply A3,
  }
end

--For Pr_disjoint_summable below.

lemma union_disjoint {Ω β:Type*} {p:probability_space Ω} [E:encodable β] 
    [D:decidable_eq β]
    (A:β → event p) {S:finset β} {a:β}:(pairwise (disjoint on λ (i : β), (A i).val)) →
    (a ∉ S) →
    disjoint (A a).val (⋃ (b:β) (H:b∈ S), (A b).val) :=
begin
  intros A1 A2,
  rw set.disjoint_right,
  intros ω A4 A3,
  simp at A4,
  cases A4 with i A4,
  have A5:a ≠ i,
  {
    intro A5A,
    apply A2,
    rw A5A,
    apply A4.left,
  },
  have A7 := A1 a i A5,
  unfold function.on_fun at A7,
  have A8 := set.disjoint_iff_inter_eq_empty.mp A7,
  have A9:ω ∈ (A a).val ∩ (A i).val,
  {
    simp,
    apply and.intro A3 (A4.right),
  },
  rw A8 at A9,
  apply A9
end


lemma finset.Union_insert {α β:Type*} [E:encodable β]
    [D:decidable_eq β] {f:β → set α} {b:β} {S:finset β}:
   (⋃ (b':β) (H:b'∈ (insert b S)), f b') = 
   (f b) ∪ (⋃ (b':β) (H:b'∈ S), f b') := 
begin
  simp
end



lemma Pr_sum_disjoint_eq {Ω β:Type*} {p:probability_space Ω} [E:encodable β] 
    [D:decidable_eq β]
    (A:β → event p) {S:finset β}:(pairwise (disjoint on λ (i : β), (A i).val)) →
    Pr[eany_finset S A] =
finset.sum S (λ (b:β), Pr[A b]) :=
begin
  intro A1,
  apply finset.induction_on S,
  {
    simp,
    rw ← ennreal.coe_eq_coe,
    rw event_prob_def,
    rw eany_finset_val_def,
    simp,
  },
  {
    intros a T A2 A3,
    rw ← ennreal.coe_eq_coe,
    rw event_prob_def,
    rw finset.sum_insert,
    rw ennreal.coe_add,
    rw event_prob_def,
    rw eany_finset_val_def,
    rw finset.Union_insert,
    have A4:measure_theory.measure_space.volume ((A a).val ∪ ⋃ (x : β) (H : x ∈ T), (A x).val) = 
measure_theory.measure_space.volume ((A a).val) + 
measure_theory.measure_space.volume (⋃ (x : β) (H : x ∈ T), (A x).val),
    {
      apply measure_theory.measure_union,
      apply union_disjoint,
      apply A1,
      apply A2,
      apply (A a).property,
      apply finset_union_measurable,
      intros b A4A,
      apply (A b).property,
    },
    rw measure_eq_measure,
    rw A4,
    rw ← A3,
    rw event_prob_def,
    rw eany_finset_val_def,
    rw measure_eq_measure,
    rw measure_eq_measure,
    apply A2
  },
end


lemma Pr_sum_disjoint_bounded {Ω β:Type*} {p:probability_space Ω} [E:encodable β] [decidable_eq β] 
    (A:β → event p) {S:finset β}:(pairwise (disjoint on λ (i : β), (A i).val)) →
    finset.sum S (λ (b:β), Pr[A b]) ≤ 1 :=
begin
  intro A1,
  rw ← Pr_sum_disjoint_eq,
  apply Pr_event_le_1,
  apply A1,
end

lemma Pr_disjoint_summable {Ω β:Type*} {p:probability_space Ω} [E:encodable β] [decidable_eq β]
    (A:β → event p):(pairwise (disjoint on λ (i : β), (A i).val)) →
    summable (λ (b:β), Pr[A b]) :=
begin
  intro A1,
  apply summable_bounded_nnreal,
  {
    intro S,
    apply Pr_sum_disjoint_bounded,
    apply A1,
  },
end

lemma Pr_eany_sum {Ω β:Type*} {p:probability_space Ω} [E:encodable β] [decidable_eq β] 
    (A:β → event p):(pairwise (disjoint on λ (i : β), (A i).val)) →
    Pr[eany A] = ∑' (b:β), Pr[A b] :=
begin
  intro B1,
  rw ← measurable_Union_eq_any,
  rw ← with_top.coe_eq_coe,
  rw event_prob_def,
  rw measurable_Union_val_def,
  rw ennreal.coe_tsum,
  have A1:(λ (b:β), ↑Pr[A b]) = (λ (b:β), (measure_theory.measure_space.volume 
 (A b).val)),
  {
    ext b,
    rw event_prob_def,
    rw measure_eq_measure,
  },
  rw measure_eq_measure,
  rw measure_theory.measure_Union,
  rw sum_subst,
  rw A1,
  apply B1,
  {
    intro i,
    apply (A i).property,
  },
  {
    apply Pr_disjoint_summable,
    apply B1,
  },
end

lemma mem_prod_random_variable_prod_measurable_set 
  {α β γ:Type*}
  {P:probability_space α} {Mβ:measurable_space β} {Mγ:measurable_space γ}
  (X:random_variable P Mβ) (Y:random_variable P Mγ) 
  (S:measurable_set Mβ) (T:measurable_set Mγ):
  (X ×r Y) ∈r (prod_measurable_set S T) =
  (X ∈r S) ∧ₑ (Y∈r T) :=
begin
  apply event.eq,
  rw rv_event_val_def,
  rw eand_val_def,
  rw rv_event_val_def,
  rw rv_event_val_def,
  rw prod_random_variable_val_def,
  rw prod_measurable_set_val_def,
  ext a,
  simp,
end
