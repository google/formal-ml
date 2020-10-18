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
import formal_ml.nnreal
import formal_ml.sum
import formal_ml.lattice
import formal_ml.measurable_space
import formal_ml.classical
import data.equiv.list

class probability_space (α: Type*) extends measure_theory.measure_space α :=
  (univ_one:volume.measure_of (set.univ) = 1) 

instance probability_space.to_measurable_space (α:Type*) [probability_space α]:measurable_space α :=
  measure_theory.measure_space.to_measurable_space

/-
  In measure theory (and specifically, in probability theory), not all sets of outcomes have
  probabilities that can be measured. We represent those that can be measured as measurable
  sets.
-/
def measurable_set {α:Type*} (M:measurable_space α):Type* := subtype (M.is_measurable')

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

@[simp]
lemma event_univ_val_def {Ω:Type*} {p:probability_space Ω}:
  (@event_univ Ω p).val = set.univ :=
begin
  unfold event_univ,
end

@[simp]
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

@[simp]
lemma Pr_le_one {Ω:Type*} {p:probability_space Ω} {E:event p}:
  Pr[E] ≤ 1 :=
begin
  have A1:Pr[E] ≤ Pr[@event_univ Ω p],
  {
    apply event_prob_mono2,
    rw event_univ_val_def,
    rw set.subset_def,simp,
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

@[simp]
lemma event_empty_val_def {Ω:Type*} {p:probability_space Ω}:
  (@event_empty Ω p).val = ∅  := rfl

@[simp]
lemma event_empty_val_def2 {Ω:Type*} {p:probability_space Ω}:
  (@has_emptyc.emptyc (event p) _).val = ∅  :=  rfl

@[simp]
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

@[simp]
lemma Pr_event_empty' {Ω:Type*} {p:probability_space Ω}:
  Pr[(∅:event p)] = 0 :=
begin
  rw has_emptyc_emptyc_event,
  apply Pr_event_empty,
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

@[simp]
lemma event_const_val_def {Ω:Type*} {p:probability_space Ω} (P:Prop):
  (@event_const _ p P).val={ω:Ω|P} := rfl

lemma event_const_true_eq_univ {Ω:Type*} {p:probability_space Ω} (P:Prop):P →
(@event_const _ p P)=event_univ :=
begin
  intro A1,
  apply event.eq,
  simp [A1],
end

lemma event_const_false_eq_empty {Ω:Type*} {p:probability_space Ω} (P:Prop):¬P →
(@event_const _ p P)=event_empty :=
begin
  intro A1,
  apply event.eq,
  simp [A1],
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

@[simp]
lemma measurable_inter_val_def {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set p):
  (measurable_inter A B).val= A.val ∩ B.val := rfl



instance measurable_set_has_inter {Ω:Type*} {p:measurable_space Ω}:has_inter (measurable_set p) := {
  inter := @measurable_inter Ω p,
}

@[simp]
lemma measurable_inter_val_def2 {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set p):
  (A ∩ B).val= A.val ∩ B.val := rfl


def eand {Ω:Type*} {p:probability_space Ω} (A B:event p):event p := 
  measurable_inter A B

/-{
  val:=A.val ∩ B.val,
  property := is_measurable.inter A.property B.property,
}-/

infixr `∧ₑ`:100 := eand

@[simp]
lemma eand_val_def {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∧ₑ B).val = A.val ∩ B.val :=
begin
  refl,
end

lemma eand_comm {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∧ₑ B) = (B ∧ₑ A) :=
begin
  apply event.eq,
  simp [set.inter_comm],
end

lemma eand_eq_self_of_subset_left {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A.val ⊆ B.val) →
  (A ∧ₑ B) = A :=
begin
  intro A1,
  apply event.eq,
  simp,
  --rw eand_val_def,
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

@[simp]
lemma measurable_union_val_def {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set p):
  (measurable_union A B).val=A.val ∪ B.val := rfl



instance measurable_set_has_union {Ω:Type*} {p:measurable_space Ω}:has_union (measurable_set p) := {
  union := @measurable_union Ω p,
}

@[simp]
lemma measurable_union_val_def2 {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set p):
  (A ∪ B).val = A.val ∪ B.val := rfl


def eor {Ω:Type*} {p:probability_space Ω} (A B:event p):event p := measurable_union A B
/-{
  val:=A.val ∪  B.val,
  property := is_measurable.union A.property B.property,
}-/

infixr `∨ₑ`:100 := eor

@[simp]
lemma eor_val_def {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∨ₑ B).val = A.val ∪ B.val :=
begin
  refl,
end

lemma eor_comm {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∨ₑ B) = (B ∨ₑ A) :=
begin
  apply event.eq,
  simp [set.union_comm],
end


lemma Pr_le_eor_left {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A] ≤ Pr[A ∨ₑ B] :=
begin
  apply event_prob_mono2,
  simp,
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
    repeat {rw event_prob_def},
    simp,
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
    repeat {rw event_prob_def},
    simp,
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

@[simp]
lemma enot_val_def {Ω:Type*} {p:probability_space Ω} (A:event p):
  (¬ₑ A).val = (A.val)ᶜ :=
begin
  refl,
end

/-
  Double negation elimination. However, it is hard to avoid in measure theory.
-/
@[simp]
lemma enot_enot_eq_self {Ω:Type*} {p:probability_space Ω} (A:event p):
  (¬ₑ (¬ₑ A)) = (A) :=
begin
  apply event.eq,
  simp,
end


@[simp]
lemma em_event {Ω:Type*} {p:probability_space Ω} (A:event p):
    A ∨ₑ (¬ₑ A)=event_univ :=
begin
  apply event.eq,
  simp,
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
  simp [set.inter_union_compl],
end

lemma Pr_em {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∧ₑ B] + Pr[A ∧ₑ ¬ₑ B] = Pr[A] :=
begin
  rw ← Pr_disjoint_eor,
  { --Pr[(A∧ₑ B)∨ₑ A∧ₑ ¬ₑ B] = Pr[A]
    rw em_event_cond,
  },
  { --disjoint ((A∧ₑ B).val) ((A∧ₑ ¬ₑ B).val)
    simp [set.disjoint_inter_compl],
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


lemma event_eqv_def {Ω:Type*} {p:probability_space Ω} (A B:event p):
    (A =ₑ B) = ((A ∧ₑ B) ∨ₑ ((¬ₑ A) ∧ₑ (¬ₑ B))) := rfl


lemma eor_partition {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∨ₑ B) = (A ∧ₑ ¬ₑ B) ∨ₑ  (A ∧ₑ B)  ∨ₑ (¬ₑ A ∧ₑ B) :=
begin
  apply event.eq,
  simp,
  ext ω,split;intros A1;simp at A1;simp [A1],
  {
    cases A1 with A1 A1; simp [A1],
    rw or_comm,
    apply classical.em,
    apply classical.em,
  },
  {
    cases A1 with A1 A1,
    simp [A1],
    cases A1 with A1 A1,
    simp [A1],
    simp [A1],
  },  
end

lemma Pr_eor_partition {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∨ₑ B] = Pr[A ∧ₑ ¬ₑ B] + Pr[A ∧ₑ B] + Pr[¬ₑ A ∧ₑ B] :=
begin
  rw eor_partition A B,
  rw Pr_disjoint_eor,
  rw Pr_disjoint_eor,
  ring,
  simp,
  rw set.disjoint_left,
  intros ω A1,
  simp at A1,
  simp [A1],
  simp,
  split;
  {rw set.disjoint_left,
  intros ω A1,
  simp at A1,
  simp [A1]},
end

lemma Pr_eor_plus_eand {Ω:Type*}  {p:probability_space Ω} (A B:event p):
  Pr[A ∨ₑ B] + Pr[A ∧ₑ B] = (Pr[A] + Pr[B]) :=
begin
  rw ← Pr_em A B,
  rw ← Pr_em B A,
  rw eand_comm B A,
  rw eand_comm B (¬ₑ A),
  rw Pr_eor_partition A B,
  ring,
end

lemma Pr_eor_eq_minus_eand {Ω:Type*}  {p:probability_space Ω} (A B:event p):
  Pr[A ∨ₑ B] = (Pr[A] + Pr[B])  - Pr[A ∧ₑ B] :=
begin
  rw ← Pr_eor_plus_eand,
  rw nnreal.add_sub_cancel,
end

lemma Pr_eor_eq_minus_eand_real {Ω:Type*}  {p:probability_space Ω} (A B:event p):
  (Pr[A ∨ₑ B]:real) = (Pr[A]:real) + (Pr[B]:real)  - (Pr[A ∧ₑ B]:real) :=
begin
  have A1:Pr[A ∨ₑ B] + Pr[A ∧ₑ B] = (Pr[A] + Pr[B]),
  {apply Pr_eor_plus_eand},
  rw ← nnreal.coe_eq at A1,
  repeat {rw nnreal.coe_add at A1},
  linarith,
end

def eall_encodable {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event p):event p := {
  val:=(⋂ b:β, (A b).val),
  property := is_measurable.Inter (λ b:β, (A b).property),
}

def eall' {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event p):event p := {
  val:=(⋂ b:β, (A b).val),
  property := is_measurable.Inter (λ b:β, (A b).property),
}


class has_eall (Ω β:Type*) (p:probability_space Ω) := {
  eall:(β → event p) → event p
}

--Instead of a one-off, there should be variants for a variety of types.
notation `∀ᵣ` binders `, ` r:(scoped f, has_eall.eall f) := r

class has_eall_in (Ω β γ:Type*) (p:probability_space Ω) := {
  eall_in:γ → (β → event p) → event p
}

notation `∀ᵣ` binders  ` in `  A, r:(scoped f, has_eall_in.eall_in A f) := r


instance has_eall_encodable {Ω β:Type*} {p:probability_space Ω} [encodable β]:has_eall Ω β p := {
  eall := λ (A:β → event p), eall_encodable A 
} 





--Instead of a one-off, there should be variants for a variety of types.
notation `∀ᵣ` binders `, ` r:(scoped f, has_eall.eall f) := r

@[simp]
lemma eall_val_def {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event p):
  (eall_encodable A).val = (⋂ b:β, (A b).val) := rfl

lemma eall_binder_def {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event p):
  (∀ᵣ x, A x) = (eall_encodable A):= rfl



def eall_prop {Ω β:Type*} {p:probability_space Ω} [E:encodable β]
  (P:β → Prop) [D:decidable_pred P]
  (A:β → event p):event p := @eall_encodable _ _ _ (@encodable.subtype β P E D) (λ (b:(subtype P)), A (b.val) )

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


instance has_eall_in.finset {Ω β:Type*} {p:probability_space Ω}:has_eall_in Ω β (finset β) p := {
  eall_in := (λ S f, eall_finset S f)
}


@[simp]
lemma eall_finset_val_def {Ω β:Type*} {p:probability_space Ω}
  (S:finset β) (A:β → event p):(eall_finset S A).val = ⋂ s∈ S, (A s).val := rfl

lemma has_eall_in_finset_def {Ω β:Type*} {p:probability_space Ω}
  (S:finset β) (A:β → event p):
  (∀ᵣ s in S, A s) = (eall_finset S A) := rfl



@[simp]
lemma has_eall_in_finset_val_def {Ω β:Type*} {p:probability_space Ω}
  (S:finset β) (A:β → event p):
  (∀ᵣ s in S, A s).val = ⋂ s∈ S, (A s).val := rfl

@[simp]
lemma has_eall_in_finset_val_def2 {Ω β:Type*} {p:probability_space Ω} {S:finset β} {A:β → event p}:
  (has_eall_in.eall_in S A).val = ⋂ s∈ S, (A s).val := rfl


--#print instances has_coe
@[simp]
lemma has_eall_in_finset_val_def3 {Ω β:Type*} {p:probability_space Ω} {S:finset β} {A:β → event p}:
  @has_coe.coe (event p) (set Ω) (coe_subtype) (has_eall_in.eall_in S A) = ⋂ s∈ S, (A s).val := rfl



/--Since a fintype is encodable, this could be represented with eall, and then proven equivalent to
  eall_finset. -/
def eall_fintype {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event p):event p := eall_finset finset.univ A


instance has_eall.fintype {Ω β:Type*} {p:probability_space Ω} [F:fintype β]:has_eall Ω β p := {
  eall := (λ A, eall_fintype F A)
}

lemma eall_fintype_eq_eall_finset {Ω β:Type*} {p:probability_space Ω}
  [F:fintype β] (A:β → event p):(∀ᵣ b, A b) = eall_finset finset.univ A := rfl


lemma eall_fintype_def {Ω β:Type*} {p:probability_space Ω} (F:fintype β) {A:β → event p}:
  (eall_fintype F A) = (∀ᵣ b, A b) := rfl

@[simp]
lemma eall_fintype_val_def {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event p):(eall_fintype F A).val = ⋂ (s:β), (A s).val :=
begin
  unfold eall_fintype,
  simp,
end
 
def measurable_Union {Ω β:Type*} {p:measurable_space Ω} [encodable β] (A:β → measurable_set p):
  measurable_set p := {
  val:=(⋃ b:β, (A b).val),
  property := is_measurable.Union (λ b:β, (A b).property),
}

@[simp]
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

@[simp]
lemma eany_val_def {Ω β:Type*} {p:probability_space Ω} [encodable β]
  (A:β → event p):(eany A).val=(⋃ b:β, (A b).val) := rfl

class has_eany (Ω β:Type*) (p:probability_space Ω) := {
  eany:(β → event p) → event p
}


notation `∃ᵣ ` binders `, ` r:(scoped f, has_eany.eany f) := r

class has_eany_in (Ω β γ:Type*) (p:probability_space Ω) := {
  eany_in:γ → (β → event p) → event p
}

notation `∃ᵣ ` binders  ` in ` S `, ` r:(scoped f, has_eany_in.eany_in S f) := r


instance has_eany.encodable {Ω β:Type*} {p:probability_space Ω} [E:encodable β]:has_eany Ω β p := {
  eany := (λ A:β → (event p), eany A)
}


lemma eany_encodable_notation_def {Ω β:Type*} {p:probability_space Ω} [encodable β]
  (A:β → event p):(∃ᵣ a, A a) = (eany A) := rfl

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

instance has_eany_in.finset {Ω β:Type*} {p:probability_space Ω}:has_eany_in Ω β (finset β) p := {
  eany_in := (λ (S:finset β) (A:β → (event p)), eany_finset S A)
}


@[simp]
lemma eany_finset_val_def {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event p):(eany_finset S A).val = ⋃ s∈ S, (A s).val := rfl

lemma eany_in_finset_def {Ω β:Type*} {p:probability_space Ω} {S:finset β} (A:β → event p):
  (∃ᵣ s in S, A s) = eany_finset S A := rfl

@[simp]
lemma eany_in_finset_val_def {Ω β:Type*} {p:probability_space Ω} {S:finset β} (A:β → event p):
  (∃ᵣ s in S, A s).val = ⋃ s∈ S, (A s).val := rfl

def eany_fintype {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event p):event p := eany_finset finset.univ A


lemma eany_fintype_def {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event p):eany_fintype F A = eany_finset finset.univ A := rfl


instance has_eany.fintype {Ω β:Type*} {p:probability_space Ω} [F:fintype β]:has_eany Ω β p := {
  eany := (λ  (A:β → (event p)), eany_fintype F A)
}

lemma has_eany_fintype_def {Ω β:Type*} {p:probability_space Ω} [F:fintype β] {A:β→ event p}:
  (∃ᵣ s, A s) = (eany_fintype F A) := rfl

@[simp]
lemma has_eany_fintype_val_def {Ω β:Type*} {p:probability_space Ω} [F:fintype β] {A:β→ event p}:
  (∃ᵣ s, A s).val = ⋃ (s:β), (A s).val :=
begin
  rw [has_eany_fintype_def,eany_fintype_def],
  simp,
end

@[simp]
lemma exists_empty {α Ω:Type*} {P:probability_space Ω} (f:α → event P):
  (∃ᵣ a in (∅:finset α), f a) = (∅:event P) :=
begin
  apply event.eq,
  simp,
end

@[simp]
lemma eall_finset_empty {Ω β:Type*} {p:probability_space Ω}
  (A:β → event p): (∀ᵣ s in (∅:finset β), A s) = event_univ :=
begin
  apply event.eq,
  simp,
end

lemma eany_finset_insert {Ω β:Type*} [D:decidable_eq β] {p:probability_space Ω}
  {S:finset β} {A:β → event p} {a:β}:
  (∃ᵣ (a':β) in (insert a S), A a') = (A a) ∨ₑ (∃ᵣ a' in S, A a') :=
begin
  apply event.eq,
  simp,
end

lemma eall_finset_insert {Ω β:Type*} [D:decidable_eq β] {p:probability_space Ω}
  {S:finset β} {A:β → event p} {a:β}:
  (∀ᵣ (a':β) in (insert a S), A a') = (A a) ∧ₑ (∀ᵣ a' in S, A a') :=
begin
  apply event.eq,
  simp,
end

lemma eany_finset_bound {Ω β:Type*} [D:decidable_eq β]
  {p:probability_space Ω}
  (S:finset β) (A:β → event p):Pr[∃ᵣ a in S, A a] ≤ finset.sum S (λ a:β, Pr[A a]) :=
begin
  apply finset.induction_on S,
  {
    simp,
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
  [F:fintype β] (A:β → event p):Pr[∃ᵣ (s:β), A s] ≤  ∑' a:β, Pr[A a] :=
begin
  rw tsum_fintype,
  apply eany_finset_bound,
end


lemma eany_fintype_bound2 {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event p) (k:nnreal):
  (∀ a:β, Pr[A a]≤ k) →
  Pr[∃ᵣ (s:β), A s] ≤ (fintype.card β) * k :=
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
  ∀ (S:finset β), (finset.prod S (λ b, Pr[A b])) = Pr[∀ᵣ s in S, A s]

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

lemma exists_not_eq_not_forall {α Ω:Type*} {P:probability_space Ω} (f:α → event P) {S:finset α}:
  (∃ᵣ a in S, ¬ₑ(f a)) = ¬ₑ (∀ᵣ a in S, f a) :=
begin
  apply event.eq,
  simp,
  rw set.Union_eq_comp_Inter_comp,
  simp,
end

lemma not_forall_not_eq_exists {α Ω:Type*} {P:probability_space Ω} (f:α → event P) {S:finset α}:
  ¬ₑ (∀ᵣ a in S, ¬ₑ f a) = (∃ᵣ a in S, f a) :=
begin
  apply event.eq,
  simp,
  rw set.Union_eq_comp_Inter_comp,
  simp,
end

lemma not_exists_eq_forall_not {α Ω:Type*} {P:probability_space Ω} (f:α → event P) {S:finset α}:
 ¬ₑ (∃ᵣ a in S, (f a)) = (∀ᵣ a in S, ¬ₑ (f a)) :=
begin
  apply event.eq,
  simp,
end

@[simp]
lemma forall_singleton {α Ω:Type*} {P:probability_space Ω} (f:α → event P) {x:α}:
  (∀ᵣ a in ({x}:finset α), f a) = f x :=
begin
  apply event.eq,
  simp,
end

@[simp]
lemma exists_singleton {α Ω:Type*} {P:probability_space Ω} (f:α → event P) {x:α}:
  (∃ᵣ a in ({x}:finset α), f a) = f x :=
begin
  apply event.eq,
  simp,
end

@[simp]
lemma distrib_exists_and {α Ω:Type*} {P:probability_space Ω} (f:α → event P) {S:finset α} {A:event P}:
  (∃ᵣ a in S, A ∧ₑ (f a))  =   A ∧ₑ (∃ᵣ a in S, f a) :=
begin
  apply event.eq,
  simp,
  ext ω,split;intros A1;simp at A1;simp [A1],
  cases A1 with i A1,
  simp [A1],
  apply exists.intro i,
  simp [A1],
end

lemma finset.pair_erase {α:Type*} {x y:α} [decidable_eq α]:x ≠ y → ({x, y}:finset α).erase x  = {y} :=
begin
  intros A1,
  rw finset.erase_insert,
  simp [A1],
end

lemma finset.singleton_erase {α:Type*} {x:α} [decidable_eq α]:({x}:finset α).erase x = ∅ := 
begin
  have A1:{x} = insert x (∅:finset α),
  {simp},
  rw A1,
  rw finset.erase_insert,
  simp,
end

lemma finset.union_erase {α:Type*} {S T:finset α} {x:α} [decidable_eq α]:
  (S ∪ T).erase x = (S.erase x) ∪ (T.erase x) :=
begin
  ext a;split;intros A1;simp at A1;simp,
  {simp [A1]},
  {cases A1;simp [A1]},
end

lemma finset.image_sum {α β:Type*} [add_comm_monoid β] [decidable_eq α] {S:finset α} {f:α → β} {g:α → α}:
  (∀ (s t:α),s∈ S → t∈ S→ s ≠ t → g s ≠ g t) →  (finset.image g S).sum f = S.sum (f ∘ g) :=
begin
  apply finset.induction_on S,
  {
    intros A1,
    refl,
  },
  {
    intros a s B1 B2 B3,
    simp,
    rw finset.sum_insert,
    rw finset.sum_insert,
    rw B2,
    intros s' t' B4 B5 B6,
    apply B3,
    {simp [B4]},
    {simp [B5]},
    apply B6,
    apply B1,
    intro B4,
    simp at B4,
    cases B4 with u B4,
    apply B3 u a,
    {simp [B4]},
    {simp},
    intro B5,
    subst u,
    apply B1,
    {simp [B4]},
    {simp [B4]},
  },
end

-- A specialized lemma of little generic value.
lemma finset.powerset_sum {α β:Type*} [add_comm_monoid β][decidable_eq α] {x:α} {S:finset α} (f:finset α → β):
  (x ∉ S) → ((insert x S).powerset.erase ∅).sum f = (S.powerset.erase ∅).sum f 
  + (S.powerset).sum (f ∘ (insert x)) :=
begin
  intros A0,
  rw finset.powerset_insert,
  rw finset.union_erase,
  rw finset.sum_union,
  have A1:((finset.image (insert x) S.powerset).erase ∅).sum f =
          (finset.image (insert x) S.powerset).sum f,
  {have A1A:((finset.image (insert x) S.powerset).erase ∅) =
          (finset.image (insert x) S.powerset),
   { rw finset.ext_iff,
     intros T;split;intros A1A1;simp at A1A1,
     {
       simp,cases A1A1 with A1A1 A1A2,
       cases A1A2 with U A1A2,
       apply exists.intro U,
       apply A1A2,
     },
     simp,
     split,
     {cases A1A1 with U A1A1,intros A1,subst T,simp at A1A1,apply A1A1},
     {apply A1A1},
   },
   rw A1A,
  },
  rw A1,
  have B1:(finset.image (insert x) S.powerset).sum f = 
          S.powerset.sum (f ∘ (insert x)),
  {
     apply @finset.image_sum (finset α) β,
     intros s t B1A B1B B1C B1D,
     apply B1C,
     simp at B1A,
     simp at B1B,
     rw finset.subset_iff at B1B,
     rw finset.subset_iff at B1A,
     rw finset.ext_iff at B1D,
  
     rw finset.ext_iff,
     intros a;split;intros B1F,
     {
       have B1G:a ∈ insert x s,
       {simp [B1F] },
       have B1H := (B1D a).mp B1G,
       simp at B1H,
       cases B1H,
       subst a,
       exfalso,
       apply A0,
       apply B1A,
       apply B1F,
       apply B1H,       
     },
     {
       have B1G:a ∈ insert x t,{simp [B1F]},
       have B1H := (B1D a).mpr B1G,
       simp at B1H,
       cases B1H,
       subst a,
       exfalso,
       apply A0,
       apply B1B,
       apply B1F,
       apply B1H,
     },
  },
  rw B1,
  
  rw finset.disjoint_left,
  intros T A2,
  simp at A2,
  simp,
  intros A3 U A5 A6,
  subst T,
  apply A0,
  cases A2 with A2 A7,
  rw finset.subset_iff at A7,
  apply A7,
  simp,
end 

lemma distrib_forall_eand {α Ω:Type*} {P:probability_space Ω} (f:α → event P) [decidable_eq α] {S:finset α} (A:event P):S.nonempty →
  (∀ᵣ a in S, A ∧ₑ f a) = A ∧ₑ (∀ᵣ a in S, f a) := 
begin
  intros A1,
  apply event.eq,
  simp,ext ω,split;intros A2;simp at A2;simp [A2],
  {have A3:=finset.nonempty.bex A1,
   cases A3 with a A3,
   have A4 := A2 a A3,
   simp [A4],
   intros b A5,
   apply (A2 b A5).right,
  },
  {
   apply A2.right,
  },
end 

lemma Pr_exists_eq_powerset {α Ω:Type*} {P:probability_space Ω} (f:α → event P) [decidable_eq α] {S:finset α}:  (Pr[(∃ᵣ a in S, (f a))]:real) = 
  -(S.powerset.erase ∅).sum  (λ T:finset α, (Pr[∀ᵣ a in T, f a]:real) *  (-1)^(T.card)) :=
begin
  revert f,
  apply finset.case_strong_induction_on S,
  {intros f, simp [finset.singleton_erase],},
  intros x s A3 A1 f,
  have A6 := (A1 s (finset.subset.refl s) f),
  rw finset.powerset_sum,
  rw eany_finset_insert,
  rw Pr_eor_eq_minus_eand_real,
  simp,
  rw ← distrib_exists_and,
  rw A6,
  have A8:=(A1 s (finset.subset.refl s) (λ a, f x∧ₑ f a)),
  rw A8,
  have A9:
-s.powerset.sum
          (λ (x_1 : finset α), (Pr[has_eall_in.eall_in (insert x x_1) f]:real) * (-1) ^ (insert x x_1).card) =
(Pr[f x]:real) + (s.powerset.erase ∅).sum
          (λ (T : finset α), (Pr[∀ᵣ (a : α) in T,f x∧ₑ f a]:real) * (-1) ^ T.card),
  {
    have A9A:insert ∅ (s.powerset.erase ∅) = (s).powerset,
    {rw finset.insert_erase, simp},
     have A9B:
     -(s).powerset.sum
            (λ (x_1 : finset α), (Pr[has_eall_in.eall_in (insert x x_1) f]:real) * (-1) ^ (insert x x_1).card) =
     -(insert ∅ (s.powerset.erase ∅)).sum
            (λ (x_1 : finset α), (Pr[has_eall_in.eall_in (insert x x_1) f]:real) * (-1) ^ (insert x x_1).card),
     {rw A9A},
     rw A9B,
     clear A9A A9B,
     rw add_comm (Pr[f x]:real),
     --rw finset.sum_insert,
     simp,
     have A9C:-((s).powerset.erase ∅).sum
            (λ (x_1 : finset α), (Pr[has_eall_in.eall_in (insert x x_1) f]:real) * (-1) ^ (insert x x_1).card) =
((s).powerset.erase ∅).sum
            ((λ (x_1 : finset α),- (Pr[has_eall_in.eall_in (insert x x_1) f]:real) * (-1) ^ (insert x x_1).card)),
     {simp},
     rw A9C,
     clear A9C,
     apply finset.sum_congr,
     {refl},
     intros T A9D,
     simp at A9D,
     rw distrib_forall_eand,
     rw eall_finset_insert,
     rw finset.card_insert_of_not_mem,
     rw pow_succ,
     {simp},
     intro A9F,
     cases A9D with A9D A9E,
     rw finset.subset_iff at A9E,
     have A9G := A9E A9F,
     apply A3,
     apply A9G,
     apply finset.nonempty_of_ne_empty,
     apply A9D.left,
  },
  rw A9,
  linarith,
  apply A3,
end

lemma Pr_all_not_eq_powerset {α Ω:Type*} {P:probability_space Ω} (f:α → event P) [decidable_eq α] {S:finset α}:  (Pr[(∀ᵣ a in S, ¬ₑ (f a))]:real) = 
  (S.powerset).sum  (λ T:finset α, (Pr[∀ᵣ a in T, f a]:real) *  (-1)^(T.card)) :=
begin
  --rw Pr_exists_eq_powerset,
  have A1:(insert ∅ ((S.powerset).erase ∅)).sum (λ T:finset α, (Pr[∀ᵣ a in T, f a]:real) *  (-1)^(T.card))
      =     S.powerset.sum (λ (T : finset α), ↑Pr[∀ᵣ (a : α) in T,f a] * (-1) ^ T.card),
  {
    rw finset.insert_erase,
    simp,
  },
  have A1:∅ ∈ S.powerset,
  {simp},
  rw ← finset.insert_erase A1,
  rw finset.sum_insert,simp,
  rw ← not_exists_eq_forall_not,
  rw ← Pr_one_minus_eq_not,
  rw nnreal.coe_sub,
  rw Pr_exists_eq_powerset,
  repeat {simp}, 
end

lemma finset.sum_distrib_left {α:Type*} {β:Type*} [comm_semiring β] {f:β} {g:α → β} 
    {S:finset α}:S.sum (λ a:α, f * (g a))=f * (S.sum g) :=
begin
  have A1:(λ a:α, f * (g a)) = (λ a:α, (add_monoid_hom.mul_left f).to_fun (g a)),
  {
    unfold add_monoid_hom.mul_left,
  },
  rw A1,
  have A2:f * (S.sum g) = (add_monoid_hom.mul_left f).to_fun (S.sum g),
  {
    unfold add_monoid_hom.mul_left,
  },
  rw A2,
  symmetry,
  apply @add_monoid_hom.map_sum α β β _ _ (add_monoid_hom.mul_left f) g S,
end

lemma independent_events_not_of_independent_events {α Ω:Type*} {P:probability_space Ω} (f:α → event P) (F:fintype α):independent_events f → independent_events (enot ∘ f) :=
begin
  intros A1,
  unfold independent_events,
  intros S,
  haveI A3:=classical.decidable_eq α,

  apply finset.case_strong_induction_on S,
  {simp},
  intros a s B1 B2,
  rw  ← not_exists_eq_forall_not,
  have A2:∀ (A:event P), 1 - (Pr[A]:real) = (Pr[¬ₑ A]:real),
  { 
    intro A,rw ← Pr_one_minus_eq_not,
    rw nnreal.coe_sub,
    {simp},
    apply Pr_le_one,
  },
  rw ← nnreal.coe_eq,
  rw ← A2,
  rw @Pr_exists_eq_powerset α Ω P f A3,
  unfold independent_events at A1,
  rw finset.prod_insert,
  rw finset.powerset_sum,
  rw B2 s (finset.subset.refl s),
  rw nnreal.coe_mul,
  rw ← A2,
  simp,
  rw ← @Pr_exists_eq_powerset α Ω P f A3,
  have A4:∀ x∈ s.powerset, 
     (Pr[has_eall_in.eall_in (insert a x) f]:real) * (-1) ^ (insert a x).card =
    -(Pr[f a]:real) * ((Pr[has_eall_in.eall_in x f]:real) * (-1) ^ (x).card),
  {intros x A4A,
   have A4B:a ∉ x,
   {simp at A4A,intro A4B,apply B1,apply A4A,apply A4B},
   rw ← A1,rw finset.prod_insert A4B,
   rw A1,
   rw nnreal.coe_mul,
   rw finset.card_insert_of_not_mem A4B,
   rw pow_succ,
   simp,
   repeat {rw ← mul_assoc},
  },
  have A5:s.powerset = s.powerset := rfl,
  rw finset.sum_congr A5 A4,
  have A6:s.powerset.sum (λ (x : finset α), -(Pr[f a]:real) * (↑Pr[has_eall_in.eall_in x f] * (-1) ^ x.card))
    = -((Pr[f a]:real)) * s.powerset.sum (λ (x : finset α), (↑Pr[has_eall_in.eall_in x f] * (-1) ^ x.card)),
  {simp,rw finset.sum_distrib_left},
  rw A6,  
  rw ← Pr_all_not_eq_powerset,
  rw ← not_forall_not_eq_exists,
  rw ← A2,
  simp,
  ring,
  repeat {exact B1},
end

lemma events_IID_not_of_events_IID {α Ω:Type*} {P:probability_space Ω} (f:α → event P) (F:fintype α):events_IID f → events_IID (enot ∘ f) :=
begin
  intros A1,
  unfold events_IID,
  split,
  {
    apply independent_events_not_of_independent_events,
    unfold events_IID at A1,
    apply A1.left,
  },
  {
    unfold events_IID at A1,
    intros x y,
    have C2 := A1.right x y,
    simp,
    rw ← Pr_one_minus_eq_not,
    rw ← Pr_one_minus_eq_not,
    rw C2,
  },
end

lemma events_IID_iff_events_IID_enot {α Ω:Type*} {P:probability_space Ω} (f:α → event P) (F:fintype α):events_IID f ↔ events_IID (enot ∘ f) :=
begin
  split,
  {
    apply events_IID_not_of_events_IID, 
  },
  {
    intros A1,
    have A2:f = enot ∘ (enot ∘ f),
    { apply funext, intro a, simp },
    rw A2,
    apply events_IID_not_of_events_IID,
    apply A1 
  },
end


def measurable_fun {α:Type*}  {β:Type*} (Mα:measurable_space α) (Mβ:measurable_space β):Type*
    := subtype (@measurable α β _ _)

def random_variable {α:Type*} (p:probability_space α) {β:Type*}
  (Mβ:measurable_space β):Type* := measurable_fun (probability_space.to_measurable_space α) Mβ

infixr  ` →ₘ `:80 := measurable_fun
infixr  ` →ᵣ `:80 := random_variable


lemma random_variable_val_eq_coe {Ω α:Type*} {P:probability_space Ω} {M:measurable_space α}  
  (X:P →ᵣ M):X.val = 
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


infixr ` ∈ᵣ `:80 := rv_event


@[simp]
lemma rv_event_val_def {α:Type*} {p : probability_space α} {β : Type*}
  [Mβ : measurable_space β] (X:p →ᵣ Mβ) (S:measurable_set Mβ):(X ∈ᵣ S).val = {a:α|X.val a ∈ S.val} :=
begin
  refl
end


lemma rv_event_empty {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X:random_variable p Mβ):X ∈ᵣ ∅ = ∅ :=
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
  {A B:measurable_set Mβ}:X ∈ᵣ (measurable_union A B) = (X ∈ᵣ A) ∨ₑ (X∈ᵣ B) :=
begin
  apply event.eq,
  repeat {rw rv_event_val_def},
  rw eor_val_def,
  repeat {rw rv_event_val_def},
  rw measurable_union_val_def,
  ext ω;split;intros A1;simp;simp at A1;apply A1
end

lemma rv_event_val_def' {α:Type*} {p : probability_space α} {β : Type*}
  [Mβ : measurable_space β] (X:p →ᵣ Mβ) (S:measurable_set Mβ) {ω:α}:
  (ω ∈ ((X ∈ᵣ S)))↔ (X.val ω ∈ S.val) :=
begin
  refl
end


lemma set.mem_Prop_def {α:Type*} {P:α → Prop} {a:α}:
    (a ∈ {a':α|P a'} )= P a := rfl


lemma rv_event_measurable_Union {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] {γ:Type*} [E:encodable γ] (X:random_variable p Mβ) 
  {f:γ → measurable_set Mβ}:X ∈ᵣ (measurable_Union f) = 
  measurable_Union (λ i, X ∈ᵣ (f i)) :=
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

@[simp]
lemma measurable_set_compl_val_def {α:Type*} [M:measurable_space α] {E:@measurable_set α M}:
    (Eᶜ).val = (E.val)ᶜ  :=rfl


instance event_has_compl {α:Type*} [M:probability_space α]:has_compl (@event α M) := {
  compl := λ E, ⟨E.valᶜ, is_measurable.compl E.property⟩,
}


lemma event_neg_def {α:Type*} [M:probability_space α] {E:@event α M}:
    Eᶜ = ⟨ E.valᶜ, is_measurable.compl E.property⟩ :=rfl

@[simp]
lemma event_neg_val_def {α:Type*} [M:probability_space α] {E:@event α M}:
    (Eᶜ).val = (E.val)ᶜ := rfl


--@[simp]
lemma event_simp_def {α:Type*} [p:probability_space α] {X:set α} {H:is_measurable X}:
  (subtype.mk X H).val = X := rfl

--@[simp]
lemma measurable_set_simp_def {α:Type*} [p:measurable_space α] {X:set α} {H:is_measurable X}:
  (subtype.mk X H).val = X := rfl

lemma pr_comp_event {Ω:Type*} {p:probability_space Ω} {X:p →ᵣ borel real}
 {E:@measurable_set ℝ (borel ℝ)}:
 (X ∈ᵣ (Eᶜ)) = (X ∈ᵣ E)ᶜ :=
begin
  apply event.eq,
  simp,
  refl,
end

lemma rv_event_compl {Ω:Type*} {MΩ:probability_space Ω} {β:Type*} [Mβ:measurable_space β]
  (X:MΩ →ᵣ Mβ) (S:measurable_set Mβ):(X ∈ᵣ (Sᶜ)) = (rv_event X S)ᶜ :=
begin
  apply event.eq,
  simp,
  refl,
end

lemma neg_eq_not {Ω:Type*} {p:probability_space Ω} (A:event p):
  Aᶜ = ¬ₑ A :=
begin
  apply event.eq,
  simp,
end

def random_variable_identical {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X Y:random_variable p Mβ):Prop :=
  ∀ (S:measurable_set Mβ), Pr[X ∈ᵣ S] = Pr[Y ∈ᵣ S]

def random_variable_independent_pair {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] {γ:Type*} [Mγ:measurable_space γ] (X:p →ᵣ Mβ)
  (Y:p →ᵣ Mγ):Prop :=
  ∀ (S:measurable_set Mβ) (T:measurable_set Mγ), independent_event_pair (X ∈ᵣ S) (Y ∈ᵣ T)

def random_variable_independent {α:Type*} {p:probability_space α} {β:Type*}
  [fintype β]
  {γ:β → Type*} [Mγ:Π b, measurable_space (γ b)] (X:Π b, random_variable p (Mγ b)):Prop :=
  ∀ (S:Π b, measurable_set (Mγ b)), independent_events (λ b:β, ((X b) ∈ᵣ (S b)))

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

@[simp]
lemma compose_measurable_fun_val_def {Ω : Type*} {β : Type*} {γ : Type*}
  [MΩ : measurable_space Ω] [Mβ : measurable_space β]
  [Mγ : measurable_space γ] (Y:Mβ →ₘ Mγ) (X:MΩ →ₘ Mβ):
  (Y ∘m X).val = (λ ω:Ω, Y.val (X.val ω)) :=
begin
  refl
end


def rv_compose {α : Type*} {β : Type*} {γ : Type*}
  {p : probability_space α} {Mβ : measurable_space β}
  {Mγ : measurable_space γ} (X:measurable_fun Mβ Mγ) (Y:random_variable p Mβ):random_variable p Mγ :=
  compose_measurable_fun X Y


infixr  ` ∘r `:80 := rv_compose

@[simp]
lemma rv_compose_val_def {Ω : Type*} {β : Type*} {γ : Type*}
  [Mβ : measurable_space β]
  [Mγ : measurable_space γ] {p : probability_space Ω} (Y:Mβ →ₘ Mγ) (X:p →ᵣ Mβ):
  (Y ∘r X).val = (λ ω:Ω, Y.val (X.val ω)) :=
begin
  refl
end

def prod_space {α β:Type*} (Mα:measurable_space α) (Mβ:measurable_space β):=(@prod.measurable_space α β Mα Mβ)

infixr  ` ×ₘ `:80 := prod_space


def mf_fst {α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}:measurable_fun
    (Mα ×ₘ Mβ) Mα := {
    val:= (λ x:(α × β), x.fst),
    property := fst_measurable,
  }

def mf_snd {α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}:measurable_fun (prod_space Mα Mβ) Mβ := {
    val:= (λ x:(α × β), x.snd),
    property := snd_measurable,
  }

def const_measurable_fun {Ω : Type*} [MΩ : measurable_space Ω] {β : Type*}
   [Mβ : measurable_space β] (c : β):MΩ →ₘ Mβ := {
     val := (λ (ω : Ω), c),
     property := const_measurable c,
   }

lemma const_measurable_fun_val_def {Ω : Type*} [MΩ : measurable_space Ω] {β : Type*}
   [Mβ : measurable_space β] (c : β):(const_measurable_fun c).val = (λ (ω : Ω), c) := rfl

def const_random_variable {Ω : Type*} {P:probability_space Ω}
   {β : Type*}
   [Mβ : measurable_space β] (c : β):P →ᵣ Mβ := const_measurable_fun c


def prod_measurable_fun
{α β γ:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β} {Mγ:measurable_space γ}
  (X:measurable_fun Mα Mβ) (Y:measurable_fun Mα Mγ):measurable_fun Mα (Mβ ×ₘ Mγ) := {
    val := (λ a:α, prod.mk (X.val a) (Y.val a)),
    property := measurable_fun_product_measurable X.val Y.val X.property Y.property,
  }

lemma prod_measurable_fun_val_def {Ω : Type*} {β : Type*} {γ : Type*} {MΩ : measurable_space Ω}
  {Mβ : measurable_space β} {Mγ : measurable_space γ} {X:MΩ  →ₘ Mβ}
  {Y:MΩ  →ₘ Mγ}: (prod_measurable_fun X Y).val = λ ω:Ω, prod.mk (X.val ω) (Y.val ω) :=
begin
  refl
end

def prod_random_variable
{α β γ:Type*}
  {P:probability_space α} {Mβ:measurable_space β} {Mγ:measurable_space γ}
  (X:random_variable P Mβ) (Y:random_variable P Mγ):random_variable P (Mβ ×ₘ Mγ) :=
  prod_measurable_fun X Y

infixr  ` ×ᵣ `:80 := prod_random_variable


@[simp]
lemma prod_random_variable_val_def {Ω : Type*} {β : Type*} {γ : Type*}
  {P : probability_space Ω} {Mβ : measurable_space β} {Mγ : measurable_space γ} {X:P →ᵣ Mβ}
  {Y:P →ᵣ Mγ}: (X ×ᵣ Y).val = λ ω:Ω, prod.mk (X.val ω) (Y.val ω) :=
begin
  refl
end


def prod_measurable_set {β : Type*} {γ : Type*}
  {Mβ : measurable_space β} 
  {Mγ : measurable_space γ} 
  (X:measurable_set Mβ) (Y:measurable_set Mγ):measurable_set (Mβ ×ₘ Mγ) := {
  val := (set.prod X.val Y.val),
  property := is_measurable_prod' X.property Y.property
}

@[simp]
lemma prod_measurable_set_val_def {β : Type*} {γ : Type*}
  {Mβ : measurable_space β} 
  {Mγ : measurable_space γ} 
  (X:measurable_set Mβ) (Y:measurable_set Mγ):
  (prod_measurable_set X Y).val = set.prod X.val Y.val := rfl


class has_measurable_equality {α:Type*} (M:measurable_space α):Prop := (is_measurable_eq:is_measurable {p:α × α|p.fst = p.snd})

def measurable_set_eq {α:Type*} {M:measurable_space α} [E:has_measurable_equality M]
  :measurable_set (M ×ₘ M) := measurable_set.mk E.is_measurable_eq



lemma measurable_set_eq_val {α:Type*} {M:measurable_space α} [E:has_measurable_equality M]:
  (@measurable_set_eq α M E).val = {p:α × α|p.fst = p.snd} := rfl


def measurable_set_ne {α:Type*} {M:measurable_space α} [E:has_measurable_equality M]
  :measurable_set (M ×ₘ M) := measurable_set.mk (is_measurable.compl E.is_measurable_eq)



lemma measurable_set_ne_val {α:Type*} {M:measurable_space α} [E:has_measurable_equality M]:
  (@measurable_set_ne α M E).val = {p:α × α|p.fst ≠ p.snd} := rfl




lemma diagonal_eq {α:Type*}:{p:α × α|p.fst  = p.snd}=⋃ (a:α), set.prod {a} {a} :=
begin
    ext,split;intros A1A;simp;simp at A1A,
    {
      apply exists.intro x.fst,
      ext;simp,
      rw A1A,
    },
    {
      cases A1A with i A1A,
      cases A1A,
      simp,
    },
end


instance measurable_set_eq_top_measurable {α:Type*} (E:encodable α) (M:top_measurable α):has_measurable_equality (M.to_measurable_space) :=  {
  is_measurable_eq := begin
  rw diagonal_eq,
  apply is_measurable.Union,
  intros a,
  apply is_measurable_prod',
  repeat {apply M.all_measurable},
end
}

instance measurable_set_eq_bool:has_measurable_equality bool.measurable_space :=  {
  is_measurable_eq := begin
  rw diagonal_eq,
  apply is_measurable.Union,
  intros a,
  apply is_measurable_prod',
  repeat {apply measurable_space.is_measurable_top},
end
}

instance measurable_set_eq_int:has_measurable_equality int.measurable_space :=  {
  is_measurable_eq := begin
  rw diagonal_eq,
  apply is_measurable.Union,
  intros a,
  apply is_measurable_prod',
  repeat {apply measurable_space.is_measurable_top},
end
}

def random_variable_eq {Ω:Type*} {P:probability_space Ω} {α:Type*} [M:measurable_space α]
   [E:has_measurable_equality M] (X Y:P →ᵣ M):event P := 
    (X ×ᵣ Y) ∈ᵣ (measurable_set_eq)

infixr  ` =ᵣ `:100 := random_variable_eq  


@[simp]
lemma rv_eq_val_def {α:Type*} {p : probability_space α} {β : Type*}
   [Mβ :measurable_space β] [has_measurable_equality Mβ] (X Y:p →ᵣ Mβ):
  (X =ᵣ Y).val = {a:α| X.val a = Y.val a} :=
begin
  unfold random_variable_eq,
  rw rv_event_val_def,
  rw prod_random_variable_val_def,
  rw measurable_set_eq_val,
  simp,
end


def random_variable_ne {Ω:Type*} {P:probability_space Ω} {α:Type*} [M:measurable_space α]
   [E:has_measurable_equality M] (X Y:P →ᵣ M):event P := 
    ¬ₑ (X =ᵣ Y)

infixr  ` ≠ᵣ `:100 := random_variable_ne

@[simp]
lemma rv_ne_val_def {α:Type*} {p : probability_space α} {β : Type*}
   [Mβ :measurable_space β] [has_measurable_equality Mβ] (X Y:p →ᵣ Mβ):
  (X ≠ᵣ Y).val = {a:α| X.val a ≠ Y.val a} :=
begin
  unfold random_variable_ne,
  rw enot_val_def,
  rw rv_eq_val_def,
  simp,
  ext a,split;intros A1;simp;simp at A1;apply A1,
end



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
  [fintype β] {γ : Type*} [Mγ : measurable_space γ] (X:β → p →ᵣ Mγ) (S:measurable_set Mγ):
  random_variables_IID X  → events_IID (λ b:β, (X b) ∈ᵣ S) :=
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

@[simp]
lemma measurable_set_preimage_val_def {α:Type*}  {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β]
  (f:measurable_fun Mα Mβ) (S:measurable_set Mβ):
  (measurable_set_preimage f S).val = (set.preimage (f.val) (S.val)) := rfl

lemma compose_measurable_fun_measurable_set {Ω : Type*} {β : Type*} {γ : Type*}
  [MΩ : measurable_space Ω] [Mβ : measurable_space β]
  [Mγ : measurable_space γ] (Y:Mβ →ₘ Mγ) (X:MΩ →ₘ Mβ) (S:measurable_set Mγ):
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
  (X ∘r Y) ∈ᵣ S = (Y ∈ᵣ (measurable_set_preimage X S)) :=
begin
  apply compose_measurable_fun_measurable_set,
end

lemma compose_independent {α:Type*} {p:probability_space α} {β:Type*}
  [fintype β]
  {γ:Type*} [Mγ:measurable_space γ]
  {κ:Type*} [Mκ:measurable_space κ] (X:β → random_variable p Mγ) (Y:Mγ →ₘ  Mκ):
  random_variable_independent X → random_variable_independent (λ b:β, Y ∘r (X b)) :=
begin
  unfold random_variable_independent,
  intros A1 S T,
  unfold independent_events,
  have A2:(λ (b : β), Pr[(Y ∘r X b) ∈ᵣ S b]) =
      (λ (b : β), Pr[(X b) ∈ᵣ (measurable_set_preimage Y (S b))]),
  {
    ext b,
    rw rv_compose_measurable_set,
  },
  rw A2,
  have A3:(λ (b : β), (Y ∘r X b) ∈ᵣ S b) =
      (λ (b : β), (X b) ∈ᵣ (measurable_set_preimage Y (S b))),
  {
    ext b,
    rw rv_compose_measurable_set,
  },
  rw A3,
  apply A1,
end


lemma compose_identical {α:Type*} {p:probability_space α}
  {γ:Type*} [Mγ:measurable_space γ]
  {κ:Type*} [Mκ:measurable_space κ] (X₁ X₂:random_variable p Mγ) (Y:Mγ →ₘ  Mκ):
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
  {κ:Type*} [Mκ:measurable_space κ] (X:β → random_variable p Mγ) (Y:Mγ →ₘ  Mκ):
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
    rw finset.Union_insert',
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
  apply Pr_le_one,
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
  (X ×ᵣ Y) ∈ᵣ (prod_measurable_set S T) =
  (X ∈ᵣ S) ∧ₑ (Y∈ᵣ T) :=
begin
  apply event.eq,
  simp,
  refl
end

