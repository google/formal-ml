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
import formal_ml.real_random_variable
import data.complex.exponential
import formal_ml.ennreal
import formal_ml.nnreal
import formal_ml.sum
import formal_ml.exp_bound


/-
  The Vapnik-Chevronenkis Dimension and its connection to learning is one of the most
  remarkable and fundamental results in machine learning. In particular, it allows us
  to understand simple, infinite hypothesis spaces, like the separating hyperplane,
  and begin to understand the complexity of neural networks. This analysis is also a
  precursor to understanding support vector machines and structural risk.
 -/

lemma finset.subset_of_not_mem_of_subset_insert {α:Type*} [decidable_eq α] {x:α} {S T:finset α}:x∉ S →
  S ⊆ insert x T → S ⊆ T :=
begin
  intros A1 A2,
  rw finset.subset_iff,
  rw finset.subset_iff at A2,
  intros a B1,
  have B2 := A2 B1,
  rw finset.mem_insert at B2,
  cases B2,
  subst a,
  exfalso,
  apply A1,
  apply B1,
  apply B2,
end



/-
  A type is of class inhabited if it has at least one element.
  Thus, its cardinality is not zero.
--Not sure where to put this. Here is fine for now.
--Note: this is the kind of trivial thing that takes ten minutes to prove.
-/

/--
  Normally, we would not assume that the representation type was encodable (i.e. countable).
  Specifically, one could imagine real numbers as part of the representation type.
  However, that creates some issues with measurability.
 -/
structure VC_PAC_problem :=
   (Ω:Type*)                           -- Underlying outcome type
   (p:probability_space Ω)             -- Underlying probability space
   (X:Type*)                           -- instance type
   (MX:measurable_space X)             -- Measurable space for the instances
   (H:Type*)                           -- Representation type
   (ER:encodable H)                    -- The representation type is encodable.
   (R:H → (set X))                     -- Representation scheme
   (MC:∀ h:H, is_measurable (R(h)))   -- Concepts are measurable.
   (Di:Type*)                          -- number of examples
   (FDi:fintype Di)                    -- number of examples are finite
   (EDi:encodable Di)                  -- example index is encodable
   (D:Di → (p →ᵣ MX))                  -- example distribution
   (IID:random_variables_IID D)        -- examples are IID
   (has_example:inhabited Di)          -- there exists an example
   (c:H)                               -- the correct hypothesis



namespace VC_PAC_problem

variable (P:VC_PAC_problem)


--The measurable space for the hypotheses is ⊤.
--Everything is measurable.
def MH:measurable_space (P.H) := ⊤

--The space of training datasets.
def data_space:measurable_space (P.Di → P.X) := @measurable_space.pi P.Di (λ i, P.X) (λ i, P.MX)


--The learning algorithm is a function of the training dataset.
def algorithm:Type* := measurable_fun (P.data_space) P.MH


def concept (h:P.H):measurable_set P.MX := measurable_set.mk (P.MC h)  

def target_concept:measurable_set P.MX := (P.concept P.c)  

def in_concept (h:P.H) (i:P.Di):event (P.p) := @rv_event P.Ω P.p P.X P.MX (P.D i) (P.concept h)

def label_positive (i:P.Di):event (P.p) := P.in_concept P.c i

def example_correct (h:P.H) (i:P.Di):event (P.p) :=
    (P.in_concept h i) =ₑ (P.label_positive i)

def example_error (h:P.H) (i:P.Di):event (P.p) :=
    ¬ₑ (P.example_correct h i)

/-
  num_examples P is the number of examples in the problem.
  This is defined as the cardinality of the index type of the examples.
-/
def num_examples:nat
   := @fintype.card P.Di P.FDi

--the measurable space on hypotheses and instances.
def MHX:measurable_space (P.H × P.X) := P.MH ×ₘ P.MX

noncomputable def training_error (h:P.H):P.p →ᵣ (borel nnreal) :=
  average_identifier (P.example_error h) (P.FDi)

/-
  The number of examples is the number of elements of type P.Di.
  P.FDi.elems is the set of all elements in P.Di, and P.FDi.elems.card is the cardinality of
  P.FDi.elems.
-/
lemma num_examples_eq_finset_card:
  P.num_examples = P.FDi.elems.card :=
begin
  refl,
end

/-
  The number of examples do not equal zero.
 -/
lemma num_examples_ne_zero:
  P.num_examples ≠ 0 :=
begin
  unfold VC_PAC_problem.num_examples,
  apply @card_ne_zero_of_inhabited P.Di P.has_example P.FDi,
end

/-
  The expected test error.
  The test error is equal to the expected training error. Because we have not defined a generating
  process for examples, we use this as the definition.
-/
noncomputable def test_error' 
    (h:P.H):ennreal := E[P.training_error h]


lemma example_error_IID (P:VC_PAC_problem) (i:P.H):
  @events_IID P.Ω P.Di P.p P.FDi  (P.example_error i) :=
begin
  /-
    To prove that the errors of a particular hypothesis are IID, we must use an alternate
    formulation of the example_error events. Specifically, instead of constructing a hierarchy
    of random variables, we must make a leap from the established IID random variable
    (the data), construct another IID random variable (the product of
    the classification and the label), and show that the set of all label/classification pairs
    that aren't equal are a measurable set (because has_measurable_eq Mγ).

    The indexed set of events of each IID random variable being in a measurable set is IID,
    so the result holds.

    Note that while this proof looks a little long, most of the proof is just unwrapping
    the traditional and internal definitions of example error, and then using simp to show that
    they are equal on all outcomes.
  -/
  let S:measurable_set P.MX := (P.concept i ∩ (P.target_concept)ᶜ) ∪ ((P.concept i)ᶜ ∩ (P.target_concept)),
  begin
  have B1:S = (P.concept i ∩ P.target_conceptᶜ) ∪ (((P.concept i)ᶜ) ∩ ((P.target_concept))) := rfl,
  have A1:@random_variables_IID P.Ω P.p P.Di P.FDi P.X P.MX P.D,
  {
    apply P.IID,
  },
  have A2:@events_IID P.Ω P.Di P.p P.FDi (λ j:P.Di, @rv_event P.Ω P.p P.X P.MX (P.D j) S),
  {
    apply rv_event_IID,
    apply A1,
  },
  have A3: (λ j:P.Di, @rv_event P.Ω P.p P.X P.MX (P.D j) S) = P.example_error i,
  {
    apply funext,
    intro j,
    apply event.eq,
    rw B1,     
    unfold VC_PAC_problem.example_error VC_PAC_problem.example_correct VC_PAC_problem.target_concept
    VC_PAC_problem.label_positive  VC_PAC_problem.in_concept,
    rw enot_val_def,
    rw event_eqv_def,
    rw rv_event_val_def,
    rw eor_val_def,
    repeat {rw eand_val_def},
    rw measurable_union_val_def2,
    repeat {rw measurable_inter_val_def2},
    repeat {rw measurable_set_compl_val_def},
    repeat {rw enot_val_def},
    repeat {rw rv_event_val_def},
    ext ω,
    split;intros A3B;simp;simp at A3B,
    {
      cases A3B with A3B A3B,
      {
        split,
        {
          intros A3BA,
          apply A3B.right,
        },
        {
          intro A3BA,
          exfalso,
          apply A3BA,
          apply A3B.left,
        },
      },
      {
        split;intros A3BA,
        {
          intros A3BB,
          apply A3B.left A3BA,
        },
        {
          apply A3B.right,
        },
      },
    },
    {
      cases (classical.em ((P.D j).val ω ∈ (P.concept i).val)) with A3C A3C,
      {
        apply or.inl (and.intro A3C (A3B.left A3C)),
      },
      {
        apply or.inr (and.intro A3C (A3B.right A3C)),
      },
    },
  },
  rw ← A3,
  exact A2,
  end
end


/-
  The expected test error.
  The test error is equal to the expected training error. Because we have not defined a generating
  process for examples, we use this as the definition.
-/
lemma test_error_def
    (h:P.H) (i:P.Di):P.test_error' h = Pr[P.example_error h i] :=
begin
  unfold VC_PAC_problem.test_error' VC_PAC_problem.training_error,
  rw average_identifier_eq_pr_elem,
  apply VC_PAC_problem.example_error_IID,  
end



--This is probably true, but just very hard to prove.
def test_error_measurable:Prop := 
  @measurable P.H ennreal P.MH (borel ennreal) P.test_error'




noncomputable def test_error (TEM:P.test_error_measurable):P.MH →ₘ (borel ennreal) := {
  val := P.test_error',
  property := TEM,
}

def C:set (set P.X) := set.range P.R


def Φ:ℕ → ℕ → ℕ
| 0 m := 1
| d 0 := 1
| (nat.succ d) (nat.succ m) :=  Φ (d.succ) m + Φ d m

@[simp]
lemma phi_d_zero_eq_one {d:ℕ}:Φ d 0 = 1 :=
begin
  cases d;unfold Φ,
end

@[simp]
lemma phi_zero_m_eq_one {m:ℕ}:Φ 0 m = 1 :=
begin
  cases m;unfold Φ,
end

lemma phi_succ_succ {d m:ℕ}:Φ d.succ m.succ = Φ d.succ m + Φ d m := rfl


end VC_PAC_problem




def finset.to_set_of_sets {α:Type*} (C:finset (finset α)):set (set α) :=
  (λ c:finset α, (↑c:set α)) '' (↑C:set (finset α))


lemma finset.mem_to_set_of_sets {α:Type*} {C:finset (finset α)} {c:finset α}:
  (↑c ∈ (C.to_set_of_sets)) ↔ c ∈ C :=
begin
  unfold finset.to_set_of_sets,
  simp,
end

lemma finset.mem_to_set_of_sets' {α:Type*} {C:finset (finset α)} {c:set α}:
  c∈ C.to_set_of_sets ↔ ∃ c' ∈ C, c=(↑c') :=
begin
  unfold finset.to_set_of_sets,
  split;intro A1,
  {
    simp at A1,
    cases A1 with c' A1,
    apply exists.intro c',
    apply exists.intro A1.left,
    rw A1.right,
  },
  {
    simp,
    cases A1 with c' A1,
    apply exists.intro c',
    cases A1 with A1 A2,
    simp [A1, A2],
  },
end


/-
  It is important to be able to talk about the VC dimension of a set of sets without
  referring to a particular problem. For that reason, I have placed it outside of the
  VC_PAC_problem.
-/
namespace VC_PAC_problem
section VC_PAC_problem
universe u
variable {α:Type u}
open_locale classical

--The set of restrictions of concepts onto S, conventionally written as Πc(S) and represented as vectors.
noncomputable def restrict_set (C:set (set α)) (S:finset α):finset (finset α) := 
  S.powerset.filter (λ x, ∃ c∈ C, c ∩ (↑S) = (↑x)) 


--Does there exist a concept that agrees with any subset of S on S?
def shatters (C:set (set α)) (S:finset α):Prop := 
  (restrict_set C S) = S.powerset

--What is the largest extended natural number n such that all finite sets of size ≤ n can be shattered?
--Note that if the VC dimension is infinity, then that means that any finite set can be shattered, 
--but it does not say anything about infinite sets. See Kearns and Vazirani, page 51.
--For example, the Borel algebra on the reals shatters every finite set, but does not shatter
--all infinite sets (e.g. it does not shatter the reals themselves), so it has a VC dimension of
--infinity.
--Note: an empty hypothesis space, by this definition, has a VCD of infinity. This may cause problems.
/-noncomputable def VCD (C:set (set α)):enat := Sup {n:enat|∃ (X':finset α), ((X'.card:enat) = n)  ∧
  shatters C (X')}-/

/-
  Consider all sets that can be shattered. What is the supremum of their sizes (in enat)?
 -/
noncomputable def VCD (C:set (set α)):enat := Sup 
  ((λ X':finset α, (↑(X'.card):enat)) '' {X':finset α|shatters C (X')})


/-
  Normally, this restriction is defined for sets of exactly size m. However, this
  runs into problems if there do not exist sets of a certain size.
 -/
noncomputable def restrict_set_bound (C:set (set α)) (m:ℕ):nat := Sup ((λ X', (restrict_set C X').card) '' 
   {X':finset α|X'.card ≤ m})



lemma restrict_set_subset {C:set (set α)} (S:finset α):restrict_set C S⊆ S.powerset :=
begin
  unfold restrict_set,
  simp,
end

lemma mem_restrict_set_subset {C:set (set α)} {S:finset α} {c:finset α}:c ∈ restrict_set C S →
  c⊆ S :=
begin
  intros A1,
  rw ← finset.mem_powerset,
  have A2:= @restrict_set_subset α C S,
  apply A2,
  apply A1,
end

-- filter (λ x, true)
--{S':set P.X|∃ c ∈ P.C, (S')= c ∩ (S)}
lemma mem_restrict_set {C:set (set α)} (S:finset α) (T:finset α):
  T ∈ restrict_set C S ↔ (∃ c∈ C, c ∩ (↑S) = (↑T)) :=
begin
  unfold restrict_set,
  rw finset.mem_filter,
  split;intros B1,
  {
    apply B1.right,
  },
  {
    split,
    rw finset.mem_powerset,
    cases B1 with c B1,
    cases B1 with B1 B2,
    rw finset.subset_iff,
    intros x A1,
    have B3:= set.inter_subset_right c (↑S),
    rw B2 at B3,
    apply B3,
    simp,
    apply A1,
    apply B1,
  },
end

lemma shatters_iff {C:set (set α)} (S:finset α):
   (shatters C S) ↔ (∀ S'⊆ S, ∃ c∈ C, c ∩(↑S) = (↑S')) :=
begin
  unfold shatters,
  split;intros A1,
  {
    intros S' B1,
    rw finset.ext_iff at A1,
    have B2 := A1 S',
    rw finset.mem_powerset at B2,
    rw ← B2 at B1,
    rw mem_restrict_set at B1,
    apply B1,
  },
  {
    apply finset.subset.antisymm,
    apply restrict_set_subset,
    rw finset.subset_iff,
    intros S' C1,
    rw finset.mem_powerset at C1,
    have C2 := A1 S' C1,
    rw mem_restrict_set,
    apply C2,
  },
end

lemma shatters_def (C:set (set α)) (S:finset α):
  shatters C S = ((restrict_set C S) = S.powerset) := rfl

/-Introducing a trivial upper bound establishes that Sup exists meaningfully (instead
  of a default value of zero).-/
lemma restrict_set_trivial_upper_bound  {C:set (set α)} (X':finset α):
  (restrict_set C X').card ≤ 2^(X'.card) :=
begin
  have B1:(restrict_set C X').card ≤ X'.powerset.card,
  {
    apply finset.card_le_of_subset,
    apply restrict_set_subset,
  },
  apply le_trans B1,
  rw finset.card_powerset,
end

lemma restrict_set_le_upper_bound {C:set (set α)} (X':finset α):
  (restrict_set C X').card ≤ restrict_set_bound C (X'.card) :=
begin
  apply le_cSup,
  rw bdd_above_def,
  unfold upper_bounds,
  apply exists.intro (2^(X'.card)),
  simp,
  intros a X'',
  intros A1 A2,
  subst A2,
  have A3:2^(X''.card) ≤ 2^(X'.card),
  {
    apply linear_ordered_semiring.pow_monotone one_le_two A1,
  },
  apply le_trans _ A3,
  apply restrict_set_trivial_upper_bound,
  simp,
  apply exists.intro X',
  split,
  refl,
  refl,
end


lemma shatters_card_le_VCD {C:set (set α)} {S:finset α}:shatters C S → (S.card:enat) ≤ VCD C :=
begin
  unfold VCD,
  intros A1,
  apply le_Sup,
  simp,
  apply exists.intro S,
  simp [A1],
end

lemma VCD_le {C:set (set α)} {d:enat}:(∀ S:finset α, shatters C S → (↑S.card)  ≤ d) → VCD C ≤ d :=
begin
  intros A1,
  unfold VCD,
  apply Sup_le,
  intros b B1,
  simp at B1,
  cases B1 with X' B1,
  cases B1 with B1 B2,
  subst b,
  apply A1 X' B1,
end


lemma restrict_set_elements_subset_of_VCD_zero {C:set (set α)} {S T U:finset α}:(VCD C = 0) →
  T ∈ (restrict_set C S) → U ∈ (restrict_set C S) → T ⊆ U :=
begin
  intros A1 A2 A3,
  rw finset.subset_iff,
  intros x B1,
  apply by_contradiction,
  intros B2,
  have B3 := (mem_restrict_set _ _).mp A2,
  have B4 := (mem_restrict_set _ _).mp A3,
  cases B3 with c_yes B3,
  cases B4 with c_no B4,
  cases B3 with B3 B5,
  cases B4 with B4 B6,
  have C1:↑T ⊆ c_yes, {rw ← B5,apply set.inter_subset_left},
  have C2:x∈ c_yes,{apply C1,simp,apply B1},
  have C3:c_yes ∩ {x} = {x},
  {ext,split;intros B8A;simp;simp at B8A,apply B8A.right,subst x_1,simp [C2]},
  have C4:↑U ⊆ c_no, {rw ← B6,apply set.inter_subset_left},
  have C5:T ⊆ S,
  {
    rw ← finset.coe_subset,rw ← B5, apply set.inter_subset_right,
  },
  have C6:x ∈ S,
  {
    apply C5, apply B1,
  },
  have C7:x∉ c_no,
  {
    intros C5A,apply B2,rw ← finset.mem_coe,rw ← B6, simp,
    apply and.intro C5A C6,
  },  
  have C8:c_no ∩ ↑({x}:finset α) = ↑(∅:finset α),
  {
    simp,
    ext,split;intros C8A,
    simp at C8A,cases C8A with C8A C8B,subst x_1,exfalso,apply C7 C8A,
    exfalso, apply C8A, 
  },
  have C9:shatters C {x},
  {
    unfold shatters,
    rw finset.powerset_singleton,
    apply finset.subset.antisymm,
    apply restrict_set_subset,
    rw finset.subset_iff,
    intros X' C9A,
    simp at C9A,cases C9A;subst X';rw mem_restrict_set,
    {apply exists.intro c_no, apply exists.intro B4, exact C8},
    {apply exists.intro c_yes, apply exists.intro B3,simp,apply C3},
  },
  have C10:1 ≤ VCD C,
  {
    apply shatters_card_le_VCD C9,
  },
  rw A1 at C10,  
  have C11:(0:enat) < (1:enat) := enat.zero_lt_one,
  rw lt_iff_not_ge at C11,
  apply C11,
  apply C10,
end

lemma restrict_set_elements_eq_of_VCD_zero {C:set (set α)} {S T U:finset α}:(VCD C = 0) →
  T ∈ (restrict_set C S) → U ∈ (restrict_set C S) → T = U :=
begin
  intros A1 A2 A3,
  apply finset.subset.antisymm,
  apply restrict_set_elements_subset_of_VCD_zero A1 A2 A3,
  apply restrict_set_elements_subset_of_VCD_zero A1 A3 A2,
end

--Note: S could be either empty or have a unique element.
lemma finset.card_identical_elements {α:Type*} [decidable_eq α] {S:finset α}:
   (∀ a b:α,  a ∈ S → b ∈ S → a=b ) → S.card ≤ 1 :=
begin
  --intros A1,
  apply finset.induction_on S,
  {
    simp,
  },
  {
    intros a s B1 B2 B3,
    have C1:s = ∅,
    {
      rw ← finset.subset_empty,
      rw finset.subset_iff,
      intros b C1A,
      exfalso,
      apply B1,
      have C1B:a = b,
      {
        apply B3;simp [C1A],
      },
      rw C1B,
      apply C1A,
    },
    rw C1,
    simp,
  },
end
 
lemma mem_restrict_set_of_mem_restrict_set {C:set (set α)} {S₁ S₂ T:finset α}:
  T ∈ restrict_set C S₂ →
  S₁ ⊆ S₂ →
  (T ∩ S₁) ∈ restrict_set C S₁ :=
begin
  repeat {rw mem_restrict_set},
  intros A1 A2,
  cases A1 with c A1,
  apply exists.intro c,
  cases A1 with A1 A3,
  apply exists.intro A1,
  simp,
  rw ← A3,
  rw set.inter_assoc,
  rw ← finset.coe_subset at A2,
  rw set.inter_eq_self_of_subset_right A2,
end

lemma set.insert_inter_of_not_mem {α:Type*} {A B:set α} {x:α}:(x∉ B) → ((insert x A) ∩ B = A ∩ B) :=
begin
  intros A1,
  ext a,
  split;intros A2;simp at A2;simp,
  {
    cases A2 with A2 A3,
    cases A2 with A2 A4,
    {
      subst A2,
      exfalso,
      apply A1 A3,
    },
    {
      apply and.intro A4 A3,
    },
  },
  {
    apply and.intro (or.inr A2.left) A2.right, 
  },
end

lemma set.inter_insert_of_not_mem {α:Type*} {A B:set α} {x:α}:(x∉ A) → (A ∩ (insert x B) = A ∩ B) :=
begin
  intros A1,
  rw set.inter_comm,
  rw set.insert_inter_of_not_mem A1,
  rw set.inter_comm,
end

lemma set.not_mem_of_inter_insert {α:Type*} {A B:set α} {x:α}:(x∉ A) → (A ∩ (insert x B) = A ∩ B) :=
begin
  intros A1,
  rw set.inter_comm,
  rw set.insert_inter_of_not_mem A1,
  rw set.inter_comm,
end


lemma set.inter_insert_of_mem {α:Type*} {A B:set α} {x:α}:(x∈ A) → (A ∩ (insert x B) = insert x (A ∩ B)) :=
begin
  intros A1,
  rw set.insert_inter,
  rw set.insert_eq_of_mem A1,
end

lemma set.mem_of_inter_insert {α:Type*} {A B C:set α} {x:α}:
  (A ∩ (insert x B) = insert x (C)) → (x ∈ A) :=
begin
  intros A1,
  have B1 := set.mem_insert x (C),
  rw ← A1 at B1,
  simp at B1,
  apply B1,
end


lemma set.eq_of_insert_of_not_mem {α:Type*} {A B:set α} {x:α}:(x∉ A) → (x∉ B) → (insert x A  = insert x B)
  → A = B :=
begin
  intros A1 A3 A2,
  ext a;split;intros B1;have C1 := set.mem_insert_of_mem x B1,
  {
    rw A2 at C1,
    apply set.mem_of_mem_insert_of_ne C1,
    intros C2,
    subst a,
    apply A1 B1,
  },
  {
    rw ← A2 at C1,
    apply set.mem_of_mem_insert_of_ne C1,
    intros C2,
    subst a,
    apply A3 B1,
  },
end

lemma set.insert_subset_insert {α:Type*} {A B:set α} {x:α}:A ⊆ B → (insert x A) ⊆ (insert x B) :=
begin
  intros A1,
  rw set.subset_def,
  intros a B1,
  simp at B1,
  simp,
  cases B1 with B1 B1,
  apply or.inl B1,
  apply or.inr (A1 B1),
end

lemma finset.eq_of_insert_of_not_mem {α:Type*} {A B:finset α} {x:α}:(x∉ A) → (x∉ B) → (insert x A  = insert x B)
  → A = B :=
begin
  intros A1 A3 A2,
  ext a;split;intros B1;have C1 := finset.mem_insert_of_mem B1,
  {
    rw A2 at C1,
    apply finset.mem_of_mem_insert_of_ne C1,
    intros C2,
    subst a,
    apply A1 B1,
  },
  {
    rw ← A2 at C1,
    apply finset.mem_of_mem_insert_of_ne C1,
    intros C2,
    subst a,
    apply A3 B1,
  },
end

lemma mem_restrict_set_insert {C:set (set α)} {S c:finset α} {x:α}:x∉ S → (x∉ c) →
  ((c ∈ restrict_set C S) ↔ (insert x c ∈ restrict_set C (insert x S)) ∨ c∈ restrict_set C (insert x S))
 :=
begin
  repeat {rw mem_restrict_set},
  intros A1 AX,split;intros A2,
  {
    cases A2 with c' A2,
    cases A2 with A2 A3,
    cases (em (x∈ c')) with B1 B1,
    {
      left,
      apply exists.intro c',
      apply exists.intro A2,
      simp,
      have B2:insert x c' = c' := set.insert_eq_of_mem B1,
      rw ← B2,
      rw ← set.insert_inter,
      rw A3,
    },
    {
      right,
      apply exists.intro c',
      apply exists.intro A2,
      simp,
      rw set.inter_insert_of_not_mem B1,
      apply A3,
    },
  },
  {
    cases A2 with A2 A2;cases A2 with c' A2;cases A2 with A2 A3;
    apply exists.intro c';apply exists.intro A2,
    {
      simp at A3,
      have C1:=set.mem_of_inter_insert A3,      
      rw set.inter_insert_of_mem C1 at A3,
      apply set.eq_of_insert_of_not_mem _ _ A3,
      simp,
      intro C2,
      apply A1,
      apply AX,
    },
    {
      ext a;split;intros D1,
      {
        rw ← A3,
        simp at D1,
        simp [D1],
      },
      {
        have D2:a ≠ x,
        {
          intros D2A,
          subst a,
          apply AX D1,
        },
        rw ← A3 at D1,
        simp [D2] at D1,
        simp [D1],
      },
    },
  },
end


lemma finset.insert_inter_eq_insert_inter_insert {α:Type*} [decidable_eq α]
  {S T:finset α} {a:α}:(insert a S) ∩ (insert a T) = insert a (S ∩ T) :=
begin
  ext b,
  split;intros A1,
  {
    rw finset.mem_insert,
    simp at A1,
    cases A1,
    subst a,
    simp,
    cases A1 with A1 A2,
    cases A1 with A1 A1,
    apply or.inl A1,
    simp [A1,A2],    
  },
  {
    simp,
    simp at A1,
    cases A1 with A1 A1,
    apply or.inl A1,
    simp [A1],
  },
end


lemma mem_restrict_set_erase {C:set (set α)} {S c:finset α} {x:α}:x∉ S → (x∈ c) →
  (c ∈ restrict_set C (insert x S))  → (c.erase x ∈ restrict_set C S) 
 :=
begin
  intros A1 A2 A3,
  rw mem_restrict_set_insert A1,
  left,
  rw finset.insert_erase,
  apply A3,
  apply A2,
  apply finset.not_mem_erase,  
end

lemma restrict_card_le_one_of_VCD_zero {C:set (set α)} {S:finset α}:(VCD C = 0) →
  (restrict_set C S).card ≤ 1 :=
begin
  intros A1,
  apply finset.card_identical_elements,
  intros T U B1 B2,
  apply restrict_set_elements_eq_of_VCD_zero A1 B1 B2,
end

lemma restrict_set_empty_of_empty {S:finset α}:restrict_set ∅ S = ∅ :=
begin
  ext c,
  rw mem_restrict_set,
  split;intros B1,
  {
    cases B1 with c2 B1,
    cases B1 with B1 B2,
    simp at B1,
    exfalso,
    apply B1,
  },
  {
    exfalso,
    simp at B1,
    apply B1,
  },
end

lemma restrict_set_nonempty_empty {C:set (set α)}:
  set.nonempty C → restrict_set C ∅ = {∅} :=
begin
  intros A1,
  ext c,
  rw mem_restrict_set,split;intros B1,
  {
    simp,
    cases B1 with c' B1,
    cases B1 with B1 B2,
    rw ← finset.coe_inj,
    rw ← B2,
    simp,
  },
  {
    simp at B1,
    subst c,
    rw set.nonempty_def at A1,
    cases A1 with c' A1,
    apply exists.intro c',
    apply exists.intro A1,
    simp,    
  },
end

lemma restrict_set_empty_card_le_1 {C:set (set α)}:
  (restrict_set C ∅).card ≤ 1 :=
begin
  cases (set.eq_empty_or_nonempty C) with B1 B1,
  {
    subst C,
    rw restrict_set_empty_of_empty,
    simp,
  },
  {
    rw restrict_set_nonempty_empty B1,
    simp,
  },
end

lemma filter_union {S:finset α} {P:α → Prop}:
  finset.filter P S ∪ finset.filter (λ a, ¬P a)  S = S :=
begin
  ext a;split;intro A1,
  {
    simp at A1,
    cases A1 with A1 A1;apply A1.left,
  },
  {
    simp,
    simp [A1],
    apply em,
  },
end

lemma filter_disjoint {S T:finset α} {P:α → Prop}:
  disjoint (finset.filter P S) (finset.filter (λ a, ¬P a)  T) :=
begin
  rw finset.disjoint_left,
  intros a B1 B2,
  simp at B1,
  simp at B2,
  apply B2.right,
  apply B1.right,
end 

lemma filter_disjoint' {S:finset α} {P:α → Prop}:
  disjoint (finset.filter P S) (finset.filter (λ a, ¬P a)  S) :=
  @filter_disjoint α S S P

lemma filter_card {S:finset α} {P:α → Prop}:
  (finset.filter P S).card + (finset.filter (λ a, ¬P a)  S).card = S.card :=
begin
  have A1:(finset.filter P S ∪ finset.filter (λ a, ¬P a)  S).card = S.card,
  {
    rw filter_union,
  },
  rw ← A1,
  rw finset.card_union_eq,
  apply filter_disjoint,
end

lemma recursive_restrict_set_card {C:set (set α)} {x:α} {S:finset α}:x∉ S →
  ((restrict_set C (insert x S)).filter (λ c,(x∉c ∧ (insert x c) ∈ (restrict_set 
C (insert x S))))).card + (restrict_set C S).card = (restrict_set C (insert x S)).card :=
begin
  intro A1,
  let Ex := restrict_set C (insert x S),
  let E := restrict_set C S,
  begin
    have B1:Ex = restrict_set C (insert x S) := rfl,
    have B2:E = restrict_set C S := rfl,

    repeat {rw ← B1},
    repeat {rw ← B2},
    rw add_comm,
    rw ← @filter_card _ Ex (λ c, x ∈ c),
    simp,
    simp,
    rw ← @filter_card _ (finset.filter (λ c, x∉ c) Ex)
       (λ c, (insert x c) ∈ Ex),
    simp,
    repeat {rw finset.filter_filter},
    rw add_comm _ (finset.filter (λ (a : finset α), x ∉ a ∧ insert x a ∉ Ex) Ex).card,
    rw ← add_assoc,
    simp,
    have C1:(finset.filter (λ (a : finset α), x ∉ a ∧ insert x a ∉ Ex) Ex) =
      (finset.filter (λ (a : finset α), insert x a ∉ Ex) E),
    {
      ext c,split;repeat {rw B1};repeat {rw B2};intros C1A;simp at C1A;simp [C1A],
      { rw mem_restrict_set_insert A1 C1A.right.left, apply or.inr C1A.left},
      { 
        have C1B:x ∉ c,
        {
          have C1B1:c ⊆ S := mem_restrict_set_subset C1A.left,
          intro C1B2,
          apply A1,
          apply C1B1,
          apply C1B2,
        },
        have C1C := (mem_restrict_set_insert A1 C1B).mp C1A.left, 
        simp [C1A.right] at C1C,
        apply and.intro C1C C1B,
      },
    },
    rw C1,
    clear C1,
    have C2:(finset.filter (has_mem.mem x) Ex).card = 
      (finset.filter (λ a, insert x a ∈ Ex) E).card ,
    {
      have C2A:(finset.filter (has_mem.mem x) Ex) = 
        (finset.filter (λ a, insert x a ∈ Ex) E).image (insert x),
      {
        ext a,split;repeat {rw B1};repeat {rw B2};intros C2A1;simp at C2A1;simp,
        {
          apply exists.intro (a.erase x),
          cases C2A1 with C2A1 C2A2,
          have C2A3:insert x (a.erase x) = a := finset.insert_erase C2A2,
          have C2A4:x ∉ a.erase x := finset.not_mem_erase x a,
          split,
          split,
          apply mem_restrict_set_erase A1 C2A2 C2A1,
          rw C2A3,
          apply C2A1,
          apply C2A3,
        },
        {
          cases C2A1 with c C2A1,
          cases C2A1 with C2A1 C2A2,
          cases C2A1 with C2A1 C2A3,
          subst a,
          simp [C2A3],
        },
      },
      rw C2A,
      clear C2A,
      repeat {rw B1},
      repeat {rw B2},   
      apply finset.card_image_of_inj_on, 
      intros c C2B c' C2C,
      simp at C2B,
      simp at C2C,
      have C2D:∀ {c'':finset α}, c'' ∈ restrict_set C S → x ∉ c'',
      {
        intros c'' C2D1 C2D3,
        apply A1,
        have C2D2 := mem_restrict_set_subset C2D1,
        apply C2D2,
        apply C2D3,
      },
      apply finset.eq_of_insert_of_not_mem,
      apply C2D C2B.left,
      apply C2D C2C.left,
    },
    
    rw C2,
    rw  ← @filter_card _ E (λ a, insert x a ∈ Ex),
    simp,
  end    
end

lemma enat.le_coe_eq_coe {v:enat} {d:nat}:v ≤ d → ∃ d':ℕ, v = d'  ∧ d' ≤ d :=
begin
  --intros A1,
  apply enat.cases_on v,
  {
    intros A1,
    simp at A1,
    exfalso,
    apply A1,
  },
  {
    intros n A1,
    apply exists.intro n,
    simp at A1,
    simp [A1],
  },
end 

lemma phi_monotone_m {d  m₁ m₂:ℕ}:m₁ ≤ m₂ → Φ d m₁ ≤ Φ d m₂ :=
begin
  intros A1,
  rw le_iff_exists_add at A1,
  cases A1 with c A1,
  subst m₂,
  induction c,
  simp,
  have A2:(m₁ + c_n.succ) = (m₁ + c_n).succ := rfl,
  rw A2,
  cases d,
  simp,
  rw phi_succ_succ,
  apply le_trans c_ih,
  simp,
end


lemma phi_le_d_succ {d m:ℕ}:Φ d m ≤ Φ d.succ m :=
begin
  revert d,
  induction m,
  intro d,
  simp,
  intro d,
  rw phi_succ_succ,
  cases d,
  simp,
  rw phi_succ_succ,
  rw add_comm,
  simp,
  apply le_trans m_ih,
  apply m_ih,
end

lemma phi_monotone_d {d₁ d₂ m:ℕ}:d₁ ≤ d₂ → Φ d₁ m ≤ Φ d₂ m :=
begin
  intros A1,
  rw le_iff_exists_add at A1,
  cases A1 with c A1,
  subst d₂,
  induction c,
  simp,
  have A2:(d₁ + c_n.succ) = (d₁ + c_n).succ := rfl,
  rw A2,
  apply le_trans c_ih,
  apply phi_le_d_succ,
end

lemma eq_restrict_set {C:finset (finset α)} {S:finset α}:(∀ c∈ C , c⊆ S)→
  C = restrict_set (C.to_set_of_sets) S :=
begin
  intros A1,
  ext c,split;intros B1,
  {
    rw mem_restrict_set,
    apply exists.intro (↑c),
    split,
    rw finset.mem_to_set_of_sets,
    apply B1,
    have B2 := A1 c B1,
    apply set.inter_eq_self_of_subset_left,
    simp,
    apply B2,
  },
  {
    rw mem_restrict_set at B1,
    cases B1 with c' B1,
    cases B1 with B1 B2,
    rw finset.mem_to_set_of_sets' at B1,
    cases B1 with c'' B1,
    cases B1 with B1 B2,
    subst c',
    rw set.inter_eq_self_of_subset_left at B2,
    simp at B2,
    subst c'',
    apply B1,
    simp,
    apply A1 c'' B1,        
  },
end

lemma finite_restrict_set_eq_image {C:finset (finset α)} {S:finset α}:
  (restrict_set C.to_set_of_sets S) = C.image (λ S', S'∩ S) :=
begin
  ext,split;intros A1A,
  {
    simp,
    rw mem_restrict_set at A1A,
    cases A1A with c A1A,
    cases A1A with A1A A1B,
    rw finset.mem_to_set_of_sets' at A1A,
    cases A1A with c' A1A,
    apply exists.intro c',
    cases A1A with A1A A1C,
    rw A1C at A1B,
    rw ← finset.coe_inter at A1B,
    rw finset.coe_inj at A1B,
    apply and.intro A1A A1B,
  },
  {
    simp at A1A,
    cases A1A with c A1A,
    cases A1A with A1A A1B,
    subst a,
    rw mem_restrict_set,
    apply exists.intro (↑c),
    split,
    rw finset.mem_to_set_of_sets,
    apply A1A,
    rw finset.coe_inter,
  },
end

lemma finite_restrict_set_le {C:finset (finset α)} {S:finset α}:
  (restrict_set C.to_set_of_sets S).card ≤ C.card := 
begin
  rw finite_restrict_set_eq_image,
  apply finset.card_image_le,
end

lemma shatters_subset {S:finset α} {x:α} {C:set (set α)} {S':finset α}:x∉S → 
   shatters (
          (
            (restrict_set C (insert x S)).filter
            (λ (c:finset α),(x∉c ∧ ((insert x c) ∈ (restrict_set C (insert x S)))))
          ).to_set_of_sets
        ) S'  → S' ⊆ S :=
begin
  intros A1 A2,
  rw shatters_iff at A2,
  have D1A:S' ⊆ S' := finset.subset.refl S',
  have D1B := A2 S' D1A,
  cases D1B with c D1B,
  cases D1B with D1B D1C,
  rw finset.mem_to_set_of_sets' at D1B,
  cases D1B with c' D1B,
  cases D1B with D1B D1D,
  subst c,
  simp at D1B,
  cases D1B with D1B D1E,
  cases D1E with D1E D1F,
  have D1G:= mem_restrict_set_subset D1B,
  rw ← finset.coe_inter at D1C,
  rw finset.coe_inj at D1C,
  have D1H:S'⊆ c',
  {
    rw ← D1C,
    apply finset.inter_subset_left,
  },
  apply finset.subset.trans D1H,
  apply finset.subset_of_not_mem_of_subset_insert D1E D1G,
end

lemma shatters_succ {S:finset α} {x:α} {C:set (set α)} {S':finset α}:x∉S → 
   shatters (
          (
            (restrict_set C (insert x S)).filter
            (λ (c:finset α),(x∉c ∧ ((insert x c) ∈ (restrict_set C (insert x S)))))
          ).to_set_of_sets
        ) S'  → shatters C (insert x S') :=
begin
  intros A1 A2,
  rw shatters_iff,
  intros c B1,
  have D1:S' ⊆ S := shatters_subset A1 A2,  
  have D2:(insert x (↑S':set α)) ⊆ (insert x ↑S),
  {
    apply set.insert_subset_insert,
    simp,
    apply D1,
  },

  rw shatters_iff at A2,
  cases (em (x ∈ c)) with A3 A3,
  {
    have C1:c.erase x ⊆ S',
    {
      rw ← finset.subset_insert_iff,
      apply B1,
    },
    have B2 := A2 (c.erase x) C1,
    cases B2 with c' B2,
    cases B2 with B2 B3,
    simp,
    rw finset.mem_to_set_of_sets' at B2,
    cases B2 with c'' B2,
    cases B2 with B2 B4,
    simp at B2,
    cases B2 with B2 B5,
    cases B5 with B5 B6,
    rw mem_restrict_set at B6,
    cases B6 with c''' B6,
    cases B6 with B6 B7,
    subst c',
    apply exists.intro c''',
    apply and.intro B6,
    simp at B7,
    rw ← finset.coe_inter at B3,
    rw finset.coe_inj at B3,

    have B8:insert x (c'' ∩ S') = insert x (c.erase x),
    {
      rw B3,
    },
    rw finset.insert_erase A3 at B8,
    have B9 := set.mem_of_inter_insert B7,
    rw ← finset.insert_inter_eq_insert_inter_insert at B8,
    rw ← B8,
    rw finset.coe_inter,
    repeat {rw finset.coe_insert},
    rw ← B7,
    rw set.inter_assoc,
    rw set.inter_comm (insert x ↑S),
    rw ← set.inter_assoc,
    symmetry,
    apply set.inter_eq_self_of_subset_left,
    have B10:=set.inter_subset_right c''' (insert x ↑S'),
    apply set.subset.trans B10 D2,
   },
  {
    have E1:c ⊆ S',
    {
      rw finset.subset_iff,
      intros a E1A,
      have E1B := B1 E1A,
      rw finset.mem_insert at E1B,
      cases E1B with E1B E1B,
      {
        subst a,
        exfalso,
        apply A3 E1A,
      },
      apply E1B,
    },
    have E2 := A2 c E1,
    cases E2 with c' E2,
    cases E2 with E2 E3,
    rw finset.mem_to_set_of_sets' at E2,
    cases E2 with c'' E2,
    cases E2 with E2 E3,
    simp at E2,
    subst c',
    cases E2 with E2 E4,
    cases E4 with E4 E5,
    rw mem_restrict_set at E2,
    cases E2 with c''' E2,
    cases E2 with E2 E6,
    apply exists.intro c''',
    apply exists.intro E2,
    have E7:x ∉ (↑c'':set α),
    {simp [E4]},
    rw ← set.inter_insert_of_not_mem E7 at E3,
    simp at E6,
    rw ← E3,
    simp,
    rw ← E6,
    rw set.inter_assoc,
    rw set.inter_comm (insert x ↑S),
    rw ← set.inter_assoc,
    symmetry,
    apply set.inter_eq_self_of_subset_left,
    have E8:=set.inter_subset_right c''' (insert x ↑S'),
    apply set.subset.trans E8 D2,
  },
end

lemma VCD_succ {S:finset α} {x:α} {C:set (set α)} {d:ℕ}:x∉S → VCD C = d.succ →
    VCD (
          (
            (restrict_set C (insert x S)).filter
            (λ (c:finset α),(x∉c ∧ ((insert x c) ∈ (restrict_set C (insert x S)))))
          ).to_set_of_sets
        ) ≤ d :=
begin
  intros A1 A2,
  apply VCD_le,
  intros T B1,
  have B2:T ⊆ S := shatters_subset A1 B1, 
  have B3:x ∉ T,
  {
    intro B3A,
    apply A1,
    apply B2,
    apply B3A,
  },
  have B4:shatters C (insert x T),
  {
    apply shatters_succ,
    apply A1,
    apply B1,
  },
  have B5:((insert x T).card:enat) ≤ VCD C,
  {
    apply shatters_card_le_VCD B4,
  },
  rw A2 at B5,
  simp at B5,
  rw finset.card_insert_of_not_mem B3 at B5,
  have B6:T.card + 1 = (T.card).succ := rfl,
  rw B6 at B5,
  rw nat.succ_le_succ_iff at B5,
  simp,
  apply B5
end 


--This is known as Sauer's Lemma, or Sauer-Saleh Lemma.
--This connects VC-dimension to the complexity of the hypothesis space restricted to a finite set
--of certain size.
lemma restrict_set_le_phi {C:set (set α)} {S:finset α} (d:ℕ):
  (VCD C = d) →
  (restrict_set C S).card ≤ Φ d S.card := 
begin
  revert d,
  revert C,
  apply finset.induction_on S,
  {
    intros C d A1,
    simp,
    apply restrict_set_empty_card_le_1,
  },
  {
    intros x S B1 B2 C d B3,
    cases d,
    {
      rw phi_zero_m_eq_one,
      apply restrict_card_le_one_of_VCD_zero,
      simp at B3,
      apply B3,
    },
    let C':finset (finset α) := (restrict_set C (insert x S)).filter (λ c,(x∉c ∧ (insert x c) ∈ (restrict_set C (insert x S)))),
    begin
      have C0:C' = (restrict_set C (insert x S)).filter (λ c,(x∉c ∧ (insert x c) ∈ (restrict_set C (insert x S)))) := rfl,
      rw ← recursive_restrict_set_card B1,
      rw ← C0,
      have D1:C'.card + (restrict_set C S).card ≤ C'.card +  Φ d.succ S.card,
      {
        simp [B2,B3],
      },
      apply le_trans D1,
      
      have C5:C' = restrict_set (C'.to_set_of_sets) S,
      {
        apply eq_restrict_set,
        intros c C3A,
        rw C0 at C3A,
        simp at C3A,
        have C3C := mem_restrict_set_subset C3A.left,
        apply finset.subset_of_not_mem_of_subset_insert C3A.right.left C3C,
      },
      rw C5,
      have C6:VCD (C'.to_set_of_sets) ≤ (d:enat),
      {
        rw C0,
        apply VCD_succ,
        apply B1,
        apply B3
      },
      have C7:∃d':ℕ, VCD (C'.to_set_of_sets) = d' ∧ d' ≤ d,
      {
        apply enat.le_coe_eq_coe C6,
      },
      cases C7 with d' C7,
      have C8:(restrict_set C'.to_set_of_sets S).card + Φ d.succ S.card ≤ Φ d S.card + Φ d.succ S.card,
      {
        simp,
        have C8A:(restrict_set C'.to_set_of_sets S).card ≤ Φ d' S.card,
        {
          apply B2,
          apply C7.left,
        },
        apply le_trans C8A,
        apply phi_monotone_d,
        apply C7.right,
      },
      apply le_trans C8,
      rw finset.card_insert_of_not_mem B1,
      rw phi_succ_succ,
      rw add_comm,  
    end,
  },
end

-- TODO: prove Φ d m = (finset.range (d.succ)).sum (λ i, nat.choose m i)
-- See mathlib/src/data/nat/choose/basic.lean
-- TODO: introduce ε-nets, and show that the VC dimension of C is a bound on 
-- the VC-dimension of the ε-net.
-- TODO: show that if the training examples cover the ε-net, then any consistent
-- algorithm will get a hypothesis with low error.
-- TODO: Introduce the proof from 3.5.2 proving a bound on the probability of
-- hitting the ε-net. 
end VC_PAC_problem
end VC_PAC_problem










