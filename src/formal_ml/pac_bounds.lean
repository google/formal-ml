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
import formal_ml.classical

structure PAC_problem :=
   (Ω:Type*)
   (p:probability_space Ω)
                                       -- Underlying outcome type
                                       -- underlying probability space
    (β:Type*)                          -- instance type
    (Mβ:measurable_space β)            -- Measurable space for the instances
(γ:Type*)                              -- label type, with ⊤ measurable space
(TMγ:top_measurable γ)                 -- Measurable space for the labels
(Eγ:encodable γ)                       -- Encodable labels is very useful
(Di:Type*)                             -- number of examples
(FDi:fintype Di)                       -- number of examples are finite
(EDi:encodable Di)                     -- example index is encodable
                                       -- see trunc_encodable_of_fintype
(Hi:Type*)                             -- number of examples
(FHi:fintype Hi)                       -- number of examples are finite
(EHi:encodable Hi)                     -- hypothesis index is encodable
                                       -- see trunc_encodable_of_fintype
(H:Hi → (measurable_fun Mβ TMγ.to_measurable_space))            -- hypothesis space
(D:Di → random_variable p (prod_space Mβ TMγ.to_measurable_space))     -- example distribution
(IID:random_variables_IID D)            -- examples are IID
(has_example:inhabited Di)             -- there exists an example





--the measurable space on the labels.
def PAC_problem.Mγ (P:PAC_problem):
  measurable_space P.γ := P.TMγ.to_measurable_space

--example_instance P j is the jth instance (the features of an example)
def example_instance (P:PAC_problem)
  (j:P.Di):random_variable P.p P.Mβ :=
  (mf_fst) ∘r (P.D j)

--the measurable space on the examples.
def PAC_problem.Mβγ (P:PAC_problem):
    measurable_space (P.β × P.γ) := P.Mβ ×m P.Mγ

/-
  rv_label_eq X Y is the event that X and Y are equal, where X and Y are labels.
-/
def rv_label_eq (P:PAC_problem)
  (X Y:random_variable P.p P.Mγ):event  P.p :=
  @rv_eq _ P.p P.γ P.Eγ P.TMγ X Y

/-
  rv_label_ne X Y is the event that X and Y are not equal, where X and Y are labels.
-/
def rv_label_ne (P:PAC_problem)
  (X Y:random_variable P.p P.Mγ):event  P.p :=
  @rv_ne _ P.p P.γ P.Eγ P.TMγ X Y

/-
  example_label P j is the label of the jth example.
-/
def example_label (P:PAC_problem)
  (j:P.Di):P.p →r P.Mγ :=
  mf_snd ∘r (P.D j)


/-
  example_classification P i j is the classification by the ith hypothesis of the jth example.
-/
def example_classification (P:PAC_problem)
  (i:P.Hi) (j:P.Di):P.p →r P.Mγ :=
  (P.H i) ∘r (example_instance P j)

/-
  example_correct P i j is whether the ith hypothesis is correct on the jth example.
-/
def example_correct (P:PAC_problem)
  (i:P.Hi) (j:P.Di):event P.p :=
  rv_label_eq P (example_classification P i j) (example_label P j)

/-
  example_error P i j is whether the ith hypothesis made a mistake on the jth example.
-/
def example_error (P:PAC_problem)
  (i:P.Hi) (j:P.Di):event P.p :=
  rv_label_ne P (example_classification P i j) (example_label P j)


/-
  num_examples P is the number of examples in the problem.
  This is defined as the cardinality of the index type of the examples.
-/
def num_examples  (P:PAC_problem):nat
   := @fintype.card P.Di P.FDi


/-
  The number of examples is the number of elements of type P.Di.
  P.FDi.elems is the set of all elements in P.Di, and P.FDi.elems.card is the cardinality of
  P.FDi.elems.
-/
lemma num_examples_eq_finset_card (P:PAC_problem):
  num_examples P = P.FDi.elems.card :=
begin
  refl,
end

/-
  A type is of class inhabited if it has at least one element.
  Thus, its cardinality is not zero.
--Not sure where to put this. Here is fine for now.
--Note: this is the kind of trivial thing that takes ten minutes to prove.
-/
lemma card_ne_zero_of_inhabited {α:Type*} [inhabited α] [F:fintype α]:
  fintype.card α ≠ 0 :=
begin
  rw ← nat.pos_iff_ne_zero,
  rw fintype.card_pos_iff,
  apply nonempty_of_inhabited,
end

/-
  The number of examples do not equal zero.
 -/
lemma num_examples_ne_zero (P:PAC_problem):
  num_examples P ≠ 0 :=
begin
  unfold num_examples,
  apply @card_ne_zero_of_inhabited P.Di P.has_example P.FDi,
end


/-
  The number of hypotheses.
 -/
def num_hypotheses (P:PAC_problem):nat
   := @fintype.card P.Hi P.FHi

/-
  The number of errors on the training set, divided by the size of the training set.
  training_error P i = (∑ (j:P.Di), (example_error P i j))/(num_exmaples P)
-/
noncomputable def training_error (P:PAC_problem)
  (i:P.Hi):P.p →r (borel nnreal) :=
  (count_finset_rv P.FDi.elems (example_error P i)) * (to_nnreal_rv ((num_examples P):nnreal)⁻¹)

/-
  The expected test error.
  The test error is equal to the expected training error. Because we have not defined a generating
  process for examples, we use this as the definition.
-/
noncomputable def test_error (P:PAC_problem)
    (i:P.Hi):ennreal := E[training_error P i]

/-
  fake_hypothesis P ε i is the event that hypothesis i has zero training error, but has
  test error > ε.
-/
noncomputable def fake_hypothesis (P:PAC_problem) (ε:nnreal)
  (i:P.Hi):event P.p :=
  ((training_error P i) =ᵣ (to_nnreal_rv 0)) ∧ₑ (event_const (test_error P i > ε))

/-
  The event that all hypotheses with training error zero have test error ≤ ε.
-/
noncomputable def approximately_correct_event (P:PAC_problem)
  (ε:nnreal):event P.p :=
  enot (eany_fintype P.FHi (fake_hypothesis P ε))

def probably_approximately_correct (P:PAC_problem)
 (ε:nnreal) (δ:nnreal):Prop :=
  1 - δ ≤ Pr[approximately_correct_event P ε]





lemma is_measurable_prod_label_set (P:PAC_problem)
  {U:set (P.γ × P.γ)}:(P.Mγ ×m P.Mγ).is_measurable U :=
begin
  apply @top_measurable_prodh P.γ P.γ P.Eγ P.Eγ P.TMγ,
end

lemma enot_example_correct_eq_example_error
  (P:PAC_problem) (i:P.Hi) (j:P.Di):enot (example_correct P i j) = (example_error P i j) :=
begin
  apply event.eq,
  unfold example_error,
  unfold example_correct,
  unfold rv_label_ne,
  unfold rv_label_eq,
  rw enot_val_def,
  rw rv_ne_val_def,
  rw rv_eq_val_def,
  ext ω,
  simp,
end


lemma enot_example_error_eq_example_correct
  (P:PAC_problem) (i:P.Hi) (j:P.Di):enot (example_error P i j) = (example_correct P i j) :=
begin
  rw ← enot_example_correct_eq_example_error,
  rw enot_enot_eq_self,
end


lemma example_correct_iff_not_example_error
  (P:PAC_problem) (i:P.Hi) (j:P.Di) (ω:P.Ω): ω ∉ (example_error P i j).val ↔
  ω ∈ (example_correct P i j).val :=
begin
  rw ← enot_example_error_eq_example_correct,
  rw enot_val_def,
  simp,
end

lemma example_error_IID (P:PAC_problem) (i:P.Hi):
  @events_IID P.Ω P.Di P.p P.FDi  (example_error P i) :=
begin
  /-
    To prove that the errors of a particular hypothesis are IID, we must use an alternate
    formulation of the example_error events. Specifically, instead of constructing a hierarchy
    of random variables, we must make a leap from the established IID random variable
    (the data), construct another IID random variable (the product of
    the classification and the label), and show that the set of all label/classification pairs
    that aren't equal are a measurable set (because P.Mγ ×m P.Mγ = ⊤).

    The indexed set of events of each IID random variable being in a measurable set is IID,
    so the result holds.

    Note that while this proof looks a little long, most of the proof is just unwrapping
    the traditional and internal definitions of example error, and then using simp to show that
    they are equal on all outcomes.
  -/
  let Y:(P.Mβ ×m P.Mγ)→m (P.Mγ ×m P.Mγ) := prod_measurable_fun ((P.H i) ∘m (mf_fst)) (mf_snd),
  begin
  let S:@measurable_set _ (P.Mγ ×m P.Mγ) := {
    val := {x:P.γ × P.γ|x.fst ≠ x.snd},
    property := @top_measurable_prodh P.γ P.γ P.Eγ P.Eγ P.TMγ P.TMγ _,
  },
  begin
  have A1:@random_variables_IID P.Ω P.p P.Di P.FDi (P.γ × P.γ) (P.Mγ ×m P.Mγ)
  (λ j:P.Di, Y ∘r (P.D j) ),
  {
    apply compose_IID,
    apply P.IID,
  },
  have A2:@events_IID  P.Ω P.Di P.p P.FDi (λ j:P.Di, @rv_event P.Ω P.p _ (P.Mγ ×m P.Mγ) (Y ∘r (P.D j)) S),
  {
    apply rv_event_IID,
    apply A1,
  },
  have A3: (λ j:P.Di, @rv_event P.Ω P.p _ (P.Mγ ×m P.Mγ) (Y ∘r (P.D j)) S) = example_error P i,
  {
    apply funext,
    intro j,
    apply event.eq,
    unfold example_error example_label example_classification rv_label_ne example_instance,
    rw rv_ne_val_def,
    rw rv_event_val_def,
    have A3A:S.val = {x:P.γ × P.γ|x.fst ≠ x.snd} := rfl,
    rw A3A,
    have A3B:Y = prod_measurable_fun ((P.H i) ∘m (mf_fst)) (mf_snd) := rfl,
    rw A3B,
    rw rv_compose_val_def,
    rw prod_measurable_fun_val_def,
    rw rv_compose_val_def,
    rw rv_compose_val_def,
    rw rv_compose_val_def,
    rw compose_measurable_fun_val_def,
    simp,
  },
  rw ← A3,
  exact A2,
  end
  end
end

lemma example_correct_IID (P:PAC_problem) (i:P.Hi):
  @events_IID P.Ω P.Di P.p P.FDi  (example_correct P i) :=
begin
  /-
    Similar to example_error_IID. Theoretically, we could prove it from example_error_IID.
    However, it is easier for now to prove it from first principles.
  -/
  let Y:(P.Mβ ×m P.Mγ)→m (P.Mγ ×m P.Mγ) := prod_measurable_fun ((P.H i) ∘m (mf_fst)) (mf_snd),
  begin
  let S:@measurable_set _ (P.Mγ ×m P.Mγ) := {
    val := {x:P.γ × P.γ|x.fst = x.snd},
    property := @top_measurable_prodh P.γ P.γ P.Eγ P.Eγ P.TMγ P.TMγ _,
  },
  begin
  have A1:@random_variables_IID P.Ω P.p P.Di P.FDi (P.γ × P.γ) (P.Mγ ×m P.Mγ)
  (λ j:P.Di, Y ∘r (P.D j) ),
  {
    apply compose_IID,
    apply P.IID,
  },
  have A2:@events_IID  P.Ω P.Di P.p P.FDi (λ j:P.Di, @rv_event P.Ω P.p _ (P.Mγ ×m P.Mγ) (Y ∘r (P.D j)) S),
  {
    apply rv_event_IID,
    apply A1,
  },
  have A3: (λ j:P.Di, @rv_event P.Ω P.p _ (P.Mγ ×m P.Mγ) (Y ∘r (P.D j)) S) = example_correct P i,
  {
    apply funext,
    intro j,
    apply event.eq,
    unfold example_correct example_label example_classification rv_label_eq example_instance,
    rw rv_eq_val_def,
    rw rv_event_val_def,
    have A3A:S.val = {x:P.γ × P.γ|x.fst = x.snd} := rfl,
    rw A3A,
    have A3B:Y = prod_measurable_fun ((P.H i) ∘m (mf_fst)) (mf_snd) := rfl,
    rw A3B,
    --Unwrap the underlying sets from the events.
    rw [rv_compose_val_def, prod_measurable_fun_val_def, rv_compose_val_def, rv_compose_val_def,
        rv_compose_val_def, compose_measurable_fun_val_def],
    simp,
  },
  rw ← A3,
  exact A2,
  end
  end
end

lemma example_error_identical (P:PAC_problem) (i:P.Hi) (j j':P.Di):
  Pr[example_error P i j] = Pr[example_error P i j'] :=
begin
  have A1:@events_IID P.Ω P.Di P.p P.FDi  (example_error P i),
  {
    apply example_error_IID,
  },
  unfold events_IID at A1,
  cases A1 with A2 A3,
  apply A3,
end

--set_option pp.all true
--set_option pp.coercions true



lemma test_error_training_mistake (P:PAC_problem) (i:P.Hi) (j:P.Di):
  (Pr[example_error P i j]:ennreal) = (test_error P i) :=
begin
  have A1:E[(count_finset_rv P.FDi.elems (example_error P i)) *
  (to_nnreal_rv ((num_examples P):nnreal)⁻¹)]=(test_error P i),
  {
    unfold test_error,
    refl,
  },

  have A2:(test_error P i)=E[(count_finset_rv P.FDi.elems (example_error P i))]
  * ((num_examples P):ennreal)⁻¹,
  {
    rw ← A1,
    rw scalar_expected_value,
    rw ennreal.coe_inv,
    have A2A:(((num_examples P):nnreal)⁻¹:ennreal)=((num_examples P):ennreal)⁻¹,
    {
      simp,
    },
    rw A2A,
    simp,
    apply num_examples_ne_zero,
  },

  have A3:E[(count_finset_rv P.FDi.elems (example_error P i))]=
           P.FDi.elems.sum (λ k, Pr[(example_error P i k)]),
  {
    apply linear_count_finset_rv,
  },
  have A4:∀ k, (λ k, (Pr[(example_error P i k)]:ennreal)) k = (Pr[(example_error P i j)]:ennreal),
  {
    intro k,
    simp,
    apply (example_error_identical P i _ j),
  },
  have A5:E[(count_finset_rv P.FDi.elems (example_error P i))]=
           P.FDi.elems.card * (Pr[(example_error P i j)]:ennreal),
  {
    rw A3,
    apply finset_sum_const,
    apply A4,
  },
  have A6:E[(count_finset_rv P.FDi.elems (example_error P i))]=
           (num_examples P) * (Pr[(example_error P i j)]:ennreal),
  {
    rw A5,
    rw num_examples_eq_finset_card,
  },
  rw A6 at A2,
  rw mul_comm at A2,
  rw ← mul_assoc at A2,
  have A7:((num_examples P):ennreal)⁻¹ * ((num_examples P):ennreal) = 1,
  {
    rw mul_comm,
    apply ennreal.mul_inv_cancel,
    {
      simp,
      apply (@num_examples_ne_zero P),
    },
    {
      simp,
    }
  },
  rw A7 at A2,
  simp at A2,
  symmetry,
  exact A2,
end

lemma test_error_training_mistake2 (P:PAC_problem) (i:P.Hi) (j:P.Di):
  Pr[example_error P i j] = (test_error P i).to_nnreal :=
begin
  symmetry,
  apply ennreal_coe_eq_lift,
  rw test_error_training_mistake,
end

lemma example_correct_prob (P:PAC_problem) (i:P.Hi) (j:P.Di):
  Pr[example_correct P i j] = 1 - (test_error P i).to_nnreal :=
begin
  rw ← enot_example_error_eq_example_correct,
  rw ← Pr_one_minus_eq_not,
  rw test_error_training_mistake2,
end

lemma test_error_ne_top (P:PAC_problem) (i:P.Hi):
  (test_error P i) ≠ ⊤ :=
begin
  rw ← test_error_training_mistake,
  simp,
  apply P.has_example.default,
end



lemma finset_filter_univ {α:Type*} [F:fintype α] {P:α → Prop} {H:decidable_pred P}:
  finset.filter P (fintype.elems α) = ∅ ↔ (∀ a:α, ¬ P a) :=
begin
  split;intro A1,
  {
    intro a,
    have A2:a∉ finset.filter P (fintype.elems α),
    {
      intro A2A,
      rw A1 at A2A,
      apply A2A,
    },
    intro A3,
    apply A2,
    rw finset.mem_filter,
    split,
    {
      apply fintype.complete,
    },
    {
      apply A3,
    }
  },
  {
    ext,
    rw finset.mem_filter,
    split;intro A2,
    {
      apply (A1 a),
      apply A2.right,
    },
    {
      exfalso,
      apply A2,
    }
  }
end
/-
event_IID_pow :
  ∀ {α : Type u_1} [Mα : measurable_space α] {p : probability_measure α} {β : Type u_2} [F : fintype β]
  [I : inhabited β] {γ : Type u_3} [Mγ : measurable_space γ] (A : β → event p) (S : finset β),
    events_IID A → Pr[eall_finset S A] = Pr[A (inhabited.default β)] ^ finset.card S
-/
lemma training_error_zero_prob (P:PAC_problem) (i:P.Hi):
  Pr[training_error P i =ᵣ to_nnreal_rv 0] =
   (Pr[(example_correct P i P.has_example.default)])^(num_examples P) :=
begin
  have A1:(training_error P i =ᵣ to_nnreal_rv 0) =
      (eall_fintype P.FDi (example_correct P i) ),
  {
    apply event.eq,
    rw eall_fintype_val_def,
    unfold training_error,
    unfold count_finset_rv,
    rw event_eq_val_def,
    rw to_nnreal_rv_val_def,
    rw nnreal_random_variable_mul_val_def,
    rw to_nnreal_rv_val_def,
    simp,
    rw ← random_variable_val_eq_coe,
    rw count_finset_val_def,
    ext ω,split;intros A1A,
    {

      simp,
      intro j,
      simp at A1A,
      cases A1A,
      {
        rw finset_filter_univ at A1A,
        rw ← event_val_eq_coe,
        rw ← example_correct_iff_not_example_error,
        apply A1A,  
      },
      {
        exfalso,
        apply (@num_examples_ne_zero P),
        apply A1A,
      }
    },
    {
      simp,
      left,
      rw finset_filter_univ,
      intros j,
      simp at A1A,
      rw ← event_val_eq_coe,
      have A1B := A1A j, 
      rw ← event_val_eq_coe at A1B,
      rw example_correct_iff_not_example_error,
      apply A1A,
    }
  },
  rw A1,
  unfold eall_fintype,
  unfold num_examples,
  unfold fintype.card,
  rw @events_IID_pow P.Ω P.p P.Di P.FDi P.has_example,
  unfold finset.univ,
  apply example_correct_IID,
end


lemma fake_hypothesis_prob (P:PAC_problem)
  (ε:nnreal) (i:P.Hi):Pr[fake_hypothesis P ε i]≤(1-ε)^(num_examples P) :=
begin
  unfold fake_hypothesis,
  have A1:decidable (test_error P i ≤ ↑ε),
  {
    apply decidable_linear_order.decidable_le,
  },
  cases A1,
  {
    apply le_trans,
    apply Pr_eand_le_left,
    --Note: this could be <.
    have B1:↑ε ≤ test_error P i,
    {
      apply le_of_not_le A1,
    },
    have B2:ε ≤ (test_error P i).to_nnreal,
    {
      apply ennreal_le_to_nnreal_of_ennreal_le_of_ne_top,
      apply test_error_ne_top,
      exact B1,
    },


    rw training_error_zero_prob,
    rw example_correct_prob,
    apply nnreal_pow_mono,
    apply nnreal_sub_le_sub_of_le,
    --ε ≤ (test_error P i).to_nnreal
    exact B2,
  },
  {
    apply le_trans,
    apply Pr_eand_le_right,
    rw Pr_event_const_false,
    {
      simp,
    },
    {
      rw ← le_iff_not_gt,
      exact A1,
    },
  },
end


lemma fake_hypothesis_prob2 (P:PAC_problem)
  (ε:nnreal) (i:P.Hi):
   Pr[fake_hypothesis P ε i] ≤ nnreal.exp (- ε * (num_examples P)) :=
begin
  apply le_trans,
  apply fake_hypothesis_prob,
  apply nnreal_exp_bound2,
end

lemma eany_fake_hypothesis_prob (P:PAC_problem)
  (ε:nnreal):
   Pr[ eany_fintype P.FHi (fake_hypothesis P ε)] ≤ (num_hypotheses P) * nnreal.exp (- ε * (num_examples P)) :=
begin
  apply eany_fintype_bound2,
  intro,
  apply fake_hypothesis_prob2,
end


lemma pac_bound (P:PAC_problem)
  (ε:nnreal):
  (1:nnreal) - (num_hypotheses P) * nnreal.exp (-(ε:real) * (num_examples P:real)) ≤
  Pr[approximately_correct_event P ε]  :=
begin
  have A1:Pr[approximately_correct_event P ε] = 1 - Pr[eany_fintype P.FHi (fake_hypothesis P ε)],
  {
    symmetry,
    unfold approximately_correct_event,
    apply Pr_one_minus_eq_not (eany_fintype P.FHi (fake_hypothesis P ε)),
  },
  rw A1,
  apply nnreal_sub_le_left,
  have A2:Pr[ eany_fintype P.FHi (fake_hypothesis P ε)]
      ≤ (num_hypotheses P) * nnreal.exp (- ε * (num_examples P)),
  {
    apply eany_fake_hypothesis_prob,
  },
  apply A2,
end

lemma pac_bound2 (P:PAC_problem) (ε:nnreal):
  probably_approximately_correct P ε
  ((num_hypotheses P) * nnreal.exp (-ε * (num_examples P))) :=
begin
  unfold probably_approximately_correct,
  apply pac_bound,
end
