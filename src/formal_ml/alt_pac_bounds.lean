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


namespace alt_pac

/- A first option is to define our concepts minimally. -/

def raw_error {Ω:Type*} [M:measurable_space Ω]  (μ:measure_theory.measure Ω) {β:Type*} 
 (X_test:Ω → (β × bool)) (h:set β):ennreal := 
  μ (X_test ⁻¹' (h.prod {ff} ∪ (hᶜ).prod {tt}))

def raw_false_positive_rate {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) {β:Type*} 
 (X_test:Ω → (β × bool)) (h:set β):ennreal := 
  μ (X_test ⁻¹' (h.prod {ff}))

def raw_false_negative_rate {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) {β:Type*} 
 (X_test:Ω → (β × bool)) (h:set β):ennreal := 
  μ (X_test ⁻¹' (hᶜ.prod {tt}))

def raw_error_eq_raw_fpr_add_raw_fnr {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) {β:Type*} 
 (X_test:Ω → (β × bool)) (h:set β):Prop := raw_error μ X_test h = raw_false_positive_rate μ X_test h + raw_false_negative_rate μ X_test h

/- However, this leads us to require additional constraints for
concepts that should always be true. -/
lemma measurable_error_eq_fpr_add_fnr {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) {β:Type*} 
 (X_test:Ω → (β × bool)) (h:set β) [measurable_space β]:(measurable_set h) → (measurable X_test) → raw_error_eq_raw_fpr_add_raw_fnr μ X_test h := begin
  intros h_h_meas h_X_test_measurable,
  simp only [raw_error_eq_raw_fpr_add_raw_fnr, raw_false_negative_rate, raw_false_positive_rate,
        raw_error, set.preimage_union],
  rw measure_theory.measure_union,
  { rw set.disjoint_iff, apply set.disjoint_preimage, rw set.subset_def,
    intros x, intros h_contra, simp at h_contra, 
    cases h_contra with h_contra_fp h_contra_fn,
    cases h_contra_fp with x' h_contra_fp,
    cases h_contra_fn with x'' h_contra_fn,
    cases h_contra_fp with h_contra_fp_pos h_contra_fp_false,
    cases h_contra_fn with h_contra_fn_neg h_contra_fn_true,
    subst h_contra_fp_false,
    simp at h_contra_fn_true,
    apply false.elim h_contra_fn_true, },
  apply measurable_elim,
  apply h_X_test_measurable,
  apply measurable_set.prod,
  apply h_h_meas,
  apply measurable_space.measurable_set_top,
  apply measurable_elim,
  apply h_X_test_measurable,
  apply measurable_set.prod,
  apply measurable_set.compl,
  apply h_h_meas,
  apply measurable_space.measurable_set_top,
end

/-Another possibility is to require measurability as error is defined. -/
def meas_error {Ω:Type*} [M:measurable_space Ω]  (μ:measure_theory.measure Ω) 
[measure_theory.probability_measure μ] {β:Type*} [measurable_space β] 
 (X_test:Ω → (β × bool)) (h_meas_X_test:measurable X_test) (h:set β) (h_h_meas:measurable_set h):ennreal := 
  μ (X_test ⁻¹' (h.prod {ff} ∪ (hᶜ).prod {tt}))

lemma meas_error_eq_raw_error {Ω:Type*} [M:measurable_space Ω]  (μ:measure_theory.measure Ω) 
[measure_theory.probability_measure μ] {β:Type*} [measurable_space β] 
 (X_test:Ω → (β × bool)) (h_meas_X_test:measurable X_test) (h:set β) (h_h_meas:measurable_set h):
 meas_error μ X_test h_meas_X_test h h_h_meas = raw_error μ X_test h := rfl

def meas_false_positive_rate 
{Ω:Type*} [M:measurable_space Ω]  (μ:measure_theory.measure Ω) 
[measure_theory.probability_measure μ] {β:Type*} [measurable_space β] 
 (X_test:Ω → (β × bool)) (h_meas_X_test:measurable X_test) (h:set β) (h_h_meas:measurable_set h):ennreal := 
  μ (X_test ⁻¹' (h.prod {ff}))

lemma meas_false_positive_rate_eq_raw_false_positive_rate 
{Ω:Type*} [M:measurable_space Ω]  (μ:measure_theory.measure Ω) 
[measure_theory.probability_measure μ] {β:Type*} [measurable_space β] 
 (X_test:Ω → (β × bool)) (h_meas_X_test:measurable X_test) (h:set β) (h_h_meas:measurable_set h):
  meas_false_positive_rate μ X_test h_meas_X_test h h_h_meas = raw_false_positive_rate μ X_test h := rfl
 

def meas_false_negative_rate {Ω:Type*} [M:measurable_space Ω]  (μ:measure_theory.measure Ω) 
[measure_theory.probability_measure μ] {β:Type*} [measurable_space β] 
 (X_test:Ω → (β × bool)) (h_meas_X_test:measurable X_test) (h:set β) (h_h_meas:measurable_set h):ennreal := 
  μ (X_test ⁻¹' (hᶜ.prod {tt}))

lemma meas_false_negative_rate_eq_raw_false_negative_rate 
{Ω:Type*} [M:measurable_space Ω]  (μ:measure_theory.measure Ω) 
[measure_theory.probability_measure μ] {β:Type*} [measurable_space β] 
 (X_test:Ω → (β × bool)) (h_meas_X_test:measurable X_test) (h:set β) (h_h_meas:measurable_set h):
  meas_false_negative_rate μ X_test h_meas_X_test h h_h_meas = raw_false_negative_rate μ X_test h := rfl


def meas_error_eq_meas_fpr_add_meas_fnr {Ω:Type*} [M:measurable_space Ω]  (μ:measure_theory.measure Ω)
[measure_theory.probability_measure μ] {β:Type*} [measurable_space β] 
 (X_test:Ω → (β × bool)) (h_meas_X_test:measurable X_test) (h:set β) (h_h_meas:measurable_set h):Prop := 
  meas_error μ X_test h_meas_X_test h h_h_meas = meas_false_positive_rate μ X_test h_meas_X_test h h_h_meas + 
  meas_false_negative_rate μ X_test h_meas_X_test h h_h_meas

lemma meas_error_eq_meas_fpr_add_meas_fnr' {Ω:Type*} [M:measurable_space Ω]  (μ:measure_theory.measure Ω)
[measure_theory.probability_measure μ] {β:Type*} [measurable_space β] 
 (X_test:Ω → (β × bool)) (h_meas_X_test:measurable X_test) (h:set β) (h_h_meas:measurable_set h):
 meas_error_eq_meas_fpr_add_meas_fnr μ X_test h_meas_X_test h h_h_meas :=
begin
  unfold meas_error_eq_meas_fpr_add_meas_fnr,
  rw meas_error_eq_raw_error,
  rw meas_false_positive_rate_eq_raw_false_positive_rate,
  rw meas_false_negative_rate_eq_raw_false_negative_rate,
  apply measurable_error_eq_fpr_add_fnr,
  apply h_h_meas,
  apply h_meas_X_test,
end

end alt_pac

/- A final approach is to embed measurability within the arguments themselves. We can add a great deal of syntactic sugar as well. -/

section error_def
variables {Ω:Type*} {p:probability_space Ω} {β:Type*} {Mβ:measurable_space β}
variables (X_test:p →ᵣ (Mβ ×ₘ bool.measurable_space)) (h:measurable_setB Mβ)
def error:nnreal := 
   Pr[(X_test.fst ∈ᵣ h ∧ X_test.snd =ᵣ ff) ∨ (X_test.fst ∉ᵣ h) ∧ (X_test.snd =ᵣ tt)] 

def false_positive_rate:nnreal :=
   Pr[(X_test.fst ∈ᵣ h ∧ X_test.snd =ᵣ ff)] 

def false_negative_rate:nnreal :=
   Pr[(X_test.fst ∉ᵣ h) ∧ (X_test.snd =ᵣ tt)] 

lemma error_eq_fpr_add_fnr:error X_test h = false_positive_rate X_test h + false_negative_rate X_test h :=
begin
  simp only [error, false_positive_rate, false_negative_rate],
  apply Pr_disjoint_eor,  
  simp,
  rw set.disjoint_iff,
  apply set.subset.trans,
  apply set.inter_subset_inter,
  apply set.inter_subset_left,
  apply set.inter_subset_left,
  rw set.inter_compl_self,
end 

end error_def

/-A concept of PAC bounds separated from the method of generating a hypothesis. -/
section pac_def
variables {Ω:Type*} {p:probability_space Ω} {β:Type*} {Mβ:measurable_space β} (X_test:p →ᵣ (Mβ ×ₘ bool.measurable_space))
 {H:Type*} (R:H → measurable_setB Mβ)  [TM:top_measurable H] (A:p →ᵣ TM.to_measurable_space)

def error_fun:H → nnreal := (λ (h:H), error X_test (R h)) 

noncomputable def error_mf:(@top_measurable.to_measurable_space H TM) →ₘ nnreal.measurable_space := 
top_measurable_fun (λ h, error X_test (R h)) _


/- A generic variant of probably approximately correct.
  This is the probability that a hypothesis drawn from some arbitrary distribution A is
  probably approximately correct. -/
def gen_probably_approximately_correct (δ ε:nnreal):Prop := Pr[((error_mf X_test R) ∘r A) ≤ᵣ ε] ≥ 1 - δ

 
/- A problem is realizable if there exists a representation for a correct hypothesis. -/
def realizable:Prop := ∃ (h:H), error X_test (R h) = 0



lemma gen_probably_approximately_correct_trivial (ε:nnreal):
  gen_probably_approximately_correct X_test R A 1 ε := begin
  simp [gen_probably_approximately_correct],
end 

lemma gen_probably_approximately_correct_mono (δ δ' ε:nnreal):
  (δ ≤ δ') →
  gen_probably_approximately_correct X_test R A δ ε → 
  gen_probably_approximately_correct X_test R A δ' ε := begin
  simp [gen_probably_approximately_correct],
  intros h1 h2,
  apply le_trans,
  apply h2,
  apply add_le_add,
  apply le_refl _,
  apply h1,
end 

end pac_def


section pac_def
variables {Ω:Type*} {p:probability_space Ω} {β:Type*} [Mβ:measurable_space β] (X_test:p →ᵣ (Mβ ×ₘ bool.measurable_space))
{D:Type*} (X_train:D → (p →ᵣ (Mβ ×ₘ bool.measurable_space)))
{H:Type*} [TM:top_measurable H]
(A:(Πₘ (d:D), Mβ ×ₘ bool.measurable_space) →ₘ TM.to_measurable_space)  
 (R:H → measurable_setB Mβ) 

def algorithm_rv:p →ᵣ TM.to_measurable_space := A ∘r (pi.random_variable_combine X_train)

/- A proposition that an algorithm based upon training data X_train is probably approximately
   correct. -/
def probably_approximately_correct (δ ε:nnreal):Prop :=
  gen_probably_approximately_correct X_test R (algorithm_rv X_train A) δ  ε

def example_error (h:H) (d:D):event p := 
  (((X_train d).fst ∈ᵣ (R h)) ∧ ((X_train d).snd =ᵣ ff)) ∨
  (((X_train d).fst ∉ᵣ (R h)) ∧ ((X_train d).snd =ᵣ tt))

/- Rather than consider these concepts as events, we insist that they
   hold for all instances. -/
def consistent_hypothesis (x:D→ β × bool) (h:H):Prop :=
   ∀ d:D, (x d).fst ∈ (R h).val ↔ (x d).snd

def consistent_algorithm:Prop := ∀ x:(D → (β × bool)), 
  (∃ (c:H), consistent_hypothesis R x c) →
  (consistent_hypothesis R x (A.val x))


lemma probably_approximately_correct_trivial (ε:nnreal):
  probably_approximately_correct X_test X_train A R 1 ε := begin
  simp [probably_approximately_correct],
  apply gen_probably_approximately_correct_trivial,
end 

lemma probably_approximately_correct_mono (δ δ' ε:nnreal):
  (δ ≤ δ') →
  probably_approximately_correct X_test X_train A R δ ε → 
  probably_approximately_correct X_test X_train A R δ' ε := begin
  simp [probably_approximately_correct],
  intros h1 h2,
  apply gen_probably_approximately_correct_mono ,
  apply h1,
  apply h2,
end

end pac_def

lemma const_measurable_fun_val {Ω:Type*} {M:measurable_space Ω} (x:nnreal):
  ((↑x:(M →ₘ nnreal.measurable_space)).val) = (λ ω:Ω, x) := rfl


section pac_proof
variables {Ω:Type*} {p:probability_space Ω} {β:Type*} [Mβ:measurable_space β] (X_test:p →ᵣ (Mβ ×ₘ bool.measurable_space))
{D:Type*} (X_train:D → (p →ᵣ (Mβ ×ₘ bool.measurable_space)))
{H:Type*} [TM:top_measurable H]
(A:(Πₘ (d:D), Mβ ×ₘ bool.measurable_space) →ₘ TM.to_measurable_space)  
 (R:H → measurable_setB Mβ) 

lemma error_as_measurable_setB (h:H) (Y:p →ᵣ (Mβ ×ₘ bool.measurable_space)):
 ((mf_fst ∘r Y) ∈ᵣ R h∧(mf_snd ∘r Y) =ᵣ ↑ff ∨ (mf_fst ∘r Y)∉ᵣ R h∧(mf_snd ∘r Y) =ᵣ ↑tt)
 = Y ∈ᵣ ((R h).prod (measurable_setB_top {ff}) ∪ ((R h)ᶜ).prod (measurable_setB_top {tt})) :=
begin
    apply event.eq,
    simp,
    ext ω,
    simp, split; intros A1; cases A1,
    { left, apply exists.intro (Y.val ω).fst, simp [A1], rw ← A1.right, simp },
    { right, apply exists.intro (Y.val ω).fst, simp [A1], rw ← A1.right, simp },
    { left, cases A1 with x A1, rw ← A1.right, simp [A1] },
    { right, cases A1 with x A1, rw ← A1.right, simp [A1] }
end

lemma Pr_example_error_eq_error (h:H) (d:D):
(random_variable_identical X_test (X_train d)) → Pr[example_error X_train R h d] = error X_test (R h) :=
begin
  intros h1,
  simp [error],
  simp [example_error],
  rw error_as_measurable_setB R h (X_train d),
  rw error_as_measurable_setB R h X_test,
  symmetry,
  apply h1,
end


/- The average number of errors for a hypothesis in the training data, 
   as a random variable. -/
noncomputable def training_error (h:H) [FD:fintype D]:p →ᵣ (borel nnreal) :=
   average_identifier (example_error X_train R h) FD

def hypothesis_consistent_event (h:H) [FD:fintype D]:
  event p := (∀ᵣ (d:D), enot (example_error X_train R h d)) 

lemma in_hypothesis_consistent_event_iff_consistent_hypothesis (h:H) [FD:fintype D] (ω:Ω):
   ω ∈ (hypothesis_consistent_event X_train R h) ↔ (consistent_hypothesis R (λ (d:D), (X_train d).val ω) h) :=
begin
  classical,
  simp [hypothesis_consistent_event],
  split, 
  { intros h1, rw event_mem_val at h1,
    simp only [consistent_hypothesis],
    intros d,
    simp at h1,
    have h2 := h1 d,
    rw ← subtype.val_eq_coe at h2,
    simp [example_error] at h2,
    rw decidable.not_or_iff_and_not at h2,
    cases h2 with h2 h3,
    rw not_and at h2,
    rw and_comm at h3,
    rw not_and at h3,
    simp at h3,
    simp at h2,
    split, intros h4,
    simp at h4,
    apply h2,
    apply h4,
    intros h5,
    simp,
    apply h3,
    apply h5 },
  { intros h1, rw event_mem_val,
    simp only [consistent_hypothesis] at h1,
    simp, 
    intros d,
    simp [example_error],
    rw ← subtype.val_eq_coe,
    simp,
    rw decidable.not_or_iff_and_not,
    have h2 := h1 d,
    simp at h2,
    split,
    { rw not_and, intros h3,
      simp, rw h2 at h3, 
      apply h3 },
    { rw and_comm, rw not_and, intros h3,
      simp, rw h2, apply h3,  },
  },
end

def he_hypothesis_consistent_event (h:H) [FD:fintype D] (ε:nnreal):
  event p := (hypothesis_consistent_event X_train R h) ∧ event_const (error X_test (R h) > ε)

--set_option trace.class_instances true
def he_hypothesis_consistent_pac [encodable H] [fintype D] (δ ε:nnreal):Prop :=
  Pr[∃ᵣ (h:H), he_hypothesis_consistent_event X_test X_train R h ε] ≤ δ  

/- A realizable hypothesis has probability one of being consistent, i.e.
   almost surely it is consistent. -/
lemma exists_consistent_hypothesis_of_realizable [fintype D]:realizable X_test R →
(∀ (d:D), random_variable_identical X_test (X_train d)) →
∃ (h:H), Pr[hypothesis_consistent_event X_train R h]=1 := begin
  classical,
  intros h1 h2,
  simp [realizable] at h1,
  cases h1 with h h1,
  existsi [h],
  rw ← Pr_one_minus_not_eq,
  
  simp [hypothesis_consistent_event],
  rw not_forall_not_eq_exists',
  have h3:Pr[∃ᵣ  (a : D), @example_error Ω p β Mβ D X_train H R h a] = 0,
  { 
    rw ← le_zero_iff,
    apply le_trans,
    apply eany_fintype_bound,
    rw tsum_fintype,
    have h3_1:(λ (d:D), Pr[@example_error Ω p β Mβ D X_train H R h d]) =(λ (d:D), 0),
    { ext1 d,
      rw Pr_example_error_eq_error,
      apply h1,
      apply h2 },
    rw h3_1,
    simp,
     },
  rw h3,
  simp,
end

lemma approximately_correct_if_he_hypothesis_consistent [encodable H] [fintype D] [nonempty D]
  (ε:nnreal) (h:H):
(Pr[hypothesis_consistent_event X_train R h] = 1) →
(consistent_algorithm A R) →
(((∃ᵣ (h:H), he_hypothesis_consistent_event X_test X_train R h ε)ᶜ ∧
 hypothesis_consistent_event X_train R h
).val)
⊆ 
((error_mf X_test R ∘r algorithm_rv X_train A) ≤ᵣ ε).val 
 :=
begin
  intros h0 h1,
  rw set.subset_def,
  intros ω h2,
  simp only [error_mf, top_measurable_fun, algorithm_rv, pi.measurable_fun, set.mem_set_of_eq, subtype.val_eq_coe,
  event_le_val_def],
  rw ← subtype.val_eq_coe,  
  rw ← subtype.val_eq_coe,
  rw const_measurable_fun_val,
  simp,  
  simp [he_hypothesis_consistent_event,
        const_measurable_fun] at h2,
  let h':H := A.val (λ (d : D), (X_train d).val ω),
  begin
    have B2:error X_test (R h') ≤ ε,
    { cases h2 with h2 h3,
      apply h2,
      rw ← subtype.val_eq_coe,
      rw ← event_mem_val,
      rw in_hypothesis_consistent_event_iff_consistent_hypothesis,
      simp [consistent_algorithm] at h1,
      simp [h'], apply h1, 
      rw ← subtype.val_eq_coe at h3,
      rw ← event_mem_val at h3,
      rw in_hypothesis_consistent_event_iff_consistent_hypothesis at h3,
      apply h3 },
    apply B2,
  end
end

lemma consistent_pac [encodable H] [fintype D] [nonempty D] (δ ε:nnreal):(realizable X_test R) →
  (∀ (d:D), random_variable_identical X_test (X_train d)) →
  (he_hypothesis_consistent_pac X_test X_train R δ ε) → (consistent_algorithm A R) →
  (probably_approximately_correct X_test X_train A R δ ε) :=
begin
  intros h_realizable h_identical h1 h2,
  unfold probably_approximately_correct gen_probably_approximately_correct,
  unfold he_hypothesis_consistent_pac at h1,
  have h3:∃ (h:H), Pr[hypothesis_consistent_event X_train R h]=1,
  { apply exists_consistent_hypothesis_of_realizable, apply h_realizable,
    apply h_identical },
  cases h3 with c h3,

  have h4:Pr[(∃ᵣ  (h : H), he_hypothesis_consistent_event X_test X_train R h ε)ᶜ ∧ (hypothesis_consistent_event X_train R c)] ≥ 1 - δ,
  { 
    have h4_1:Pr[(hypothesis_consistent_event X_train R c)ᶜ]=0,
    { rw neg_eq_not, rw ← Pr_one_minus_eq_not, rw h3, simp },
    have h4_2:Pr[(∃ᵣ  (h : H), he_hypothesis_consistent_event X_test X_train R h ε) ∨ (hypothesis_consistent_event X_train R c)ᶜ] ≤ δ,
    { apply le_trans, apply Pr_le_eor_sum,
      rw h4_1,
      rw add_zero,
      apply h1 },
    have h4_3:Pr[((∃ᵣ  (h : H), he_hypothesis_consistent_event X_test X_train R h ε) ∨ (hypothesis_consistent_event X_train R c)ᶜ)ᶜ] ≥ 1 - δ,
    { apply Pr_compl_ge_of_Pr_le, apply h4_2 },
    have h4_4:((∃ᵣ  (h : H), he_hypothesis_consistent_event X_test X_train R h ε) ∨ (hypothesis_consistent_event X_train R c)ᶜ)ᶜ = ((∃ᵣ  (h : H), he_hypothesis_consistent_event X_test X_train R h ε)ᶜ ∧ (hypothesis_consistent_event X_train R c)),
    { rw compl_eor_eq_compl_eand_compl, repeat {rw neg_eq_not}, rw enot_enot_eq_self, },
    rw ← h4_4,
    apply h4_3, 
     },
  apply le_trans h4,
  apply event_prob_mono2,
  apply approximately_correct_if_he_hypothesis_consistent,
  apply h3,
  apply h2,
end

end pac_proof


section finite_pac_proof
variables {Ω:Type*} {p:probability_space Ω} {β:Type*} [Mβ:measurable_space β] (X_test:p →ᵣ (Mβ ×ₘ bool.measurable_space))
{D:Type*} (X_train:D → (p →ᵣ (Mβ ×ₘ bool.measurable_space)))
{H:Type*} [TM:top_measurable H]
(A:(Πₘ (d:D), Mβ ×ₘ bool.measurable_space) →ₘ TM.to_measurable_space)  
 (R:H → measurable_setB Mβ) 

def example_correct (h:H) (d:D):event p := ¬ₑ (example_error X_train R h d)

lemma example_correct_def (h:H) (d:D):example_correct X_train R h d = ¬ₑ (example_error X_train R h d) := rfl

lemma example_error_IID (h:H):
  (random_variables_IID X_train) →
  (events_IID (example_error X_train R h)) :=
begin
  intros h1,
  have h2:(example_error X_train R h) = (λ (d:D),
    (X_train d) ∈ᵣ ((R h).prod (measurable_setB_top {ff}) ∪ ((R h)ᶜ).prod (measurable_setB_top {tt}))),
  { ext1 d,
    simp [example_error],
    rw error_as_measurable_setB },
  rw h2,
  apply rv_event_IID,
  apply h1,
end
lemma example_correct_IID (h:H):
  (random_variables_IID X_train) →
  (events_IID (example_correct X_train R h)) :=
begin
  intros h1,
  have h2:events_IID (enot ∘ (example_error X_train R h)),
  { apply events_IID_not_of_events_IID,
    apply example_error_IID,
    apply h1,
  },
  apply h2,
end

lemma Pr_hypothesis_consistent_event (h:H) [FD:fintype D] [NE:nonempty D]:
  (∀ (d:D), random_variable_identical X_test (X_train d)) →
  (random_variables_IID X_train) →
  Pr[hypothesis_consistent_event X_train R h] = (1-error X_test (R h))^(fintype.card D) :=
begin
  intros h1 h2,
  simp [hypothesis_consistent_event],
  have h3:(λ (d:D), ¬ₑ example_error X_train R h d) =
    (λ (d:D), example_correct X_train R h d) := rfl,
  rw h3,
  haveI:inhabited D := classical.inhabited_of_nonempty NE,
  rw eall_fintype_eq_eall_finset, rw events_IID_pow,
  have h4:finset.univ.card = fintype.card D := rfl,
  rw h4,
  have h5:Pr[example_correct X_train R h (default D)]
    = (1 - error X_test (R h)),
  { rw example_correct_def, rw ← Pr_one_minus_eq_not,
    rw Pr_example_error_eq_error,  
    apply h1 },
  rw h5,
  apply example_correct_IID, apply h2, 
end

lemma Pr_he_hypothesis_consistent_event (h:H) [FD:fintype D] [NE:nonempty D] (ε:nnreal):
  (∀ (d:D), random_variable_identical X_test (X_train d)) →
  (random_variables_IID X_train) →
  Pr[he_hypothesis_consistent_event X_test X_train R h ε] ≤ (1-ε)^(fintype.card D) :=
begin
  intros h1 h2,
  simp [he_hypothesis_consistent_event],
  cases decidable.em (ε < error X_test (R h)) with h3 h3,
  { apply le_trans,
    apply Pr_eand_le_left,
    rw Pr_hypothesis_consistent_event X_test,
    apply nnreal_pow_mono,
    apply nnreal_sub_le_sub_of_le,
    apply le_of_lt h3,
    apply h1,
    apply h2 },
  { apply le_trans,
    apply Pr_eand_le_right, 
    rw Pr_event_const_false,
    simp,
    apply h3 },
end

lemma Pr_he_hypothesis_consistent_event_exp (h:H) [FD:fintype D] [NE:nonempty D] (ε:nnreal):
  (∀ (d:D), random_variable_identical X_test (X_train d)) →
  (random_variables_IID X_train) →
  Pr[he_hypothesis_consistent_event X_test X_train R h ε] ≤ nnreal.exp (-ε * fintype.card D) :=
begin
  intros h1 h2,
  apply le_trans,
  apply Pr_he_hypothesis_consistent_event,
  apply h1,
  apply h2,
  apply nnreal_exp_bound2,
end



def he_hypothesis_consistent_pac_fintype [FH:fintype H] [fintype D] (δ ε:nnreal):Prop :=
  @he_hypothesis_consistent_pac _ _ _ _ X_test _ X_train _ R (fintype.encodable H) _ δ ε
--  Pr[∃ᵣ (h:H), he_hypothesis_consistent_event X_test T R h ε] ≤ δ  

lemma he_hypothesis_consistent_pac_fintype_def [FH:fintype H] [fintype D] (δ ε:nnreal):
  he_hypothesis_consistent_pac_fintype X_test X_train R δ ε = 
  (Pr[∃ᵣ (h:H), he_hypothesis_consistent_event X_test X_train R h ε] ≤ δ) := begin
  have h1:(∃ᵣ (h:H), he_hypothesis_consistent_event X_test X_train R h ε) =
          eany_fintype FH (λ (h:H), he_hypothesis_consistent_event X_test X_train R h ε) := rfl,
  rw h1,
  clear h1,
  simp [he_hypothesis_consistent_pac_fintype, he_hypothesis_consistent_pac],
  rw eany_encodable_notation_def,
  rw eany_eq_eany_fintype,
end

lemma he_hypothesis_consistent_pac_fintype_bound [FH:fintype H] [FD:fintype D] 
  [NE:nonempty D] (ε:nnreal):
  (∀ (d:D), random_variable_identical X_test (X_train d)) →
  (random_variables_IID X_train) →
  he_hypothesis_consistent_pac_fintype X_test X_train R 
    ((fintype.card H) * nnreal.exp (-ε * fintype.card D)) ε :=
begin
  intros h1 h2,
  rw he_hypothesis_consistent_pac_fintype_def,
  apply eany_fintype_bound2,
  intros h,
  apply Pr_he_hypothesis_consistent_event_exp,
  apply h1,
  apply h2,
end


lemma consistent_pac_finite [fintype H] [fintype D] [nonempty D] (δ ε:nnreal):(realizable X_test R) →
  (∀ (d:D), random_variable_identical X_test (X_train d)) →
  (he_hypothesis_consistent_pac_fintype X_test X_train R δ ε) → (consistent_algorithm A R) →
  (probably_approximately_correct X_test X_train A R δ
   ε) :=
begin
  intros h1 h2 h3 h4,
  haveI:encodable H :=fintype.encodable H,
  apply consistent_pac,
  apply h1,
  apply h2,
  apply h3,
  apply h4,
end 

/--
  This is the meat of the proof of PAC bounds on a finite set of hypotheses.
  The only condition that makes it incomplete is that it requires the training data
  to be nonempty, whereas the result is trivially true if D is empty.
 -/
lemma pac_finite_bound_nonempty 
  [fintype H]                                    -- hypothesis space is finite
  [fintype D]                                    -- examples are finite
  [nonempty D]                                   -- examples are nonempty
  (ε:nnreal):                                    -- approximation parameter
  (realizable X_test R) →                        -- there exists a hypothesis with zero error
  (∀ (d:D), random_variable_identical X_test (X_train d)) →
                                                 -- the training data is identically
                                                 -- distributed as the test
  (random_variables_IID X_train) →               -- the training data is IID
  (consistent_algorithm A R) →                   -- the algorithm is consistent.
  (probably_approximately_correct X_test X_train A R
  ((fintype.card H) * nnreal.exp (-ε * fintype.card D))
  ε)                                             
  -- The algorithm has error less than ε with probability at least
  -- 1 - ((fintype.card H) * nnreal.exp (-ε * fintype.card D))
 :=
begin
  intros h1 h2 h3 h4,
  apply consistent_pac_finite,
  apply h1,
  apply h2,
  apply he_hypothesis_consistent_pac_fintype_bound,
  apply h2,
  apply h3,
  apply h4,
end

/-- A trivial result: if there are no examples, then the bound is trivial. -/
lemma pac_finite_bound_empty 
  [fintype H]                                    -- hypothesis space is finite
  [fintype D]                                    -- examples are finite
  (ε:nnreal):                                    -- approximation parameter
  (realizable X_test R) →                             -- (Just to prove H is nonempty).
  (fintype.card D = 0) →
  (probably_approximately_correct X_test X_train A R
  ((fintype.card H) * nnreal.exp (-ε * fintype.card D))
  ε)
  -- The algorithm has error less than ε with probability at least
  -- 1 - ((fintype.card H) * nnreal.exp (-ε * fintype.card D))
 :=
begin
  intros h1 h2,
  cases h1 with c h1,
  have h3:nonempty H := nonempty.intro c,
  have h4:(1:nnreal) ≤ ((fintype.card H) * nnreal.exp (-ε * fintype.card D)),
  { rw h2, simp, rw nat.succ_le_iff, rw fintype.card_pos_iff, apply h3 },
  apply probably_approximately_correct_mono,
  apply h4,
  apply probably_approximately_correct_trivial,
end

end finite_pac_proof

theorem pac_finite_bound 
  {Ω:Type*}                                      -- Outcome space 
  {p:probability_space Ω}                        -- Probability space
  {β:Type*}                                      -- instance space
  [Mβ:measurable_space β]                        -- measurable space over instances
  (X_test:p →ᵣ (Mβ ×ₘ bool.measurable_space))    -- test data
  {D:Type*}                                      -- training data index
  (T:D → (p →ᵣ (Mβ ×ₘ bool.measurable_space)))   -- training data
  {H:Type*}                                      -- hypothesis space
  [TM:top_measurable H]                          -- measurable space over hypotheses
  (A:(Πₘ (d:D), Mβ ×ₘ bool.measurable_space) →ₘ TM.to_measurable_space)
                                                 -- algorithm
  (R:H → measurable_setB Mβ)                      -- representation schema
  [fintype H]                                    -- hypothesis space is finite
  [fintype D]                                    -- examples are finite
  (ε:nnreal):                                    -- approximation parameter
  (realizable X_test R) →                        -- there exists a hypothesis with zero error
  (∀ (d:D), random_variable_identical X_test (T d)) →
                                                 -- the training data is identical to test
  (random_variables_IID T) →                     -- the training data is IID
  (consistent_algorithm A R) →                   -- the algorithm is consistent.
  (probably_approximately_correct X_test T A R
  ((fintype.card H) * nnreal.exp (-ε * fintype.card D))
  ε)                                             
  -- The algorithm has error less than ε with probability at least
  -- 1 - ((fintype.card H) * nnreal.exp (-ε * fintype.card D))
 :=
begin
  intros h1 h2 h3 h4,
  cases decidable.em (fintype.card D = 0),
  { apply pac_finite_bound_empty,
    apply h1,
    apply h },
  { have h5:0 < fintype.card D,
    { apply decidable.by_contradiction, intros contra,
      apply h, simp at contra, apply contra },
    rw fintype.card_pos_iff at h5,
    haveI: nonempty D := h5,
    apply pac_finite_bound_nonempty,
    repeat { assumption } },
end


/-
def generate_training_data
  {β:Type*}                                      -- instance space
  [Mβ:measurable_space β]                        -- measurable space over instances
  {H:Type*}                                      -- hypothesis space
  [TM:top_measurable H]                          -- measurable space over hypotheses
  (R:H → measurable_setB Mβ)                      -- representation schema
  {Ω:Type*}                                      -- For all
  (A:nnreal → nnreal → Π m:ℕ, (Πₘ (d:fin m), Mβ ×ₘ bool.measurable_space) →ₘ TM.to_measurable_space):
-/



#check 3


/-

Ultimately, we want to be able to talk about an algorithm that has access
to a process of independent and identical random variables EX(c, D). While
we have shown how to create the product of two measures and the product
of a finite number of measures.
From Kearns and Vazirani, An Introduction to Computational Learning Theory:

--------------------------------------------------------------------
Definition: (The PAC Model, Preliminary definition), PAC-learnable
Let C be a concept class over X. We say that C is PAC learnable if there exists
an algorithm L with the following property: for every concept c∈ C, for every 
distribution D on X, and for all 0 < ε < 1/2, and 0 < δ < 1/2, if L is
given access to EX(c, D), and inputs ε and δ, then with probability at
least 1 - δ, L outputs a hypothesis concept h ∈ C satisfying error(h) ≤ ε.
This probability is taken over the random examples drawn by calls to 
EX(c, D), and any internal randomization of L.

If L runs in time polynomial in (1/ε) and (1/δ), we say that C is 
efficiently PAC learnable. We will sometimes refer to the input ε
as the error parameter, and the input δ as the confidence parameter.
--------------------------------------------------------------------

Alternately, we can write down a simpler variant that covers many
PAC learning algorithms.
0. For a specific concept class C (represented by R):
1. Consider ε and δ:
2. Algorithm (part 1) chooses an m given ε and δ.
3. Get a distribution of examples.
4. Algorithm (part 2) uses m, ε, and δ,
   to produce an hypothesis in h.
-/ 

/- TODO: delete or fix! -/
def pac_learnable_simple_algorithm
  {β:Type*}                                      -- instance space
  [Mβ:measurable_space β]                        -- measurable space over instances
  {H:Type*}                                      -- hypothesis space
  [TM:top_measurable H]                          -- measurable space over hypotheses
  (R:H → measurable_setB Mβ)                      -- representation schema
  (num_examples:nnreal → nnreal → nat)           -- number of examples as a function of the hypothesis.
  (A:nnreal → nnreal → Π m:ℕ, (Πₘ (d:fin m), Mβ ×ₘ bool.measurable_space) →ₘ TM.to_measurable_space):
                                                 -- An algorithm for choosing a hypothesis.
  Prop := ∀ (h:H)                                -- For all hypotheses,
            (ε:nnreal)                           -- For all error parameters (see constraints below),
            (δ:nnreal)                           -- For all confidence parameters (see constraints),
            {Ω:Type*}                            -- For all
            {p:probability_space Ω} 
            (X:p →ᵣ Mβ), true
            
   
  
