/-
Copyright 2021 Google LLC

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
import formal_ml.prod_measure
import formal_ml.finite_pi_measure
import formal_ml.probability_space

/-
  This file allows the construction of new probability spaces. This is useful
  in particular when you want to consider a hypothetical scenario to relate back
  to a real one.

  For a family of random variables X indexed over β, there are a variety of operations.
  1. pi.random_variable: We can create a new family of random variables Y, where for all (b:β),
     X b and Y b are identical, and for any (b b':β), Y b and Y b' are independent.
     A new probability measure is created for Y.
  2. pi.random_variable_combine: create a new single random variable whose domain is
     a function. Note: this does not create a new probability measure.

  There are also some functions which work with a single random variable.
  1. pi.rv: create a random variable that maps from a product probability measure to
     a outcome space of a single measure in the product.
  


-/


noncomputable def prod.measure_space {α β:Type*} (Mα:measure_theory.measure_space α) (Mβ:measure_theory.measure_space β):measure_theory.measure_space (α × β) :=
  @measure_theory.measure_space.mk (α × β) (@prod.measurable_space α β Mα.to_measurable_space Mβ.to_measurable_space) (prod.measure Mα.volume Mβ.volume)

lemma prod.measure_space.apply (α β:Type*) (Mα:measure_theory.measure_space α) (Mβ:measure_theory.measure_space β) (S:set (α × β)):
  @measure_theory.measure_space.volume _ (prod.measure_space Mα Mβ) S =
  (prod.measure Mα.volume Mβ.volume) S := rfl 



lemma prod.measure_space.apply_prod (α β:Type*) (Mα:measure_theory.measure_space α) (Mβ:measure_theory.measure_space β) (A:set α) (B:set β):measurable_set A →
  measurable_set B →
  @measure_theory.measure_space.volume _ (prod.measure_space Mα Mβ) (A.prod B) = 
  (@measure_theory.measure_space.volume _ Mα (A)) * 
  (@measure_theory.measure_space.volume _ Mβ (B)) := begin
  intros h1 h2,
  rw prod.measure_space.apply,
  rw prod.measure.apply_prod,
  apply h1,
  apply h2,
end
/- This is best understood through the lemma prod.probability_space.apply_prod -/
noncomputable def probability_space.prod {α β:Type*} (Pα:probability_space α) (Pβ:probability_space β):probability_space (α × β) := 
@probability_space.mk (α × β) 
  (prod.measure_space Pα.to_measure_space Pβ.to_measure_space)
  begin
  simp,
  have A1:(@set.univ α).prod (@set.univ β) = (@set.univ (α × β)),
  { simp },
  rw ← A1,  
  rw prod.measure_space.apply_prod,
  repeat { simp },
end

def event.prod {α β:Type*} {Pα:probability_space α} {Pβ:probability_space β} 
  (A:event Pα) (B:event Pβ):
  event (Pα.prod Pβ) := measurable_setB.prod A B

lemma event.prod_def {α β:Type*} {Pα:probability_space α} {Pβ:probability_space β} 
  (A:event Pα) (B:event Pβ):A.prod B = measurable_setB.prod A B := rfl


/- This proves that events are independent in the resulting probability space. -/
lemma prod.probability_space.apply_prod (α β:Type*) (Pα:probability_space α) (Pβ:probability_space β) (A:event Pα) (B:event Pβ):
  Pr[A.prod B] = Pr[A] * Pr[B] := begin
  rw ← ennreal.coe_eq_coe,
  rw ennreal.coe_mul,
  rw event_prob_def,
  rw event_prob_def,
  rw event_prob_def,
  simp,
  apply prod.measure_space.apply_prod,
  apply A.property,
  apply B.property,
end


/- Measurable functions from a product space to each multiplicand. -/

def rv_prod_fst {α β:Type*} (Pα:probability_space α) (Pβ:probability_space β):
(Pα.prod Pβ) →ᵣ Pα.to_measurable_space := mf_fst

def rv_prod_snd {α β:Type*} (Pα:probability_space α) (Pβ:probability_space β):
(Pα.prod Pβ) →ᵣ Pβ.to_measurable_space := mf_snd


/- Now that we have random variables mapping one probability space to another,
   we need to compose random variables. -/
def rv_compose_rv {α β γ:Type*} {Pα:probability_space α} {Pβ:probability_space β}
{Mγ:measurable_space γ} (X:Pβ →ᵣ Mγ) (Y:Pα →ᵣ Pβ.to_measurable_space):Pα →ᵣ Mγ := 
compose_measurable_fun X Y




noncomputable def random_variable.on_fst {α β γ:Type*} {Pα:probability_space α} {Mγ:measurable_space γ} 
(X:Pα →ᵣ Mγ) (Pβ:probability_space β) := rv_compose_rv X (rv_prod_fst Pα Pβ)

noncomputable def random_variable.on_snd {α β γ:Type*} {Pβ:probability_space β} {Mγ:measurable_space γ} 
(X:Pβ →ᵣ Mγ) (Pα:probability_space α) := rv_compose_rv X (rv_prod_snd Pα Pβ)


lemma Pr_rv_prod_fst_eq {α β:Type*} {Pα:probability_space α} 
  {Pβ:probability_space β} (A:event Pα):

  Pr[(rv_prod_fst Pα Pβ) ∈ᵣ A] = Pr[A] :=
begin
  have h_event_rw:(rv_prod_fst Pα Pβ ∈ᵣ A) = 
           A.prod event_univ,
  { apply event.eq, simp [rv_prod_fst, event_univ, event.prod], ext ω, simp,
    split; intros h_1; simp [h_1], }, 
  rw h_event_rw,
  rw prod.probability_space.apply_prod,
  simp [rv_prod_fst, mf_fst],
end

lemma Pr_rv_prod_snd_eq {α β:Type*} {Pα:probability_space α} 
  {Pβ:probability_space β} (B:event Pβ):
  Pr[(rv_prod_snd Pα Pβ) ∈ᵣ B] = Pr[B] :=
begin
  have h_event_rw:(rv_prod_snd Pα Pβ ∈ᵣ B) = 
           event_univ.prod B,
  { apply event.eq, simp [rv_prod_snd, event_univ, event.prod], ext ω, simp,
    split; intros h_1; simp [h_1], }, 
  rw h_event_rw,
  rw prod.probability_space.apply_prod,
  simp [rv_prod_fst, mf_fst],
end


lemma ind_rv_prod_fst_rv_prod_snd {α β:Type*} {Pα:probability_space α} 
  {Pβ:probability_space β}:
  random_variable_independent_pair (rv_prod_fst Pα Pβ) (rv_prod_snd Pα Pβ) :=
begin
  intros A B,
  let A':event Pα := A,
  let B':event Pβ := B,
  begin
    unfold independent_event_pair,
    have h_event_rw:(rv_prod_fst Pα Pβ ∈ᵣ A∧rv_prod_snd Pα Pβ ∈ᵣ B) = 
             A'.prod B',
    { apply event.eq, simp [rv_prod_fst, rv_prod_snd, A', B', event.prod], ext ω, simp },
    rw h_event_rw,
    rw Pr_rv_prod_fst_eq,
    rw Pr_rv_prod_snd_eq,
    rw prod.probability_space.apply_prod,
  end
end



lemma random_variable.on_fst_on_snd_ind {α β γ κ:Type*} {Pα:probability_space α} 
  {Pβ:probability_space β} {Mγ:measurable_space γ} {Mκ:measurable_space κ} 
{X:Pα →ᵣ Mγ} {Y:Pβ →ᵣ Mκ}:
  random_variable_independent_pair (X.on_fst Pβ) (Y.on_snd Pα) :=
begin
  simp [random_variable.on_fst, random_variable.on_snd, rv_compose_rv],
  apply compose_independent_pair_left,
  apply compose_independent_pair_right,
  apply ind_rv_prod_fst_rv_prod_snd,
end


/- Creates a pair of random variables that are independent and defined over the
   same probability space that are identical to the given random variables X and Y. -/
noncomputable def random_variable.pair_ind {α β γ κ:Type*} {Pα:probability_space α} 
  {Pβ:probability_space β} {Mγ:measurable_space γ} {Mκ:measurable_space κ} 
(X:Pα →ᵣ Mγ) (Y:Pβ →ᵣ Mκ):prod (Pα.prod Pβ →ᵣ Mγ) (Pα.prod Pβ →ᵣ Mκ) :=
   prod.mk (X.on_fst Pβ) (Y.on_snd Pα)

noncomputable def pi.measure_space {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} (M:∀ a, measure_theory.measure_space (β a)):
  measure_theory.measure_space (Π a, β a) :=
  @measure_theory.measure_space.mk (Π a, β a) (@measurable_space.pi α β (λ a, (M a).to_measurable_space)) (pi.measure (λ a, (M a).volume))

lemma pi.measure_space.apply {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} (M:∀ a, measure_theory.measure_space (β a)) (S:set (Π a, β a)):
  @measure_theory.measure_space.volume _ (pi.measure_space M) S =
  (pi.measure  (λ a, (M a).volume)) S := rfl 


lemma pi.measure_space.apply_prod {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} (M:∀ a, measure_theory.measure_space (β a)) {S:Π a, set (β a)}:
  (∀ a, measurable_set (S a)) →
  @measure_theory.measure_space.volume _ (pi.measure_space M) (set.pi set.univ S) =
  finset.univ.prod (λ a, @measure_theory.measure_space.volume _ (M a) (S a)) := begin
  intros h1,
  rw pi.measure_space.apply,
  rw pi.measure.apply_prod,
  apply h1,
end

lemma pi.measure_space.Inf_sum2 {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*} (M:Π (a:α), measure_theory.measure_space (β a)) {P:set (Π (a:α), β a)}:
  measurable_set P →
  @measure_theory.measure_space.volume _ (pi.measure_space M) P = 

  (⨅ (f:ℕ → (Π (a:α), set (β a))) (h₁:∀ n m, measurable_set (f n m))
  (h₃:P ⊆ ⋃ (n:ℕ), set.pi set.univ (f n)), 
  ∑' (n:ℕ), finset.univ.prod (λ (m:α), 
  @measure_theory.measure_space.volume _ (M m) (f n m))) := begin
  intros h1,
  rw pi.measure_space.apply,
  rw pi.measure_apply,
  rw pi.outer_measure.Inf_sum2,
  apply h1,
end


noncomputable def pi.probability_space {α:Type*} [F:fintype α] [N:nonempty α] {β:α → Type*}
   (P:Π a, probability_space (β a)):probability_space (Π a, β a) := 
  @probability_space.mk (Π a, β a) 
  (pi.measure_space (λ a, (P a).to_measure_space))
  begin
  simp,
  have A1:set.pi set.univ (λ a, @set.univ (β a)) = (@set.univ (Π a, β a)),
  { ext1 ω, split;intros A1_1; simp at A1_1, simp, },
  rw ← A1,
  rw pi.measure_space.apply_prod,
  simp,
  simp, 
end


def set.pi_event {α:Type*} {β:α → Type*} [F:fintype α] [N:nonempty α] 
  {P:Π a, probability_space (β a)}
  (T:set α) (E:Π a, event (P a)):event (pi.probability_space P) := T.pi_measurable E


lemma set.pi_event_univ {α:Type*} [F:fintype α] [N:nonempty α] 
{β:α → Type*} {P:Π a, probability_space (β a)}
(S:Π a, event (P a)) (T:set α) [decidable_pred T]:set.pi_event T S = set.pi_event 
(@set.univ α) (λ (a:α), if (a∈ T) then (S a) else (@event_univ (β a) (P a))) :=
begin
  apply set.pi_measurable_univ,
end


lemma pi.probability_space.apply_prod {α:Type*} {β:α → Type*} [F:fintype α] [N:nonempty α] 
  {P:Π a, probability_space (β a)}
  (E:Π a, event (P a)):Pr[set.pi_event set.univ E] = finset.univ.prod (λ a, Pr[E a]) := begin  
  rw ← ennreal.coe_eq_coe,
  rw ennreal.coe_finset_prod,
  simp [event_prob_def],
  apply pi.measure_space.apply_prod,
  intros a,
  apply (E a).property,
end

lemma pi.probability_space.apply_prod' {α:Type*} {β:α → Type*} [F:fintype α] [N:nonempty α] 
  {P:Π a, probability_space (β a)} {T:finset α}
  (E:Π a, event (P a)):Pr[set.pi_event (↑T) E] = T.prod (λ a, Pr[E a]) := begin
  classical,
  --have A1:=decidable.pred T,
  rw set.pi_event_univ,
  rw pi.probability_space.apply_prod,
  --rw @finset.prod_congr _ _ finset.univ finset.univ,
  
  have A2:finset.univ.prod (λ (a:α), if (a ∈ @coe (finset α) (set α) _ T) then Pr[E a] else 1) = 
          T.prod (λ (a:α), if (a ∈ @coe (finset α) (set α) _ T) then Pr[E a] else 1),
  { rw ← finset.prod_subset,
    { rw finset.subset_iff, intros x h_1, simp },
    intros x h_unused h_x_notin_T,
    rw if_neg,
    intros contra,
    apply h_x_notin_T,
    rw ← finset.mem_coe,
    apply contra },
  have A3:T.prod (λ (a:α), if (a ∈ @coe (finset α) (set α) _ T) then Pr[E a] else 1) =
          T.prod (λ (a:α), Pr[E a]),
  { apply finset.prod_congr,
    refl,
    intros x A3_1,
    rw if_pos,
    simp,
    apply A3_1 },
  rw ← A3,
  rw ← A2,
  apply finset.prod_congr,
  { refl },
  { intros x A4, 
    cases classical.em (x ∈ @coe (finset α) (set α) _ T) with A5 A5,
    rw if_pos A5,
    rw if_pos A5,
    rw if_neg A5,
    rw if_neg A5,
    simp },
end

def mf_pi {α:Type*} {β:α → Type*} (M:Π a, measurable_space (β a)) 
   (a:α):measurable_fun (@measurable_space.pi α β M) (M a) := @subtype.mk
  ((Π a, β a) → (β a))
  measurable
  (λ (d:Π a, β a), d a)
  begin
    apply measurable_pi_apply,
  end


def pi.rv {α:Type*} {β:α → Type*} [F:fintype α] [N:nonempty α] 
  (P:Π a, probability_space (β a)) (a:α):(pi.probability_space P) →ᵣ (P a).to_measurable_space := mf_pi (λ a, (P a).to_measurable_space) a

noncomputable def pi.random_variable_proj {α:Type*} {β:α → Type*} {γ:Type*} [F:fintype α] [N:nonempty α] 
  (P:Π a, probability_space (β a)) (a:α) {M:measurable_space γ} (X:(P a) →ᵣ (M)):(pi.probability_space P) →ᵣ M := X ∘r (pi.rv P a)

/- Unify a collection of random variables to be independent random variables under a single probability measure. -/
noncomputable def pi.random_variable {α:Type*} {β:α → Type*} {γ:α → Type*} [F:fintype α] [N:nonempty α] 
  {P:Π a, probability_space (β a)} {M:Π a, measurable_space (γ a)} (X:Π a, (P a) →ᵣ (M a)):Π a, (pi.probability_space P) →ᵣ (M a) := (λ a, pi.random_variable_proj P a (X a))

lemma pi.rv_eq {α:Type*} {β:α → Type*} [F:fintype α] [N:nonempty α] 
  (P:Π a, probability_space (β a)) (a:α) (E:event (P a)):
  Pr[(pi.rv P a)∈ᵣ E] = Pr[E] := begin
  classical,
  have A1:∀ (a':α), ∃ (E':event (P a')), Π (h:a=a'),E = @cast (event (P a')) 
    (event (P a)) begin rw h end E',  
  { intros a', cases classical.em (a=a') with A1_1 A1_1,
    { subst a', apply exists.intro E, intros h, refl },
    { apply exists.intro (@event_univ (β a') (P a')),
      intros h, exfalso, apply A1_1, apply h } },
  have A2 := classical.axiom_of_choice A1,
  cases A2 with E' A2,
  have A4:a=a := rfl,
  have A5 := A2 a A4,
  have A3:(set.pi_event (@coe (finset α) (set α) _ {a}) E') = ((pi.rv P a)∈ᵣ E),
  { apply event.eq,
    ext ω,
    simp [set.pi_event,pi.rv,set.pi_measurable,mf_pi],
    subst E,
    refl, 
     },
  rw ← A3,
  rw pi.probability_space.apply_prod',
  simp,
  subst E,
  refl,
end

lemma pi.random_variable_proj_identical {α:Type*} {β:α → Type*} {γ:Type*} [F:fintype α] [N:nonempty α] 
  (P:Π a, probability_space (β a)) (a:α) {M:measurable_space γ} (X:(P a) →ᵣ (M)):
  random_variable_identical (pi.random_variable_proj P a X) X :=
begin
  intros S,
  simp [pi.random_variable_proj],
  rw rv_compose_measurable_setB,
  apply pi.rv_eq,
end

--(pi.probability_space P) →ᵣ M := X ∘r (pi.rv P a)



lemma pi.rv_independent {α:Type*} {β:α → Type*} [F:fintype α] [N:nonempty α] 
  (P:Π a, probability_space (β a)):
  random_variable_independent (pi.rv P) :=
begin
  classical,
  intros S,
  intros T,
  have h1:(∀ᵣ (s : α) in T,(λ (b : α), @pi.rv α (λ (a : α), β a) F N P b ∈ᵣ S b) s) =
          set.pi_event (↑T) S,
  { apply event.eq,
    ext1 ω,
    simp [set.pi_event, set.pi_measurable, pi.rv, mf_pi] },
  rw h1,
  rw pi.probability_space.apply_prod',
  apply finset.prod_congr,
  refl,
  intros x A1,
  rw pi.rv_eq,
end

lemma pi.random_variable_independent {α:Type*} {β:α → Type*} {γ:α → Type*} [F:fintype α] 
  [N:nonempty α] (P:Π a, probability_space (β a)) {M:Π a, measurable_space (γ a)} 
  (X:Π a, (P a) →ᵣ (M a)):
  random_variable_independent (pi.random_variable X) :=
begin
  simp [pi.random_variable, pi.random_variable_proj, rv_compose_rv],
  apply compose_independent',
  apply pi.rv_independent,
end

noncomputable def pi.random_variable_IID {β γ:Type*} {P:probability_space β} 
  {M:measurable_space γ} (X:P →ᵣ M) (m:nat):(fin m.succ) → 
  (pi.probability_space (λ (m:fin m.succ), P) →ᵣ M)

 := 
@pi.random_variable (fin m.succ) (λ (a:fin m.succ), β) 
  (λ (a:fin m.succ), γ) _  _ 
  (λ a, P) (λ a, M) (λ a, X) 


lemma pi.random_variable_IID_independent {β γ:Type*} {P:probability_space β} 
  {M:measurable_space γ} (X:P →ᵣ M) (m:nat):
  random_variable_independent (pi.random_variable_IID X m) := begin
  simp [random_variable_independent],
  apply pi.random_variable_independent,
end


lemma pi.random_variable_IID_identical {β γ:Type*} {P:probability_space β} 
  {M:measurable_space γ} (X:P →ᵣ M) (m:nat) (i:fin m.succ):
  random_variable_identical (pi.random_variable_IID X m i) 
  X := begin
  simp [pi.random_variable_IID, pi.random_variable],
  apply pi.random_variable_proj_identical,
end

lemma pi.random_variable_IID_identical' {β γ:Type*} {P:probability_space β} 
  {M:measurable_space γ} (X:P →ᵣ M) (m:nat) (i j:fin m.succ):
  random_variable_identical (pi.random_variable_IID X m i) 
  (pi.random_variable_IID X m j) := begin
  apply random_variable_identical.trans,
  apply pi.random_variable_IID_identical,
  apply random_variable_identical.symm,
  apply pi.random_variable_IID_identical,
end

lemma pi.random_variable_IID_IID {β γ:Type*} {P:probability_space β} 
  {M:measurable_space γ} (X:P →ᵣ M) (m:nat):
  random_variables_IID (pi.random_variable_IID X m) := begin
  simp [random_variables_IID],
  split,
  apply pi.random_variable_IID_independent,
  intros i j,
  apply pi.random_variable_IID_identical',
end

/- Pair a random variable with a collection of random variables.
   Since the collection of random variables already share a probability
   measure, we make sure that the resulting random variables
   share the product measure of Pα and Pβ. -/
noncomputable def random_variable.pair_collection {α β γ κ δ:Type*}  
  {Pα:probability_space α} 
  {Pβ:probability_space β} {Mγ:measurable_space γ} {Mκ:measurable_space κ} 
(X:δ → Pα →ᵣ Mγ) (Y:Pβ →ᵣ Mκ):prod (δ → Pα.prod Pβ →ᵣ Mγ) (Pα.prod Pβ →ᵣ Mκ) :=
   prod.mk (λ (d:δ), (X d).on_fst Pβ) (Y.on_snd Pα)



