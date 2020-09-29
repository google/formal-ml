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
import measure_theory.set_integral
import measure_theory.borel_space
import data.set.countable
import formal_ml.nnreal
import formal_ml.sum
import formal_ml.core
import formal_ml.measurable_space
import formal_ml.semiring
import formal_ml.real_measurable_space
import formal_ml.set
import formal_ml.filter_util
import topology.instances.ennreal
import formal_ml.int

/-
  The simple way to think about a continuous random variable is as a
  continuous function (a density function). Formally, this is the Radon-Nikodym derivative.
  Using the operation with_density, one can transform this Radon-Nikodym derivative into
  a measure using measure_theory.with_density, which is provided in measure_theory.integration
  in mathlib. Specifically, one can write:
  μ.with_density f
  where μ is normally the Lebesgue measure on the real number line, and generate a probability
  measure for a continuous density function.

  In this file,
  measure_theory.with_density.compose_eq_multiply connects the integration (or expectation) of 
  a function with respect to the probability measure derived from the density function with the
  integral using the original base measure. So, if μ is again the base measure, f is the density
  function, and g is the function we want to take the expectation of, then:
  (μ.with_density f).integral g = μ.integral (f * g)

  This is the familiar connection that we use to integrate functions of real random variables on
  a regular basis.
 -/




---Revisit these finite measure proofs: make sure that they are not replicated in mathlib.
def measure_theory.finite_measure_of_lt_top {Ω:Type*} [M:measurable_space Ω] 
  {μ:measure_theory.measure Ω} (H:μ set.univ < ⊤):
  measure_theory.finite_measure μ := {
    measure_univ_lt_top := H,
}

def measure_theory.finite_measure_of_le {Ω:Type*} [M:measurable_space Ω] 
  (μ ν:measure_theory.measure Ω) [measure_theory.finite_measure ν] (H:μ ≤ ν):
  measure_theory.finite_measure μ :=
begin
  have B1:μ set.univ ≤ ν set.univ,
  {
    apply H,
    simp,
  },
  have B2:μ set.univ < ⊤,
  {
    apply lt_of_le_of_lt B1,
    apply measure_theory.measure_lt_top,
  },
  apply measure_theory.finite_measure_of_lt_top B2,
end 

def measure_theory.finite_measure_restrict {Ω:Type*} [M:measurable_space Ω] 
  (μ:measure_theory.measure Ω) [measure_theory.finite_measure μ] (S:set Ω):
  measure_theory.finite_measure (μ.restrict S) :=
begin
  have A1:= @measure_theory.measure.restrict_le_self Ω M μ S,
  apply measure_theory.finite_measure_of_le (μ.restrict S) μ A1,
end

------------------------Core theorems---------------------------------------


--This seems to be legitimately new.
lemma  lt_iff_le_not_eq {α:Type*} [linear_order α] {a b:α}:
    (a < b) ↔ ((a ≤ b) ∧  (a ≠ b)) :=
begin
  split;intros A1,
  {
    split,
    {
      apply le_of_lt A1,
    },
    {
      apply ne_of_lt A1,
    },
  },
  {
    rw lt_iff_le_not_le,
    split,
    {
      apply A1.left,
    },
    {
      intro A2,
      apply A1.right,
      apply  le_antisymm,
      apply A1.left,
      apply A2,
    },
  },
end




------------------------Theorems of complete lattices ----------------------

lemma Sup_image_le {α β:Type*} [complete_lattice β] {f:α → β} {S:set α} {x:β}:
  (∀ s∈ S, f s ≤ x) → (Sup (f '' S)≤ x) :=
begin
  intro A1,
  apply Sup_le,
  intros b A2,
  cases A2 with a A2,
  rw ← A2.right,
  apply (A1 a A2.left),
end

lemma le_Sup_image {α β:Type*} [complete_lattice β] {f:α → β} {S:set α} {a:α}:
  (a∈ S) →
  (f a) ≤ Sup (f '' S) :=
begin
  intro A1,
  apply le_Sup,
  simp,
  apply exists.intro a,
  split,
  apply A1,
  refl,
end

lemma Sup_Sup_image_image_le {α β γ:Type*} [complete_lattice γ] {f:α → β → γ} {S:set α}
    {T:set β} {x:γ}:
    (∀ a∈ S, ∀ b∈T, f a b ≤ x) →
    (Sup ((λ a:α, Sup  ((f a) '' T)) '' S) ≤ x) :=
begin
  intro A1,
  apply Sup_image_le,
  intros a A2,
  apply Sup_image_le,
  intros b A3,
  apply A1 a A2 b A3,
end

lemma le_Sup_Sup_image_image {α β γ:Type*} [complete_lattice γ] {f:α → β → γ} 
    {S:set α} {T:set β} {a:α} {b:β}:
    (a∈ S) → (b∈ T) → 
    (f a b) ≤ (Sup ((λ a:α, Sup  ((f a) '' T)) '' S)) :=
begin
  intros A1 A2,
  apply le_trans,
  apply @le_Sup_image β γ _ (f a) T b A2,
  apply @le_Sup_image α γ _ ((λ a:α, Sup  ((f a) '' T))) S a A1,
end

lemma Sup_le_Sup_of_monotone {α β:Type*} [complete_lattice α]
    [complete_lattice β] 
    {f:α → β} {s:set α}:
   (monotone f) →
    Sup (f '' s) ≤ f (Sup s) :=
begin
  intro A1,
  apply Sup_le,
  intros b A2,
  simp at A2,
  cases A2 with x A2,
  cases A2 with A2 A3,
  subst b,
  apply A1,
  apply le_Sup,
  apply A2,
end

lemma supr_le_supr_of_monotone {α β γ:Type*} [complete_lattice α]
    [complete_lattice β] 
    {f:α → β} {g:γ → α}:
   (monotone f) →
    supr (f ∘ g) ≤ f (supr g) :=
begin
  intro A1,
  apply Sup_le,
  intros b A2,
  simp at A2,
  cases A2 with x A2,
  subst b,
  apply A1,
  apply le_Sup,
  simp,
end

lemma infi_le_infi_of_monotone {α β γ:Type*} [complete_lattice α]
    [complete_lattice β] 
    {f:α → β} {g:γ → α}:
   (monotone f) →
     f (infi g) ≤ infi (f ∘ g) :=
begin
  intro A1,
  apply le_infi,
  intros b,
  apply A1,
  apply infi_le,
end

lemma Inf_le_Inf_of_monotone {α β:Type*} [complete_lattice α]
    [complete_lattice β] 
    {f:α → β} {s:set α}:
   (monotone f) →
     f (Inf s) ≤ Inf (f '' s) :=
begin
  intro A1,
  apply le_Inf,
  intros b A2,
  simp at A2,
  cases A2 with b' A2,
  cases A2 with A2 A3,
  subst b,
  apply A1,
  apply Inf_le,
  apply A2,
end


lemma supr_prop_def {α:Type*} [complete_lattice α]
    {v:α} {P:Prop} (H:P):(⨆ (H2:P), v) = v :=
begin
  apply le_antisymm,
  {
    apply supr_le,
    intro A1,
    apply le_refl v,
  },
  {
    apply @le_supr α P _ (λ H2:P, v),
    apply H,
  },
end

lemma infi_prop_def {α:Type*} [complete_lattice α]
    {v:α} {P:Prop} (H:P):(⨅ (H2:P), v) = v :=
begin
  apply le_antisymm,
  {
    apply infi_le,
    apply H,
  },
  {
    apply @le_infi,
    intro A1,
    apply le_refl v,
  },
end


lemma supr_prop_false {α:Type*} [complete_lattice α]
    {v:α} {P:Prop} (H:¬P):(⨆ (H2:P), v) = ⊥ :=
begin
  apply le_antisymm,
  {
    apply supr_le,
    intro A1,
    exfalso,
    apply H,
    apply A1,
  },
  {
    apply bot_le,
  },
end

lemma infi_prop_false {α:Type*} [complete_lattice α]
    {v:α} {P:Prop} (H:¬P):(⨅ (H2:P), v) = ⊤ :=
begin
  apply le_antisymm,
  {
    apply le_top,
  },
  {
    apply le_infi,
    intro A1,
    exfalso,
    apply H,
    apply A1,
  },
end


------------------------Theorems of int-----------------------------------------------

def monoid_hom_nat_int:monoid_hom nat int := {
  to_fun := int.of_nat,
  map_mul' := begin
    intros x y,
    simp,
  end,
  map_one' := rfl,
}

def add_monoid_hom_nat_int:add_monoid_hom nat int := {
  to_fun := int.of_nat,
  map_add' := begin
    intros x y,
    simp,
  end,
  map_zero' := rfl,
}


def ring_hom_nat_int:ring_hom nat int := {
  ..monoid_hom_nat_int,
  ..add_monoid_hom_nat_int,
}

lemma ring_hom_nat_int_to_fun_def {n:ℕ}:
    ring_hom_nat_int.to_fun n = n := rfl

lemma int.coe_nat_eq_coe_nat {a b:ℕ}:(a:ℤ) = (b:ℤ) ↔ a = b :=
begin
 
  split;intros A1,
  {
    simp at A1,
    apply A1,
  },
  {
    simp,
    apply A1,
  },
end

lemma ring_hom_nat_int_eq {a b:ℕ}:(ring_hom_nat_int.to_fun a)=(ring_hom_nat_int.to_fun b) ↔ a = b :=
begin
  repeat {rw ring_hom_nat_int_to_fun_def},
  rw int.coe_nat_eq_coe_nat,
end


------------------------Theorems of rat ----------------------------------------------


lemma rat.nonpos_of_num_nonpos {q:ℚ}:q.num ≤ 0 → q ≤ 0  :=
begin
  intro A1,
  have A3:(0:ℤ) < (((0:rat).denom):ℤ),
  {
    simp,
    apply (0:rat).pos,     
  },
  rw ← @rat.num_denom q,
  rw ← @rat.num_denom 0,
  rw rat.le_def,
  simp,
  have A4:(0:ℤ) < (((q:rat).denom):ℤ),
  {
    simp,
    apply (q:rat).pos,     
  },
  apply mul_nonpos_of_nonpos_of_nonneg,
  apply A1,
  apply le_of_lt,
  apply A3,
  {
    simp,
    apply q.pos,
  },
  apply A3,    
end


lemma rat.num_nonneg_of_nonneg {q:ℚ}:q≤ 0 → q.num ≤ 0 :=
begin
  intro A1,
  have A3:(0:ℤ) < (((0:rat).denom):ℤ),
  {
    simp,
    apply (0:rat).pos,     
  },
  have A4:(0:ℤ) < (((q:rat).denom):ℤ),
  {
    simp,
    apply (q:rat).pos,     
  },  
  rw ← @rat.num_denom q at A1,
  rw ← @rat.num_denom 0 at A1,
  rw rat.le_def at A1,
  simp at A1,
  apply nonpos_of_mul_nonpos_right A1 A3,
  apply A4,
  apply A3,
end


lemma rat.nonpos_iff_num_nonpos {q:ℚ}:q.num ≤ 0 ↔ q ≤ 0  :=
begin
  have A3:(0:ℤ) < (((0:rat).denom):ℤ),
  {
    simp,
    apply (0:rat).pos,     
  },
  have A4:(0:ℤ) < (((q:rat).denom):ℤ),
  {
    simp,
    apply (q:rat).pos,     
  },

  rw ← @rat.num_denom q,
  rw ← @rat.num_denom 0,
  rw rat.le_def,
  simp,
  split;intros A1,
  {
    apply mul_nonpos_of_nonpos_of_nonneg,
    apply A1,
    apply le_of_lt,
    apply A3,
  },
  {
    have B1:(0:ℤ) * ↑((0:ℚ).denom) = (0:ℤ) := zero_mul _,
    rw ← B1 at A1,
    apply le_of_mul_le_mul_right,
    apply A1,
    apply A3,
  },
  apply A4,
  apply A3,
end

lemma rat.num_pos_of_pos {q:ℚ}:0 < q → 0 < q.num :=
begin
  intro A1,
  apply lt_of_not_ge,
  rw lt_iff_not_ge at A1,
  intro A2,
  apply A1,
  apply rat.nonpos_of_num_nonpos A2,
end

lemma rat.pos_iff_num_pos {q:ℚ}:0 < q ↔ 0 < q.num :=
begin
  split;intro A1,
  {
    apply lt_of_not_ge,
    rw lt_iff_not_ge at A1,
    intro A2,
    apply A1,
    apply rat.nonpos_of_num_nonpos A2,
  },
  {
    apply lt_of_not_ge,
    rw lt_iff_not_ge at A1,
    intro A2,
    apply A1,
    apply rat.num_nonneg_of_nonneg A2,
  },
end



def monoid_hom_int_rat:monoid_hom int rat := {
  to_fun := rat.of_int,
  map_mul' := begin
    intros x y,
    repeat {rw rat.of_int_eq_mk},
    rw rat.mul_def one_ne_zero one_ne_zero,
    simp,
  end,
  map_one' := rfl,
}

def add_monoid_hom_int_rat:add_monoid_hom int rat := {
  to_fun := rat.of_int,
  map_add' := begin
    intros x y,
    repeat {rw rat.of_int_eq_mk},
    rw rat.add_def one_ne_zero one_ne_zero,
    simp,
  end,
  map_zero' := rfl,
}


def ring_hom_int_rat:ring_hom int rat := {
  ..monoid_hom_int_rat,
  ..add_monoid_hom_int_rat,
}

lemma ring_hom_int_rat_to_fun_def {n:ℤ}:
    ring_hom_int_rat.to_fun n = rat.of_int n := rfl


lemma ring_hom_int_rat_to_fun_def2 {n:ℤ}:
    ring_hom_int_rat.to_fun n = n :=
begin
  rw rat.coe_int_eq_of_int,
  rw ring_hom_int_rat_to_fun_def,
end


lemma ring_hom_int_rat_eq {a b:ℤ}:(ring_hom_int_rat.to_fun a)=(ring_hom_int_rat.to_fun b) ↔ (a = b) :=
begin
  repeat {rw ring_hom_int_rat_to_fun_def2},
  simp,
end




def ring_hom_nat_rat:=
  ring_hom.comp ring_hom_int_rat ring_hom_nat_int




lemma ring_hom_nat_rat_to_fun_def {n:ℕ}:
    ring_hom_nat_rat.to_fun n = ring_hom_int_rat.to_fun ( ring_hom_nat_int.to_fun n) :=
begin
  refl,
end

lemma ring_hom_nat_rat_to_fun_def2 {n:ℕ}:
    ring_hom_nat_rat.to_fun n = n :=
begin
  rw ring_hom_nat_rat_to_fun_def,
  rw ring_hom_nat_int_to_fun_def,
  rw ring_hom_int_rat_to_fun_def2,
  simp,
end


lemma ring_hom_nat_rat_eq {a b:ℕ}:(ring_hom_nat_rat.to_fun a)=(ring_hom_nat_rat.to_fun b) ↔ a = b :=
begin
  repeat {rw ring_hom_nat_rat_to_fun_def},
  rw ring_hom_int_rat_eq,
  rw ring_hom_nat_int_eq,
end


lemma rat.exists_unit_frac_le_pos {q:ℚ}:0 < q → (∃ n:ℕ, (1/((n:rat) + 1)) ≤ q) := 
begin
  intro A1,
  have A3 := @rat.num_denom q,
  rw ← A3,
  
  apply exists.intro (q.denom.pred),
  
  have A2:(((nat.pred q.denom):rat) + 1) = q.denom,
  {
    have A2A:((@has_one.one ℕ _):ℚ) = 1 := rfl,
    rw ← A2A,
    repeat {rw ← ring_hom_nat_rat_to_fun_def2},
    rw ← ring_hom_nat_rat.map_add',
    rw ring_hom_nat_rat_eq,
    have A2B:nat.pred q.denom + 1 = nat.succ (nat.pred q.denom) := rfl,
    rw A2B,
    rw nat.succ_pred_eq_of_pos,
    apply q.pos,
  },
  rw A2,
  have A3:(1/(q.denom:rat))= rat.mk 1 q.denom,
  {
    have A3A:((1:nat):rat) = 1 := rfl,
    have A3B:((1:ℤ):rat)/((q.denom:ℤ):rat)=1/(q.denom:rat),
    {
      refl,
    },
    rw ← A3B,
    rw ← rat.mk_eq_div,
  },
  rw A3,
  rw rat.le_def,
  {
    simp,
    rw le_mul_iff_one_le_left,
    apply rat.num_pos_of_pos A1,
    simp,
    apply q.pos,
  },
  repeat {
    simp,
    apply q.pos,
  },
end

lemma rat.mk_pos_denom {p:ℤ} {n:pnat}:(rat.mk p (n:ℤ))=
  rat.mk_pnat p n :=
begin
  cases n,
  rw rat.mk_pnat_eq,
  simp,
end


lemma rat.pos_mk {p q:ℤ}:(0 < p) → (1 ≤ q) → 
  0 < (rat.mk p q) :=
begin
  intros A1 A2,
  cases q,
  {
    cases q,
    {
      -- q cannot be zero.
      exfalso,
      simp at A2,
      apply not_lt_of_le A2,
      apply zero_lt_one,
    },
    let n := q.succ_pnat,
    begin
      have B1:(n:ℤ) = int.of_nat q.succ := rfl,
      rw ← B1,
      rw rat.mk_pos_denom,
      rw ← rat.num_pos_iff_pos,
      rw rat.mk_pnat_num,
      simp,
      cases p,
      {
        simp, 
        rw ← int.coe_nat_div,
        have B2:((0:ℕ):ℤ) = (0:ℤ) := rfl,
        rw ← B2,
        rw int.coe_nat_lt, 
        apply nat.div_pos,
        apply nat.gcd_le_left,
        simp at A1,
        apply A1,
        apply nat.gcd_pos_of_pos_right,
        simp,
      },
      {
        -- p cannot be negative.
        exfalso,
        apply not_le_of_lt A1,
        apply le_of_lt,
        apply int.neg_succ_of_nat_lt_zero p,
      },
    end 
  },
  -- q cannot be negative.
  rw ← rat.num_pos_iff_pos,
  unfold rat.mk,
  {
    exfalso,
    apply not_le_of_lt (int.neg_succ_of_nat_lt_zero q),
    apply le_of_lt,
    apply lt_of_lt_of_le,
    apply zero_lt_one,
    apply A2,
  },
end

------------------------Theorems of real ---------------------------------------------

lemma real.add_sub_add_eq_sub_add_sub {a b c d:real}:
    a + b - (c + d) = (a - c) + (b - d) :=
begin
  linarith,
end

lemma real.unit_frac_pos (n:ℕ):0 < (1/((n:real) + 1)) :=
begin
  simp,
  -- ⊢ 0 < ↑n + 1
  rw add_comm,
  apply add_pos_of_pos_of_nonneg,
  {
    apply zero_lt_one,
  },
  {
    simp,
  },
end


--TODO:Unlikely to be novel.
--Solvable by linarith.
lemma real.sub_lt_sub_of_lt {a b c:real}:a < b →
  a - c < b - c :=
begin
  simp,
end

lemma real.rat_le_rat_iff {q r:ℚ}:q ≤ r ↔ (q:ℝ) ≤  (r:ℝ) := 
begin
  rw ← real.of_rat_eq_cast,
  rw ← real.of_rat_eq_cast,
  rw le_iff_lt_or_eq,
  rw le_iff_lt_or_eq,
  split;intros A3;cases A3,
  {
    left,
    rw real.of_rat_lt,
    apply A3,
  },
  {
    right,
    simp,
    apply A3,
  },
  {
    left,
    rw ← real.of_rat_lt,  
    apply A3,
  },
  {
    right,
    simp at A3,
    apply A3,
  },
end

lemma real.eq_add_of_sub_eq {a b c:real}:
  a - b = c → a = b + c :=
begin
  intros A1,
  linarith [A1],
end


lemma real.sub_add_sub {a b c:real}:(a - b) + (b - c) = a - c := by linarith


------------------------Theorems of nnreal --------------------------------------------

lemma nnreal.not_add_le_of_lt {a b:nnreal}:
   (0 < b) → ¬(a + b) ≤ a :=
begin
  intros A1 A2,
  simp at A2,
  subst A2,
  apply lt_irrefl _ A1,
end

lemma nnreal.sub_lt_of_pos_of_pos {a b:nnreal}:(0 < a) → 
    (0 < b) → (a - b) < a :=
begin
  intros A1 A2,
  cases (le_total a b) with A3 A3,
  {
    rw nnreal.sub_eq_zero A3,
    apply A1,
  },
  {
    rw ← nnreal.coe_lt_coe,
    rw nnreal.coe_sub A3,
    rw ← nnreal.coe_lt_coe at A2,
    rw sub_lt_self_iff,
    apply A2,
  }
end

lemma nnreal.add_sub_add_eq_sub_add_sub {a b c d:nnreal}:c ≤ a → d ≤ b →
    a + b - (c + d) = (a - c) + (b - d) :=
begin
  intros A1 A2,
  have A3:c + d ≤ a + b,
  {
    apply add_le_add A1 A2,
  },
  rw ← nnreal.eq_iff,
  rw nnreal.coe_sub A3,
  rw nnreal.coe_add,
  rw nnreal.coe_add,
  rw nnreal.coe_add,
  rw nnreal.coe_sub A1,
  rw nnreal.coe_sub A2,
  apply real.add_sub_add_eq_sub_add_sub,
end

lemma nnreal.sub_eq_of_add_of_le {a b c:nnreal}:a = b + c →
  c ≤ a → a - c = b :=
begin
  intros A1 A2,
  have A3:a - c + c = b + c,
  {
    rw nnreal.sub_add_cancel_of_le A2,
    apply A1,  
  },
  apply add_right_cancel A3,
end

lemma nnreal.inverse_le_of_le {a b:nnreal}:
  0 < a →
  a ≤ b →
  b⁻¹ ≤ a⁻¹ :=
begin
  intros A1 A2, 
  have B1: (a⁻¹ * b⁻¹) * a ≤  (a⁻¹ * b⁻¹) * b,
  {
    apply mul_le_mul,
    apply le_refl _,
    apply A2,
    simp,
    simp,
  },
  rw mul_comm a⁻¹  b⁻¹ at B1,
  rw mul_assoc at B1,
  rw inv_mul_cancel at B1,
  rw mul_comm b⁻¹  a⁻¹ at B1,
  rw mul_assoc at B1,
  rw mul_one at B1,
  rw inv_mul_cancel at B1,
  rw mul_one at B1,
  apply B1,
  {
    have B1A := lt_of_lt_of_le A1 A2,
    intro B1B,
    subst b,
    simp at B1A,
    apply B1A,
  },
  {
    intro C1,
    subst a,
    simp at A1,
    apply A1,
  },
end

lemma nnreal.unit_frac_pos (n:ℕ):0 < (1/((n:nnreal) + 1)) :=
begin
  apply nnreal.div_pos,
  apply zero_lt_one,
  have A1:(0:nnreal) < (0:nnreal) + (1:nnreal),
  {
    simp,
    apply zero_lt_one,
  },
  apply lt_of_lt_of_le A1,
  rw add_comm (0:nnreal) 1,
  rw add_comm _ (1:nnreal),
  apply add_le_add_left,
  simp,
end


lemma nnreal.real_le_real {q r:ℝ}:q ≤ r → (nnreal.of_real q ≤ nnreal.of_real r) :=
begin
  intro A1,
  cases (le_total 0 q) with A2 A2,
  {
    have A3 := le_trans A2 A1,
    rw ←  @nnreal.coe_le_coe,
    rw nnreal.coe_of_real q A2,
    rw nnreal.coe_of_real r A3,
    apply A1,
  },
  {
    have B1 := nnreal.of_real_of_nonpos A2,
    rw B1,
    simp,
  },
end


lemma nnreal.rat_le_rat {q r:ℚ}:q ≤ r → (nnreal.of_real q ≤ nnreal.of_real r) :=
begin
  rw real.rat_le_rat_iff,
  apply nnreal.real_le_real,
end


lemma nnreal.real_lt_nnreal_of_real_le_real_of_real_lt_nnreal {q r:real} {s:nnreal}:
  q ≤ r → (nnreal.of_real r) < s → (nnreal.of_real q) < s :=
begin
  intros A1 A2,
  apply lt_of_le_of_lt _ A2,
  apply nnreal.real_le_real,
  apply A1,
end


lemma nnreal.rat_lt_nnreal_of_rat_le_rat_of_rat_lt_nnreal {q r:ℚ} {s:nnreal}:
  q ≤ r → (nnreal.of_real r) < s → (nnreal.of_real q) < s :=
begin
  
  intros A1 A2,
  rw real.rat_le_rat_iff at A1,
  apply nnreal.real_lt_nnreal_of_real_le_real_of_real_lt_nnreal A1 A2,
end


lemma nnreal.of_real_inv_eq_inv_of_real {x:real}:(0 ≤ x) →
    nnreal.of_real x⁻¹ = (nnreal.of_real x)⁻¹ :=
begin
  intro A1,
  rw ← nnreal.eq_iff,
  simp,
  have A2:0 ≤ x⁻¹,
  {
    apply inv_nonneg.2 A1,
  },
  rw nnreal.coe_of_real x A1,
  rw nnreal.coe_of_real _ A2,
end



lemma nnreal.one_div_eq_inv {x:nnreal}:1/x = x⁻¹ := 
begin
  rw nnreal.div_def,
  rw one_mul,
end

lemma nnreal.exists_unit_frac_lt_pos {ε:nnreal}:0 < ε → (∃ n:ℕ, (1/((n:nnreal) + 1)) < ε) :=
begin
  intro A1,
  have A2 := A1,
  rw nnreal.lt_iff_exists_rat_btwn at A2,
  cases A2 with q A2,
  cases A2 with A2 A3,
  cases A3 with A3 A4,
  simp at A3,
  have A5 := rat.exists_unit_frac_le_pos A3,
  cases A5 with n A5,
  apply exists.intro n,
  simp at A5,
  rw nnreal.one_div_eq_inv,
  have B2:(0:ℝ) ≤ 1,
  {
    apply le_of_lt,
    apply zero_lt_one,
  },
  have A7:nnreal.of_real 1 = (1:nnreal),
  {
    rw ← nnreal.coe_eq,
    rw nnreal.coe_of_real,
    rw nnreal.coe_one,
    apply B2,
  },
  rw ← A7,
  have A8:nnreal.of_real n = n,
  {
    rw ← nnreal.coe_eq,
    rw nnreal.coe_of_real,
    simp, 
    simp,
  },
  rw ← A8,
  have B1:(0:ℝ) ≤ n,
  {
    simp,  
  },
  have B3:(0:ℝ) ≤ n + (1:ℝ),
  {
    apply le_trans B1,
    simp,
    apply B2
  },

  rw ← nnreal.of_real_add B1 B2,
  rw ← nnreal.of_real_inv_eq_inv_of_real B3,
  have A9 := nnreal.rat_le_rat A5,
  have A10:((n:ℝ) + 1)⁻¹ = (↑((n:ℚ) + 1)⁻¹:ℝ),
  {
    simp,
  },
  rw A10,
  apply lt_of_le_of_lt A9 A4,
end

lemma nnreal.of_real_div {x y:real}:0 ≤ x → 0 ≤ y →
    nnreal.of_real (x / y) =
    nnreal.of_real x / nnreal.of_real y :=
begin
  intros A1 A2,
  rw ← nnreal.coe_eq,
  rw nnreal.coe_of_real,
  simp,
  repeat {rw nnreal.coe_of_real},
  apply A2,
  apply A1,
  apply div_nonneg A1 A2,
end


lemma nnreal.of_real_eq_coe_nat {n:ℕ}:nnreal.of_real n = n :=
begin
  rw ← nnreal.coe_eq,
  rw nnreal.coe_of_real,
  repeat {simp},
end

lemma nnreal.sub_le_sub_of_le {a b c:nnreal}:b ≤ a →
  c - a ≤ c - b :=
begin
  intro A1,
  cases (classical.em (a ≤ c)) with B1 B1,
  {
    rw ← nnreal.coe_le_coe,
    rw nnreal.coe_sub B1,
    have B2:=le_trans A1 B1,
    rw nnreal.coe_sub B2,
    simp,
    rw nnreal.coe_le_coe,
    apply A1,
  },
  {
    simp at B1,
    have C1:= le_of_lt B1,
    rw nnreal.sub_eq_zero C1,
    simp
  },
end


--Replace c < b with c ≤ a.
lemma nnreal.sub_lt_sub_of_lt_of_lt {a b c:nnreal}:a < b →
  c ≤ a →
  a - c < b - c :=
begin
  intros A1 A2,
  rw ← nnreal.coe_lt_coe, 
  rw nnreal.coe_sub A2,
  have B1:=lt_of_le_of_lt A2 A1,
  have B2 := le_of_lt B1,
  rw nnreal.coe_sub B2,
  apply real.sub_lt_sub_of_lt,
  rw nnreal.coe_lt_coe,
  apply A1,
end


lemma nnreal.sub_lt_sub_of_lt_of_le {a b c d:nnreal}:a < b →
  c ≤ d →
  d ≤ a →
  a - d < b - c :=
begin
  intros A1 A2 A3,
  have A3:a - d < b - d,
  {
    apply nnreal.sub_lt_sub_of_lt_of_lt A1 A3,
  },
  apply lt_of_lt_of_le A3,
  apply nnreal.sub_le_sub_of_le A2,
end

lemma nnreal.eq_add_of_sub_eq {a b c:nnreal}:b ≤ a →
  a - b = c → a = b + c :=
begin
  intros A1 A2,
  apply nnreal.eq,
  rw  nnreal.coe_add,
  rw ← nnreal.eq_iff at A2,
  rw  nnreal.coe_sub A1 at A2,
  apply real.eq_add_of_sub_eq A2,
end


lemma nnreal.sub_add_sub {a b c:nnreal}:c ≤ b → b ≤ a → (a - b) + (b - c) = a - c :=
begin
  intros A1 A2,
  rw ← nnreal.coe_eq,
  rw nnreal.coe_add,
  repeat {rw nnreal.coe_sub},
  apply real.sub_add_sub,
  apply le_trans A1 A2,
  apply A1,
  apply A2,
end



------------------------Theorems of ennreal -------------------------------------------


lemma le_coe_ne_top {x:nnreal} {y:ennreal}:y≤(x:ennreal) → y≠ ⊤ :=
begin
  intro A1,
  have A2:(x:ennreal)< ⊤,
  {
    apply with_top.coe_lt_top,
  },
  have A3:y < ⊤,
  {
    apply lt_of_le_of_lt,
    apply A1,
    apply A2,
  },
  rw ← lt_top_iff_ne_top,
  apply A3,
end 

--Unnecessary
lemma upper_bounds_nnreal (s : set ennreal) {x:nnreal} {y:ennreal}: 
  (x:ennreal) ∈ upper_bounds s →  (y∈ s) →  y≠ ⊤:=
begin
  intros A1 A2,
  rw mem_upper_bounds at A1,
  have A3 := A1 y A2,
  apply le_coe_ne_top A3,
end


--Unnecessary
lemma upper_bounds_nnreal_fn {α:Type*} {f:α → ennreal} {x:nnreal}:
  (x:ennreal) ∈ upper_bounds (set.range f)  → (∃ g:α → nnreal,
  f = (λ a:α, (g a:ennreal))) :=
begin
  intro A1,
  let g:α → nnreal := λ a:α, ((f a).to_nnreal),
  begin
    have A2:g = λ a:α, ((f a).to_nnreal) := rfl,
    apply exists.intro g,
    rw A2,
    ext a,
    split;intro A3,
    {
      simp,
      simp at A3,
      rw A3,
      rw ennreal.to_nnreal_coe,
    },
    {
      simp,
      simp at A3,
      rw ← A3,
      symmetry,
      apply ennreal.coe_to_nnreal,
      apply upper_bounds_nnreal,
      apply A1,
      simp,
    },
  end
end


lemma ennreal.infi_le {α:Type*} {f:α → ennreal} {b : ennreal}:
   (∀ (ε : nnreal), 0 < ε → b < ⊤ → (∃a, f a  ≤ b + ↑ε)) → infi f ≤ b :=
begin
  intro A1,
  apply @ennreal.le_of_forall_epsilon_le,
  intros ε A2 A3,
  have A4 := A1 ε A2 A3,
  cases A4 with a A4,
  apply le_trans _ A4,
  apply @infi_le ennreal _ _,
end


lemma ennreal.le_supr {α:Type*} {f:α → ennreal} {b : ennreal}:(∀ (ε : nnreal), 0 < ε → (supr f < ⊤) → (∃a,  b ≤ f a + ε)) → b ≤ supr f :=
begin
  intro A1,
  apply @ennreal.le_of_forall_epsilon_le,
  intros ε A2 A3,
  have A4 := A1 ε A2 A3,
  cases A4 with a A4,
  apply le_trans A4,
  have A5:=@le_supr ennreal _ _ f a,
  apply add_le_add A5,
  apply le_refl _, 
end


lemma ennreal.not_add_le_of_lt_of_lt_top {a b:ennreal}:
   (0 < b) → (a < ⊤) → ¬(a + b) ≤ a :=
begin
  intros A1 A2 A3,
  have A4:(⊤:ennreal) = none := rfl,
  cases a,
  {
    simp at A2,
    apply A2,
  },
  cases b,
  {
    rw ←A4 at A3,
    rw with_top.add_top at A3,
    rw top_le_iff at A3,
    simp at A3,
    apply A3,
  },
  simp at A3,
  rw ← ennreal.coe_add at A3,
  rw ennreal.coe_le_coe at A3,
  simp at A1,
  apply nnreal.not_add_le_of_lt A1,
  apply A3,
end


lemma ennreal.lt_add_of_pos_of_lt_top {a b:ennreal}:
   (0 < b) → (a < ⊤) → a < a + b :=
begin
  intros A1 A2,
  apply lt_of_not_ge,
  apply ennreal.not_add_le_of_lt_of_lt_top A1 A2,
end

lemma ennreal.infi_elim {α:Sort*} {f:α → ennreal} {ε:nnreal}:
   (0 < ε) → (infi f < ⊤) → (∃a, f a  ≤ infi f + ↑ε) :=
begin
  intros A1 A2,
  have A3:¬(infi f+(ε:ennreal)≤ infi f),
  {
    apply ennreal.not_add_le_of_lt_of_lt_top _ A2,
    simp,
    apply A1,
  },
  apply (@classical.exists_of_not_forall_not α (λ (a  : α), f a ≤ infi f + ↑ε)),
  intro A4,
  apply A3,
  apply @le_infi ennreal α _,
  intro a,
  cases  (le_total (infi f + ↑ε) (f a)) with A5 A5,
  apply A5,
  have A6 := A4 a,
  exfalso,
  apply A6,
  apply A5,
end


lemma ennreal.zero_le {a:ennreal}:0 ≤ a :=
begin
  simp,
end


lemma ennreal.sub_top {a:ennreal}:a - ⊤ = 0 :=
begin
  simp,
end


lemma ennreal.sub_lt_of_pos_of_pos {a b:ennreal}:(0 < a) → 
    (0 < b) → (a ≠ ⊤) → (a - b) < a :=
begin
  intros A1 A2 A3,
  cases a,
  {
    exfalso,
    simp at A3,
    apply A3,
  },
  cases b,
  {
    rw ennreal.none_eq_top,
    rw ennreal.sub_top,
    apply A1,  
  },
  simp,
  rw ← ennreal.coe_sub,
  rw ennreal.coe_lt_coe,
  apply nnreal.sub_lt_of_pos_of_pos,
  {
    simp at A1,
    apply A1,
  },
  {
    simp at A2,
    apply A2,
  },
end

lemma ennreal.Sup_elim {S:set ennreal} {ε:nnreal}:
   (0 < ε) → (S.nonempty)  → (Sup S ≠ ⊤) → (∃s∈S, (Sup S) - ε ≤ s) :=
begin
  intros A1 A2 A3,
  cases classical.em (Sup S = 0) with A4 A4,
  {
    rw A4,
    have A5:= set.nonempty_def.mp A2,
    cases A5 with s A5,
    apply exists.intro s,
    apply exists.intro A5,
    simp,
  },
  have A5:(0:ennreal) = ⊥ := rfl,
  have B1:(Sup S) - ε < (Sup S),
  {
    apply ennreal.sub_lt_of_pos_of_pos,
    rw A5,
    rw bot_lt_iff_ne_bot,
    rw ← A5,
    apply A4,
    simp,
    apply A1,
    apply A3,
  },
  rw lt_Sup_iff at B1,
  cases B1 with a B1,
  cases B1 with B2 B3,
  apply exists.intro a,
  apply exists.intro B2,
  apply le_of_lt B3,
end

lemma ennreal.top_of_infi_top {α:Type*} {g:α → ennreal} {a:α}:((⨅ a', g a') = ⊤) → 
  (g a = ⊤) :=
begin
  intro A1,
  rw ← top_le_iff,
  rw ← A1,
  apply @infi_le ennreal α _,
end



lemma of_infi_lt_top {P:Prop} {H:P→ ennreal}:infi H < ⊤ → P :=
begin
  intro A1,
  cases (classical.em P) with A2 A2, 
  {
    apply A2,
  },
  {
    exfalso,
    unfold infi at A1,
    unfold set.range at A1,
    have A2:{x : ennreal | ∃ (y : P), H y = x}=∅,
    {
      ext;split;intro A2A,
      simp at A2A,
      exfalso,
      cases A2A with y A2A,
      apply A2,
      apply y,
      exfalso,
      apply A2A,
    },
    rw A2 at A1,
    simp at A1,
    apply A1,
  },
end

lemma ennreal.add_le_add_left {a b c:ennreal}:
   b ≤ c → a + b ≤ a + c :=
begin
  intro A1,
  cases a,
  {
    simp,
  },
  cases b,
  {
    simp at A1,
    subst c,
    simp,
  },
  cases c,
  {
    simp,
  },
  simp,
  simp at A1,
  repeat {rw ← ennreal.coe_add},
  rw ennreal.coe_le_coe,
  apply @add_le_add_left nnreal _,
  apply A1,
end



lemma ennreal.le_of_add_le_add_left {a b c:ennreal}:a < ⊤ →
    a + b ≤ a + c → b ≤ c :=
begin
  intros A1 A2,
  cases a,
  {
    exfalso,
    simp at A1,
    apply A1,
  },
  cases c,
  {
    simp,
  },
  cases b,
  {
    exfalso,
    simp at A2,
    rw ← ennreal.coe_add at A2,
    apply ennreal.coe_ne_top A2,
  },
  simp,
  simp at A2,
  repeat {rw  ← ennreal.coe_add at A2},
  rw ennreal.coe_le_coe at A2,
  apply le_of_add_le_add_left A2,
end

lemma ennreal.le_of_add_le_add_right 
    {a b c:ennreal}:(c < ⊤)→
   (a + c ≤ b + c) → (a ≤ b) :=
begin
  intros A1 A2,
  rw add_comm a c at A2,
  rw add_comm b c at A2,
  apply ennreal.le_of_add_le_add_left A1 A2,
end


lemma ennreal.top_sub_some {a:nnreal}:(⊤:ennreal) - a = ⊤ :=
begin
  simp,
end


lemma ennreal.add_sub_add_eq_sub_add_sub {a b c d:ennreal}:c < ⊤ → d < ⊤ → 
    c ≤ a → d ≤ b →
    a + b - (c + d) = (a - c) + (b - d) :=
begin
  intros A1 A2 A3 A4,
  cases c,
  {
    simp at A1,
    exfalso,
    apply A1,
  },
  cases d,
  {
    simp at A2,
    exfalso,
    apply A2,
  },
  cases a,
  {
    simp,
    rw ← ennreal.coe_add,
    apply ennreal.top_sub_some,
  },
  cases b,
  {
    simp,
    rw ← ennreal.coe_add,
    apply ennreal.top_sub_some,
  },
  simp,
  rw ← ennreal.coe_add,
  rw ← ennreal.coe_add,
  rw ← ennreal.coe_sub,
  rw ← ennreal.coe_sub,
  rw ← ennreal.coe_sub,
  rw ← ennreal.coe_add,
  rw ennreal.coe_eq_coe,
  simp at A3,
  simp at A4,
  apply nnreal.add_sub_add_eq_sub_add_sub A3 A4,
end


lemma ennreal.le_add {a b c:ennreal}:a ≤ b → a ≤ b + c :=
begin
  intro A1,
  apply @le_add_of_le_of_nonneg ennreal _,
  apply A1,
  simp,
end


lemma ennreal.add_lt_add_of_lt_of_le_of_lt_top {a b c d:ennreal}:d < ⊤ → c ≤ d → a < b → a + c < b + d :=
begin
  intros A1 A2 A3,
  rw le_iff_lt_or_eq at A2,
  cases A2 with A2 A2,
  {
    apply ennreal.add_lt_add A3 A2,
  },
  subst d,
  rw with_top.add_lt_add_iff_right,
  apply A3,
  apply A1,
end 

lemma ennreal.le_of_sub_eq_zero {a b:ennreal}:
    a - b = 0 → a ≤ b :=
begin
  intros A1,
  simp at A1,
  apply A1,
end


lemma ennreal.le_zero_iff {a:ennreal}:a ≤ 0 ↔ a=0 :=
begin
  simp
end

lemma ennreal.sub_le {a b:ennreal}:a - b ≤ a :=
begin
  simp,
  apply ennreal.le_add,
  apply le_refl _,
end


lemma ennreal.multiply_mono {α β:Type*} [preorder α] {f g:α → β → ennreal}:
    monotone f →  
    monotone g →
    monotone (f * g) :=
begin
  intros A1 A2 a1 a2 A3,
  rw le_func_def2,
  intro b,
  simp,
  apply @ennreal.mul_le_mul (f a1 b) (f a2 b) (g a1 b) (g a2 b),
  {
    apply A1,
    apply A3,
  },
  {
    apply A2,
    apply A3,
  },
end


lemma ennreal.supr_zero_iff_zero {α:Type*}  {f:α → ennreal}:
  supr f = 0 ↔ f = 0 := 
begin
  have A0:(0:ennreal) = ⊥ := rfl,
  rw A0,
  have A1:f = 0 ↔ (∀ a:α, f a = 0),
  {
    split; intro A1,
    {
      intro a,
      rw A1,
      simp,
    },
    apply funext,
    intro a,
    simp,
    apply A1,
  },
  rw A1,
  split;intros A2,
  {
    intro a,
    rw A0,
    rw ← @le_bot_iff ennreal _ (f a),
    rw ← A2,
    apply le_supr f,
  },
  {
    rw ← @le_bot_iff ennreal _ (supr f),  
    apply @supr_le ennreal α _ f,
    intro a,
    rw  @le_bot_iff ennreal _ (f a),
    rw ← A0,
    apply A2,
  },
end


lemma le_supr_mul_of_supr_zero {α:Type*}  {f g:α → ennreal}:supr f = 0 → (supr f) * (supr g) ≤ supr (f * g) :=
begin
  intro A1,
  rw A1,
  rw zero_mul,
  apply @bot_le ennreal _,
end


lemma ennreal.zero_of_mul_top_lt {a b:ennreal}:a * ⊤ < b → a = 0 :=
begin
  intro A1,
  have A2:a=0 ∨ a≠ 0 := eq_or_ne,
  cases A2,
  {
    apply A2,
  },
  {
    exfalso,
    rw with_top.mul_top A2 at A1,
    apply @not_top_lt ennreal _ b,
    apply A1,
  },
end

lemma ennreal.sub_add_sub {a b c:ennreal}:c ≤ b → b ≤ a → (a - b) + (b - c) = a - c :=
begin
  intros A1 A2,
  cases c,
  {
    rw ennreal.none_eq_top at A1,
    rw top_le_iff at A1,
    subst b,
    rw top_le_iff at A2,
    subst a,
    simp,
  },
  rw ennreal.some_eq_coe at A1,
  rw ennreal.some_eq_coe,
  cases b,
  {
    rw ennreal.none_eq_top at A2,
    rw top_le_iff at A2,
    subst a,
    simp,
  },
  rw ennreal.some_eq_coe at A1,
  rw ennreal.some_eq_coe at A2,
  rw ennreal.some_eq_coe,
  cases a,
  {
    simp,
  },
  rw ennreal.some_eq_coe at A2,
  rw ennreal.some_eq_coe,
  repeat {rw ← ennreal.coe_sub},
  repeat {rw ← ennreal.coe_add},
  rw ennreal.coe_eq_coe,
  rw ennreal.coe_le_coe at A1,
  rw ennreal.coe_le_coe at A2,
  apply nnreal.sub_add_sub A1 A2,
end

lemma ennreal.coe_mul_coe_lt_top {a b:nnreal}:(a:ennreal) * (b:ennreal) < (⊤:ennreal) :=
begin
  rw lt_top_iff_ne_top,
  intros A1,
  rw with_top.mul_eq_top_iff at A1,
  simp at A1,
  apply A1,
end


lemma ennreal.lt_div_iff_mul_lt {a b c : ennreal}:
     (b ≠ 0) →
     (b ≠ ⊤) → 
     (a < c / b ↔ a * b < c) :=
begin
  intros A1 A2,
  cases b,
  {
    exfalso,
    simp at A2,
    apply A2,
  },
  cases a,
  {
    simp,
    rw mul_comm,
    rw with_top.mul_top,
    apply @le_top ennreal _,
    apply A1,
  },
  simp at A2,
  cases c,
  {
    simp,
    apply ennreal.coe_mul_coe_lt_top,
  },
  simp,
  split;intros A3,
  {
    rw lt_iff_le_not_eq,
    split,
    {
      rw ← ennreal.le_div_iff_mul_le,
      apply @le_of_lt ennreal _ (↑a)  ((↑c)/(↑b)),
      apply A3,
      apply or.inl A1,
      left,
      simp,
    },
    {
      intro A4,
      rw ← A4 at A3,
      rw ennreal.mul_div_assoc at A3,
      rw @ennreal.div_self at A3,
      simp at A3,
      have A5 :=  ne_of_lt A3,
      simp at A5,
      apply A5,
      apply A1,
      have A6 := @with_top.some_lt_none nnreal _ b,
      apply ne_of_lt A6,
    },
  },
  {
    rw lt_iff_le_not_eq,
    split,
    {
      rw ennreal.le_div_iff_mul_le,
      
      apply @le_of_lt ennreal _,
      apply A3,
      apply or.inl A1,
      left,
      simp,
    },
    {
      intro A4,
      rw A4 at A3,
      rw ennreal.mul_div_cancel at A3,
      simp at A3,
      have A5 :=  ne_of_lt A3,
      simp at A5,
      apply A5,
      apply A1,
      have A6 := @with_top.some_lt_none nnreal _ b,
      apply ne_of_lt A6,
    },
  },
end


lemma ennreal.lt_of_mul_lt_mul {a b c:ennreal}:
    (b ≠ 0) → (b ≠ ⊤) → (a < c) → (a * b < c * b)  :=
begin
  intros A1 A2 A3,
  apply ennreal.mul_lt_of_lt_div,
  rw ennreal.mul_div_assoc,
  have A4:(b/b)=1,
  {
    apply ennreal.div_self,
    apply A1,
    apply A2,
  },
  rw A4,
  simp,
  apply A3,
end

---------------------- Theorems of topology ------------------------------------------------------



lemma Pi.topological_space_def {α:Type*} {β : α → Type*} [t₂ : Πa, topological_space (β a)] :
  @Pi.topological_space α β t₂ = ⨅a, topological_space.induced (λf, f a) (t₂ a) := rfl


lemma Pi.topological_space_le_induced {α:Type*} {β : α → Type*} [t₂ : Πa, topological_space (β a)] {a:α}:@Pi.topological_space α β t₂ ≤ topological_space.induced (λf, f a) (t₂ a) :=
begin
  rw Pi.topological_space_def,
  have A1:(λ a2:α, topological_space.induced (λf:(Π a:α, β a) , f a2) (t₂ a2)) a = 
         topological_space.induced (λf, f a) (t₂ a) := rfl,
  rw ← A1,
  apply infi_le (λ a2:α, topological_space.induced (λf:(Π a:α, β a) , f a2) (t₂ a2)),
end

lemma is_open_iff_is_open {α:Type*} {T:topological_space α} {U:set α}:
  is_open U = topological_space.is_open T U := rfl





lemma topological_space_le_is_open {α:Type*} {T1 T2:topological_space α}:
  ((topological_space.is_open T1)≤ (topological_space.is_open T2)) = (T2 ≤ T1) := rfl

lemma topological_space_le_is_open_2 {α:Type*} {T1 T2:topological_space α}:
  (T1 ≤ T2) ↔ 
  (∀ S:set α, topological_space.is_open T2 S → 
               topological_space.is_open T1 S) :=
begin
  rw ← topological_space_le_is_open,
  rw set.le_eq_subset,
  rw set.subset_def,
  refl,
end


--These are the most basic open sets: don't even form a basis.
lemma Pi.topological_space_is_open {α:Type*} {β : α → Type*} [t₂ : Πa, topological_space (β a)] {a:α} (S:set (Π a:α, β a)):
topological_space.is_open (topological_space.induced (λf:(Π a:α, β a), f a) (t₂ a)) S →
topological_space.is_open (@Pi.topological_space α β t₂) S :=
begin
  have A1:=@Pi.topological_space_le_induced α β t₂ a,
  rw topological_space_le_is_open_2 at A1, 
  apply A1 S,
end

lemma topological_space_infi {α β:Type*} {T:β → topological_space α}:
  (⨅ b:β, T b) = topological_space.generate_from (
  (⋃ b:β, (T b).is_open)) :=
begin
  apply le_antisymm,
  {
    rw le_generate_from_iff_subset_is_open,
    rw set.subset_def,
    intros U A1,
    simp at A1,
    simp,
    cases A1 with b A1,
    have A2:infi T ≤ T b,
    {
       have A3:T b ≤ T b,
       {
         apply le_refl (T b),
       },
       apply (infi_le_of_le b) A3,
    },
    rw topological_space_le_is_open_2 at A2,
    apply A2,
    apply A1,
  },
  {
    apply @le_infi (topological_space α) _ _,
    intro b,
    rw topological_space_le_is_open_2,
    intros S A1,
    unfold topological_space.generate_from,
    simp,
    apply topological_space.generate_open.basic,
    simp,
    apply exists.intro b,
    apply A1,
  },
end 



lemma is_open_infi_elim {α β:Type*} [decidable_eq β] {T:β → topological_space α} {U:set α} {x:α}:
  (x∈ U) →
  topological_space.is_open (⨅ b:β, T b) U → 
  (∃ S:finset β, ∃ f:β →set α,  
  (∀ s∈ S, topological_space.is_open (T s) (f s)) ∧ 
  (∀ s∈ S, x ∈ f s) ∧ 
  (⋂s∈ S, f s)⊆  U)  :=
begin
  intros A1 A2,
  rw @topological_space_infi α β T at A2,
  unfold topological_space.generate_from at A2,
  simp at A2,
  induction A2,
  {
    simp at A2_H,
    cases A2_H with b A2,
    apply exists.intro ({b}),
    {
      apply exists.intro (λ b:β, A2_s),
      split,
      {
        intros b2 A3,
        simp,
        rw @finset.mem_singleton β b b2 at A3,
        rw A3,
        apply A2,
      },
      split,
      {
         intros b2 A3,
         simp,
         apply A1,
      },
      {
         rw set.subset_def,
         intros x2 A3,
         simp at A3,
         apply A3,
      },
    },
  },
  {
    apply exists.intro ∅,
    apply exists.intro (λ b:β, set.univ),
    split,
    {
      intros b A2,
      simp,
      apply topological_space.is_open_univ,
    },
    split,
    {
      intros b A2,
      simp,
    },
    {
      apply set.subset_univ,
    },
    {
      apply finset.has_emptyc,
    },
  },
  {
    simp at A1,
    cases A1 with A3 A4,
    have A5 := A2_ih_a A3,
    cases A5 with S A5,
    cases A5 with f A5,
    have A6 := A2_ih_a_1 A4,
    cases A6 with S2 A6,
    cases A6 with f2 A6,
    let z:β → set α := λ b:β, 
        if (b∈ S) then 
          (if (b∈ S2) then ((f b) ∩ (f2 b)) else f b)
          else (f2 b),
    begin
      have B1:z = λ b:β, 
        if (b∈ S) then 
          (if (b∈ S2) then ((f b) ∩ (f2 b)) else f b)
          else (f2 b) := rfl,
      apply exists.intro (S ∪ S2),
      apply exists.intro z,
      split,
      {
        intros s B2,
        rw union_trichotomy at B2,
        rw B1,
        simp,
        cases B2,
        {
          rw if_pos B2.left,
          rw if_neg B2.right,
          apply A5.left s B2.left,
        },
        cases B2,
        {
          rw if_pos B2.left,
          rw if_pos B2.right,
          apply topological_space.is_open_inter,
          apply A5.left s B2.left,
          apply A6.left s B2.right,
        },
        {
          rw if_neg B2.left,
          apply A6.left s B2.right,
        },
      },
      split,
      {
        intros s B2,
        rw B1,
        simp,
        rw union_trichotomy at B2,
        cases B2,
        {
          rw if_pos B2.left,
          rw if_neg B2.right,
          apply A5.right.left s B2.left,
        },
        cases B2,
        {
          rw if_pos B2.left,
          rw if_pos B2.right,
          simp,
          split,
          apply A5.right.left s B2.left,
          apply A6.right.left s B2.right,
        },
        {
          rw if_neg B2.left,
          apply A6.right.left s B2.right,
        },
      },
      {
        rw set.subset_def,
        rw B1,
        intros a B2,
        simp at B2,
        split,
        {
          have B3 := A5.right.right,
          rw set.subset_def at B3,
          apply B3,
          simp,
          intros b B4,
          have B5 := B2 b (or.inl B4),
          rw if_pos B4 at B5,
          have B6:(b ∈ S2) ∨ (b ∉ S2),
          {
            apply classical.em,
          },
          cases B6,
          {
            rw if_pos B6 at B5,
            simp at B5,
            apply B5.left,
          },
          {
            rw if_neg B6 at B5,
            apply B5,
          },
        },
        {
          have B3 := A6.right.right,
          rw set.subset_def at B3,
          apply B3,
          simp,
          intros b B4,
          have B5 := B2 b (or.inr B4),
          rw if_pos B4 at B5,
          have B6:(b ∈ S) ∨ (b ∉ S),
          {
            apply classical.em,
          },
          cases B6,
          {
            rw if_pos B6 at B5,
            simp at B5,
            apply B5.right,
          },
          {
            rw if_neg B6 at B5,
            apply B5,
          },
        },
      },
    end
  },
  {
    simp at A1,
    cases A1 with S A1,
    cases A1 with A3 A4,
    have A5 := A2_ih S A3 A4,
    cases A5 with S2 A5,
    cases A5 with f A5,
    apply exists.intro S2,
    apply exists.intro f,
    cases A5 with A5 A6,
    cases A6 with A6 A7,
    split,
    {
      apply A5,
    },
    split,
    {
      apply A6,
    },
    {
      apply set.subset.trans,
      apply A7,
      apply set.subset_sUnion_of_mem,
      apply A3,
    },
  },
end


def product_basis {α:Type*} {β : α → Type*} (S:finset α) 
    (f:Π a:α, set (β a)):set (Πa, β a) :=
    {x:Πa, β a|∀ a∈ S, x a ∈ f a}

lemma product_basis_def {α:Type*} {β : α → Type*} {S:finset α} 
    {f:Π a:α, set (β a)}:
    product_basis S f = {x:Πa, β a|∀ a∈ S, x a ∈ f a} := rfl


lemma finite_inter_insert {α:Type*} [decidable_eq α] {β : Type*}
    {S:finset α} {a:α}
    {f:Π a:α, set (β)}:(⋂ (a2:α) (H:a2∈ (insert a S)), f a2) = 
              (⋂ (a2:α) (H:a2∈ (S)), f a2)  ∩ (f a) :=
begin
  ext b,
  split;intro A1,
  {
    simp,
    simp at A1,
    split,
    {
      intros i A2,
      apply A1.right i,
      apply A2,
    },
    {
      apply A1.left,
    },
  },
  {
    simp,
    simp at A1,
    apply and.intro A1.right A1.left,
  },
end

lemma is_open_finite_inter {α:Type*} [decidable_eq α] {β : Type*}
    [topological_space β]
    {S:finset α} 
    {f:Π a:α, set (β)}:
    (∀ a∈ S, is_open (f a))  → is_open (⋂ (a:α) (H:a∈ S), f a) := 
begin
  apply finset.induction_on S,
  intro A1,
  {
    simp,
  },
  {
    intros a S A2 A3 A4,
    rw finite_inter_insert,
    apply is_open_inter,
    {
      apply A3,
      simp at A4,
      intros a2 A5,
      apply A4,
      apply or.inr A5,
    },
    {
      apply A4,
      simp,
    },
  },
end




--This is missing that f b is open.
lemma Pi.is_open_topological_space {α:Type*} {β : α → Type*} [decidable_eq α]
    [t₂ : Πa, topological_space (β a)]
    {U:set (Π a, β a)} {x:(Π a, β a)}:
  (x∈ U) →  
  (@is_open _ (@Pi.topological_space α β t₂) U) →
(∃ S:finset α, ∃ (f:Π a:α, set (β a)), 
   x∈ product_basis S f ∧
   (∀ a∈ S, (is_open (f a))) ∧  
   product_basis S f ⊆ U)  :=
begin
  intros AX A1,
  rw Pi.topological_space_def at A1,
  have A2 := is_open_infi_elim AX A1,
  cases A2 with S A2,
  cases A2 with f A2,
  cases A2 with A2 A3,
  cases A3 with A3A A3B,
  apply exists.intro S,
  unfold product_basis,
  have A4:∀ s∈ S, ∃  t:set (β s), 
      @is_open (β s) (t₂ s) t ∧
      (λ (f : Π (a : α), β a), f s) ⁻¹' t = f s,
  {
    intros s A4A,
    have A4B := A2 s A4A,
    simp at A4B,
    rw ← is_open_iff_is_open at A4B,
    rw @is_open_induced_iff 
       (Π (a: α), β a) (β s) (t₂ s) (f s) 
       (λ (f : Π (a : α), β a), f s) at A4B,
    cases A4B with t A4B,
    apply exists.intro t,
    apply A4B,
  },
  let z:(Π (a:α), set (β a)) := λ (a:α), 
    (@dite (a∈ S) _  (set (β a))  (λ h:(a∈ S), @classical.some _ _ (A4 a h))
        (λ h, ∅)),
  begin
    have A5:z= λ (a:α), 
    (@dite (a∈ S) _  (set (β a))  (λ h:(a∈ S), @classical.some _ _ (A4 a h))
        (λ h, ∅)) := rfl,
    have AY:∀ s∈ S, is_open (z s) ∧ (
            λ (f : Π (a : α), β a), f s) ⁻¹' (z s) = f s,
    {
      intros i A8,
      have A10 := A4 i A8,
      have A11:(λ q:set (β i), @is_open (β i) (t₂ i) q ∧ (λ (f : Π (a : α), β a), f i) ⁻¹' q = f i)
            ((@classical.some (set (β i))
      (λ (t : set (β i)), @is_open (β i) (t₂ i) t ∧ (λ (f : Π (a : α), β a), f i) ⁻¹' t = f i)) A10),
        {
           apply @classical.some_spec (set (β i))
              (λ q:set (β i), @is_open (β i) (t₂ i) q ∧ (λ (f : Π (a : α), β a), f i) ⁻¹' q = f i),
        },
        have A12:z i = (classical.some A10),
        {
          rw A5,
          simp,
          rw dif_pos A8,
        },
        rw ← A12 at A11,
        apply A11,        
    },
    apply exists.intro z,
    have A6:{x : Π (a : α), β a | ∀ (a : α), a ∈ S → x a ∈ z a} =
            (⋂ (s : α) (H : s ∈ S), f s) ,
    {
      ext k,
      split;intros A7,
      {
        simp,
        simp at A7,
        intros i A8,
        have A9 := A7 i A8,
        cases (AY i A8) with A11 A12, 
        rw ← A12,
        simp,
        apply A9,
      },
      {
        simp,
        simp at A7,
        intros i A8,
        have A9 := AY i A8,
        cases A9 with A10 A11,
        have A12 := A7 i A8,
        rw ← A11 at A12,
        simp at A12,
        apply A12,
      },
    },
    rw A6,
    split,
    {
      simp,
      apply A3A,
    },
    split,
    {
      intros a A7,
      apply (AY a A7).left,
    },
    {
      apply A3B,
    },
  end
end


------ Measure theory --------------------------------------------------------------------------


lemma simple_func_to_fun {Ω:Type*} {M:measurable_space Ω} 
 (g:measure_theory.simple_func Ω ennreal):⇑g = g.to_fun := rfl




def is_absolutely_continuous_wrt 
  {Ω:Type*} {M:measurable_space Ω} (μ ν:measure_theory.measure Ω):Prop :=
  ∀ A:set Ω, is_measurable A → (ν A = 0) → (μ A = 0)


lemma measure_zero_of_is_absolutely_continuous_wrt 
  {Ω:Type*} {M:measurable_space Ω} (μ ν:measure_theory.measure Ω) (A:set Ω):
  is_absolutely_continuous_wrt μ ν → 
  is_measurable A → (ν A = 0) → (μ A = 0) :=
begin
  intros A1 A2 A3,
  unfold is_absolutely_continuous_wrt at A1,
  apply A1 A A2 A3,
end


noncomputable def lebesgue_measure_on_borel := measure_theory.real.measure_space.volume


lemma lebesgue_measure_on_borel_def:
  lebesgue_measure_on_borel = measure_theory.real.measure_space.volume := rfl


lemma lebesgue_measure_on_borel_apply {S:set ℝ}:
  lebesgue_measure_on_borel S = measure_theory.lebesgue_outer S := rfl



def is_absolutely_continuous_wrt_lebesgue
  (μ:measure_theory.measure ℝ):Prop :=
  is_absolutely_continuous_wrt μ lebesgue_measure_on_borel

lemma prob_zero_of_is_absolute_continuous_wrt_lebesgue (μ:measure_theory.measure ℝ) (E:set ℝ):is_absolutely_continuous_wrt_lebesgue μ →
   is_measurable E →   
   measure_theory.lebesgue_outer E = 0 →
    μ E=0 :=
begin
  intros A1 A2 A3,
  apply measure_zero_of_is_absolutely_continuous_wrt μ lebesgue_measure_on_borel
  _ A1 A2,
  rw lebesgue_measure_on_borel_apply,
  apply A3,
end





lemma outer_measure.has_coe_to_fun_def {Ω:Type*} (O:measure_theory.outer_measure Ω):
  ⇑O = O.measure_of := rfl


lemma outer_measure.ext2 {Ω:Type*} (O1 O2:measure_theory.outer_measure Ω):
   (O1.measure_of = O2.measure_of) → (O1 = O2) :=
begin
    intro A1,
    apply measure_theory.outer_measure.ext,
    intro s,
    repeat {rw outer_measure.has_coe_to_fun_def},
    rw A1,
end

lemma filter.has_mem_def {α : Type*} (S:set α) (F:filter α):
  S ∈ F = (S∈ F.sets) := rfl


lemma finset.subset_Union {α:Type*} [decidable_eq α] {S:finset (finset α)} {T:finset α}:T ∈ S → T ⊆ (finset.Union S) := 
begin
  apply finset.induction_on S,
  {
    simp,
  },
  {
    
    intros T2 S2 A1 A2 A3,
    simp at A3,
    rw finset.Union_insert,
    cases A3,
    {
      subst T2,
      apply finset.subset_union_left,
    },
    {
      apply finset.subset.trans (A2 A3),
      apply finset.subset_union_right,
    },
  },
end


--This is proving that the functions sum to a function if they sum to a function elementwise.
lemma has_sum_product {α β:Type*} [Dα:decidable_eq α] [Dβ:decidable_eq β] {γ:β → Type*} [Π b:β,add_comm_monoid (γ b)] 
  [T:Π b:β,topological_space (γ b)] {f:α → (Π b:β, γ b)} {g:Π b:β, γ b}:
  (∀ b:β, has_sum  (λ n, f n b) (g b)) →  
  has_sum f g :=
begin
  intro A1,
  unfold has_sum filter.tendsto filter.map,
  rw le_nhds_iff,
  intros S A1A A2,
  rw Pi.topological_space_def at A2,
  rw ← filter.has_mem_def,
  simp,

  --At some point, we want to apply filter_at_top_intro3, but
  --only after we better understand the set S.
  have A3:= @Pi.is_open_topological_space β γ Dβ T S g A1A A2,
  cases A3 with S2 A3,
  cases A3 with f2 A3,
  have A4:∀ b∈ S2, ∃ S3:finset α, ∀S4⊇ S3,
          S4.sum (λ a:α, f a b) ∈ f2 b,
  {
    intros b A4A,
    have A4B := A1 b,
    unfold has_sum filter.tendsto filter.map at A4B,
    have A4C:f2 b ∈ nhds (g b),
    {
      apply mem_nhds_sets,
      {
        have D1 := A3.right.left,
        apply D1 b A4A,
      },
      {
        have C1:= A3.left,
        unfold product_basis at C1,
        simp at C1,
        apply C1 b A4A,
      },
    }, 
    have A4D := filter_le_elim A4B A4C,
    simp at A4D,
    cases A4D with S3 A4D,
    apply exists.intro S3,
    intros S4 A4E,
    have A4F := A4D S4 A4E,
    apply A4F,
  },
  let z:β → (finset α) := λ b:β, @dite (b∈ S2)  _ (finset α)
        (λ H:b∈ S2, classical.some (A4 b H))
        (λ H, ∅),
  let S3 := finset.Union (finset.image z S2),  
  begin
    have A5:z= λ b:β, @dite (b∈ S2)  _ (finset α)
        (λ H:b∈ S2, classical.some (A4 b H))
        (λ H, ∅) := rfl, 
    have A6:S3 = finset.Union (finset.image z S2) := rfl,
    apply exists.intro S3,
    intros S4 A7,
    have A8:S4.sum f ∈ product_basis S2 f2,
    {
      unfold product_basis,
      simp,
      intros b A8A,
      have A8X:z b ⊆ S3,
      {
        have A8BA:z b ∈ finset.image z S2,
        {
           apply (@finset.mem_image_of_mem β (finset α) _ z b S2 A8A),
        },        
        apply @finset.subset_Union α Dα (finset.image z S2) (z b) A8BA,
      },

      have A8B:z b ⊆ S4,
      {
        apply finset.subset.trans,
        apply A8X,
        apply A7,
      },
      have A9C:(λ (S3 : finset α), 
                ∀ (S4 : finset α), S4 ⊇ S3 → 
                finset.sum S4 (λ (a : α), f a b) ∈ f2 b) 
                (classical.some (A4 b A8A)),
      {
         apply @classical.some_spec (finset α) (λ (S3 : finset α), 
                ∀ (S4 : finset α), S4 ⊇ S3 → 
                finset.sum S4 (λ (a : α), f a b) ∈ f2 b) ,
      },

      have A9D:z b = classical.some (A4 b A8A),
      {
        rw A5,
        simp,
        rw dif_pos A8A,
      },
      rw ← A9D at A9C,
      have A9E := A9C S4 A8B,
      apply A9E,
    },    
    apply set.mem_of_mem_of_subset A8 A3.right.right,
  end
end

/- This is true, but for an odd reason. Note that the product topology
   has the finite product of bases as a basis. So, we can take the
   finite product of elements to get the neighborhood. For each of these
   elements in the finite product, there is some finite set such that
   it is within the limit. So, the union of N finite sets will give us
   a finite set. QED. -/
lemma has_sum_fn {α Ω γ:Type*} [Dα:decidable_eq α] [DΩ:decidable_eq Ω] [C:add_comm_monoid γ] [T:topological_space γ] {f:α → Ω → γ} {g:Ω → γ}:
  (∀ ω:Ω, has_sum  (λ n, f n ω) (g ω)) →  
  has_sum f g :=
begin
  intro A1,
  apply (@has_sum_product α Ω Dα DΩ _ (λ ω:Ω, C) (λ ω:Ω, T) f g A1),
end




lemma has_sum_fn_ennreal_2 {α β:Type*} [decidable_eq α] [decidable_eq β] (f:α → β → ennreal):
  has_sum f (λ b:β, ∑' a:α, f a b) :=
begin
  apply has_sum_fn,
  intro ω,
  rw summable.has_sum_iff,
  apply ennreal.summable,
end

lemma summable_fn_ennreal {α β:Type*} [decidable_eq α] [decidable_eq β] {f:α → β → ennreal}:summable f :=
begin
  have A1 := has_sum_fn_ennreal_2 f,
  apply has_sum.summable A1,
end


lemma tsum_fn {α Ω:Type*} [decidable_eq α] [decidable_eq Ω] {f:α → Ω → ennreal}:
    (∑' n, f n) =  (λ ω, ∑' n, (f n ω)) :=
begin
  apply has_sum.tsum_eq,
  apply has_sum_fn_ennreal_2,
end

lemma set_indicator_le_sum {Ω:Type*} [decidable_eq Ω] (f:Ω → ennreal) (s: ℕ → set Ω): (set.indicator (⋃ (i : ℕ), s i) f) ≤ ∑' i:ℕ, set.indicator (s i) f  :=
begin
  rw has_le_fun_def, 
  intro ω,
  have A1:ω ∈ (⋃ (i : ℕ), s i)  ∨ ω ∉ (⋃ (i : ℕ), s i),
  {
    apply classical.em,
  },
  cases A1,
  {
    rw set.indicator_apply,
    rw if_pos,
    {
      cases A1 with S A1,
      cases A1 with A1 A2,
      simp at A1,
      cases A1 with y A1,
      subst S,
      have A3:f ω = set.indicator (s y) f ω,
      {
        rw set.indicator_apply,
        rw if_pos,
        apply A2,
      },
      rw A3,
      have A4 := @ennreal.le_tsum _ (λ i, set.indicator (s i) f ω) y,
      simp at A4,
      rw tsum_fn,
      apply A4,
    },
    {
      apply A1,
    },
  },
  {
    rw set.indicator_apply,
    rw if_neg,
    {
      simp,
    },
    {
      apply A1,
    },
  },
end



lemma set.indicator_tsum {Ω:Type*}  
     (f:Ω → ennreal) (g:ℕ → set Ω):
     pairwise (disjoint on g) →
     set.indicator  (⋃ (i : ℕ), g i) f = 
   ∑' (i : ℕ), set.indicator (g i) f 
  :=
begin
  intro A1,
  apply funext,
  intro ω,
  have A2:decidable_eq Ω := classical.decidable_eq Ω,
  rw @tsum_fn ℕ Ω nat.decidable_eq A2 (λ i:ℕ, set.indicator (g i) f),
  simp,
  have A3:ω ∈ (set.Union g) ∨ (ω ∉ (set.Union g)) := classical.em  (ω ∈ (set.Union g) ),
  cases A3,
  {
    rw set.indicator_of_mem A3,
    simp at A3,
    cases A3 with i A3,
    rw tsum_eq_single i,
    rw set.indicator_of_mem A3,
    intros b' A4,
    rw set.indicator_of_not_mem,
    have A5:disjoint (g b') (g i),
    {
      apply A1,
      apply A4,
    },
    rw set.disjoint_right at A5,
    apply A5,
    apply A3,
    apply ennreal.t2_space,
  },
  {
    rw set.indicator_of_not_mem A3,
    have A6:(λ i:ℕ, set.indicator (g i) f ω)=0,
    {
      apply funext,
      intro i,
      simp at A3,
      rw set.indicator_of_not_mem (A3 i),
      simp,
    },
    rw A6,
    symmetry,
    apply has_sum.tsum_eq,
    apply has_sum_zero,
  },
end


lemma set_indicator_def {Ω:Type*} {S:set Ω} {f:Ω → ennreal}:
    (λ (a : Ω), ⨆ (h : a ∈ S), f a)  = set.indicator S f := 
begin
  apply funext,
  intro ω,
  cases (classical.em (ω ∈ S)) with A1 A1,
  {
    simp [A1],
  },
  {
    simp [A1],
  },
end



lemma measure.apply {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)  (S:set Ω):
    μ S = μ.to_outer_measure.measure_of S :=
begin
  refl
end



--TODO: Can this be replaced with measure_theory.lintegral_supr?
--Look more closely: this is using supr_apply, which means it is more 
--than just measure_theory.lintegral_supr.
lemma  measure_theory.lintegral_supr2 {α : Type*} 
    [N:measurable_space α]
    {μ:measure_theory.measure α}
     {f : ℕ → α → ennreal}:
    (∀ (n : ℕ), measurable (f n)) → 
    monotone f → 
    ((∫⁻ a:α,  (⨆ (n : ℕ), f n) a ∂ μ) = 
    ⨆ (n : ℕ), (∫⁻ a:α, (f n) a ∂ μ)) :=
begin
  intros A1 A2,
  have A3:(λ a, (⨆ (n : ℕ), f n a)) = (⨆ (n : ℕ), f n),
  {
    apply funext,
    intro a,
    rw supr_apply,
  },
  rw ← A3,
  apply measure_theory.lintegral_supr,
  apply A1,
  apply A2,
end


lemma supr_indicator {Ω:Type*} (g:ℕ → Ω → ennreal) (S:set Ω):
     (set.indicator S (supr g)) =
     (⨆ (n : ℕ), (set.indicator S (g n))) :=
begin
  apply funext,
  intro ω,
  rw (@supr_apply Ω (λ ω:Ω, ennreal) ℕ _ (λ n:ℕ, set.indicator S (g n)) ),
  have A0:(λ (i : ℕ), (λ (n : ℕ), set.indicator S (g n)) i ω) =
      (λ (i : ℕ), set.indicator S (g i) ω),
  {
    apply funext,
    intro i,
    simp,
  },
  rw A0,
  have A1:ω ∈ S ∨ ω ∉ S ,
  {
    apply classical.em,
  },
  cases A1,
  {
    rw set.indicator_of_mem A1,
    have B1A:(λ (i : ℕ), set.indicator S (g i) ω) =
        (λ (i : ℕ), g i ω),
    {
      apply funext,
      intro i,
      rw set.indicator_of_mem A1,
    },
    rw B1A,
    rw supr_apply,
  },
  {
    rw set.indicator_of_not_mem A1,
    have B1A:(λ (i : ℕ), set.indicator S (g i) ω) = (λ (i:ℕ), 0),
    {
      apply funext,
      intro i,
      rw set.indicator_of_not_mem A1,
    },
    rw B1A,
    rw @supr_const ennreal ℕ _ _ 0,
  },
end

lemma supr_eapprox {α:Type*} {M:measurable_space α} (f : α → ennreal) (hf : measurable f):
 (⨆ n:ℕ, (measure_theory.simple_func.eapprox f n).to_fun) = f :=
begin
  apply funext,
  intro a,
  rw supr_apply,
  rw ← @measure_theory.simple_func.supr_eapprox_apply α M f hf a,
  refl,
end


lemma supr_eapprox' {α:Type*} {M:measurable_space α} (f : α → ennreal) (hf : measurable f):
  (⨆ (n : ℕ), (⇑(measure_theory.simple_func.eapprox f n)):
             (α → ennreal))=(f:α → ennreal) :=
begin
  have A1:(λ (n : ℕ), (⇑(measure_theory.simple_func.eapprox f n)))=
          (λ (n : ℕ), ((measure_theory.simple_func.eapprox f n).to_fun)),
  {
    apply funext,
    intro n,
    rw simple_func_to_fun,
  },
  rw A1,
  rw supr_eapprox,
  apply hf,
end


lemma set_indicator_monotone {Ω:Type*} {g:ℕ → Ω → ennreal} {S:set Ω}:
  monotone g → monotone (λ n:ℕ, set.indicator S (g n)) :=
begin
  intro A1,
  intros n1 n2 A2,
  simp,
  intro ω,
  have A3:ω ∈ S ∨ ω ∉ S := classical.em (ω ∈ S),
  cases A3,
  {
    repeat {rw @set.indicator_of_mem Ω _ _ S ω A3},
    apply A1,
    apply A2,
  },
  {
    repeat {rw @set.indicator_of_not_mem Ω _ _ S ω A3},
    apply le_refl (0:ennreal),  
  },
end

def finset.filter_nonzero {α: Type*} [decidable_eq α] [has_zero α]
    (S:finset α):finset α :=
    S.filter (λ a:α, a ≠ 0)


def finset.mem_filter_nonzero {α: Type*} [decidable_eq α] [has_zero α]
    (S:finset α) (x:α):
    (x ∈ S.filter_nonzero) ↔ (x∈ S) ∧ (x ≠ 0) :=
begin
  unfold finset.filter_nonzero,
  rw finset.mem_filter,
end
  
lemma filter_nonzero_congr {S:finset ennreal} {f g:ennreal → ennreal}:
  (∀ x ≠ 0, f x = g x) → (S.filter_nonzero.sum f = S.filter_nonzero.sum g) :=
begin
  intro A1,
  rw finset.sum_congr,
  refl,
  intros x A2,
  apply A1,
  rw finset.mem_filter_nonzero at A2,
  apply A2.right,
end


lemma set_indicator_inter {Ω:Type*} 
    (f:Ω → ennreal) 
    {g:Ω → ennreal} {x y:ennreal}:
    (y ≠ 0) →
    (set.indicator (g ⁻¹' {x}) (f))⁻¹' {y} = 
    (g⁻¹' {x}) ∩ (f⁻¹' {y}) :=
begin
  intro A1,
  ext ω,
  split;intros B1;simp at B1;simp,
  {
    have C1:g ω = x ∨ g ω ≠ x := eq_or_ne,
    cases C1,
    {
      rw set.indicator_of_mem at B1,
      apply and.intro C1 B1,
      simp [C1],          
    },
    {
      exfalso,
      apply A1,
      rw set.indicator_of_not_mem at B1,
      symmetry,
      apply B1,
      simp [C1],  
    },
  },
  {
    rw set.indicator_of_mem,
    apply B1.right,
    simp [B1.left],
  },
end

lemma set_indicator_inter2 {Ω:Type*} {M:measurable_space Ω} 
    (f:measure_theory.simple_func Ω ennreal) 
    {g:measure_theory.simple_func Ω ennreal} {x y:ennreal}:
    (y ≠ 0) →
    (set.indicator (⇑g ⁻¹' {x}) (⇑f))⁻¹' {y} = 
    (g⁻¹' {x}) ∩ (f⁻¹' {y}) :=
begin
  apply set_indicator_inter,
end

/--
  A piece of a simple function. Every simple function is a finite sum of its
  pieces. Thus, operations that work on the pieces can often be extended to
  simple functions, and to measurable functions as well.
 -/
noncomputable def measure_theory.simple_func.piece {Ω:Type*} [measurable_space Ω]
  (g:measure_theory.simple_func Ω ennreal) (x:ennreal):
  measure_theory.simple_func Ω ennreal :=
  (measure_theory.simple_func.const Ω x).restrict (g.to_fun ⁻¹' {x})

lemma measure_theory.simple_func.piece_def {Ω:Type*} [measurable_space Ω]
  (g:measure_theory.simple_func Ω ennreal) (x:ennreal):
  g.piece x =
  (measure_theory.simple_func.const Ω x).restrict (g.to_fun ⁻¹' {x}) := rfl

lemma measure_theory.simple_func.piece_apply_of_eq {Ω:Type*} [measurable_space Ω]
  (g:measure_theory.simple_func Ω ennreal) (x:ennreal) (ω:Ω):
  (g ω = x) → 
  g.piece x ω = x := 
begin
  intro A1,
  rw measure_theory.simple_func.piece_def,
  rw measure_theory.simple_func.restrict_apply,
  rw if_pos,
  rw measure_theory.simple_func.const_apply,
  {
    rw simple_func_to_fun at A1,
    simp [A1],
  },
  apply g.is_measurable_fiber',
end


lemma measure_theory.simple_func.piece_apply_of_ne {Ω:Type*} [measurable_space Ω]
  (g:measure_theory.simple_func Ω ennreal) (x:ennreal) (ω:Ω):
  (g ω ≠ x) → 
  g.piece x ω = 0 := 
begin
  intro A1,
  rw measure_theory.simple_func.piece_def,
  rw measure_theory.simple_func.restrict_apply,
  rw if_neg,
  simp,
  rw simple_func_to_fun at A1,
  apply A1,
  apply g.is_measurable_fiber',
end


/--
  measure_theory.simple_func.to_fun is a homomorphism from simple functions to functions.
 -/
noncomputable def simple_func_to_fun_add_monoid_hom (Ω:Type*) [measurable_space Ω]:
  add_monoid_hom (measure_theory.simple_func Ω ennreal) (Ω → ennreal) := {
  to_fun := measure_theory.simple_func.to_fun,
  map_add' := begin
    intros x y,
    refl,
  end,
  map_zero' := rfl,
}

lemma simple_func_to_fun_add_monoid_hom_to_fun_def' {Ω:Type*} [M:measurable_space Ω] {g:measure_theory.simple_func Ω ennreal}:
  (simple_func_to_fun_add_monoid_hom Ω) g = g.to_fun := rfl


lemma measure_theory.simple_func.finset_sum_to_fun {β:Type*} 
  {Ω:Type*} [measurable_space Ω]
  (g:β → (measure_theory.simple_func Ω ennreal)) (S:finset β):
  ⇑(S.sum g) = (S.sum (λ b:β, (g b).to_fun)) :=
begin
  have A1:(λ b:β, (g b).to_fun) =
          ((λ b:β, (simple_func_to_fun_add_monoid_hom Ω) (g b))),
  {
    apply funext,
    intro b,
    rw simple_func_to_fun_add_monoid_hom_to_fun_def',
  },
  rw A1,
  clear A1,
  rw simple_func_to_fun,
  rw ← simple_func_to_fun_add_monoid_hom_to_fun_def',
  rw add_monoid_hom.map_sum,
end

/--
  The application of a function is a homomorphism.
 -/
def apply_add_monoid_hom {α:Type*} (β:Type*) [add_monoid β] (a:α):
  add_monoid_hom (α → β) β := {
  to_fun := (λ f:α → β, f a),
  map_add' := begin
    intros x y,
    refl,
  end,
  map_zero' := rfl,
}

lemma apply_add_monoid_hom_to_fun_def' {α β:Type*} [add_monoid β]
    {f:α → β} {a:α}:
  (apply_add_monoid_hom β a) f = f a := rfl

/--
  The application of a simple function is a homomorphism.
 -/
noncomputable def simple_func_apply_add_monoid_hom {Ω:Type*} [measurable_space Ω] (ω:Ω):
  add_monoid_hom (measure_theory.simple_func Ω ennreal) (ennreal) := {
  to_fun := (λ (g:measure_theory.simple_func Ω ennreal), g ω),
  map_add' := begin
    intros x y,
    refl,
  end,
  map_zero' := rfl,
}

lemma simple_func_apply_add_monoid_hom_apply_def {Ω:Type*} [M:measurable_space Ω] {g:measure_theory.simple_func Ω ennreal}
  {ω:Ω}:
  (@simple_func_apply_add_monoid_hom Ω M ω) g = g ω := rfl


lemma measure_theory.simple_func.finset_sum_apply {β:Type*} 
  {Ω:Type*} [measurable_space Ω]
  (g:β → (measure_theory.simple_func Ω ennreal)) (S:finset β) (ω:Ω):
  (S.sum g) ω = (S.sum (λ b:β, (g b ω))) :=
begin
  rw ← simple_func_apply_add_monoid_hom_apply_def,
  have A1:(λ (b : β), (⇑(simple_func_apply_add_monoid_hom ω):((measure_theory.simple_func Ω ennreal) → ennreal)) (g b)) = (λ (b : β), g b ω),
  {
    apply funext,
    intro b,
    rw ← simple_func_apply_add_monoid_hom_apply_def,
  },
  rw ← A1,
  rw add_monoid_hom.map_sum,
end

lemma measure_theory.simple_func.sum_piece {Ω:Type*} [measurable_space Ω]
  (g:measure_theory.simple_func Ω ennreal):
  g = g.range.sum (λ x:ennreal, g.piece x) :=
begin
  apply measure_theory.simple_func.ext,
  intro ω,
  rw @measure_theory.simple_func.finset_sum_apply,
  rw finset.sum_eq_single (g ω),
  {
    rw measure_theory.simple_func.piece_apply_of_eq,
    refl,
  },
  {
    intros ω2 A1 A2,
    rw measure_theory.simple_func.piece_apply_of_ne,
    symmetry,
    apply A2,
  },
  {
    intro A1,
    exfalso,
    apply A1,
    rw measure_theory.simple_func.mem_range,
    apply exists.intro ω,
    refl,
  },
end


lemma measure_theory.simple_func.const_preimage 
  {Ω:Type*} [measurable_space Ω] (x:ennreal):
  (measure_theory.simple_func.const Ω x) ⁻¹' {x} = set.univ :=
begin
  ext,
  split;intro B1;simp,
end

lemma measure_theory.simple_func.const_preimage_of_ne
  {Ω:Type*} [measurable_space Ω] (x y:ennreal):x ≠ y →
  (measure_theory.simple_func.const Ω x) ⁻¹' {y} = ∅ :=
begin
  intro A1,
  ext,
  split;intro B1;simp;simp at B1,
  {
    apply A1,
    apply B1,  
  },
  {
    exfalso,
    apply B1,
  },
end


lemma emptyset_of_not_nonempty {Ω:Type*} (S:set Ω):(¬(nonempty Ω)) → S = ∅ :=
begin
  intro A1,
  ext ω,split;intros A2;exfalso,
  {
    apply A1,
    apply nonempty.intro ω,
  },
  {
    apply A2,
  },
end

-- This lifts measure_theory.simple_func.restrict_const_lintegral
-- to measure_theory.lintegral.
lemma integral_const_restrict_def' {Ω:Type*} {M:measurable_space Ω} 
  (μ:measure_theory.measure Ω) (S:set Ω) (x:ennreal):(is_measurable S) →
  ∫⁻ (a : Ω), ((measure_theory.simple_func.const Ω x).restrict S) a ∂μ = 
  x * (μ S) :=
begin
  intro A1,
  rw measure_theory.simple_func.lintegral_eq_lintegral,
  rw measure_theory.simple_func.restrict_const_lintegral,
  apply A1,
end

lemma mul_restrict_def {Ω:Type*} {M:measurable_space Ω} (f:Ω → ennreal) (S:set Ω) (x:ennreal):(is_measurable S) →
    ((f * ⇑((measure_theory.simple_func.const Ω x).restrict S))) = 
    (λ ω:Ω, (x * (set.indicator S f ω))) := 
begin
  intro A1,
  apply funext,
  intro ω,
  simp,
  rw measure_theory.simple_func.restrict_apply,
  rw measure_theory.simple_func.const_apply,
  simp,
  rw mul_comm,
  apply A1,
end

lemma function_support_le_subset {Ω:Type*} {f g:Ω → ennreal}:
  f ≤ g → (function.support f) ⊆ (function.support g) :=
begin
  intro A1,
  rw set.subset_def,
  intros x B1,
  unfold function.support,
  unfold function.support at B1,
  simp at B1,
  simp,
  intro B2,
  apply B1,
  have B3 := A1 x,
  rw B2 at B3,
  have C1:⊥ = (0:ennreal) := rfl,
  rw ← C1 at B3,
  rw ← C1,
  rw ← le_bot_iff,
  apply B3,
end

lemma function_support_indicator_subset {Ω:Type*} {f:Ω → ennreal} {S:set Ω}:
  (function.support (S.indicator f)) ⊆ S :=
begin
  rw set.subset_def,
  intros x A1,
  unfold function.support at A1,
  simp at A1,
  unfold set.indicator at A1,
  cases (classical.em (x ∈ S)) with B1 B1,
  {
    apply B1,
  },
  {
    exfalso,
    apply A1,
    apply if_neg,
    apply B1,
  },
end


lemma indicator_le {Ω:Type*} {f:Ω → ennreal} {S:set Ω}:
  (S.indicator f) ≤ f :=
begin
  intro x,
  cases (classical.em (x ∈ S)) with A1 A1,
  {
     rw set.indicator_of_mem A1,
     apply le_refl _,
  },
  {
     rw set.indicator_of_not_mem A1,
     have B1:(0:ennreal) = ⊥ := rfl,
     rw B1,
     apply @bot_le ennreal _,
  },
end

lemma simple_func_restrict_of_is_measurable {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (g:measure_theory.simple_func Ω ennreal) (S:set Ω) (H:is_measurable S):
(g.restrict S)=measure_theory.simple_func.piecewise S H g 0 :=
begin
  unfold measure_theory.simple_func.restrict,
  rw dif_pos,
end

lemma simple_func_piecewise_range_subset {Ω:Type*} {M:measurable_space Ω} (f g:measure_theory.simple_func Ω ennreal) (S:set Ω) (H:is_measurable S):
(measure_theory.simple_func.piecewise S H f g).range ⊆ (f.range ∪ g.range) :=
begin
  rw finset.subset_iff,
  intros x B1,
  rw measure_theory.simple_func.mem_range at B1,
  rw finset.mem_union,
  rw measure_theory.simple_func.mem_range,
  rw measure_theory.simple_func.mem_range,
  rw measure_theory.simple_func.coe_piecewise at B1,
  rw set.mem_range at B1,
  cases B1 with ω B1,
  cases (classical.em (ω ∈ S)) with B2 B2,
  {
    left,
    rw set.piecewise_eq_of_mem at B1,
    rw set.mem_range,
    apply exists.intro ω B1,
    apply B2,
  },
  {
    right,
    rw set.piecewise_eq_of_not_mem at B1,
    rw set.mem_range,
    apply exists.intro ω B1,
    apply B2,
  },
end

/--
  If we sum over the superset of a simple function, it is still equal to the 
  original lintegral.
 -/
lemma measure_theory.simple_func.lintegral_eq_of_range_subset {Ω:Type*} {M:measurable_space Ω} {f:measure_theory.simple_func Ω ennreal} {μ:measure_theory.measure Ω} {S:finset ennreal}:
  f.range ⊆ S →
  f.lintegral μ = S.sum (λ x:ennreal, x * μ (f ⁻¹' {x})) := 
begin
  intros A1,
  apply @measure_theory.simple_func.lintegral_eq_of_subset Ω M,
  intros x B1 B2,
  rw finset.subset_iff at A1,
  apply A1,
  apply @measure_theory.simple_func.mem_range_of_measure_ne_zero Ω ennreal M f _ μ,
  apply B2,
end

lemma simple_func_piecewise_preimage {Ω:Type*} {M:measurable_space Ω}
    (f g:measure_theory.simple_func Ω ennreal) (S:set Ω) (H:is_measurable S) (T:set ennreal):
    (measure_theory.simple_func.piecewise S H f g) ⁻¹' T  =
    (S ∩ (f ⁻¹' T)) ∪ ((Sᶜ) ∩ (g ⁻¹' T)) := 
begin
  rw measure_theory.simple_func.coe_piecewise,
  rw set.piecewise_preimage,
end


lemma simple_func_piecewise_integral {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f g:measure_theory.simple_func Ω ennreal) (S:set Ω) (H:is_measurable S):
(measure_theory.simple_func.piecewise S H f g).lintegral μ  =
 f.lintegral (μ.restrict S)  + g.lintegral (μ.restrict Sᶜ) := 
begin
  let Z := (f.range ∪ g.range),
  begin
    have B1:Z = (f.range ∪ g.range) := rfl,
    have C1:f.range ⊆ Z,
    {
      rw B1,
      apply finset.subset_union_left,
    },
    have C2:g.range ⊆ Z,
    {
      rw B1,
      apply finset.subset_union_right,
    },
    have C3:(measure_theory.simple_func.piecewise S H f g).range ⊆ Z,
    {
      rw B1,
      apply simple_func_piecewise_range_subset,
    },
    rw measure_theory.simple_func.lintegral_eq_of_range_subset C1,
    rw measure_theory.simple_func.lintegral_eq_of_range_subset C2,
    rw measure_theory.simple_func.lintegral_eq_of_range_subset C3,
    rw ← finset.sum_add_distrib,
    have D1:(λ (x : ennreal), x * μ (⇑(measure_theory.simple_func.piecewise S H f g) ⁻¹' {x})) =
        (λ (x : ennreal), x * (μ.restrict S) (⇑f ⁻¹' {x}) + x * (μ.restrict Sᶜ) (⇑g ⁻¹' {x})),
    {
      apply funext,
      intros x,
      rw simple_func_piecewise_preimage,
      have D1A:μ (⇑f ⁻¹' {x} ∩ S ∪ ⇑g ⁻¹' {x} ∩ Sᶜ) =
       μ (⇑f ⁻¹' {x} ∩ S) + μ (⇑g ⁻¹' {x} ∩ Sᶜ),
      {
        apply measure_theory.measure_union,
        apply set.disjoint_inter_compl,
        apply is_measurable.inter,
        apply f.is_measurable_fiber',
        apply H,
        apply is_measurable.inter,
        apply g.is_measurable_fiber',
        apply is_measurable.compl,
        apply H,
      },
      rw set.inter_comm,
      rw set.inter_comm Sᶜ,
      rw D1A,
      rw measure_theory.measure.restrict_apply,
      rw measure_theory.measure.restrict_apply,
      rw left_distrib,
      apply g.is_measurable_fiber',
      apply f.is_measurable_fiber',
    },
    rw D1,
  end
end


lemma simple_func_integral_restrict {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (g:measure_theory.simple_func Ω ennreal) (S:set Ω):
 (is_measurable S) →
(g.restrict S).lintegral μ = g.lintegral (μ.restrict S) := 
begin
  intro A1,
  rw simple_func_restrict_of_is_measurable μ g S A1,
  rw simple_func_piecewise_integral,
  rw measure_theory.simple_func.zero_lintegral,
  rw add_zero,
end


lemma simple_func_integral_restrict' {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (g:measure_theory.simple_func Ω ennreal) (S:set Ω):
 (is_measurable S) →
 (function.support g⊆ S) →
g.lintegral μ = g.lintegral (μ.restrict S) :=
begin
  intros A1 A2,
  rw ← simple_func_integral_restrict,
  have B1:g.restrict S = g,
  {
    apply measure_theory.simple_func.ext,
    intro ω,
    rw measure_theory.simple_func.restrict_apply,
    cases (classical.em (ω ∈ S)) with B1A B1A,
    {
      rw if_pos,
      apply B1A,
    },
    {
      rw if_neg,
      unfold function.support at A2,
      rw set.subset_def at A2,
      have B1B := A2 ω,
      apply classical.by_contradiction,
      intro B1C,
      apply B1A,
      apply B1B,
      simp,
      intro B1D,
      apply B1C,
      rw B1D,
      apply B1A,
    },
    apply A1,
  },
  rw B1,
  apply A1,
end

--Prefer measure_theory.with_density_apply
lemma measure_theory.with_density_apply2' {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (S:set Ω):(is_measurable S) →
    (μ.with_density f) S = (∫⁻ a:Ω, (set.indicator S f) a ∂ μ) :=
begin
  intro A1,
  rw measure_theory.with_density_apply f A1,
  rw measure_theory.lintegral_indicator,
  apply A1,
end


/--
  This is compose_eq_multiply on a restricted constant.
  This is the first step to proving compose_eq_multiply
  A key question is whether measurability is required (H).
 -/
lemma measure_theory.simple_func.restrict.compose_eq_multiply {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (H:measurable f) (S:set Ω) (x:ennreal):
    is_measurable S →
    ((measure_theory.simple_func.const Ω x).restrict S).lintegral (μ.with_density f)
    = (∫⁻ a:Ω, (f * ⇑((measure_theory.simple_func.const Ω x).restrict S)) a ∂ μ) :=
begin
  intro A1,
  rw measure_theory.simple_func.restrict_const_lintegral,
  rw measure_theory.with_density_apply2',
  rw mul_restrict_def,
  rw measure_theory.lintegral_const_mul,
  apply measurable.indicator,
  apply H,
  apply A1,
  apply A1,
  repeat {apply A1},  
end

/--
  This is the closest thing to compose_eq_multiply on a piece.
 -/
lemma measure_theory.simple_func.piece.compose_eq_multiply {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (H:measurable f) {g:measure_theory.simple_func Ω ennreal} (x:ennreal):
    (g.piece x).lintegral (μ.with_density f)
    = (∫⁻ a:Ω, (f * ⇑(g.piece x)) a ∂ μ) :=
begin
  rw measure_theory.simple_func.piece_def,
  rw measure_theory.simple_func.restrict.compose_eq_multiply,
  apply H,
  apply g.is_measurable_fiber',
end

lemma with_density.zero {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω):
    (μ.with_density 0) = 0 :=
begin
  apply measure_theory.measure.ext,
  intros S A1,
  rw measure_theory.with_density_apply2',
  {
    simp,
  },
  {
    apply A1,
  }
end

--TODO: Add to mathlib if novel.
lemma finset.sum_measurable {β:Type*} {Ω:Type*} {M:measurable_space Ω}
    (f:β → Ω → ennreal) (S:finset β):(∀ b∈ S, measurable (f b)) →
     measurable (S.sum f) :=
begin
  have A1:decidable_eq β := classical.decidable_eq β,
  apply @finset.induction_on β _ A1 S,
  {
    intro A2,
    rw finset.sum_empty,
    have A3:(λ ω:Ω, (0:ennreal)) = (0:Ω → ennreal) := rfl,
    rw ← A3,
    apply measurable_const,
  },
  {
    intros b S2 B1 B2 B3,
    rw finset.sum_insert,
    apply measurable.ennreal_add,
    apply B3,
    simp,
    apply B2,
    intros b2 B4,
    apply B3,
    simp,
    right,
    apply B4,
    apply B1, 
  },
end


lemma finset.sum_measurable' {β:Type*} {Ω:Type*} {M:measurable_space Ω}
    (f:β → Ω → ennreal) (S:finset β):(∀ b∈ S, measurable (f b)) →
     measurable (λ a:Ω, (S.sum (λ b:β, f b a))) :=
begin
  intros A1,
  have B1:(λ a:Ω, (S.sum (λ b:β, f b a))) = (S.sum f),
  {
    apply funext,
    intro a,
    rw finset.sum_apply,    
  },
  rw B1,
  apply finset.sum_measurable,
  apply A1,
end

--  Because we need an additional constraint, this cannot be handled with
--  add_monoid_hom.

lemma finset.sum_integral' {β:Type*} {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:β → Ω → ennreal) (S:finset β):
  (∀ b∈S, measurable  (f b)) →  
  S.sum (λ b,(∫⁻ a:Ω, (f b a) ∂ μ)) =
  (∫⁻ a:Ω, (S.sum f) a ∂ μ) := 
begin
  have A1:decidable_eq β := classical.decidable_eq β,
  apply @finset.induction_on β _ A1 S,
  {
    rw finset.sum_empty,
    rw finset.sum_empty,
    simp,
  },
  {
    intros b S2 A2 A3 A4,
    rw finset.sum_insert,
    rw A3,
    rw finset.sum_insert,
    simp,
    rw measure_theory.lintegral_add,
    {
      apply A4,
      simp,
    },
    {
      apply finset.sum_measurable',
      intros b2 A5,
      apply A4,
      simp [A5],
    },
    {
      apply A2,
    },
    {
      intros b A5,
      apply A4,
      simp [A5],
    },
    {
      apply A2,
    },
  },
end

noncomputable def simple_func_lintegral_add_monoid_hom {Ω:Type*} [measurable_space Ω] (μ:measure_theory.measure Ω):
  add_monoid_hom (measure_theory.simple_func Ω ennreal) ennreal := {
  to_fun := λ f:(measure_theory.simple_func Ω ennreal), f.lintegral μ,
  map_add' := begin
    intros x y,
    rw measure_theory.simple_func.add_lintegral,
  end,
  map_zero' := begin
    rw measure_theory.simple_func.zero_lintegral,
  end
}

/-
lemma measure_theory.simple_func.finset_sum_to_fun {β:Type*} 
  {Ω:Type*} [measurable_space Ω]
  (g:β → (measure_theory.simple_func Ω ennreal)) (S:finset β):
  ⇑(S.sum g) = (S.sum (λ b:β, (g b).to_fun)) :=
begin
  have A1:(λ b:β, (g b).to_fun) =
          ((λ b:β, (simple_func_to_fun_add_monoid_hom Ω) (g b))),
  {
    apply funext,
    intro b,
    rw simple_func_to_fun_add_monoid_hom_to_fun_def',
  },
  rw A1,
  clear A1,
  rw simple_func_to_fun,
  rw ← simple_func_to_fun_add_monoid_hom_to_fun_def',
  rw add_monoid_hom.map_sum,
end
-/

lemma finset.sum_integral_simple_func'' {β:Type*} {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:β → (measure_theory.simple_func Ω ennreal)) (S:finset β):
  S.sum (λ b, (f b).lintegral μ) =
  (S.sum f).lintegral μ := 
begin
  have A2:(λ b, (f b).lintegral μ) = (λ b, (simple_func_lintegral_add_monoid_hom μ) (f b)),
  {
    apply funext,
    intro b,
    refl,
  },
  rw A2,
  have A3:(S.sum f).lintegral μ = (simple_func_lintegral_add_monoid_hom μ) (S.sum f) := rfl,
  rw A3,
  rw add_monoid_hom.map_sum,
end



--TODO:If novel, add to finset.sum?
lemma finset.sum_distrib {α:Type*} {β:Type*} [comm_semiring β] {f:β} {g:α → β} 
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


lemma measure_theory.simple_func.compose_eq_multiply {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) 
  (f:Ω → ennreal) (H:measurable f) {g:measure_theory.simple_func Ω ennreal}:
    g.lintegral (μ.with_density f) = ∫⁻ a, (f * ⇑g) a ∂ μ :=
begin
  have D1:∀ g2 g3:measure_theory.simple_func Ω ennreal,
           g2 = g3 → 
         g2.lintegral (μ.with_density f) = g3.lintegral (μ.with_density f), 
  {
    intros g2 g3 A1A,
    rw A1A,
  }, 

  rw D1 g (finset.sum (measure_theory.simple_func.range g) (λ (x : ennreal), measure_theory.simple_func.piece g x)) (measure_theory.simple_func.sum_piece g),

  rw ← finset.sum_integral_simple_func'',
  have A1A:(λ (b : ennreal), (measure_theory.simple_func.piece g b).lintegral (μ.with_density f)) =
     (λ b, ∫⁻ a:Ω, (f * ⇑(measure_theory.simple_func.piece g b)) a ∂ μ),
  {
    apply funext,
    intro x,
    rw measure_theory.simple_func.piece.compose_eq_multiply,
    apply H,
  },
  rw A1A,
  clear A1A,
  rw finset.sum_integral',
  
  rw @finset.sum_distrib ennreal (Ω → ennreal),
  have A3:
      (@finset.sum ennreal (Ω → ennreal) _ g.range
           (λ (a : ennreal), (⇑(measure_theory.simple_func.piece g a):Ω → ennreal))) = (⇑g:Ω → ennreal),
  {
    have A3A:(λ (a:ennreal), ⇑(measure_theory.simple_func.piece g a)) =
        (λ (a:ennreal), (measure_theory.simple_func.piece g a).to_fun),
    {
      apply funext,
      intro x,
      rw simple_func_to_fun,
    },
    rw A3A,
    rw ← @measure_theory.simple_func.finset_sum_to_fun ennreal Ω M
         g.piece g.range,
    symmetry,
    have A3B:∀ g2 g3:measure_theory.simple_func Ω ennreal,
             g2 = g3 →
             (g2:Ω → ennreal) = (g3:Ω → ennreal),
    {
      intros g2 g3 A1,
      rw A1,
    },
    
    rw A3B,
    apply @measure_theory.simple_func.sum_piece Ω M g,
  },
  rw A3,
  intros b B1,
  apply measurable.ennreal_mul,
  apply H,
  apply (g.piece b).measurable,
end

lemma supr_const_mul {Ω:Type*} {k:ennreal} {g:Ω → ennreal}:
  supr (λ n:Ω, k * (g n)) = k * (supr g) := 
begin
  apply le_antisymm,
  {
    simp,
    intro ω,
    apply ennreal.mul_le_mul,
    apply le_refl k,
    apply le_supr g,
  },
  {
    have A1:k = 0 ∨ k ≠ 0 := eq_or_ne,
    cases A1,
    {
      subst k,
      simp,
    },
    have A3:supr g = 0 ∨ supr g ≠ 0 := eq_or_ne,
    cases A3,
    {
      rw A3,
      rw ennreal.supr_zero_iff_zero at A3,
      rw A3,
      simp,
    },
    have A4:(∃ ω:Ω, g ω ≠ 0),
    {
      apply classical.exists_not_of_not_forall,
      intro contra,
      apply A3,
      rw ennreal.supr_zero_iff_zero,
      apply funext,
      intro ω,
      simp,
      apply contra,
    },
    cases A4 with ω A4,
    have A5:k = ⊤ ∨ k ≠ ⊤ := eq_or_ne,
    cases A5,
    {
      subst k,
      rw with_top.top_mul A3,
      have A3A:⊤ * (g ω) ≤ ⨆ (n : Ω), ⊤ * g n,
      {
        apply le_supr (λ ω:Ω, ⊤ * g ω),
      },
      rw with_top.top_mul A4 at A3A,
      apply A3A,
    },
    rw mul_comm,
    rw ← ennreal.le_div_iff_mul_le,
    simp,
    intro ω,
    rw ennreal.le_div_iff_mul_le,
    rw mul_comm,
    apply le_supr (λ (ω:Ω), k * g ω),
    apply (or.inl A1),
    apply (or.inl A5),
    apply (or.inl A1),
    apply (or.inl A5),
  },
end


lemma supr_fn_const_mul {α Ω:Type*} {f:Ω → ennreal} {g:α → Ω → ennreal}:
  supr (λ n:α, f * (g n)) = f * (supr g) := 
begin
  apply funext,
  intro ω,
  rw supr_apply,
  simp,
  rw supr_apply,
  apply @supr_const_mul α (f ω) (λ i:α, g i ω),
end

lemma monotone_fn_const_mul {α Ω:Type*} [preorder α] {f:Ω → ennreal} {g:α → Ω → ennreal}:
  monotone g → monotone (λ n:α, f * (g n)) := 
begin
  intros A1 α1 α2 A2,
  rw le_func_def2,
  intro ω,
  simp,
  apply ennreal.mul_le_mul,
  apply le_refl (f ω),
  apply A1,
  apply A2,
end

lemma measure_theory.with_density.compose_eq_multiply' {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f g:Ω → ennreal) (H:measurable f) (H2:measurable g):
 ∫⁻ a, g a ∂ (μ.with_density f)  =  ∫⁻ a,(f * g) a ∂ μ :=
begin
  have A1:∫⁻ a, g a ∂ (μ.with_density f) =
          supr (λ n:ℕ, ∫⁻ (a : Ω), (measure_theory.simple_func.eapprox g n) a ∂ (μ.with_density f)),
  {
    rw ← measure_theory.lintegral_supr2,
    rw supr_eapprox',
    apply H2,
    intro n,
    apply (measure_theory.simple_func.eapprox g n).measurable,
    apply measure_theory.simple_func.monotone_eapprox,
  },
  rw A1,
  clear A1,
  have A2:(λ n:ℕ, ∫⁻ (a : Ω), (measure_theory.simple_func.eapprox g n) a ∂ (μ.with_density f))
        = (λ n:ℕ, ∫⁻ (a : Ω), (f * (measure_theory.simple_func.eapprox g n)) a ∂ μ),
  {
    apply funext,
    intro n,
    rw measure_theory.simple_func.lintegral_eq_lintegral,
    rw measure_theory.simple_func.compose_eq_multiply,
    apply H,
  },
  rw A2,
  clear A2,
  rw ← measure_theory.lintegral_supr2,
  have A3:(⨆ (n : ℕ), f * ⇑(measure_theory.simple_func.eapprox g n)) = (f * g),
  {
    rw supr_fn_const_mul,
    rw supr_eapprox',
    apply H2,
  },
  rw A3,
  intro n,
  apply measurable.ennreal_mul,
  apply H,
  apply measure_theory.simple_func.measurable,
  apply monotone_fn_const_mul,
  apply measure_theory.simple_func.monotone_eapprox,
end

