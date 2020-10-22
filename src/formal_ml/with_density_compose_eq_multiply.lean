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
--import formal_ml.with_density_compose_eq_multiply_part_one
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

lemma nat.one_le_iff_zero_lt {a:ℕ}:1 ≤ a ↔ 0 < a :=
begin
  rw ← nat.succ_le_iff_lt,
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
    have B1:(int.succ 0) = 1 := rfl,
    rw ← B1,
    rw @int.succ_le_iff 0 q.num,
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
    rw ← nnreal.coe_le_coe at A1,    
    linarith [A1],
  },
  {
    simp only [not_le] at B1,
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

lemma ennreal.le_of_add_le_add_right 
    {a b c:ennreal}:(c < ⊤)→
   (a + c ≤ b + c) → (a ≤ b) :=
begin
  rw add_comm a c,
  rw add_comm b c,
  apply ennreal.le_of_add_le_add_left
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

--Used once in hahn.lean.
lemma ennreal.sub_add_sub {a b c:ennreal}:c ≤ b → b ≤ a → (a - b) + (b - c) = a - c :=
begin
  cases c;cases b;cases a;try {simp},
  repeat {rw ← ennreal.coe_sub <|> rw ← ennreal.coe_add <|> rw ennreal.coe_eq_coe},
  apply nnreal.sub_add_sub,
end



------ Measure theory --------------------------------------------------------------------------



--Used EVERYWHERE.
lemma measure.apply {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω)  (S:set Ω):
    μ S = μ.to_outer_measure.measure_of S :=
begin
  refl
end


--Use in hahn.lean
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


--Used in hahn.lean
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

--Used all over.
--Prefer measure_theory.with_density_apply
lemma measure_theory.with_density_apply2' {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) (f:Ω → ennreal) (S:set Ω):(is_measurable S) →
    (μ.with_density f) S = (∫⁻ a:Ω, (set.indicator S f) a ∂ μ) :=
begin
  intro A1,
  rw measure_theory.with_density_apply f A1,
  rw measure_theory.lintegral_indicator,
  apply A1,
end

--Move to Radon-Nikodym (?)
lemma with_density.zero {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω):
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
