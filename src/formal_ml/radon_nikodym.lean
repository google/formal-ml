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
import formal_ml.integral
import formal_ml.int

--This file represents the first part of proving the Radon-Nikodym theorem.
--All theorems in this file are complete.
--A second file, radon_nikodym_part_two.lean, consists of theorems and
--proofs in a variety of stages.
--When the theorems are more stable, I will bring them to this file.


-- set complement symbol:ᶜ
-- sum:∑ (now ∑') 
-- sigma-type:Σ
-- pi-type:Π
-- prod:∏
-- infimum of a function: ⨅
-- binary inf operator:⊓


------------------------Core theorems---------------------------------------

lemma lt_of_not_le {α:Type*} [linear_order α] {a b:α}:
   ¬(a ≤ b) → (b < a) :=
begin
  intros A1,
  have A2 := lt_trichotomy a b,
  cases A2,
  {
    exfalso, 
    apply A1,
    apply le_of_lt A2,
  },
  cases A2,
  {
    exfalso,
    apply A1,
    subst a,
  },
  {
    apply A2,
  },
end

lemma not_le_iff_lt {α : Type*} [linear_order α] {a b : α}:
   ¬a ≤ b ↔ b < a :=
begin
  split;intro A1,
  {
    apply lt_of_not_le A1,
  },
  {
    apply not_le_of_lt A1,
  },
end



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



------------------------Theorems of sets------------------------------------

lemma set.eq_empty_elim {α:Type*} {S:set α} {a:α}:S = ∅ → a ∉ S :=
begin
  intro A1,
  subst S,
  simp,
end



lemma set.nonempty_iff_ne_empty {α:Type*} {S:set α}:S.nonempty ↔ (S ≠ ∅) := 
begin
  split;intros A1,
  {
    apply set.nonempty.ne_empty A1,
  },
  {
    cases (@empty_or_nonempty α S) with C1 C1,
    {
      apply C1,
    },
    {
      exfalso,
      apply A1,
      apply C1,
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
  apply lt_of_not_le,
  rw ← not_le_iff_lt at A1,
  intro A2,
  apply A1,
  apply rat.nonpos_of_num_nonpos A2,
end

lemma rat.pos_iff_num_pos {q:ℚ}:0 < q ↔ 0 < q.num :=
begin
  split;intro A1,
  {
    apply lt_of_not_le,
    rw ← not_le_iff_lt at A1,
    intro A2,
    apply A1,
    apply rat.nonpos_of_num_nonpos A2,
  },
  {
    apply lt_of_not_le,
    rw ← not_le_iff_lt at A1,
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


lemma rat.coe_int_div {p q:ℤ}:rat.mk p q = (p:ℚ) / (q:ℚ) :=
begin
  --rw rat.coe_int_eq_mk,
  --rw rat.coe_int_eq_mk,
  rw rat.div_num_denom,
  repeat {rw rat.coe_int_num},
  repeat {rw rat.coe_int_denom},
  have A1:((1:ℕ):ℤ)=1 := rfl,
  rw A1,
  simp,
end

------------------------Theorems of real ---------------------------------------------

lemma real.add_sub_add_eq_sub_add_sub {a b c d:real}:
    a + b - (c + d) = (a - c) + (b - d) :=
begin
  rw add_sub_assoc,
  rw sub_add_eq_sub_sub_swap,
  rw sub_add_eq_add_sub,
  rw add_sub_assoc,
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


lemma real.sub_lt_sub_of_lt {a b c:real}:a < b →
  a - c < b - c :=
begin
  intros A1,
  simp,
  apply A1,
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
  have A2:((a:ℝ)-(b:ℝ))+(b:ℝ)=(c:ℝ)+(b:ℝ),
  {
    rw A1,
  },
  simp at A2,
  rw add_comm at A2,
  apply A2,
end



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
  rw upper_bounds_def at A1,
  simp at A1,
  have A3 := A1 A2,
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
  apply lt_of_not_le,
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
    have A5:= set.contains_of_nonempty A2,
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

lemma measurable_set_indicator {Ω:Type*} {M:measurable_space Ω} (s:set Ω) (f:Ω → ennreal):
  (is_measurable s) → 
  (measurable f) →
  measurable (set.indicator s f) :=
begin
  intros A1 A2,
  unfold set.indicator,
  apply measurable.if,
  apply A1,
  apply A2,
  apply measurable_const,
end


lemma filter.has_mem_def {α : Type*} (S:set α) (F:filter α):
  S ∈ F = (S∈ F.sets) := rfl


def finset.Union {α:Type*} [decidable_eq α] (S:finset (finset α)):finset α :=
  @finset.fold (finset α) (finset α)  (@has_union.union (finset α) _) _
  _ ∅ id S


lemma finset.Union_insert {α:Type*} [decidable_eq α] (S:finset (finset α)) {T:finset α}:(T∉ S) → finset.Union (insert T S) = T ∪ (finset.Union S) :=
begin
  intro A1,
  unfold finset.Union,
  rw finset.fold_insert A1,
  simp,
end


lemma finset.subset_Union {α:Type*} [decidable_eq α] {S:finset (finset α)} {T:finset α}:T ∈ S → T ⊆ (finset.Union S) := 
begin
  apply finset.induction_on S,
  {
    intros A1,
    exfalso,
    simp at A1,
    apply A1,
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
    apply A1,
  },
end


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


lemma lintegral_tsum2 {α β:Type*} [M:measure_theory.measure_space α] 
  [E:encodable β] [Dα:decidable_eq α] {f : β → α → ennreal} (hf : ∀i, measurable (f i)) :
  (measure_theory.lintegral M.volume ∑' i, f i ) = (∑' i, measure_theory.lintegral M.volume (f i)) :=
begin
  begin
    have A0:(∑' i, f i) = λ a:α, ∑' (i:β), f i a,
    {
      have A0A:decidable_eq β,
      {
        apply encodable.decidable_eq_of_encodable,
      },
      apply @tsum_fn β α A0A,
    },
    have A1:(∫⁻ (a : α), ∑' (i : β), f i a) = (measure_theory.lintegral M.volume  ∑' i, f i ),
    {
      rw A0,    
    },
    rw ← A1,
    apply @measure_theory.lintegral_tsum α β (M.to_measurable_space) (M.volume) E f,
    apply hf,
  end
end


lemma integral_tsum {α β:Type*} [measurable_space α] {μ:measure_theory.measure α} 
  [E:encodable β] {f : β → α → ennreal} (hf : ∀i, measurable (f i)) :
  (μ.integral  ∑' i, f i ) = (∑' i, μ.integral (f i)) :=
begin
  let M:measure_theory.measure_space α := {volume := μ},
  begin
    unfold measure_theory.measure.integral,
    have A1:decidable_eq α := classical.decidable_eq α,
    apply @lintegral_tsum2 α β M E A1 f,
    apply hf,
  end
end


lemma monotone_convergence_for_series {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:ℕ → Ω → ennreal):(∀ n, measurable (f n)) →
  μ.integral (∑' n:ℕ, f n) = ∑' n:ℕ, μ.integral (f n) :=
begin
  intro A1,
  apply integral_tsum,
  apply A1,
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



lemma  measure_theory.lintegral_supr2 {α : Type*} 
    [M : measure_theory.measure_space α] {f : ℕ → α → ennreal}:
    (∀ (n : ℕ), measurable (f n)) → 
    monotone f → 
    ((measure_theory.lintegral (M.volume) (⨆ (n : ℕ), f n)) = 
    ⨆ (n : ℕ), measure_theory.lintegral (M.volume) (f n)) :=
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

lemma measure_theory.integral_supr {Ω : Type*} {M:measurable_space Ω}
  {μ:measure_theory.measure Ω} {f : ℕ → Ω → ennreal}:
  (∀ (n : ℕ), measurable (f n)) → monotone f → 
((μ.integral (⨆ (n : ℕ), f n)) = ⨆ (n : ℕ), μ.integral (f n)) :=
begin
  intros A1 A2,
  unfold measure_theory.measure.integral,
  rw @measure_theory.lintegral_supr2 Ω {volume := μ} f,
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
  rw has_le_fun_def,
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



lemma integral_simple_func_def {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (g:measure_theory.simple_func Ω ennreal):
  μ.integral g = @measure_theory.simple_func.lintegral _ M g μ := 
begin
  unfold measure_theory.measure.integral,
  rw measure_theory.simple_func.lintegral_eq_lintegral,
end


lemma measure_of_measure_space {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω):({volume := μ}:measure_theory.measure_space Ω).volume = μ := rfl



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
  


lemma finset.sum_eq_sum_of_filter_nonzero {α : Type*} {β : Type*}
    [canonically_ordered_add_monoid β] 
    {s₁ s₂: finset α} {f : α → β}:
    (∀ (x : α), (x ∈ s₁ ∧ f x ≠ 0) → x ∈ s₂) → 
    s₂ ⊆ s₁ → 
    finset.sum s₁ f = finset.sum s₂ f :=
begin
 intros A1 A2,
 apply le_antisymm,
 {
   apply finset.sum_le_sum_of_ne_zero,
   intros x B1 B2,
   apply A1,
   apply and.intro B1 B2,
 },
 {
   apply finset.sum_le_sum_of_subset,
   apply A2,
 },
end


lemma integral_simple_func_def2 {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (g:measure_theory.simple_func Ω ennreal):
  μ.integral g = finset.sum (measure_theory.simple_func.range g)
       (λ x:ennreal, x * μ.to_outer_measure.measure_of (g.to_fun ⁻¹'  {x})) :=
begin
  rw integral_simple_func_def,
  unfold measure_theory.simple_func.lintegral,
  have A2:(λ (x : ennreal), x * (μ  (⇑g ⁻¹' {x})))=
      (λ x:ennreal, x * μ.to_outer_measure.measure_of (g.to_fun ⁻¹'  {x})),
  {
    apply funext,
    intro x,
    rw measure.apply,
    rw simple_func_to_fun,
  },
  rw A2,
end


lemma integral_simple_func_def3 {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (g:measure_theory.simple_func Ω ennreal):
  μ.integral g = finset.sum (measure_theory.simple_func.range g).filter_nonzero
       (λ x:ennreal, x * μ.to_outer_measure.measure_of (g.to_fun ⁻¹'  {x})) :=
begin
  rw ← @finset.sum_eq_sum_of_filter_nonzero ennreal ennreal _
       (measure_theory.simple_func.range g),
  rw integral_simple_func_def2,
  {
    intros x A1,
    rw finset.mem_filter_nonzero,
    split,
    apply A1.left,
    intro contra,
    apply A1.right,
    rw contra,
    simp,
  },
  {
    unfold finset.filter_nonzero,
    apply finset.filter_subset,
  },
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


lemma integral_const_restrict_def {Ω:Type*} {M:measurable_space Ω} 
  (μ:measure_theory.measure Ω) (S:set Ω) (x:ennreal):(is_measurable S) →
  μ.integral ((measure_theory.simple_func.const Ω x).restrict S) = 
  x * (μ.to_outer_measure.measure_of S) :=
begin
  intro A1,
  rw integral_simple_func_def,
  rw measure_theory.simple_func.restrict_const_lintegral,
  rw measure.apply,
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


lemma measure_theory.integral_mul_const {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (H:measurable f) (x:ennreal):
  x * μ.integral f = μ.integral (λ ω:Ω, x * (f ω)) :=
begin
  unfold measure_theory.measure.integral,
  rw measure_theory.lintegral_const_mul,
  simp [H],
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
        apply disjoint_inter_compl',
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



--This just lifts measure_theory.lintegral_indicator.
lemma integral_set_indicator {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (S:set Ω):(is_measurable S) →
  (μ.integral (set.indicator S f)) = (μ.restrict S).integral f :=
begin
  intro A1,
  unfold measure_theory.measure.integral,
  rw measure_theory.lintegral_indicator,
  apply A1,
end


lemma measure_theory.with_density_apply2 {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (S:set Ω):(is_measurable S) →
    (μ.with_density f) S = (μ.integral (set.indicator S f)) :=
begin
  intro A1,
  rw measure_theory.with_density_apply f A1,
  rw integral_set_indicator,
  unfold measure_theory.measure.integral,
  --apply H,
  apply A1,
end




lemma measure_theory.with_density_apply3 {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (S:set Ω):(is_measurable S) →
    (μ.with_density f).to_outer_measure.measure_of S = (μ.integral (set.indicator S f)) :=
begin
  intro A1,
  rw ← measure_theory.with_density_apply2,
  refl,
  --apply H,
  apply A1,
end


lemma integral_measure.apply3 {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (H:measurable f) (S:set Ω):(is_measurable S) →
    (μ.with_density f).to_outer_measure.measure_of S = supr (λ n, (μ.integral (set.indicator S (measure_theory.simple_func.eapprox f n)))) :=
begin
  intro A1,
  rw measure_theory.with_density_apply3,
  rw ← @measure_theory.integral_supr Ω M μ,
  rw ← supr_indicator,
  have C1:(λ (n : ℕ), ⇑(measure_theory.simple_func.eapprox f n))=
          (λ (n : ℕ), (measure_theory.simple_func.eapprox f n).to_fun),
  {
    ext,
    rw simple_func_to_fun,
  },
  rw C1,
  clear C1,
  rw supr_eapprox,
  apply H,
  {
    intro n,
    apply measurable_set_indicator,
    apply A1,
    apply measure_theory.simple_func.measurable,
  },
  {
    apply set_indicator_monotone,
    apply measure_theory.simple_func.monotone_eapprox,
  },
  --apply H,
  apply A1,
end


lemma integral_measure_restrict_def {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (H:measurable f) (S:set Ω) (x:ennreal):
    is_measurable S →
    (μ.with_density f).integral ((measure_theory.simple_func.const Ω x).restrict S) 
    = μ.integral (f * ⇑((measure_theory.simple_func.const Ω x).restrict S)) :=
begin
  intro A1,
  rw integral_const_restrict_def,
  rw measure_theory.with_density_apply3,
  rw mul_restrict_def,
  rw measure_theory.integral_mul_const,
  apply measurable_set_indicator,
  apply A1,
  apply H,
  apply A1,
  repeat {apply A1},
end

lemma integral_measure_piece_def {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (H:measurable f) {g:measure_theory.simple_func Ω ennreal} (x:ennreal):
    (μ.with_density f).integral (g.piece x)
    = μ.integral (f * ⇑(g.piece x)) :=
begin
  rw measure_theory.simple_func.piece_def,
  rw integral_measure_restrict_def,
  apply H,
  apply g.is_measurable_fiber',
end


lemma integral_zero {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω):
  μ.integral 0 = 0 :=
begin
  have A1:μ.integral (0:Ω → ennreal) = μ.integral (λ ω:Ω, 0),
  {
    have A1A:(λ ω:Ω, (0:ennreal)) = 0 := rfl,
    rw ← A1A,
  },
  rw A1,
  unfold measure_theory.measure.integral,
  rw measure_theory.lintegral_zero,
end


lemma with_density.zero {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω):
    (μ.with_density 0) = 0 :=
begin
  apply measure_theory.measure.ext,
  intros S A1,
  rw measure_theory.with_density_apply2,
  {
    simp,
    have B1:(set.indicator S (0:Ω → ennreal) = 0),
    {
      apply @set.indicator_zero Ω ennreal _ S,
    },
    rw B1,
    rw integral_zero,
  },
  {
    apply A1,
  }
end

lemma measure_theory.measure.integral_def {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) {x:Ω → ennreal}:
μ.integral x = ∫⁻ (a : Ω), x a  ∂μ := rfl


lemma measure_theory.measure.integral_add {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) {x y:Ω → ennreal}:measurable x → measurable y →
   μ.integral (x + y) = μ.integral x + μ.integral y :=
begin
  intros A1 A2,
  repeat {rw measure_theory.measure.integral_def},
  simp,
  rw @measure_theory.lintegral_add Ω M μ x y,
  apply A1,
  apply A2,
end


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



--  Because we need an additional constraint, this cannot be handled with
--  add_monoid_hom.
lemma finset.sum_integral {β:Type*} {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:β → Ω → ennreal) (S:finset β):
  (∀ b∈S, measurable  (f b)) →
  S.sum (λ b, (μ.integral (f b))) =
  (μ.integral (S.sum f)) := 
begin
  have A1:decidable_eq β := classical.decidable_eq β,
  apply @finset.induction_on β _ A1 S,
  {
    rw finset.sum_empty,
    rw finset.sum_empty,
    rw integral_zero,
    intro A1,
    refl,
  },
  {
    intros b S2 A2 A3 A4,
    rw finset.sum_insert,
    rw A3,
    rw finset.sum_insert,
    rw measure_theory.measure.integral_add,
    {
      apply A4,
      simp,
    },
    {
      apply finset.sum_measurable,
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


lemma finset.sum_integral_simple_func {β:Type*} {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:β → (measure_theory.simple_func Ω ennreal)) (S:finset β):
  S.sum (λ b, (μ.integral (f b))) =
  (μ.integral (⇑(S.sum f))) := 
begin
  rw measure_theory.simple_func.finset_sum_to_fun,
  rw finset.sum_integral,
  have A1:(λ (b : β), ⇑(f b)) = (λ (b : β), (f b).to_fun),
  {
    apply funext,
    intro b,
    rw simple_func_to_fun,
  },
  rw A1,
  intros b A2,
  apply measure_theory.simple_func.measurable,
end


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
   

lemma simple_func.compose_eq_multiply {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f:Ω → ennreal) (H:measurable f) {g:measure_theory.simple_func Ω ennreal}:
    (μ.with_density f).integral g = μ.integral (f * ⇑g) :=
begin
  have A1:∀ g2 g3:measure_theory.simple_func Ω ennreal,
           g2 = g3 → 
           (μ.with_density f).integral g2 =
           (μ.with_density f).integral g3,
  {
    intros g2 g3 A1A,
    rw A1A,
  }, 
  rw A1 g (finset.sum (measure_theory.simple_func.range g) (λ (x : ennreal), measure_theory.simple_func.piece g x)) (measure_theory.simple_func.sum_piece g),

  rw ← finset.sum_integral_simple_func,
  have A1A:(λ (b : ennreal),
      measure_theory.measure.integral (μ.with_density f) ⇑(measure_theory.simple_func.piece g b))=λ b, μ.integral (f * ⇑(measure_theory.simple_func.piece g b)),
  {
    apply funext,
    intro x,
    rw integral_measure_piece_def,
    apply H,
  },
  rw A1A,
  clear A1A,
  rw finset.sum_integral,
  
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




lemma integral_le {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) 
    (f:Ω → ennreal) (H:measurable f) (x:ennreal):(∀ g:measure_theory.simple_func Ω ennreal, (⇑g ≤ f) →
     μ.integral g ≤ x) →
    (μ.integral f ≤ x) :=
begin
  intros A1,
  unfold measure_theory.measure.integral,
  unfold measure_theory.lintegral,
  unfold supr,
  apply @Sup_le ennreal _,
  intros b A2,
  simp at A2,
  cases A2 with g A2,
  subst b,
  simp,
  intros b A3 A4,
  subst b,
  rw ← integral_simple_func_def,
  apply A1 g A3,
end


lemma integral.monotone {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) 
    (f g:Ω → ennreal):
    (f ≤ g) →
    (μ.integral f ≤ μ.integral g) :=
begin
  intros A3,
  apply measure_theory.lintegral_mono,
  apply A3,
end

--This seems like a specific example of integrals being monotone.
lemma le_integral {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) 
    (f:Ω → ennreal) (g:measure_theory.simple_func Ω ennreal):
    (⇑g ≤ f) →
    (μ.integral g ≤ μ.integral f) :=
begin
  intros A1,
  apply integral.monotone,
  apply A1,
end


lemma integral_eq_Sup {Ω:Type*} {M:measurable_space Ω}
    (μ:measure_theory.measure Ω) 
    (f:Ω → ennreal):
    (measurable f) →
    μ.integral f = Sup ((λ g:measure_theory.simple_func Ω ennreal,
    μ.integral g) '' 
      {g:measure_theory.simple_func Ω ennreal|(⇑g ≤ f)}) :=
begin
  intro A1,
  apply le_antisymm,
  {
    apply integral_le,
    apply A1,
    intros g A2,
    apply @le_Sup_image (measure_theory.simple_func Ω ennreal) ennreal _,
    simp,
    apply A2,
  },
  {
    apply @Sup_image_le (measure_theory.simple_func Ω ennreal) ennreal _,
    intros g A2,
    apply le_integral,
    simp at A2,
    apply A2,
  },
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
    rw ennreal.div_def,
    rw mul_comm,
    rw with_top.mul_top,
    split;intros A3,
    {
      rw ← ennreal.coe_mul,
      apply with_top.coe_lt_top,
    },
    {
      simp,
    },
    {
      simp,
    },
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
      have A6 := @with_top.none_lt_some nnreal _ b,
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
      have A6 := @with_top.none_lt_some nnreal _ b,
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



--  In general, given two monotone functions, the supremum of the product
--  equals the product of the supremum. Here, we prove a part of that,
--  when one function has a supremum of infinity.
lemma supr_mul_top {α:Type*} [linear_order α] {f g:α → ennreal}:
    monotone f →
    monotone g →
    supr f = ⊤  →
    supr g ≠ 0 → 
    supr (f * g) = ⊤ :=
begin
  intros A1 A2 A3 A4,
  rw supr_eq_top,
  intros b A5,
  have C0F1:(0:ennreal) = ⊥ := rfl,

  rw supr_eq_top at A3,
  have C0:(∃ a:α, g a = ⊤) ∨  ¬ (∃ a:α, g a = ⊤) := classical.em _,  
  cases C0,
  {
    cases C0 with j C0,
    have C0B := (@ennreal.coe_lt_top 1),
    have C0C := A3 1 C0B,
    cases C0C with i C0C,
    have C0D :(i ≤ j) ∨ (j ≤ i) := le_total i j,
    cases C0D,
    {
      apply exists.intro j,
      have C0E:(f * g) j = f j * g j := rfl,
      rw C0E,
      have C0F:(f j) * (g j)=⊤,
      {
        rw C0,
        rw with_top.mul_top,
        rw C0F1,
        rw ← bot_lt_iff_ne_bot,
        rw ← C0F1,
        apply lt_trans,
        apply ennreal.zero_lt_one,
        apply lt_of_lt_of_le,
        apply C0C,
        apply A1,
        apply C0D,
      },
      rw C0F,
      apply A5,
    },
    {
      apply exists.intro i,
      simp,
      have C0G:g i = ⊤,
      {
        apply top_unique,
        rw ← C0,
        apply A2,
        apply C0D,    
      },
      have C0H:f i * g i = ⊤,
      {
        rw C0G,
        simp,
        left,
        rw C0F1,
        have C0H1:(¬f i = ⊥) = (f i ≠ ⊥) := rfl,
        rw C0H1,
        rw ← @bot_lt_iff_ne_bot ennreal _ (f i),
        apply lt_of_le_of_lt,
        apply @bot_le ennreal _ 1,
        apply C0C,   
      },
      rw C0H,
      apply A5,
    },
  }, 
  have C1:∀ a:α, g a ≠ ⊤,
  {
    apply forall_not_of_not_exists,
    apply C0,
  },
  have A6:∃ j, g j ≠ 0,
  {
    have A6A: g ≠ 0,
    {
      intro A6A1,
      apply A4,
      rw ennreal.supr_zero_iff_zero,
      apply A6A1,
    },
    rw ← classical.not_forall_iff_exists_not,
    intro A6B,
    apply A6A,
    apply funext,
    intro a,
    apply A6B,
  },
  cases A6 with j A6,
  let c := b / (g j),
  begin
    have B1 : c = b / (g j) := rfl,
    have B2 : c < ⊤,
    {
      rw B1,
      rw lt_top_iff_ne_top,
      intro B2A,
      rw ennreal.div_eq_top at B2A,
      cases B2A,
      {
        apply A6,
        apply B2A.right,
      },
      {
        rw lt_top_iff_ne_top at A5,
        apply A5,
        apply B2A.left,
      },
    },
    have B3 := A3 c B2,
    cases B3 with i B3,
      have B7 :c * (g j) = b,
      {
        have B7A:c * (g j) = (b / (g j)) * (g j),
        {
          rw B1,
        },
        rw B7A,
        rw ennreal.mul_div_cancel,
        apply A6,
        apply C1,
      },
      rw ← B7,
    have B4: i ≤ j ∨ j ≤ i := le_total i j,
    cases B4,
    {
      apply exists.intro j,
      have B5:c < f j,
      {
        apply lt_of_lt_of_le,
        apply B3,
        apply A1,
        apply B4,
      },
      have B6:(f * g) j = f j * g j := rfl,
      rw B6,
      apply ennreal.lt_of_mul_lt_mul,
      apply A6,
      apply C1,
      apply B5,
    },
    {
      apply exists.intro i,
      have B6:(f * g) i = f i * g i := rfl,
      rw B6,
      have B8:c * g j < f i * g j,
      {
        rw lt_iff_le_and_ne,
        split,
        {
          apply ennreal.mul_le_mul,
          apply le_of_lt B3,
          apply le_refl (g j),
        },
        {
          intro B8A,
          rw ennreal.mul_eq_mul_right at B8A,
          rw ← B8A at B3,
          have B8B := ne_of_lt B3,
          apply B8B,
          refl,
          apply A6,
          apply C1,
        },
      },
      have B9:f i * g j ≤ f i * g i,
      {
        apply ennreal.mul_le_mul,
        apply le_refl (f i),
        apply A2 B4,
      },
      apply lt_of_lt_of_le B8 B9,
    },
  end
end

lemma supr_mul_of_supr_top {α:Type*} [linear_order α] {f g:α → ennreal}:
    monotone f →
    monotone g →
    supr f = ⊤  →
    supr g ≠ 0 → 
    supr f * supr g ≤ supr (f * g) :=
begin
  intros A1 A2 A3 A4,
  rw supr_mul_top A1 A2 A3 A4,
  apply @le_top ennreal _ ((supr f) * (supr g)),
end

lemma ne_top_of_supr_ne_top {α:Type*} {f:α → ennreal} {a:α}:
    supr f ≠ ⊤  → f a ≠ ⊤ :=
begin
  intro A1,
  intro A2,
  apply A1,
  rw ← top_le_iff,
  rw ← A2,
  apply le_supr f a,
end


lemma multiply_supr {α:Type*} [linear_order α] {f g:α → ennreal}:
    monotone f →
    monotone g →
    supr (f * g) = (supr f) * (supr g) :=
begin
  intros A1 A2,
  apply le_antisymm,
  {
    apply supr_le _,
    intro x,
    simp,
    apply ennreal.mul_le_mul,
    apply le_supr f x,
    apply le_supr g x,
  },
  {
    /- If for all x and all y, (f x) * (f y) ≤ z,
       then (supr x) * (supr y) ≤ z.
       Consider a particular x, y. If x < y, then
       f x ≤ f y. Thus (f x) * (g y) ≤ (f y) * (g y) ≤ supr (f * g)
       However, I don't know how to prove the first part. -/
    have A3:supr f = 0 ∨ supr f ≠ 0  := eq_or_ne,
    cases A3,
    {
      apply le_supr_mul_of_supr_zero,
      apply A3,
    },
    have A4:supr g = 0 ∨ supr g ≠ 0  := eq_or_ne,
    cases A4,
    {
      rw mul_comm,
      rw mul_comm f g,
      apply le_supr_mul_of_supr_zero,
      apply A4,
    },
    have A3A:supr f = ⊤ ∨ supr f ≠ ⊤ := eq_or_ne,
    cases A3A,
    {
      apply supr_mul_of_supr_top A1 A2 A3A A4,
    },
    have A5:supr g = ⊤ ∨ supr g ≠ ⊤ := eq_or_ne,
    cases A5,
    {
      rw mul_comm,
      rw mul_comm f g,
      apply supr_mul_of_supr_top A2 A1 A5 A3,
    },
    rw ← ennreal.le_div_iff_mul_le (or.inl A4) (or.inl A5),
    apply @supr_le ennreal α _,
    intro i,
    have B4:f i ≠ ⊤,
    {
      apply ne_top_of_supr_ne_top A3A,
    },
    have A6:f i = 0 ∨ f i ≠ 0 := eq_or_ne,
    cases A6,
    {
       rw A6,
       simp,
    },
    rw ennreal.le_div_iff_mul_le (or.inl A4) (or.inl A5),
    rw mul_comm,
    rw ← ennreal.le_div_iff_mul_le (or.inl A6) (or.inl B4),
    apply @supr_le ennreal α _,
    {
    intro j,
    rw  ennreal.le_div_iff_mul_le (or.inl A6) (or.inl B4),
    have A7:i ≤ j ∨ j ≤ i := le_total i j, 
    cases A7,
    {
       have B1:f i ≤ f j,
       {
         apply A1,
         apply A7,
       },
       rw mul_comm,
       have B2:f i * g j ≤ f j * g j,
       {
         apply ennreal.mul_le_mul B1,
         apply le_refl (g j),
       },
       apply le_trans B2,
       have B3:f j * g j = (f * g) j := rfl,
       rw B3,
       apply @le_supr ennreal α _ (f * g),
    },
    {
       have B1:g j ≤ g i,
       {
         apply A2,
         apply A7,
       },
       rw mul_comm,
       have B2:f i * g j ≤ f i * g i,
       {
         apply ennreal.mul_le_mul _ B1,
         apply le_refl (f i),
       },
       apply le_trans B2,
       have B3:f i * g i = (f * g) i := rfl,
       rw B3,
       apply @le_supr ennreal α _ (f * g),
    },
    },
  },
end

lemma pointwise_monotone {α β γ:Type*} [preorder α] [preorder γ] 
   {f:α → β → γ}:monotone f 
   ↔ (∀ b:β, monotone (λ a:α, f a b)) := 
begin
  split;intros A1,
  {
    intro b,
    let g:β → α → γ := (λ (b:β) (a:α), f a b),
    begin
      have A2:g = (λ (b:β) (a:α), f a b) := rfl,
      have A3:(λ (a:α), f a b)=g b,
      {
        rw A2,
      },
      rw A3,
      apply @monotone_app α β γ _ _,
      have A4:(λ (a : α) (b : β), g b a) = f,
      {
        ext a b2,
        rw A2,
      },
      rw A4,
      apply A1,
    end
  },
  {
    apply @monotone_lam α β γ _ _,
    apply A1,
  },
end


lemma pointwise_supr {α β:Type*} [preorder α] {f:α → β → ennreal} 
  {g:β → ennreal}:supr f = g ↔ (∀ b:β, supr (λ a:α, f a b)=g b) := 
begin
  split;intros A1,
  {
    intro b,
    rw ← A1,
    rw supr_apply,
  },
  {
    apply funext,
    intro b,
    rw ← (A1 b),
    rw supr_apply,
  },
end

lemma multiply_supr2 {α β:Type*} [linear_order α] {f g:α → β → ennreal}:
    monotone f → monotone g →
    supr (f * g) = (supr f) * (supr g) :=
begin
  intro A1,
  intro A2,
  rw pointwise_supr,
  intro b,
  have A3:(⨆ (a : α), (f * g) a b) = 
         (supr ((λ (a : α), f a b) * (λ a:α, g a b))),
  {
    have A3A:(λ (a:α), f a b) * (λ (a:α), g a b)=(λ a:α, (f * g) a b),
    {
      apply funext,
      intro a,
      simp,
    },
    rw A3A,
  },
  rw A3,
  rw multiply_supr,
  {
    simp,
    rw supr_apply,
    rw supr_apply,
  },
  rw pointwise_monotone at A1,
  apply A1,
  rw pointwise_monotone at A2,
  apply A2,
end

lemma eapprox.mul_mono {α β:Type*} [preorder α] [encodable α] [measurable_space β] (f g:β → ennreal):
  monotone ((measure_theory.simple_func.eapprox f) * (measure_theory.simple_func.eapprox g)) :=
begin
  apply ennreal.multiply_mono,
  apply measure_theory.simple_func.monotone_eapprox,
  apply measure_theory.simple_func.monotone_eapprox,
end

/-
  This theorem leaves us in an interesting position. We now have a sequence
  of functions that is separable, and yet the limit is f * g.
-/
lemma eapprox.mul_supr {β:Type*}  [measurable_space β] (f g:β → ennreal):
  (measurable f) → (measurable g) →
  supr ((λ n:ℕ, (measure_theory.simple_func.eapprox f n).to_fun) * (λ n:ℕ, ⇑(measure_theory.simple_func.eapprox g n))) = (f * g) :=
begin
  intros A1 A2,
  rw multiply_supr2,
  apply funext,
  intro a,
  simp,
  rw supr_apply,
  rw supr_apply,
  rw measure_theory.simple_func.supr_eapprox_apply g A2 a,
  have A3:(⨆ (a_1 : ℕ), (measure_theory.simple_func.eapprox f a_1).to_fun a) 
  =   (⨆ n:ℕ, (⇑(measure_theory.simple_func.eapprox f n):β → ennreal) a) := rfl,
  rw A3,
  rw measure_theory.simple_func.supr_eapprox_apply f A1 a,
  apply measure_theory.simple_func.monotone_eapprox,
  apply measure_theory.simple_func.monotone_eapprox,
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


lemma integral_measure.compose_eq_multiply {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (f g:Ω → ennreal) (H:measurable f) (H2:measurable g):
  (μ.with_density f).integral g = μ.integral (f * g) :=
begin
  have A1:(μ.with_density f).integral g =
          supr (λ n:ℕ, (μ.with_density f).integral (measure_theory.simple_func.eapprox g n)),
  {
    rw ← measure_theory.integral_supr,
    rw supr_eapprox',
    apply H2,
    intro n,
    apply (measure_theory.simple_func.eapprox g n).measurable,
    apply measure_theory.simple_func.monotone_eapprox,
  },
  rw A1,
  clear A1,
  have A2:(λ n:ℕ, (μ.with_density f).integral (measure_theory.simple_func.eapprox g n)) = (λ n:ℕ, μ.integral (f * (measure_theory.simple_func.eapprox g n))),
  {
    apply funext,
    intro n,
    rw simple_func.compose_eq_multiply,
    apply H,
  },
  rw A2,
  clear A2,
  rw ← measure_theory.integral_supr,
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


def is_radon_nikodym_deriv  {Ω:Type*} {M:measurable_space Ω} (ν μ:measure_theory.measure Ω) (f:Ω → ennreal):Prop :=
   (measurable f) ∧ μ.with_density f = ν


lemma is_radon_nikodym_deriv_elim {Ω:Type*} {M:measurable_space Ω} (ν μ:measure_theory.measure Ω) (f:Ω → ennreal) (S:set Ω):
  (is_radon_nikodym_deriv ν μ f) →
  (is_measurable S) →
  (μ.integral (set.indicator S f) = ν S) :=
begin
  intros A1 A2,
  unfold is_radon_nikodym_deriv at A1,
  cases A1 with A3 A1,
  subst ν,
  rw measure_theory.with_density_apply2,
  --apply A3,
  apply A2,
end


lemma measurable_of_is_radon_nikodym_deriv {Ω:Type*} {M:measurable_space Ω} (ν μ:measure_theory.measure Ω) (f:Ω → ennreal) (S:set Ω):
  (is_radon_nikodym_deriv ν μ f) →
  (measurable f) :=
begin
  intro A1,
  cases A1 with A1 A2,
  apply A1,
end


lemma is_radon_nikodym_deriv_intro {Ω:Type*} {M:measurable_space Ω} (ν μ:measure_theory.measure Ω) (f:Ω → ennreal):
  (measurable f) →
  (∀ S:set Ω, (is_measurable S) →
  (μ.integral (set.indicator S f) = ν S)) →
  (is_radon_nikodym_deriv ν μ f)  :=
begin
  intros A1 A2,
  unfold is_radon_nikodym_deriv,
  split,
  apply A1,
  apply measure_theory.measure.ext,
  intros S A3,
  rw measure_theory.with_density_apply2,
  apply A2,
  repeat {apply A3},
end



-- There used to be a definition close to this, measure_theory,measure.a_e, and
-- This used to be ∀ᶠ a in μ.a_e, P a
-- For now, we use a local definition.
def measure_theory.measure.all_ae {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P:Ω → Prop):Prop :=
   (μ ({ω:Ω|(P ω)}ᶜ)) = 0


lemma measure_theory.measure.all_ae_def2 {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P:Ω → Prop):
    μ.all_ae P = ( (μ ({ω:Ω|(P ω)}ᶜ)) = 0) :=
begin
  unfold measure_theory.measure.all_ae,
end


lemma measure_theory.measure.all_ae_and {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P Q:Ω → Prop):
    (μ.all_ae P) →
    (μ.all_ae Q) →
    (μ.all_ae (λ a, P a ∧ Q a)) := 
begin
  intros A1 A2,
  rw measure_theory.measure.all_ae_def2,
  have A3:{ω:Ω| P ω ∧ Q ω}ᶜ =  ({ω:Ω|P ω}ᶜ) ∪ ({ω:Ω|Q ω}ᶜ),
  {
    ext ω,
    split;intros A3A;simp;simp at A3A,
    {
      have A3B:P ω ∨ ¬(P ω) := classical.em (P ω),
      cases A3B,
      {
        apply or.inr (A3A A3B),
      },
      {
        apply or.inl A3B,
      },
    },
    {
      cases A3A,
      {
        intro A3B,
        exfalso,
        apply A3A,
        apply A3B,
      },
      {
        intro A3B,
        apply A3A,
      },
    },
  },
  rw A3,
  have A4:(⊥:ennreal)=(0:ennreal) := rfl,
  rw ← A4,
  rw ← le_bot_iff,
  apply le_trans (measure_theory.measure_union_le ({ω:Ω|P ω}ᶜ) ({ω:Ω|Q ω}ᶜ)),
  rw measure_theory.measure.all_ae_def2 at A1,
  rw measure_theory.measure.all_ae_def2 at A2,
  rw A1,
  rw A2,
  simp,
end


lemma measure_theory.all_ae_imp {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P Q:Ω → Prop):
    (μ.all_ae (λ a, P a → Q a)) →
    (μ.all_ae P) →
    (μ.all_ae Q) :=
begin
  intros A1 A2,
  rw measure_theory.measure.all_ae_def2 at A1,
  rw measure_theory.measure.all_ae_def2 at A2,
  rw measure_theory.measure.all_ae_def2,
  have A3:{ω:Ω|Q ω}ᶜ ⊆ ({ω:Ω|P ω → Q ω}ᶜ) ∪ ({ω:Ω|P ω}ᶜ),
  {
    rw set.subset_def,
    intro ω,
    simp,
    intro A3A,
    cases (classical.em (P ω)) with A3B A3B,
    {
      apply or.inl (and.intro A3B A3A),
    },
    {
      apply or.inr A3B,
    },
  },
  have A4:(⊥:ennreal)=(0:ennreal) := rfl,
  rw ← A4,
  rw ← le_bot_iff,
  apply le_trans (measure_theory.measure_mono A3),
  apply le_trans (measure_theory.measure_union_le ({ω:Ω|P ω → Q ω}ᶜ) ({ω:Ω|P ω}ᶜ)),
  rw A1,
  rw A2,
  simp,
end


lemma measure_theory.all_ae2_of_all {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P:Ω → Prop):
    (∀ a, P a) → 
    (μ.all_ae P) :=
begin
  intro A1,
  rw measure_theory.measure.all_ae_def2,
  have A2:{ω:Ω|P ω}ᶜ = ∅,
  {
    ext ω,split;intros A2A,
    exfalso,
    simp at A2A,
    apply A2A,
    apply A1,
    exfalso,
    apply A2A,
  },
  rw A2,
  simp,
end


lemma measure_theory.not_ae {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P:Ω → Prop):
  (∃ S:set Ω, (μ S > 0) ∧ (∀ ω∈ S, ¬ (P ω)) )→
  (¬(μ.all_ae P)) :=
begin
  intros A1 A2,
  cases A1 with S A3,
  cases A3 with A3 A4,
  rw measure_theory.measure.all_ae_def2 at A2,
  have A5:S⊆ {ω:Ω|P ω}ᶜ,
  {
    rw set.subset_def,
    intro ω,
    intro A5A,
    apply A4 _ A5A,
  },
  have A6 := measure_theory.outer_measure.mono (μ.to_outer_measure) A5,
  have A7 := lt_of_lt_of_le A3 A6,
  rw measure.apply at A2,
  rw A2 at A7,
  apply lt_irrefl (0:ennreal) A7,
end

lemma ennreal.eq_zero_or_zero_lt {x:ennreal}:¬(x=0) → (0 < x) :=
begin
  intro A1,
  have A2:= @lt_trichotomy ennreal _ x 0,
  cases A2,
  {
    exfalso,
    apply @ennreal.not_lt_zero x,
    apply A2,
  },
  cases A2,
  {
    exfalso,
    apply A1,
    apply A2,
  },
  {
    apply A2,
  },
end

/-
  Notice that it is not necessarily the case that a measurable set exists.
  For example, consider where Ω = {a,b}.
  The measurable sets are {} and {a,b}, where μ ∅ = 0 and μ {a,b} = 1.
  Define (P a) and (¬P b).
  Thus S={a}, which is not measurable.
-/
lemma measure_theory.not_ae_elim {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω) (P:Ω → Prop):
  (¬(μ.all_ae P)) →
  (∃ S:set Ω, (μ S > 0) ∧ (∀ ω∈ S, ¬ (P ω)) ) :=
begin
  intro A1,
  rw measure_theory.measure.all_ae_def2 at A1,
  have A2 := ennreal.eq_zero_or_zero_lt A1,
  apply exists.intro ({ω : Ω | P ω}ᶜ),
  split,
  apply A2,
  intros ω A3,
  simp at A3,
  apply A3,
end


def measure_theory.measure.is_finite {Ω:Type*} {M:measurable_space Ω} 
  (μ:measure_theory.measure Ω):Prop := (μ (@set.univ Ω))<⊤




lemma measure_theory.measure.is_finite_def {Ω:Type*} {M:measurable_space Ω} 
  (μ:measure_theory.measure Ω):
  μ.is_finite ↔ (μ (@set.univ Ω))<⊤ :=
begin
  unfold measure_theory.measure.is_finite,
end

lemma measure_theory.measure.is_finite_le {Ω:Type*} {M:measurable_space Ω} 
  (μ ν:measure_theory.measure Ω):(μ ≤ ν) → ν.is_finite → μ.is_finite :=
begin
  intros A1 A2,
  rw measure_theory.measure.is_finite_def,
  rw measure_theory.measure.is_finite_def at A2,
  apply lt_of_le_of_lt _ A2,
  apply A1,
  apply is_measurable.univ,
end

lemma measure_theory.measure.is_finite_all {Ω:Type*} {M:measurable_space Ω} 
  (μ:measure_theory.measure Ω) (S:set Ω):
  μ.is_finite → (μ S)<⊤ :=
begin
  rw measure_theory.measure.is_finite_def,
  intro A1,
  apply lt_of_le_of_lt _ A1,
  apply μ.mono,
  simp,
end

def measure_theory.measure.is_finite_all_ne {Ω:Type*} {M:measurable_space Ω} 
  (μ:measure_theory.measure Ω) {S:set Ω}:
  μ.is_finite → (μ S)≠⊤ :=
begin
  rw ← lt_top_iff_ne_top,
  apply measure_theory.measure.is_finite_all,
end


lemma measures_equal {Ω:Type*} {M:measurable_space Ω}
    (μ ν:measure_theory.measure Ω):
  (ν.is_finite) →
  (μ ≤ ν) →
  (μ set.univ = ν set.univ) →
  (μ = ν) :=
begin
  intros A2 A3 A4,
  apply measure_theory.measure.ext,
  intros S A5,
  have B3:is_measurable (Sᶜ),
  {
    apply is_measurable.compl,
    apply A5,
  },
  apply le_antisymm,
  {
    apply A3,
    apply A5,
  },
  {
    apply @le_of_not_lt ennreal _,
    intro A6,
    have A7:μ (Sᶜ) ≤ ν (Sᶜ),
    {
      apply A3,
      apply B3,
    },
    have B1:S ∪ (Sᶜ) = set.univ ,
    {
      simp,
    },
    have B2:disjoint S (Sᶜ),
    {
      unfold disjoint,
      simp,
    },
    have A8:μ set.univ = μ S + μ (Sᶜ),
    {
      rw ← B1,
      apply measure_theory.measure_union,
      apply B2,
      apply A5,
      apply B3,
    },
    have A9:ν set.univ = ν S + ν (Sᶜ),
    {
      rw ← B1,
      apply measure_theory.measure_union,
      apply B2,
      apply A5,
      apply B3,
    },
    have A10:μ set.univ < ν set.univ,
    {
      rw A8,
      rw A9,
      apply ennreal.add_lt_add_of_lt_of_le_of_lt_top,
      {
        apply ν.is_finite_all (Sᶜ) A2,
      },
      {
        apply A7,
      },
      {
        apply A6,
      },
    },
    rw A4 at A10,
    apply lt_irrefl _ A10,
  },
end


lemma measurable_supr_of_measurable {Ω:Type*} [M:measurable_space Ω]
    {h:ℕ → Ω → ennreal}:
    (∀ n:ℕ, measurable (h n)) →
    (measurable (supr h)) :=
begin
  intros A1,
  apply is_ennreal_measurable_intro_Ioi,
  intro x,
  have A3:((supr h) ⁻¹' {y : ennreal | x < y}) =⋃ (n:ℕ), (h n) ⁻¹' {y:ennreal | x < y},
  {
    simp,
    ext ω,
      have A3B:supr h ω = supr (λ n, h n ω),
      {
        apply supr_apply,
      },
    split;
    intros A3A;simp;simp at A3A,
    {
      rw A3B at A3A,
      rw @lt_supr_iff ennreal _ at A3A,
      apply A3A,
    },
    {
      cases A3A with i A3A,
      apply lt_of_lt_of_le A3A,
      rw A3B,
      apply @le_supr ennreal ℕ _,
    },
  },    
  rw A3,
  apply is_measurable.Union,
  intro b,
  apply A1 b,
  apply is_ennreal_is_measurable_intro_Ioi,
end 




lemma monotone_set_indicator {Ω β:Type*} [has_zero β] [preorder β] {S:set Ω}:
    monotone ((set.indicator S):(Ω → β) → (Ω → β)) :=
begin
  unfold monotone,
  intros f g A1,
  rw le_func_def2,
  intro ω,
  cases (classical.em (ω ∈ S)) with A2 A2,
  {
    rw set.indicator_of_mem A2,
    rw set.indicator_of_mem A2,
    apply A1,
  },
  {
    rw set.indicator_of_not_mem A2,
    rw set.indicator_of_not_mem A2,
  },
end


lemma supr_with_density_apply_eq_with_density_supr_apply {Ω:Type*} [measurable_space Ω] {μ:measure_theory.measure Ω}
    {h:ℕ → Ω → ennreal} {S:set Ω}:
    is_measurable S →
    (∀ n:ℕ, measurable (h n)) →
    (monotone h) →
    supr (λ n:ℕ, μ.with_density (h n) S) = μ.with_density (supr h) S :=
begin
  intros A1 A2 A3,
  have A4:(λ n, μ.with_density (h n) S) = (λ n, μ.integral (set.indicator S (h n))),
  {
    apply funext,
    intro n,
    rw measure_theory.with_density_apply2,
    --apply A2 n,
    apply A1,
  },
  rw A4,
  clear A4,
  rw measure_theory.with_density_apply2,
  rw supr_indicator,
  rw measure_theory.integral_supr,
  {
    intro n,
    apply measurable_set_indicator,
    apply A1,
    apply A2 n,
  },
  {
    have B1:(λ (n:ℕ), set.indicator S (h n)) = (set.indicator S) ∘ h := rfl,
    rw B1,
    apply @monotone.comp ℕ (Ω → ennreal) (Ω → ennreal) _ _ _,
    apply @monotone_set_indicator Ω ennreal _ _,
    apply A3,
  },
  {
    apply A1,
  },
end 


lemma with_density_supr_apply_le {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}
    {h:ℕ → Ω → ennreal} {S:set Ω}:
    is_measurable S →
    (∀ n:ℕ, measurable (h n)) →
    (monotone h) →
    (∀ n:ℕ, μ.with_density (h n) ≤  ν) →
    μ.with_density (supr h) S ≤ ν S :=
begin
  intros A1 A2 A3 A4,
  rw ← supr_with_density_apply_eq_with_density_supr_apply A1 A2 A3,
  apply @supr_le ennreal ℕ _,
  intro n,
  apply A4,
  apply A1,
end


-- So, although there is a LOT below, this is the easiest third of the
-- Radon-Nikodym derivative: namely, that if we have a monotone sequence
-- of functions, the sequence will be less than or equal to ν.
lemma with_density_supr_le {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}
    {h:ℕ → Ω → ennreal}:
    (∀ n:ℕ, measurable (h n)) →
    (monotone h) →
    (∀ n:ℕ, μ.with_density (h n) ≤  ν) →
    μ.with_density (supr h) ≤ ν :=
begin
  intros A1 A2 A3,
  intros S A4,
  apply with_density_supr_apply_le A4 A1 A2 A3,
end


lemma measure_of_monotone' {Ω:Type*} [measurable_space Ω] {S:set Ω}
    :is_measurable S →
    monotone (λ μ:measure_theory.measure Ω, μ S) :=
begin
  intros A0 μ ν A1,
  simp,
  rw measure.apply,
  rw measure.apply,
  apply A1,
  apply A0,
end



-- Compare with ennreal.has_sub.
-- I think that this is the equivalent of (a - b)⁺, if 
-- a and b were signed measures.
-- Specifically, note that if you have α = {1,2}, and
-- a {1} = 2, a {2} = 0, and 
-- b {2} = 2, b {1} = 0, then 
-- (a - b) {1, 2} = 2. However, if a ≤ b, and
--  a set.univ ≠ ⊤, then (a - b) + b = a.
-- Also, a - b ≤ a.
noncomputable instance measure_theory.measure.has_sub {α:Type*}
  [measurable_space α]:has_sub (measure_theory.measure α) := ⟨λa b, Inf {d | a ≤ d + b}⟩


lemma measure_theory.measure.sub_def {α:Type*}
  [measurable_space α] {a b:measure_theory.measure α}:
  (a - b) = Inf {d | a ≤ d + b} := rfl


def sub_pred {α:Type*} (f:ℕ → set α):ℕ → set α
  | (nat.succ n) := f n.succ \ f n
  | 0 := f 0 


lemma sub_pred_subset {α:Type*} (f:ℕ → set α) {n:ℕ}:
  sub_pred f n ⊆ f n :=
begin
  cases n,
  {
    unfold sub_pred,
  },
  {
    unfold sub_pred,
    apply set.diff_subset,
  },
end

lemma sub_pred_subset' {α:Type*} (f:ℕ → set α) {n:ℕ} {x:α}:
  x∈ sub_pred f n → x ∈ f n :=
begin
  intro A1,
  have A2:sub_pred f n ⊆ f n := @sub_pred_subset α f n, 
  rw set.subset_def at A2,
  apply A2 _ A1,
end


def prefix_union {α:Type*} (f:ℕ → set α) (n:ℕ):=
  (⋃ (m∈ finset.range n.succ), f m )


lemma prefix_union_def {α:Type*} (f:ℕ → set α) (n:ℕ):
  (⋃ (m∈ finset.range n.succ), f m )= prefix_union f n := rfl


lemma prefix_union_zero {α:Type*} (f:ℕ → set α):
  (prefix_union f 0) = f 0 :=
begin
  rw ← prefix_union_def,
  apply set.ext,
  intros a,
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

lemma prefix_union_succ {α:Type*} (f:ℕ → set α) (n:ℕ):
  (prefix_union f n.succ) = (prefix_union f n) ∪ f n.succ :=
begin
  rw ← prefix_union_def,
  rw ← prefix_union_def,
  ext,
  split;intros A1;simp;simp at A1,
  {
    cases A1 with m A1,
    cases (classical.em (m = nat.succ n)) with A2 A2,
    {
      subst m,
      right,
      apply A1.right,
    },
    {
      left,
      apply exists.intro m,
      split,
      apply lt_of_le_of_ne,
      apply lt_succ_imp_le m (nat.succ n) A1.left,  
      apply A2,
      apply A1.right,
    },
  },
  {
    cases A1 with A1 A1,
    {
      cases A1 with m A1,
      apply exists.intro m,
      split,
      apply lt_trans A1.left,
      apply nat.lt.base,
      apply A1.right,
    },
    {
      apply exists.intro (nat.succ n),
      split,
      apply nat.lt.base,
      apply A1,
    },
  },
end


lemma prefix_union_def2 {α:Type*} (f:ℕ → set α) (n:ℕ):
  (⨆  (m:ℕ) (H:m ≤ n), f m)=prefix_union f n :=
begin
  unfold prefix_union,
  ext,split;intros A1;simp at A1;simp,
  {
    cases A1 with m A1,
    apply exists.intro m,
    split,
    apply nat.lt_succ_of_le A1.left,
    apply A1.right,
  },
  {
    cases A1 with m A1,
    apply exists.intro m,
    split,
    apply lt_succ_imp_le m n A1.left,
    apply A1.right, 
  },
end


lemma prefix_union_contains {α:Type*} (f:ℕ → set α) {m n:ℕ}:
    m ≤ n → 
    f m ⊆ prefix_union f n :=
begin
  intro A1,
  rw ← prefix_union_def2,
  rw set.subset_def,
  intros ω A2,
  simp,
  apply exists.intro m,
  apply and.intro A1 A2,
end


lemma prefix_union_contains' {α:Type*} (f:ℕ → set α) {m n:ℕ} {x:α}:
    m ≤ n → 
    x∈ f m → x ∈ prefix_union f n :=
begin
  intros A1 A2,
  have A3 := prefix_union_contains f A1,
  rw set.subset_def at A3,
  apply A3 x A2,
end


lemma prefix_union_sub_pred {α:Type*} (f:ℕ → set α):
    prefix_union (sub_pred f) = prefix_union f :=
begin
  apply funext,
  intro n,
  induction n,
  {
    repeat {rw prefix_union_zero},
    unfold sub_pred,
  },
  {
    rw prefix_union_succ,
    rw prefix_union_succ f,
    rw n_ih,
    ext;split;intros A1;simp;simp at A1;cases A1 with A1 A1;
    try {
      apply or.inl A1,
    },
    {
      right,
      apply sub_pred_subset',
      apply A1,
    },
    {
      cases (classical.em (x ∈ f n_n)) with A2 A2,
      {
        left,
        apply prefix_union_contains' f _ A2,
        apply le_refl,
      },
      {
        right,
        unfold sub_pred,
        simp,
        apply and.intro A1 A2,
      },
    },
  },
end


lemma Union_sub_pred {α:Type*} {f:ℕ → set α}:
  set.Union (sub_pred f) = set.Union f :=
begin
  apply set.ext,
  intro a,
  split;intros A1;simp at A1;simp;cases A1 with n A1,
  {
    apply exists.intro n,
    apply sub_pred_subset',
    apply A1,
  },
  {
    have A2:a ∈ prefix_union f n,
    {
      apply prefix_union_contains' f (le_refl n) A1,
    },
    rw ← prefix_union_sub_pred at A2,
    rw ← prefix_union_def at A2,
    simp at A2,
    cases A2 with n A2,
    apply exists.intro n,
    apply A2.right,
  },
end


lemma mem_sub_pred_succ {α:Type*} {n:ℕ} {x:α} {f:ℕ → set α}:
    x ∉ f n → (x ∈ f (nat.succ n)) →
    x ∈ sub_pred f (nat.succ n) :=
begin
  intros A1 A2,
  unfold sub_pred,
  apply and.intro A2 A1,
end

lemma not_mem_of_sub_pred_succ {α:Type*} {n:ℕ} {x:α} {f:ℕ → set α}:
    x ∈ sub_pred f (nat.succ n) → x ∉ f n  :=
begin
  intros A1,
  unfold sub_pred at A1,
  simp at A1,
  apply A1.right,
end


lemma sub_pred_pairwise_disjoint_helper {α:Type*} {f:ℕ → set α} {m n:ℕ}:
  (monotone f) →
  m < n →
  disjoint (sub_pred f m) (sub_pred f n) :=
begin
  intros A1 A2,
  apply set_disjoint_intro,
  intros x A3 A4,
  cases n,
  {
    apply nat.not_lt_zero m A2,
  },
  have A5 := lt_succ_imp_le m n A2,
  have A6:f m ⊆ f n,
  {
    apply A1 A5,
  },
  have A7:sub_pred f m ⊆ f m,
  {
    apply sub_pred_subset,
  },
  have A8:x ∈ f n,
  {
     have A8:=set.subset.trans A7 A6,
     rw set.subset_def at A8,
     apply A8 x A3,
  },
  apply not_mem_of_sub_pred_succ A4 A8,
end


lemma sub_pred_pairwise_disjoint {α:Type*} {f:ℕ → set α}:
  (monotone f) →
  pairwise (disjoint on (sub_pred f)) :=
begin
  intro A1,
  intros m n A2,
  have A3:disjoint (sub_pred f m) (sub_pred f n),
  {
    have A3A:=lt_trichotomy m n,
    cases A3A with A3A A3A,
    {
      apply sub_pred_pairwise_disjoint_helper A1 A3A,
    },
    cases A3A with A3A A3A,
    {
      exfalso,
      apply A2,
      apply A3A,
    },
    {
      apply set_disjoint_comm,
      apply sub_pred_pairwise_disjoint_helper A1 A3A,      
    },
  },
  apply A3,
end


lemma measure_finset_sum {α:Type*}
    [measurable_space α] {μ:measure_theory.measure α}
    {f:ℕ → set α} {n:ℕ}:(∀ n, is_measurable (f n)) →
    (pairwise (disjoint on f)) →
    (finset.range n).sum (λ m, μ (f m)) = 
    μ (⋃  (m∈ finset.range n), f m) :=
begin
  intros A1 A2,
  rw measure_theory.measure_bUnion_finset,
  {
    intros m B1 n B2 B3,
    apply A2,
    apply B3,
  },
  {
    intros m C1,
    apply A1,
  },
end


lemma union_range_sub_pred {α:Type*} {f:ℕ → set α} {n:ℕ}:
 (⋃ (m : ℕ) (H : m ∈ finset.range n), sub_pred f m) =
     (⋃ (m : ℕ) (H : m ∈ finset.range n), f m) :=
begin
  cases n,
  {
    simp,
  },
  {
    rw prefix_union_def,
    rw prefix_union_def,
    rw prefix_union_sub_pred,
  },
end


lemma is_measurable_sub_pred {α:Type*} [measurable_space α] 
  {f:ℕ → set α} {n:ℕ}:
  (∀ m, is_measurable (f m)) → is_measurable (sub_pred f n) :=
begin
  intro A1,
  cases n,
  {
    unfold sub_pred,
    apply A1,
  },
  {
    unfold sub_pred,
    apply is_measurable.diff,
    repeat {apply A1},
  },
end



lemma union_finset_range_monotone {α:Type*} {f:ℕ → set α} {n:ℕ}:
    monotone f →
    (⋃ m ∈ finset.range (n.succ), f m) = f n :=
begin
  intro A1,
  ext,split;intros A2,
  {
    simp at A2,
    cases A2 with m A2,
    have A3 := lt_succ_imp_le m n A2.left,
    have A4 := A1 A3,
    have A5:(f m ⊆ f n)= (f m ≤ f n ):= rfl,
    rw ← A5 at A4,
    rw set.subset_def at A4,
    apply A4,
    apply A2.right,
  },
  {
    simp,
    apply exists.intro n,
    split,
    apply nat.lt.base,
    apply A2,
  },
end


def le_on_subsets {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) (X:set α):Prop :=
    is_measurable X ∧ 
    (∀ X':set α, X'⊆ X → is_measurable X' → μ X' ≤ ν X') 


lemma le_on_subsets_def {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) (X:set α):
    le_on_subsets μ ν X =
    (is_measurable X ∧ 
    (∀ X':set α, X'⊆ X → is_measurable X' → μ X' ≤ ν X')) := rfl


lemma le_on_subsets_is_measurable {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X:set α}:
    le_on_subsets μ ν X →
    (is_measurable X) :=
begin
  intros A1,
  rw le_on_subsets_def at A1,
  apply A1.left,
end


lemma le_on_subsets_self {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X:set α}:
    le_on_subsets μ ν X →
    μ X ≤ ν X :=
begin
  intro A1,
  rw le_on_subsets_def at A1,
  apply A1.right X (le_refl X) A1.left,
end


lemma le_on_subsets_empty {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):
    le_on_subsets μ ν ∅ := 
begin
  rw le_on_subsets_def,
  split,
  {
    apply is_measurable.empty,
  },
  {
    intros X' A1 A2,
    have A3 := empty_of_subset_empty X' A1,
    subst X',
    simp,
  },
end

lemma le_on_subsets_union {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X Y:set α}:
    le_on_subsets μ ν X →
    le_on_subsets μ ν Y →
    le_on_subsets μ ν (X ∪ Y) :=
begin
  repeat {rw le_on_subsets_def},
  intros A1 A2,
  split,
  {
     apply is_measurable.union A1.left A2.left,
  },
  {
     intros X' A3 A4,
     rw @measure_theory.measure_eq_inter_diff _ _ μ _ X A4 A1.left,
     rw @measure_theory.measure_eq_inter_diff _ _ ν _ X A4 A1.left,
     have A5:X' ∩ X ⊆ X := set.inter_subset_right X' X,
     have A6:X' \ X ⊆ Y,
     {
       rw set.subset_def,
       intros a A6A,
       rw set.subset_def at A3,
       simp at A6A,
       have A6B := A3 a A6A.left,
       simp at A6B,
       cases A6B,
       {
         exfalso,
         apply A6A.right,
         apply A6B,
       },
       {
         apply A6B,
       },
     },
     
     have A7:is_measurable (X' ∩ X) := is_measurable.inter A4 A1.left,
     have A8:is_measurable (X' \ X) := is_measurable.diff A4 A1.left,
     have A9:=A1.right (X' ∩ X) A5 A7,
     have A10:=A2.right (X' \ X) A6 A8,
     apply @add_le_add ennreal _ _ _ _ _ A9 A10,
  },
end


lemma le_on_subsets_subset {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) (X Y:set α):
    le_on_subsets μ ν X →
    Y ⊆ X →
    is_measurable Y →
    le_on_subsets μ ν Y :=
begin
  repeat {rw le_on_subsets_def},
  intros A1 A2 A3,
  split,
  apply A3,
  intros X' A4 A5,
  apply A1.right X' (set.subset.trans A4 A2) A5,
end


lemma le_on_subsets_diff {α:Type*} [measurable_space α]
    {μ ν:measure_theory.measure α} {X Y:set α}:
    le_on_subsets μ ν X →
    le_on_subsets μ ν Y →
    le_on_subsets μ ν (X \ Y) :=
begin
  intros A1 A2,
  apply le_on_subsets_subset μ ν X (X \ Y) A1,
  {
    apply set.diff_subset,
  },
  {
    apply is_measurable.diff 
       (le_on_subsets_is_measurable A1)
       (le_on_subsets_is_measurable A2),
  },
end


lemma le_on_subsets_m_Union {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) {f:ℕ → set α}:
    monotone f →
    (∀ n:ℕ, le_on_subsets μ ν (f n)) → 
    (le_on_subsets μ ν (set.Union f)) :=
begin
  intros A1 A2,
  have A3:∀ n, le_on_subsets μ ν ((sub_pred f) n),
  {
    intros n,
    cases n,
    {
      unfold sub_pred,
      apply A2,
    },
    {
      unfold sub_pred,
      apply le_on_subsets_diff,
      apply A2,
      apply A2,
    },
  },
  rw ← Union_sub_pred,
  
  rw le_on_subsets_def,
  split,
  {
    apply is_measurable.Union,
    intro n,
    apply le_on_subsets_is_measurable (A3 n),
  },
  {
    intros X' A4 A5,
    have D1:pairwise (disjoint on λ (i : ℕ), X' ∩ sub_pred f i),
    {
      intros m n C1,
      have C2:disjoint (X' ∩ sub_pred f m) (X' ∩ sub_pred f n),
      {
        rw set.inter_comm,
        apply disjoint_inter_left,
        apply disjoint_inter_right,
        apply sub_pred_pairwise_disjoint A1,
        apply C1,
      },
   
      apply C2,
    },
    have D2:∀ n, is_measurable (X' ∩ (sub_pred f n)),
    {
      intro n,
      apply is_measurable.inter A5 (le_on_subsets_is_measurable (A3 n)),
    },
    
    have A6:X' = ⋃ n, X' ∩ (sub_pred f n),
    {
      ext,split;intros A4A,
      {
        simp,
        apply and.intro A4A,
        rw set.subset_def at A4,
        have A4B := A4 x A4A,
        simp at A4B,
        apply A4B,
      },
      {
        simp at A4A,
        apply A4A.left,
      },
    },
    rw A6,
    repeat {rw measure_theory.measure_Union},
    apply @tsum_le_tsum ennreal ℕ _ _ _,
    {
      intro b,
      have B1 := A3 b,
      rw le_on_subsets_def at B1,
      apply B1.right,
      apply set.inter_subset_right,
      apply is_measurable.inter A5 B1.left,
    },
    repeat {
      apply ennreal.summable,
    },
    apply D1,
    apply D2,
    apply D1,
    apply D2,
  },
end


lemma le_measurable_add {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) {X Y:set α}:
    μ X < ⊤ →
    μ Y < ⊤ →
    is_measurable X →
    is_measurable Y →
    μ X ≤ ν X →
    μ Y ≤ ν Y →
    disjoint X Y →
    ν (X ∪ Y) - μ (X ∪ Y) = (ν X - μ X) +  (ν Y - μ Y) :=
begin
  intros A1 A2 A3 A4 A5 A6 A7,
  rw measure_theory.measure_union A7 A3 A4,
  rw measure_theory.measure_union A7 A3 A4,
  rw ennreal.add_sub_add_eq_sub_add_sub A1 A2 A5 A6,
end


lemma le_on_subsets_add {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) {X Y:set α}:
    μ X < ⊤ →
    μ Y < ⊤ →
    le_on_subsets μ ν X → le_on_subsets μ ν Y →
    disjoint X Y →
    ν (X ∪ Y) - μ (X ∪ Y) = (ν X - μ X) +  (ν Y - μ Y) :=
begin
  intros A1 A2 A5 A6 A7,
  have A3 := le_on_subsets_is_measurable A5,
  have A4 := le_on_subsets_is_measurable A6,
  apply le_measurable_add μ ν A1 A2 A3 A4 
      (le_on_subsets_self A5) (le_on_subsets_self A6) A7,
end


--This is a function that is equivalent to the above if
--ν ≤ μ and ν is finite (ν set.univ ≠ ⊤).
--This definition is "wrong", in the sense that the
--definition below is closer to subtraction.
--This definition falls apart unless ν ≤ μ.
noncomputable def measure_sub_fn {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α):Π (s:set α),is_measurable s → ennreal := 
  λ (S:set α) (H:is_measurable S), (μ S - ν S)


--A better variant of measure_sub_fn.
--This definition is valid even if ¬(ν ≤ μ).
noncomputable def measure_sub_fn' {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α):Π (s:set α),is_measurable s → ennreal := 
  λ (S:set α) (H:is_measurable S), 
  ⨆ (S' ⊆ S) (H2:le_on_subsets ν μ S'), (μ S' - ν S')


lemma measure_sub_fn_def {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α):
  measure_sub_fn μ ν = λ (S:set α) (H:is_measurable S), (μ S - ν S) := rfl


lemma measure_sub_fn_def' {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α):measure_sub_fn' μ ν = 
  λ (S:set α) (H:is_measurable S), 
  ⨆ (S' ⊆ S) (H2:le_on_subsets ν μ S'), (μ S' - ν S') := rfl


lemma measure_sub_fn_apply {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (s:set α) (H:is_measurable s):
  measure_sub_fn μ ν s H = (μ s - ν s) := rfl

lemma measure_sub_fn_apply' {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (s:set α) (H:is_measurable s):
  measure_sub_fn' μ ν s H = 
  ⨆ (S' ⊆ s) (H2:le_on_subsets ν μ S'), (μ S' - ν S')  := rfl


lemma measure_sub_fn_apply_empty {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α): 
  (measure_sub_fn μ ν) ∅ is_measurable.empty = 0 :=
begin
  rw measure_sub_fn_apply,
  rw measure_theory.measure_empty,
  rw measure_theory.measure_empty,
  rw ennreal.sub_zero,
end


lemma measure_sub_fn_apply_empty' {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α): 
  (measure_sub_fn' μ ν) ∅ is_measurable.empty = 0 :=
begin
  rw measure_sub_fn_apply',
  apply le_antisymm,
  {
    apply @supr_le ennreal _ _,
    intro S',
    apply @supr_le ennreal _ _,
    intro A1,
    apply @supr_le ennreal _ _,
    intros A2,
    have A3:= empty_of_subset_empty S' A1,
    subst S',
    simp,
  },
  {
    simp,
  },
end


lemma sub_eq_supr_le {x y:ennreal}:
  x - y = (⨆ (H:y ≤ x), x) - (⨆ (H:y ≤ x), y) :=
begin
  cases classical.em (y ≤ x) with A1 A1,
  {
    repeat {rw supr_prop_def A1},
  },
  {
    repeat {rw supr_prop_false A1},
    simp,
    apply le_of_not_le A1,
  },
end 


lemma ennreal.sub_eq_of_add_of_not_top_of_le {a b c:ennreal}:a = b + c →
  c ≠ ⊤ →
  c ≤ a → a - c = b :=
begin
  intros A1 A4 A2,
  cases c,
  {
    exfalso,
    simp at A4,
    apply A4,
  },
  cases a,
  {
    simp,
    cases b,
    {
      refl,
    },
    exfalso,
    simp at A1,
    rw ← ennreal.coe_add at A1,
    apply ennreal.top_ne_coe A1,
  },
  cases b,
  {
    simp at A1,
    exfalso,
    apply A1,
  },
  {
    repeat {rw ennreal.some_eq_coe},
    rw ← ennreal.coe_sub,
    rw ennreal.coe_eq_coe,
    repeat {rw ennreal.some_eq_coe at A1},
    rw ← ennreal.coe_add at A1,
    rw ennreal.coe_eq_coe at A1,
    repeat {rw ennreal.some_eq_coe at A2},
    rw ennreal.coe_le_coe at A2,
    apply nnreal.sub_eq_of_add_of_le A1 A2,
  },
end


/-
  This only works if the sum of g is finite.
  The consequence of this is that f minus g
  is only well-defined if either f or g.
 -/
lemma ennreal.tsum_sub {f:ℕ → ennreal} {g:ℕ → ennreal}:
(∑' i, g i) ≠ ⊤ → (g ≤ f) → (∑' i, (f i - g i)) = (∑' i, f i) - (∑' i, g i) :=
begin
  intros A1 B2,
  let h:ℕ → ennreal := (λ i, f i - g i),
  begin
    have B1:h = (λ i, f i - g i) := rfl,
    have A2:(∑' i, (h i) + (g i))=(∑' i, h i) + (∑' i, g i),
    {
      apply tsum_add,
      apply ennreal.summable,
      apply ennreal.summable,
    },
    have A3:g ≤ (h + g),
    {
      rw B1,
      rw le_func_def2,
      intro n,
      simp,
      rw ennreal.sub_add_cancel_of_le,
      apply B2,
      apply B2,
    },
    have A4:(∑' i, g i) ≤ (∑' i, (h i) + (g i)),
    {
      apply @tsum_le_tsum ennreal ℕ _ _ _,
      {
        intro n,
        apply A3,
      },
      apply ennreal.summable,
      apply ennreal.summable,
    },
    have A5:(∑' i, (h i) + (g i))-(∑' i, g i)=(∑' i, h i),
    {
      apply ennreal.sub_eq_of_add_of_not_top_of_le A2 A1 A4,
    },
    have A6:(λ i, (h i) + (g i)) = f,
    {
      apply funext,
      intro n,
      rw B1,
      simp,
      rw ennreal.sub_add_cancel_of_le,
      apply B2,
    }, 
    rw A6 at A5,
    rw B1 at A5,
    symmetry,
    apply A5,
  end
end




lemma measure_finite {α:Type*} [M:measurable_space α] 
    {μ:measure_theory.measure α}
    (H:μ.is_finite) (S:set α): 
    (μ S ≠ ⊤) :=
begin
  rw ← lt_top_iff_ne_top,
  apply measure_theory.measure.is_finite_all μ S H,
end


lemma measure_sub_fn_m_Union {α:Type*} [M:measurable_space α] 
    (μ ν:measure_theory.measure α) (H:ν ≤ μ) 
    (H2:ν.is_finite):
(∀ (g : ℕ → set α) (h : ∀ (i : ℕ), is_measurable (g i)), 
  pairwise (disjoint on g) → 
 ((measure_sub_fn μ ν) (⋃ (i : ℕ), g i) (M.is_measurable_Union g h)) = 
  ∑' (i : ℕ), (measure_sub_fn μ ν) (g i) (h i)) :=
begin
  intros g A1 A2,
  have A5:(λ i, ν (g i)) = (λ i, ν.to_outer_measure.measure_of (g i)) := rfl,
  have A6:(λ i, μ (g i)) = (λ i, μ.to_outer_measure.measure_of (g i)) := rfl,

  rw measure_sub_fn_apply,
  have A3:(λ n:ℕ, (measure_sub_fn μ ν (g n) (A1 n)))
      =(λ n:ℕ, (μ (g n)) - (ν (g n))),
  {
    apply funext,
    intro n,
    rw measure_sub_fn_apply,
  },
  rw A3,
  clear A3,
  have A4:(∑' (n:ℕ), (μ (g n))-(ν (g n))) = 
(∑' (n:ℕ), (μ (g n)))-
(∑' (n:ℕ), (ν (g n))),
  {
    apply ennreal.tsum_sub,
    {
      rw A5,
      rw ← ν.m_Union A1 A2,
      apply ν.is_finite_all_ne H2,
    },
    {
      rw le_func_def2,
      intro i,
      apply H,
      apply A1,
    },
  },
  rw A4,
  repeat {rw measure.apply},
  rw ν.m_Union A1 A2,
  rw μ.m_Union A1 A2,
  rw ← A5,
  rw ← A6,
end

noncomputable def measure_sub {α:Type*} [M:measurable_space α] 
    {μ ν:measure_theory.measure α} (H:ν ≤ μ) 
    (H2:ν.is_finite):measure_theory.measure α := @measure_theory.measure.of_measurable α M (measure_sub_fn μ ν)  (measure_sub_fn_apply_empty μ ν) (measure_sub_fn_m_Union μ ν H H2)



lemma measure_sub_def {α:Type*} [M:measurable_space α] 
    {μ ν:measure_theory.measure α} (H:ν ≤ μ) 
    (H2:ν.is_finite):measure_sub H H2 = @measure_theory.measure.of_measurable α M (measure_sub_fn μ ν)  (measure_sub_fn_apply_empty μ ν) (measure_sub_fn_m_Union μ ν H H2) := rfl

lemma measure_sub_apply {α:Type*} [M:measurable_space α] 
    {μ ν:measure_theory.measure α} (H:ν ≤ μ) 
    (H2:ν.is_finite) {S:set α} (H3:is_measurable S):
    measure_sub H H2 S = μ S - ν S :=
begin
  rw measure_sub_def,
  rw measure_theory.measure.of_measurable_apply,
  rw measure_sub_fn_apply,
  apply H3,
end



lemma measure_sub_add {α:Type*} [M:measurable_space α] 
    {μ ν:measure_theory.measure α} (H:ν ≤ μ) 
    (H2:ν.is_finite):μ = ν + (measure_sub H H2) :=
begin
  apply measure_theory.measure.ext,
  intros s A3,
  simp,
  rw measure_sub_apply,
  rw add_comm,
  rw ennreal.sub_add_cancel_of_le,
  apply H,
  repeat {apply A3},
end




lemma measure_theory.measure.le_of_add_le_add_left {α:Type*} 
  [M:measurable_space α]
  {μ ν₁ ν₂:measure_theory.measure α}:μ.is_finite → 
  μ + ν₁ ≤ μ + ν₂ → ν₁ ≤ ν₂ :=
begin
  intros A1 A2,
  rw measure_theory.measure.le_iff,
  intros S B1,
  rw measure_theory.measure.le_iff at A2,
  have A3 := A2 S B1,
  simp at A3,
  apply ennreal.le_of_add_le_add_left _ A3,
  apply μ.is_finite_all,
  apply A1,
end


lemma measure_theory.measure.le_of_add_le_add_right 
    {α:Type*} [M:measurable_space α] 
    {μ₁ ν μ₂:measure_theory.measure α}:(ν.is_finite)→
   (μ₁ + ν ≤ μ₂ + ν) → (μ₁ ≤ μ₂) :=
begin
  intros A1 A2,
  rw add_comm μ₁ ν at A2,
  rw add_comm μ₂ ν at A2,
  apply measure_theory.measure.le_of_add_le_add_left A1 A2,
end


lemma measure_sub_eq {α:Type*} [M:measurable_space α] 
    (μ ν:measure_theory.measure α) (H:ν ≤ μ) 
    (H2:ν.is_finite):(μ - ν) = (measure_sub H H2) :=
begin
  rw measure_theory.measure.sub_def,
  have A1B:μ = ν + measure_sub H H2 :=
          measure_sub_add H H2,

  apply le_antisymm,
  {
    have A1:μ ≤ (measure_sub H H2) + ν,
    {
      rw add_comm,
      rw ← A1B,
      apply le_refl μ,
    },
    have A2:(measure_sub H H2) ∈ {d|μ ≤ d + ν} := A1, 
    apply Inf_le A2,
  },
  {
    apply @le_Inf (measure_theory.measure α) _,
    intros b B1,
    simp at B1,
    rw A1B at B1,
    rw add_comm at B1,
    apply measure_theory.measure.le_of_add_le_add_right H2 B1,
  },
end


lemma le_of_le_measure_sub {α:Type*} [M:measurable_space α] 
    {μ ν₁ ν₂:measure_theory.measure α} (H2:μ.is_finite) (H3:ν₁.is_finite)
    (H:ν₁ ≤ μ): 
    ν₂ ≤ (measure_sub H H3) →  ν₁ + ν₂ ≤ μ :=
begin
  intro A1,
  have B1:μ = ν₁ + (measure_sub H H3),
  {
    apply measure_sub_add,
  },
  rw B1,
  apply measure_theory.measure.add_le_add_left,
  apply A1,
end



def measure_theory.measure.is_support {α:Type*} [measurable_space α]
    (μ:measure_theory.measure α) (S:set α):Prop := is_measurable S ∧ μ (Sᶜ) = 0


noncomputable def scale_measure_fn {α:Type*}
    [measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α) 
    (S:set α) (H:is_measurable S):ennreal := x * μ S


noncomputable def scale_measure {α:Type*}
    [M:measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α):(measure_theory.measure α) :=
    measure_theory.measure.of_measurable
    (λ (s:set α) (H:is_measurable s), x * (μ s))
begin
  simp,
end
begin
  intros f A1 A2,
  simp,
  rw measure.apply,  
  rw μ.m_Union A1 A2,
  have A3:(λ i, μ.to_outer_measure.measure_of (f i)) =
          λ i, μ (f i) := rfl,
  rw  A3,
  rw ennreal.tsum_mul_left,
end


lemma scale_measure_apply {α:Type*}
    [M:measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α)
    (s:set α) (H:is_measurable s):
    scale_measure x μ s =
    (λ (s:set α) (H:is_measurable s), x * (μ s)) s H :=
begin
  apply measure_theory.measure.of_measurable_apply,
  apply H,
end

lemma scale_measure_apply2 {α:Type*}
    [M:measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α)
    (s:set α) (H:is_measurable s):
    scale_measure x μ s = x * (μ s) :=
begin
  rw scale_measure_apply,
  apply H,
end


noncomputable instance has_scalar_ennreal_measure {α:Type*}
    [measurable_space α]:
    has_scalar (ennreal) (measure_theory.measure α) := {
  smul := λ x y, scale_measure x y, 
}


lemma ennreal_smul_measure_def {α:Type*}
    [measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α):
    (x  • μ) = (scale_measure x μ)  := rfl


lemma ennreal_smul_measure_apply {α:Type*}
    [measurable_space α] (x:ennreal) 
    (μ:measure_theory.measure α)
    (s:set α) (H:is_measurable s):
    (x  • μ) s = x * (μ s) :=
begin
  rw ennreal_smul_measure_def,
  rw scale_measure_apply2,
  apply H,
end
    

lemma ennreal_measure_zero_smul {α:Type*}
    [measurable_space α] (μ:measure_theory.measure α):
    (0:ennreal) • μ = 0 :=
begin
  apply measure_theory.measure.ext,
  intros s A1,
  rw ennreal_smul_measure_apply,
  simp,
  apply A1,  
end


noncomputable instance mul_action_ennreal_measure
    {α:Type*}
    [M:measurable_space α]:
    mul_action (ennreal) (measure_theory.measure α)
     := {
  mul_smul := 
  begin
    intros x y μ,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply,
    rw ennreal_smul_measure_apply,
    rw ennreal_smul_measure_apply,   
    rw mul_assoc,
    repeat {apply A1},
  end,
  one_smul :=
  begin
    intro μ,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply,
    rw one_mul,
    apply A1,
  end,
}


noncomputable instance distrib_mul_action_ennreal_measure
    {α:Type*}
    [M:measurable_space α]:
    distrib_mul_action (ennreal) (measure_theory.measure α)
     := {
  smul_zero :=
  begin
    intro r,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply,
    apply mul_zero,
    apply A1,
  end,
  smul_add :=
  begin
    intros r μ ν,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply _ _ _ A1,
    have A2:(μ + ν) s = (μ s) + (ν s)
        := rfl,
    rw A2,
    have A3:((r • μ) + (r • ν)) s = ((r • μ) s) + ((r • ν) s)
        := rfl,
    rw A3,
    repeat {rw scale_measure_apply2 _ _ _ A1},
    rw left_distrib,
    rw ennreal_smul_measure_apply _ _ _ A1,
    rw ennreal_smul_measure_apply _ _ _ A1,
  end,
}


noncomputable instance ennreal_measure_semimodule {α:Type*}
    [M:measurable_space α]:
    semimodule (ennreal) (measure_theory.measure α) := {
  zero_smul :=
  begin
    intro μ,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply _ _ _ A1,
    apply zero_mul,
  end,
  add_smul := 
  begin
    intros r t μ,
    apply measure_theory.measure.ext,
    intros s A1,
    rw ennreal_smul_measure_apply _ _ _ A1,
    rw measure_theory.measure.add_apply,    
repeat {rw scale_measure_apply2 _ _ _ A1},
    rw right_distrib,
    rw ennreal_smul_measure_apply _ _ _ A1,
    rw ennreal_smul_measure_apply _ _ _ A1,
  end,
}


lemma ennreal.zero_if_lt_pos {x:ennreal}:
  (∀ y >0, x ≤ y) → x = 0 := 
begin
  intro A1,
  have A2:(0:ennreal)=⊥ := rfl,
  rw A2,
  rw ← le_bot_iff,
  rw ← A2,
  apply ennreal.le_of_forall_epsilon_le,
  intros ε A3 A4,
  rw zero_add,
  apply A1,
  have A5:(0:ennreal)=(0:nnreal) := rfl,
  rw A5,
  simp,
  apply A3,  
end


lemma outer_measure_measure_of_le {Ω:Type*} {μ ν:measure_theory.outer_measure Ω}:
    μ ≤ ν ↔
    (μ.measure_of) ≤
    (ν.measure_of) :=
begin
  refl,
end


lemma to_outer_measure_measure_of_le {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}:
    μ ≤ ν ↔
    (μ.to_outer_measure.measure_of) ≤
    (ν.to_outer_measure.measure_of) :=
begin
  split;intro A1,
  {
    rw ← measure_theory.measure.to_outer_measure_le at A1,
    rw le_func_def2,
    intro ω,
    apply A1,
  },
  {
    intros S A2,
    apply A1,
  },
end



lemma monotone_to_outer_measure {Ω:Type*} [measurable_space Ω]:
    monotone (λ μ:measure_theory.measure Ω, μ.to_outer_measure) :=
begin
  intros μ ν A1,
  simp,
  rw ← measure_theory.measure.to_outer_measure_le at A1,
  apply A1,
end


lemma monotone_to_outer_measure_measure_of {Ω:Type*} [measurable_space Ω]:
    monotone (λ μ:measure_theory.measure Ω, μ.to_outer_measure.measure_of) :=
begin
  intros μ ν A1,
  simp,
  rw ← measure_theory.measure.to_outer_measure_le at A1,
  apply A1,
end


lemma measure_apply_le_measure_apply {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω} {S:set Ω}:
    μ ≤ ν →
    (μ S) ≤ (ν S) :=
begin
  intro A1,
  rw to_outer_measure_measure_of_le at A1,
  apply A1,
end


noncomputable def measure_theory.outer_measure.of_function' {Ω:Type*} 
    (f:set Ω → ennreal):
    measure_theory.outer_measure Ω := measure_theory.outer_measure.of_function 
    (set.indicator ({(∅:set Ω)}ᶜ) f)
begin
  rw set.indicator_of_not_mem,
  simp,
end


lemma outer_measure_measure_of_def {Ω:Type*} {μ:measure_theory.outer_measure Ω}
  {S:set Ω}:μ S  = μ.measure_of S := rfl


lemma measure_theory.outer_measure.of_function_def 
  {α : Type*} (m : set α → ennreal) (m_empty : m ∅ = 0) :
  (measure_theory.outer_measure.of_function m m_empty).measure_of
    = λs, ⨅{f : ℕ → set α} (h : s ⊆ ⋃i, f i), ∑'i, m (f i)  := rfl


lemma measure_theory.outer_measure.of_function_le_of_function_of_le {Ω:Type*} 
    {f g:set Ω → ennreal} {Hf:f ∅ = 0} {Hg:g ∅ = 0}:
    f ≤ g → 
    (measure_theory.outer_measure.of_function f Hf ≤
     measure_theory.outer_measure.of_function g Hg) :=
begin
  intro A1,
  rw measure_theory.outer_measure.le_of_function,
  intro S,
  have A2 := @measure_theory.outer_measure.of_function_le _ f Hf S,
  apply le_trans A2,
  apply A1,
end


lemma measure_theory.outer_measure.monotone_of_function' {Ω:Type*}:
    monotone (@measure_theory.outer_measure.of_function' Ω) :=
begin
  unfold monotone measure_theory.outer_measure.of_function',
  intros f g A1,
  apply measure_theory.outer_measure.of_function_le_of_function_of_le,
  have A2 := @monotone_set_indicator (set Ω) ennreal _ _ ({∅}ᶜ),
  apply A2,
  apply A1,
end


lemma measure_theory.outer_measure.of_function'_le {Ω:Type*} 
    {f:set Ω → ennreal} {S:set Ω}: 
    (measure_theory.outer_measure.of_function' f S ≤ f S) :=
begin
  have A2 := @measure_theory.outer_measure.of_function_le _ 
            (@set.indicator (set Ω) ennreal _  ({(∅:set Ω)}ᶜ) f) _ S,
  apply le_trans A2,
  clear A2,
  cases classical.em (S = ∅)  with A3 A3,
  {
    subst S,
    rw set.indicator_of_not_mem,
    {
      simp,
    },
    {
      simp,
    },
  },
  {
    rw set.indicator_of_mem,
    apply le_refl (f S),
    simp [A3],
  },
end


lemma galois_connection_measure_of_of_function' {Ω:Type*}:
  galois_connection 
      (λ μ:measure_theory.outer_measure Ω, μ.measure_of) 
      (λ f:set Ω → ennreal, measure_theory.outer_measure.of_function' f)  :=
begin
  unfold galois_connection,
  intros μ f,
  unfold measure_theory.outer_measure.of_function',
  rw measure_theory.outer_measure.le_of_function,

  split;intros A1,
  {
    intro S,
    cases (classical.em (S = ∅)) with B1 B1,
    {
      subst S,
      rw outer_measure_measure_of_def,
      rw measure_theory.outer_measure.empty,
      simp,
    },
    {
      rw set.indicator_of_mem,
      apply A1,
      simp [B1],
    },
  },
  {
    rw le_func_def2,
    intro S,
    cases (classical.em (S = ∅)) with C1 C1,
    {
      subst S,  
      rw measure_theory.outer_measure.empty,
      simp,
    },
    {
      have C2:= A1 S,
      rw set.indicator_of_mem at C2,
      apply C2,
      simp [C1],
    },
  },
end


lemma of_function_replace {Ω:Type*} {f g:set Ω → ennreal} {Hf:f ∅ = 0} {Hg:g ∅ = 0}:
    (f = g) →
    measure_theory.outer_measure.of_function f Hf =
    measure_theory.outer_measure.of_function g Hg :=
begin
  intro A1,
  apply measure_theory.outer_measure.ext,
  intro S,
  repeat {rw outer_measure_measure_of_def},
  repeat {rw measure_theory.outer_measure.of_function_def},
  rw A1,
end

lemma of_function_invariant {Ω:Type*} {μ:measure_theory.outer_measure Ω}:
    measure_theory.outer_measure.of_function (μ.measure_of) (μ.empty) = μ :=
begin
  apply le_antisymm,
  {
    rw outer_measure_measure_of_le,
    rw le_func_def2,
    intro S,
    apply measure_theory.outer_measure.of_function_le,
    apply μ.empty,
  },
  {
    rw measure_theory.outer_measure.le_of_function,
    intro S,
    apply le_refl (μ.measure_of S),
  },
end 


noncomputable def galois_insertion_measure_of_of_function' {Ω:Type*}:
  @galois_insertion (order_dual (set Ω → ennreal)) (order_dual (measure_theory.outer_measure Ω)) _ _
      (λ f:set Ω → ennreal, measure_theory.outer_measure.of_function' f)
      (λ μ:measure_theory.outer_measure Ω, μ.measure_of) 
  := 
begin
  apply galois_insertion.monotone_intro,
  {
    intros μ ν B1,
    simp,
    apply B1,
  },
  {
    intros f g C1,
    apply measure_theory.outer_measure.monotone_of_function',
    apply C1,
  },
  {
    intro f,
    apply measure_theory.outer_measure.of_function'_le,
  },
  {
    intro μ,
    unfold measure_theory.outer_measure.of_function',
    have D1:(set.indicator ({∅}ᶜ) μ.measure_of)=μ.measure_of,
    {
      apply funext,
      intro S,
      cases (classical.em (S = ∅)) with D1A D1A,
      {
        subst S,
        rw set.indicator_of_not_mem,
        rw measure_theory.outer_measure.empty,
        simp,  
      },
      {
        rw set.indicator_of_mem,
        simp [D1A],  
      },
    },
    rw of_function_replace D1,
    clear D1,
    apply of_function_invariant,  
  },
end


def strictly_monotone {α β:Type*} [preorder α] [preorder β] (f:α → β):Prop :=
  ∀ a b:α, a < b → f a < f b


lemma monotone_of_strictly_monotone {α β:Type*} [partial_order α] [partial_order β] {f:α → β}:strictly_monotone f → monotone f :=
begin
  intros A1,
  intros b1 b2 A3,
  cases (classical.em (b1 = b2)) with A4 A4,
  {
    subst b2,
  },
  {
    apply le_of_lt,
    apply A1,   
    apply lt_of_le_of_ne A3 A4,
  },
end 


/-
  This represents that for all a, a', the converse of a the monotone property holds.
 -/
def monotone_converse {α β:Type*} [partial_order α] [partial_order β] (f:α → β):Prop :=
    ∀ a a':α, f a ≤ f a' → a ≤ a'


lemma Sup_eq_Sup_of_monotone_converse {α β:Type*} [complete_lattice α] [complete_lattice β] {f:α → β} {s:set α} (a:α):monotone f →
    monotone_converse f →
    (Sup (f '' s) = f a) →
    (Sup (f '' s) = f (Sup s)) :=
begin
  intros A1 A2 A3,
  apply le_antisymm,
  {
    apply Sup_le_Sup_of_monotone A1,
  },
  {
    rw A3,
    apply A1,
    apply Sup_le,
    intros b A4,
    apply A2,
    rw ← A3,
    apply le_Sup,
    apply exists.intro b,
    apply and.intro A4 rfl,
  },
end


lemma supr_eq_supr_of_monotone_converse {α β γ:Type*} [complete_lattice α] [complete_lattice β] {f:α → β} {g:γ → α} (a:α):monotone f →
    monotone_converse f →
    (supr (f ∘ g) = f a) →
    (supr (f ∘ g) = f (supr g)) :=
begin
  intros A1 A2 A3,
  apply le_antisymm,
  {
    apply supr_le_supr_of_monotone A1,
  },
  {
    rw A3,
    apply A1,
    apply Sup_le,
    intros b A4,
    apply A2,
    rw ← A3,
    cases A4 with y A4,
    subst b,
    apply le_supr (f ∘ g),
  },
end

lemma infi_eq_infi_of_monotone_converse {α β γ:Type*} [complete_lattice α] [complete_lattice β] {f:α → β} {g:γ → α} (a:α):monotone f →
    monotone_converse f →
    (infi (f ∘ g) = f a) →
    (infi (f ∘ g) = f (infi g)) :=
begin
  intros A1 A2 A3,
  apply le_antisymm,
  {
    rw A3,
    apply A1,
    apply le_infi,
    intros b,
    apply A2,
    rw ← A3,
    apply infi_le,
  },
  {
    apply infi_le_infi_of_monotone A1,
  },
end

lemma Inf_eq_Inf_of_monotone_converse {α β:Type*} [complete_lattice α] [complete_lattice β] {f:α → β} {s:set α} (a:α):monotone f →
    monotone_converse f →
    (Inf (f '' s) = f a) →
    (Inf (f '' s) = f (Inf s)) :=
begin
  intros A1 A2 A3,
  apply le_antisymm,
  {
    rw A3,
    apply A1,
    apply le_Inf,
    intros b A4,
    apply A2,
    rw ← A3,
    apply Inf_le,
    simp,
    apply exists.intro b,
    split,
    apply A4,
    refl,
  },
  {
    apply Inf_le_Inf_of_monotone A1,
  },
end


lemma monotone_converse_to_outer_measure_measure_of {Ω:Type*} [measurable_space Ω]:
    monotone_converse (λ μ:measure_theory.measure Ω, μ.to_outer_measure.measure_of) :=
begin
  intros μ ν A1,
  intros s A2,
  apply A1,
end


--TODO: write infi_eq_infi_to_outer_measure_measure_of,
-- or better, Inf_eq_Inf_to_outer_measure_measure_of...
lemma supr_eq_supr_to_outer_measure_measure_of {α γ:Type*}
   [measurable_space α]  {g:γ → measure_theory.measure α} 
   (μ:measure_theory.measure α):
    (supr ((λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) ∘ g) =
     (λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) μ) →
    (supr ((λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) ∘ g) =
    (λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) (supr g)) :=
begin
  intros A1,
  apply supr_eq_supr_of_monotone_converse μ,
  apply monotone_to_outer_measure_measure_of,
  apply monotone_converse_to_outer_measure_measure_of,
  apply A1,
end


-- This would be better if it required only for all measurable sets.
lemma supr_eq_supr_of_apply {α γ:Type*}
   [measurable_space α]  {g:γ → measure_theory.measure α} 
   {μ:measure_theory.measure α}:
    (∀ (s:set α), 
    (supr ((λ ν:measure_theory.measure α, ν s) ∘ g) = μ s)) →
    (supr ((λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) ∘ g) =
    (λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) (supr g)) :=
begin
  intros A1,
  apply supr_eq_supr_to_outer_measure_measure_of μ,
  apply funext,
  intro s,
  rw supr_apply,
  simp,
  apply A1,
end


lemma dual_galois_insertion.l_infi_u' {α : Type*} {β : Type*} {l : α → β} {u : β → α}
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β]: 
   @galois_insertion (order_dual α) (order_dual β) _ _ l u → ∀ {ι : Type*} (f : ι → β), l (⨅ (i : ι), u (f i)) = ⨅ (i : ι), f i :=
begin
  intros A1 γ f,
  have A2 := @galois_insertion.l_supr_u (order_dual α) (order_dual β) l u _ _ A1 γ f,
  apply A2,
end

lemma dual_galois_insertion.l_supr_u' {α : Type*} {β : Type*} {l : α → β} {u : β → α}
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β]: 
   @galois_insertion (order_dual α) (order_dual β) _ _ l u → ∀ {ι : Type*} (f : ι → β), l (⨆  (i : ι), u (f i)) = ⨆  (i : ι), f i :=
begin
  intros A1 γ f,
  have A2 := @galois_insertion.l_infi_u (order_dual α) (order_dual β) l u _ _ A1 γ f,
  apply A2,
end


lemma galois_insertion.le_iff_u_le_u {α : Type*} {β : Type*} {l : α → β} {u : β → α}
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β] {b b':β}: 
   @galois_insertion α β _ _ l u → 
   ((b ≤ b') ↔ (u b ≤ u b')) :=
begin
  intro A1,
  split;intros A2,
  {
    apply A1.gc.monotone_u A2,
  },
  {
    rw ← A1.gc at A2,
    rw A1.l_u_eq at A2,
    apply A2,
  },
end

lemma galois_insertion.Sup_u_eq_u_Sup {α : Type*} {β : Type*} {l : α → β} {u : β → α}
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β]: 
   @galois_insertion α β _ _ l u → 
   ∀ (S:set β), (∃ b:β, u b = Sup (u '' S)) →  u (Sup S)  = Sup (u '' S) :=
begin
  intros A1 S A2,
  cases A2 with b A2,
  apply le_antisymm,
  {
    rw ← A2,
    have A3 := A1.gc.monotone_u,
    apply A3,
    apply Sup_le,
    intros b' A4,
    rw A1.le_iff_u_le_u,
    rw A2,
    apply le_Sup,
    simp,
    apply exists.intro b',
    apply and.intro A4 _,
    refl,
  },
  {
    apply Sup_le,
    intros a A3,
    rw ← A1.gc,
    apply le_Sup,
    simp at A3,
    cases A3 with  b' A3,
    cases A3 with A3 A4,
    subst a,
    rw A1.l_u_eq,
    apply A3,
  },
end

lemma dual_galois_connection.u_Sup {α β : Type*}
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β] 
   {l : α → β} {u : β → α}:
   @galois_connection (order_dual α) (order_dual β) _ _ l u →
   ∀ (s : set β), u (Sup s) = (⨆a∈s, u a) :=
begin
  intros A1 s,
  apply A1.u_Inf,
end

lemma dual_galois_connection.u_supr {α β : Type*} {ι: Sort*} 
   [_inst_1 : complete_lattice α] [_inst_2 : complete_lattice β] 
   {l : α → β} {u : β → α}:
   @galois_connection (order_dual α) (order_dual β) _ _ l u →
   ∀  (γ:Type*) (f : γ → β), u (supr f) = (⨆a, u (f a)) :=
begin
  intros A1 γ f,
  apply A1.u_infi,
end

-- A local function for mapping the supremum as a function back to a measure.
-- It is sufficient that such a measure exists.
noncomputable def supr_as_fun {α:Type*} [measurable_space α] 
    (f:ℕ → (measure_theory.measure α)):Π (s:set α), (is_measurable s) → ennreal :=
  (λ s H,(⨆ n:ℕ, f n s)) 


lemma supr_as_fun_apply {α:Type*} [measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (s:set α) (H:is_measurable s):
   supr_as_fun f s H = (⨆ n:ℕ, f n s) := rfl


lemma supr_as_fun_empty {α:Type*} [measurable_space α] 
    {f:ℕ → (measure_theory.measure α)}:
  (supr_as_fun f) ∅ is_measurable.empty = 0 := 
begin
  unfold supr_as_fun,
  have A1:(λ n:ℕ, f n ∅ ) = 0,
  {
    apply funext,
    intro n,
    apply measure_theory.measure_empty,
  },
  rw A1,
  apply @supr_const ennreal ℕ _ _ 0,
end


lemma supr_sum_le_sum_supr {g:ℕ → ℕ → ennreal}:
  (⨆ m:ℕ, ∑' n, g m n) ≤
  (∑' m, ⨆ n:ℕ,  g n m) := 
begin
    apply @supr_le ennreal ℕ _,
    intro i,
    apply @tsum_le_tsum ennreal ℕ _ _,
    intro b,
    apply @le_supr ennreal ℕ _,
    repeat {apply ennreal.summable},
end






lemma tsum_single  {α : Type*} {β : Type*} [_inst_1 : add_comm_monoid α] [_inst_2 : topological_space α] [t2_space α] {f : β → α} (b : β): (∀ (b' : β), b' ≠ b → f b' = 0) → tsum f = (f b) :=
begin
  intro A1,
  have A2:=has_sum_single b A1,
  have A3:summable f := has_sum.summable A2, 
  rw ← summable.has_sum_iff A3,
  apply A2,
end

lemma ennreal.tsum {α:Type*} {f:α → ennreal}:tsum f = supr (λ s:finset α,s.sum f) :=
begin
  rw ← summable.has_sum_iff ennreal.summable,
  apply @ennreal.has_sum α f,
end


lemma ennreal.tsum_le {f:ℕ → ennreal} {x:ennreal}:(∀ n:ℕ,
(finset.range n).sum f ≤ x) ↔
(tsum f ≤ x) :=
begin
  rw ennreal.tsum,

  split;intros A1,
  {
    apply @supr_le ennreal (finset ℕ) _ (λ s:finset ℕ,s.sum f),
    intro s,
    have B1:=finset_range_bound s,
    cases B1 with n B1,
    apply le_trans _ (A1 n),
    simp,
    apply @finset.sum_le_sum_of_subset ℕ ennreal s (finset.range n) f _ B1,
  },
  {
    intro n,
    apply le_trans _ A1,
    apply @le_supr ennreal (finset ℕ) _ (λ s, s.sum f),
  },
end


lemma ennreal.finset_sum_le_tsum {f:ℕ → ennreal} {n:ℕ}:
(finset.range n).sum f ≤ tsum f :=
begin
  rw ennreal.tsum,
  apply @le_supr ennreal (finset ℕ) _ (λ s, s.sum f),
end 


lemma ennreal.lim_finset_sum_eq_tsum {f:ℕ → ennreal}:
(⨆  n, (finset.range n).sum f)  = tsum f :=
begin
  apply le_antisymm,
  apply @supr_le ennreal _ _,
  intro n,
  apply ennreal.finset_sum_le_tsum,
  rw ← ennreal.tsum_le,
  intro n,
  apply @le_supr ennreal _ _,
end


lemma supr_sum_eq_sum_supr {g:ℕ → ℕ → ennreal}:
  monotone g →
  (⨆ m:ℕ, ∑' n, g m n) = 
  (∑' m, ⨆ n:ℕ,  g n m) := 
begin
  intro A1,
  apply le_antisymm,
  {
    apply supr_sum_le_sum_supr,
  },
  {
    rw ← @ennreal.tsum_le (λ m, ⨆ n:ℕ,  g n m) (⨆ m:ℕ, ∑' n, g m n),
    intros n2,
    have A2:(λ m, (finset.range n2).sum (g m)) ≤ (λ m, ∑' n, g m n),
    {
      rw le_func_def2,
      intro m,
      simp,
      apply ennreal.finset_sum_le_tsum,
    },
    have A3:(⨆  m, (finset.range n2).sum (g m)) ≤ (⨆ m, ∑' n, g m n),
    {
      apply supr_le_supr A2,
    },
    apply le_trans _ A3,
    rw @ennreal.finset_sum_supr_nat ℕ ℕ _ (finset.range n2) (λ m n, g n m), 
    simp,
    intro i,
    apply @le_supr ennreal ℕ _,
    intros a,
    simp,
    intros x y A4,
    simp,
    apply A1,
    apply A4,
  },
end

lemma supr_as_fun_m_Union {α:Type*} [M:measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (H:monotone f):
(∀ {g : ℕ → set α} (h : ∀ (i : ℕ), is_measurable (g i)), 
  pairwise (disjoint on g) → 
 ((supr_as_fun f) (⋃ (i : ℕ), g i) (M.is_measurable_Union g h)) = 
  ∑' (i : ℕ), (supr_as_fun f) (g i) (h i)) :=
begin
  intros g h A1,
  rw supr_as_fun_apply,
  have A2:(λ i, supr_as_fun f (g i) (h i)) = (λ i, (⨆ n:ℕ, f n (g i) )),
  {
    apply funext,
    intro i,
    rw supr_as_fun_apply,
  },
  rw A2,
  clear A2,
  have A3:(λ (n : ℕ), (f n) (⋃ (i : ℕ), g i))= (λ (n : ℕ),∑' i,  (f n) (g i)),
  {
    apply funext,
    intro n,
    apply (f n).m_Union h A1,
  },
  rw A3,
  clear A3,
  apply supr_sum_eq_sum_supr,
  intros x y A4,
  simp,
  rw le_func_def2,
  intro n,
  apply H,
  apply A4,
  apply h,
end

noncomputable def supr_as_measure {α:Type*} [M:measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (H:monotone f):measure_theory.measure α :=
  measure_theory.measure.of_measurable (supr_as_fun f) (@supr_as_fun_empty α M f)
  (@supr_as_fun_m_Union α M f H)


lemma supr_as_measure_def {α:Type*} [M:measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (H:monotone f):(supr_as_measure f H) =
  measure_theory.measure.of_measurable (supr_as_fun f) (@supr_as_fun_empty α M f)
  (@supr_as_fun_m_Union α M f H) := rfl


lemma supr_as_measure_apply {α:Type*} [M:measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (H2:monotone f) (s:set α) (H:is_measurable s):
  (supr_as_measure f H2) s = (λ s,(⨆ n:ℕ, f n s))  s := 
begin
  rw supr_as_measure_def,
  rw measure_theory.measure.of_measurable_apply s H,
  rw supr_as_fun_apply f s,
end


lemma measure_theory.measure.Union_nat {α : Type*} [M : measurable_space α] 
    {μ:measure_theory.measure α} {f:ℕ → set α}:μ (⋃ i, f i) ≤ ∑' i, μ (f i) :=
begin
  rw measure.apply,
  have A1:(λ i, μ (f i))=(λ i, μ.to_outer_measure.measure_of (f i)) := rfl,
  rw A1,
  apply measure_theory.outer_measure.Union_nat,
end


lemma infi_eq_infi {α β:Type*} [has_Inf β] {f:α → β} {g:α → β}:
    (∀ a:α, f a =  g a) →
    (⨅ a:α, f a) = ⨅ a:α, g a :=
begin
  intro A1,
  have A2:f = g,
  {
    ext,
    apply A1,
  },
  rw A2,
end  

lemma supr_eq_supr {α β:Type*} [has_Sup β] {f:α → β} {g:α → β}:
    (∀ a:α, f a =  g a) →
    (⨆ a:α, f a) = ⨆ a:α, g a :=
begin
  intro A1,
  have A2:f = g,
  {
    ext,
    apply A1,
  },
  rw A2,
end 


lemma infi_commute_helper {α β:Sort} {γ:Type*} [complete_lattice γ] {f:α → β → γ}:
    (⨅ a:α,⨅ b:β, f a b) ≤ ⨅ b:β, ⨅ a:α, f a b :=  
begin
    apply le_infi,
    intro b,
    apply le_infi,
    intro a,
    have A1:(⨅ (a : α) (b : β), f a b)≤(⨅ (b : β), f a b),
    {
      apply infi_le,
    },
    apply le_trans A1,
    apply infi_le,
end  


lemma infi_commute {α β:Sort} {γ:Type*} [complete_lattice γ] {f:α → β → γ}:
    (⨅ a:α,⨅ b:β, f a b) = ⨅ b:β, ⨅ a:α, f a b :=  
begin
  apply le_antisymm,
  {
    apply infi_commute_helper,
  },
  {
    apply infi_commute_helper,
  },
end  


lemma measure_theory.measure.to_outer_measure_def {α : Type*} [M : measurable_space α] 
    {μ:measure_theory.measure α} {s:set α}:
   μ s = ⨅ (s':set α) (H:is_measurable s') (H2:s⊆ s'), μ s' :=
begin
  rw measure_theory.measure_eq_infi,
  apply infi_eq_infi,
  intro s',
  rw infi_commute,
end


lemma measure_theory.measure.of_measurable_apply3 {α : Type*} [M : measurable_space α] 
    {m : Π (s : set α), is_measurable s → ennreal} {m0 : m ∅ is_measurable.empty = 0} 
    {mU : ∀ (f : ℕ → set α) (h : ∀ (i : ℕ), is_measurable (f i)), pairwise (disjoint on f) → (m
    (⋃ (i : ℕ), f i) (M.is_measurable_Union f h)) = ∑' (i : ℕ), m (f i) (h i)} 
  (s : set α): 
   (measure_theory.measure.of_measurable m m0 mU) s = 
    ⨅ (s':set α) (H:is_measurable s') (H2:s⊆ s'), m s' H :=
begin
  rw measure_theory.measure.to_outer_measure_def,
  have A1:(λ s':set α, ⨅  (H : is_measurable s') (H2 : s ⊆ s'), (measure_theory.measure.of_measurable m m0 mU) s') =
    (λ s':set α,  ⨅ (H : is_measurable s') (H2 : s ⊆ s'), m s' H),
  {
    apply funext,
    intro s',
    have A1A:(λ (H : is_measurable s'), ⨅ (H2 : s ⊆ s'), 
             (measure_theory.measure.of_measurable m m0 mU) s') =
             λ (H : is_measurable s'), ⨅  (H2 : s ⊆ s'), m s' H,
    {
      apply funext,
      intro A1A1,
      have A1A2:(λ (H2 : s ⊆ s'), (measure_theory.measure.of_measurable m m0 mU) s') =
                 λ  (H2 : s ⊆ s'), m s' A1A1,
      {
        apply funext,
        intro A1A2A,
        apply @measure_theory.measure.of_measurable_apply α M m m0 mU,
      },
      rw A1A2,
    },
    rw A1A,
  },
  rw A1,
end


lemma supr_as_measure_apply2 {α:Type*} [M:measurable_space α] 
    (f:ℕ → (measure_theory.measure α)) (H2:monotone f) (s:set α):
  (supr_as_measure f H2) s = ⨅ (s':set α) (H:is_measurable s') (H2:s⊆ s'),  (⨆ n:ℕ, f n s') := 
begin
  rw supr_as_measure_def,
  rw measure_theory.measure.of_measurable_apply3,
  have A1:(λ (s' : set α), ⨅ (H : is_measurable s') (H2 : s ⊆ s'), supr_as_fun f s' H) =
    λ (s' : set α), ⨅ (H : is_measurable s') (H2 : s ⊆ s'), ⨆ (n : ℕ), (f n) s',
  {
    apply funext,
    intro s',
    have A1A:(λ (H : is_measurable s'), ⨅ (H2 : s ⊆ s'), supr_as_fun f s' H) =
              λ (H : is_measurable s'), ⨅ (H2 : s ⊆ s'), ⨆ (n : ℕ), (f n) s',
    {
      apply funext,
      intro H,
      have A1A1:(λ (H2 : s ⊆ s'), supr_as_fun f s' H) =
              λ  (H2 : s ⊆ s'), ⨆ (n : ℕ), (f n) s',
      {
        apply funext,
        intro H2,
        rw supr_as_fun_apply,
      },
      rw A1A1,
    },
    rw A1A,
  },
  rw A1,
end


lemma supr_eq_supr_to_outer_measure_measure_of_of_monotone {α:Type*}
   [M:measurable_space α]  {g:ℕ → measure_theory.measure α}
   :monotone g → 
    (supr ((λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) ∘ g) =
    (λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) (supr g)) :=
begin
  intro A1,
  apply @supr_eq_supr_to_outer_measure_measure_of α ℕ M g (@supr_as_measure α M g A1),
  simp,
  apply funext,
  intro s,
  rw supr_as_measure_apply2,
  apply le_antisymm,
  {
    apply @le_infi ennreal (set α) _,
    intro s',
    apply @le_infi ennreal _ _,
    intro H,
    apply @le_infi ennreal _ _,
    intro H2,
    rw supr_apply,
    apply @supr_le_supr ennreal ℕ _,
    intro n,
    apply measure_theory.measure_mono,
    apply H2,
  },
  {
    rw supr_apply,    
    have C1:(λ (i : ℕ), (g i) s)
            = λ i, ⨅ (s':set α) (H:is_measurable s') (H2:s⊆ s'), (g i) s' ,
    {
      apply funext,
      intro i,
      apply measure_theory.measure.to_outer_measure_def,
    },
    rw C1,
    clear C1,
    apply ennreal.infi_le,
    intros ε C2 C3,

    have C4:∃ (f:ℕ → (set α)), (∀ i:ℕ, 
        (is_measurable (f i)) ∧
        (s ⊆ (f i)) ∧
         ((g i (f i)) ≤ 
      ( ⨅ (s' : set α) (H : is_measurable s') (H2 : s ⊆ s'), (g i) s') + (ε:ennreal))), 
    {
      have C4A:(∀ i:ℕ, ∃  s'':set α,
        (is_measurable (s'')) ∧
        (s ⊆ (s'')) ∧
         ((g i (s'')) ≤ 
      ( ⨅ (s' : set α) (H : is_measurable s') (H2 : s ⊆ s'), (g i) s') + (ε:ennreal))), 
      {
        intro i,
        rw @lt_top_iff_ne_top ennreal _ _ at C3,
        have C4B:=@ne_top_of_supr_ne_top ℕ _ i C3,
        have C4C:(⨅ (s' : set α) (H : is_measurable s') (H2 : s ⊆ s'), (g i) s')≠ ⊤ ,
        {
          apply C4B,
        },
        
        have C4E := lt_top_iff_ne_top.mpr C4C,
        have C4D := ennreal.infi_elim C2 C4E,
        cases C4D with s'' C4D,
        apply exists.intro s'',
        simp at C4D,
        have C4F: (⨅ (s' : set α) (H : is_measurable s') (H2 : s ⊆ s'), (g i) s') + ↑ε < ⊤,
        {
          rw with_top.add_lt_top,
          split,
          apply C4E,
          simp,
        },
        have C4G := lt_of_le_of_lt C4D C4F,
        have C4H := of_infi_lt_top C4G,
        rw infi_prop_def at C4G,
        have C4I := of_infi_lt_top C4G,
        rw infi_prop_def at C4G,        
        split,
        {
          apply C4H,
        },
        split,
        {
          apply C4I,
        },
        rw infi_prop_def at C4D,
        rw infi_prop_def at C4D,
        apply C4D,
        apply C4I,
        apply C4H,
        apply C4I,
        apply C4H,
      },
      apply @classical.some_func ℕ (set α) _ C4A,
    },
    cases C4 with f C4,
    apply exists.intro (set.Inter f),
    rw infi_prop_def,
    rw infi_prop_def,
    rw ennreal.supr_add,
    apply @supr_le_supr ennreal ℕ _ (λ n, (g n) (set.Inter f)),
    {
      intro i,   
      have D1:(λ (n : ℕ), (g n) (set.Inter f)) i ≤ (g i) (f i),
      {
        simp,
        apply measure_theory.measure_mono,
        apply @set.Inter_subset α ℕ f,
      },
      apply le_trans D1 (C4 i).right.right,  
    },
    {
      apply set.subset_Inter,
      intro i,
      apply (C4 i).right.left,      
    },
    {
      apply is_measurable.Inter,
      intro i,
      apply (C4 i).left,      
    },
  },
end


lemma supr_eq_supr_to_outer_measure_measure_of_of_monotone' {α:Type*}
   [M:measurable_space α]  {g:ℕ → measure_theory.measure α}
   :monotone g → 
    (supr ((λ ν:measure_theory.measure α, ν.to_outer_measure.measure_of) ∘ g) =
    (supr g).to_outer_measure.measure_of) :=
begin
  apply supr_eq_supr_to_outer_measure_measure_of_of_monotone,
end


lemma ennreal.Sup_eq_supr {S:set ennreal}:S.nonempty →
   (∃ f:ℕ → ennreal, 
      (∀ n, f n ∈ S) ∧
      (supr f = Sup S)) :=
begin
  intro A1,
  cases (classical.em (Sup S = ⊤)) with A2 A2, 
  {
    -- If Sup S = ⊤, then we have a sequence that is larger than every natural.
    have B1:∀ n:ℕ, ∃ s:ennreal,  (s∈ S) ∧ (n:ennreal) ≤ s,
    {
      intro n,
      rw Sup_eq_top at A2,
      have B1A:=A2 n _,
      cases B1A with s B1A,
      cases B1A with B1A B1B,
      apply exists.intro s,
      apply and.intro B1A (@le_of_lt ennreal _ _ _ B1B),
      have B1C:(n:ennreal) = ((n:nnreal):ennreal),
      {
        simp,
      },
      rw B1C,
      apply ennreal.coe_lt_top,
    },
    have B2:=classical.some_func B1,
    cases B2 with f B2,
    apply exists.intro f,
    simp at B2,
    split,
    {
      intro n,
      apply (B2 n).left,
    },
    {
      rw A2,
      rw ← top_le_iff,
      rw ← ennreal.supr_coe_nat,
      apply @supr_le_supr ennreal ℕ _,
      intro n,
      apply (B2 n).right,
    },
  },
  {
    have C1:∀ n:ℕ, ∃ s:ennreal, (s∈S) ∧ (Sup S - (1/(n.succ:ennreal)) ≤ s),
    {
      intro n,
      have C1A:=@ennreal.Sup_elim S (1/(n.succ:nnreal)) _ A1 A2,
      cases C1A with s C1A,
      cases C1A with C1A C1B,
      apply exists.intro s,
      apply and.intro C1A _,
      rw ennreal.coe_div at C1B,
      simp at C1B,
      simp,
      apply C1B,
      simp,
      simp,
      apply zero_lt_one,  
    },
    have C2:=classical.some_func C1,
    cases C2 with f C2,
    apply exists.intro f,
    split,
    {
      intro n,
      apply (C2 n).left,
    },
    apply le_antisymm,
    {
      apply @supr_le ennreal _ _,
      intro i,
      have C3 := C2 i,
      apply @le_Sup ennreal _ _,
      apply C3.left,
    },
    apply @ennreal.le_of_forall_epsilon_le,
    intros ε C4 C5,
    have C6 := nnreal.exists_unit_frac_lt_pos C4,
    cases C6 with n C6,
    have C7 := C2 n,  
    have C8:Sup S ≤ f n + ε,
    {
      have C8A:1/ ((nat.succ n):ennreal) ≤ (ε:ennreal),
      {
        simp,
        rw ← ennreal.coe_one,
        have C8A1:(n:ennreal) = ((n:nnreal):ennreal),
        {
          simp,
        },
        rw C8A1,
        rw ← ennreal.coe_add,
        rw ← ennreal.coe_div,
        rw ennreal.coe_le_coe,
        apply le_of_lt,
        apply C6,
        simp,
      },
      have C8B:Sup S - (ε:ennreal) ≤
               Sup S - 1/ ((nat.succ n):ennreal),
      {
        apply ennreal.sub_le_sub,
        apply le_refl (Sup S),
        apply C8A,    
      },
      have C8C:Sup S - (ε:ennreal) ≤ f n,
      {
        apply le_trans C8B C7.right,
      },
      rw add_comm,
      rw ← ennreal.sub_le_iff_le_add',
      apply C8C,   
    },
    apply le_trans C8,
    have C9 := le_supr f n,
    apply add_le_add_right C9,
  },
end


def Sup_so_far {α:Type*} [semilattice_sup_bot α] (f:ℕ → α) (n:ℕ):α :=
  (finset.range (n.succ)).sup f


lemma Sup_so_far_def {α:Type*} [semilattice_sup_bot α] {f:ℕ → α} 
    {n:ℕ}:
    Sup_so_far f n = (finset.range (n.succ)).sup f := rfl


lemma le_Sup_so_far {α:Type*} [semilattice_sup_bot α] (f:ℕ → α):
   f ≤ (Sup_so_far f) := 
begin
  rw le_func_def2,
  intro n,
  rw Sup_so_far_def,
  apply finset.le_sup,
  simp,
end



lemma finset.sup_closed {α β:Type*} [decidable_eq α] 
   [semilattice_sup_bot β]
   (S:finset α) 
   (f:α → β) (T:set β):
   (⊥ ∈ T) →
   (∀ a∈ S, f a ∈ T) →
   (∀ a∈ T, ∀ b∈ T, a⊔b ∈ T) →
   (S.sup f ∈ T) :=
begin
  intros A1 A2 A3,
  revert A2,
  apply finset.induction_on S,
  {
    intros B1,
    simp,
    apply A1,
  },
  {
    intros a S C1 C2 C3,
    simp,
    apply A3,
    {
      apply C3,
      simp,  
    },
    {
      apply C2,
      intro a2,
      intro C4,
      apply C3,
      simp,
      apply or.inr C4,  
    },
  },
end


lemma finset.sup_closed_nonempty {α β:Type*} [decidable_eq α] 
   [semilattice_sup_bot β]
   (S:finset α) 
   (f:α → β) (T:set β):
   (S ≠ ∅) →
   (∀ a∈ S, f a ∈ T) →
   (∀ a∈ T, ∀ b∈ T, a⊔b ∈ T) →
   (S.sup f ∈ T) :=
begin
  intros A2 A4 A3,
  revert A2,
  revert A4,
  apply finset.induction_on S,
  {
    intros B1,
    simp,
  },
  {
    intros a S C1 C2 C3,
    simp,
    cases classical.em (S = ∅) with C5 C5,
    {
      subst S,
      simp,
      apply C3,
      simp,
    },
    apply A3,
    {
      apply C3,
      simp,  
    },
    {
      apply C2,
      intro a2,
      intro C4,
      apply C3,
      simp,
      apply or.inr C4,  
      apply C5,
    },
  },
end


lemma Sup_so_far_of_closed {α:Type*} [semilattice_sup_bot α] (f:ℕ → α) (S:set α):
   (∀ n:ℕ, f n ∈ S) →
   (∀ a∈ S, ∀ b∈ S, a⊔b ∈ S) →
   (∀ n:ℕ, (Sup_so_far f n ∈ S)) :=
begin
  intros A1 A2 n,
  rw Sup_so_far_def,
  apply finset.sup_closed_nonempty,
  {
    --simp,
    --apply set.nonempty_of_contains,
    --unfold finset.range,
    rw finset.range_eq_Ico,
    intro B1,
    rw finset.Ico.eq_empty_iff at B1,
    simp at B1,
    apply nat.succ_ne_zero n B1,
  },
  {
    intros n2 C1,
    apply A1,
  },
  {
    apply A2,
  },
end


lemma monotone_Sup_so_far {α:Type*} [semilattice_sup_bot α] (f:ℕ → α):
   monotone (Sup_so_far f) := 
begin
  intros a b A1,
  rw Sup_so_far_def,
  rw Sup_so_far_def,
  apply finset.sup_mono,
  simp,
  apply nat.succ_le_succ A1,
end


/- For supr_measure_eq_measure_supr, this is a more
   useful rewrite, as (finset.range (nat.succ n)).sum f = f n -/ 
lemma ennreal.lim_finset_sum_succ_eq_tsum {f:ℕ → ennreal}:
(⨆  n, (finset.range (nat.succ n)).sum f)  = tsum f :=
begin
  apply le_antisymm,
  {
    apply @supr_le ennreal _ _,
    intro n,
    apply ennreal.finset_sum_le_tsum,
  },
  {
    rw ← ennreal.tsum_le,
    intro n,
    cases n,
    {
      simp,
    },
    {
      apply @le_supr ennreal _ _,
    },
  }
end


/-
  This is useful to prove Hahn decomposition.
  No wait, it's not.
 -/
lemma supr_measure_eq_measure_supr {α:Type*}
    [M:measurable_space α] {μ:measure_theory.measure α}
    {f:ℕ → set α}:(∀ n, is_measurable (f n)) →
    monotone f →
    supr (λ n, μ (f n)) = μ (supr f) :=
begin
  intros A1 A2,
  rw supr_eq_Union,
  rw ← Union_sub_pred,
  rw measure.apply,
  rw measure_theory.measure.m_Union,
  rw ← ennreal.lim_finset_sum_succ_eq_tsum,
  have A3:(λ (i : ℕ), μ.to_outer_measure.measure_of (sub_pred f i))
          = (λ (i : ℕ), μ (sub_pred f i)),
  {
    apply funext,
    intro i,
    rw measure.apply,
  },
  rw A3,
  have A5:(λ (n : ℕ), finset.sum (finset.range n.succ)
          (λ (i : ℕ), μ (sub_pred f i)))=
          (λ n, μ (f n) ),
  {
    apply funext,
    intro n,
    rw @measure_finset_sum α M μ (sub_pred f) _,
    rw union_range_sub_pred,
    rw union_finset_range_monotone,
    apply A2,
    intro m,
    apply is_measurable_sub_pred A1,
    apply sub_pred_pairwise_disjoint,
    apply A2,
  },
  rw A5,
  intro m,
  apply is_measurable_sub_pred A1,
  apply sub_pred_pairwise_disjoint,
  apply A2,
end


/-
  This theorem is immediately useful to prove the
  existence of the Radon-Nikodym derivative, if 
  α = measure_theory.measure Ω, and g = (λ μ, μ T)
  (see Sup_apply_eq_supr_apply_of_closed). 
  However, if α = set Ω, and g = μ, then this
  can be used to prove the Hahn decomposition variant.
  The critical proof is that supr (μ T) =
  μ (supr T).
 -/
lemma Sup_apply_eq_supr_apply_of_closed' {α:Type*}
  [complete_lattice α] {S:set α} (g:α → ennreal):
  (∀ (a∈ S) (b∈ S), a ≤ b → g a ≤ g b) →
  (∀ f:ℕ → α, (set.range f ⊆ S) → 
               monotone f → supr (g ∘ f) = g (supr f)) →
  (S.nonempty) →
  (∀ a ∈ S, ∀ b ∈ S, a ⊔ b ∈ S)→
  (∃ f:ℕ → α,
            (∀ n, f n ∈ S) ∧ 
            (monotone f) ∧
            g (supr f) = Sup (g '' S)) :=
begin
  intros A1 AX A2 A3,
  have B1:(g '' S).nonempty,
  {
    apply set.nonempty_image_of_nonempty A2,
  },
  have B1X := ennreal.Sup_eq_supr B1,
  cases B1X with f' B1X,
  have B2:∃ f'':ℕ → α, ∀ n:ℕ, 
          (f'' n)∈ S ∧ g (f'' n) = f' n, 
  {
    apply @classical.some_func ℕ α (λ (n:ℕ) (a:α), 
        a∈ S ∧ g a = f' n),
    intro n,
    have B2A:=(B1X.left) n,
    simp at B2A,
    cases B2A with a B2A,
    apply exists.intro a,
    simp,
    apply B2A,
  },
  cases B2 with f'' B2,
  have C1:∀ (n : ℕ), Sup_so_far f'' n ∈ S,
  {
    apply Sup_so_far_of_closed,
    intro n,
    apply (B2 n).left,
    apply A3,  
  },
  apply exists.intro (Sup_so_far f''),
  split,
  {
    apply C1,
  },
  split,
  {
    apply monotone_Sup_so_far,
  },
  {
    rw ← AX,
    apply le_antisymm,
    {
      apply @supr_le ennreal _ _,
      intro n,
      apply @le_Sup ennreal _ _,
      simp,
      apply exists.intro (Sup_so_far f'' n),
      apply and.intro (C1 n),
      refl,   
    },
    {
      rw ← B1X.right,
      apply @supr_le_supr ennreal _ _,
      intros n,
      rw ← (B2 n).right,
      simp,
      apply A1,
      apply (B2 n).left,
      apply C1 n,
      apply le_Sup_so_far,
    },
    {
      rw set.subset_def,
      intros x C2,
      simp at C2,
      cases C2 with n C2,
      rw ← C2,
      apply C1,
    },
    apply monotone_Sup_so_far,
  },
end



/- This lemma presents a pattern that is repeated
   many times, both for Hahn decomposition and for
   the Lebesgue-Radon-Nikodym theorem. -/
lemma Sup_apply_has_max {α:Type*}
  [complete_lattice α] {S:set α} (g:α → ennreal):
  (∀ (a∈ S) (b∈ S), a ≤ b → g a ≤ g b) →
  (∀ f:ℕ → α, (set.range f ⊆ S) → 
               monotone f → supr (g ∘ f) = g (supr f)) →
  (∀ f:ℕ → α, (set.range f ⊆ S) → 
               monotone f → supr f ∈ S) → 
  (S).nonempty →
  (∀ a ∈ S, ∀ b ∈ S, a ⊔ b ∈ S)→
  (∃ a∈ S, g a = Sup (g '' S)) :=
begin
  intros A1 A2 A3 A4 A5,
  have B1 := Sup_apply_eq_supr_apply_of_closed' g A1 A2 A4 A5,
  cases B1 with f B1,
  apply exists.intro (supr f),
  have C1:set.range f ⊆ S,
  {
    rw set.range_subset_iff,
    apply B1.left,
  },
  have C2 := A3 f C1 B1.right.left,
  apply exists.intro C2,
  apply B1.right.right,
end


lemma Sup_apply_eq_supr_apply_of_closed {α:Type*}
   [M:measurable_space α]  {S:set (measure_theory.measure α)}
   {T:set α}:
  (S.nonempty) →
  (is_measurable T) →
  (∀ μ ∈ S, ∀ ν ∈ S, μ ⊔ ν ∈ S)→
  (∃ f:ℕ → (measure_theory.measure α),
            (∀ n, f n ∈ S) ∧ 
            (monotone f) ∧
            (supr f T = Sup ((λ μ:measure_theory.measure α, μ T) '' S))) :=
begin
  intros A1 A2 A3,
  apply @Sup_apply_eq_supr_apply_of_closed' (measure_theory.measure α) _ S (λ μ:measure_theory.measure α, μ T),
  {
     intros x B1 y B2 B3,
     apply monotone_to_outer_measure_measure_of,
     apply B3,
  },
  {
    intros f CX C1,
    simp,
    have C2:= supr_eq_supr_to_outer_measure_measure_of_of_monotone' C1,
    rw measure.apply,
    rw ← C2,
    rw supr_apply,
    refl,
  },
  {
    apply A1,
  },
  {
    apply A3,
  },
end


/- Note that for outer measures, the supremum commutes with measure_of, in a way. -/
lemma of_function'_supr_measure_of_eq_supr {Ω γ:Type*}
    {h:γ → (measure_theory.outer_measure Ω)}:
      (λ f:set Ω → ennreal, measure_theory.outer_measure.of_function' f)
      (⨆ (i:γ), 
      (λ μ:measure_theory.outer_measure Ω, μ.measure_of) (h i))
      = supr h 
  := 
begin
  apply dual_galois_insertion.l_supr_u',
  apply @galois_insertion_measure_of_of_function' Ω,
end


lemma monotone_integral {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.measure Ω} {f g:Ω → ennreal}:f ≤ g → 
    (μ.integral f)≤μ.integral g :=
begin
  intro A1,
  apply measure_theory.lintegral_mono,
  apply A1,
end

lemma monotone_integral' {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.measure Ω} {f g:Ω → ennreal}:monotone (μ.integral) :=
begin
  apply monotone_integral,
end


-- TODO(martinz): remove measurability requirement?
lemma monotone_with_density {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.measure Ω}
    {f:ℕ → (Ω → ennreal)}:
    monotone f →
    (∀ n, measurable (f n)) → 
    monotone ((μ.with_density) ∘ f) :=
begin
  intros B1 B2 a b A1,
  intros S A2,
  rw measure_theory.with_density_apply2,
  rw measure_theory.with_density_apply2,
  apply monotone_integral,
  apply @monotone_set_indicator Ω ennreal _ _,
  apply B1,
  apply A1,
  --apply B2,
  apply A2,
  --apply B2,
  apply A2,
end


-- Update: I am using this now in R-N theorem.
-- It's not clear to me anymore that this is necessary.
-- However, I am fairly certain it is true.
-- What is missing is proving that (λ i, with_density (h i)) itself is a
-- monotone. It is also probably useful.
lemma supr_with_density_eq_with_density_supr {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.measure Ω}
    {h:ℕ → Ω → ennreal}:
    (∀ n:ℕ, measurable (h n)) →
    (monotone h) →
    supr (λ n:ℕ, μ.with_density (h n)) = μ.with_density (supr h) :=
begin
  intros A1 A2,
  apply measure_theory.measure.ext,
  intros S A3,
  rw ← @supr_with_density_apply_eq_with_density_supr_apply Ω M μ h S A3 A1 A2,
  rw measure.apply,
  rw ← @supr_eq_supr_to_outer_measure_measure_of_of_monotone' Ω M (λ n, μ.with_density (h n)),
  rw supr_apply,
  apply @supr_eq_supr ℕ ennreal _,
  intro n,
  refl,
  apply monotone_with_density,
  apply A2,
  apply A1,
end 




-- The nature of this proof suggests the lemma already exists.
lemma measure_theory.measure.sup_le {Ω:Type*} {N:measurable_space Ω} (μ₁ μ₂ ν:measure_theory.measure Ω):μ₁ ≤ ν → μ₂ ≤ ν → μ₁ ⊔ μ₂ ≤ ν :=
begin
  intros A1 A2,
  simp,
  apply and.intro A1 A2,
end


lemma sup_fun_def {Ω:Type*} {f g:Ω → ennreal}:
    (f ⊔ g) = λ ω:Ω, f ω ⊔ g ω :=
begin
  refl
end

--TODO:remove, trivial?
lemma ennreal.sup_apply {Ω:Type*} {f g:Ω → ennreal} {x:Ω}:
    (f ⊔ g) x = f x ⊔ g x :=
begin
  apply sup_apply,
end


--Extensible to a (complete?) linear order.
lemma ennreal.lt_sup_iff {a b c:ennreal}:
  c < a ⊔ b ↔ c < a ∨ c < b :=
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


lemma measurable_sup {Ω:Type*} {M:measurable_space Ω} 
  {f g:Ω → ennreal}:measurable f → measurable g → 
    measurable (f ⊔ g) :=
begin
  intros A1 A2,
  /- Proof sketch:
     x is measurable iff if ∀ a, x⁻¹ (a,⊤] is measurable.
     (f ⊔ g)⁻¹ (a,⊤] =f⁻¹ (a,⊤]∪g⁻¹ (a,⊤].
     Since the union of two measurable functions is measurable,
     we are done.
   -/ 
  apply is_ennreal_measurable_intro_Ioi,
  intro a,
  have A3:(f ⊔ g) ⁻¹' {y : ennreal | a < y}=
      f ⁻¹' {y : ennreal | a < y}∪
      g ⁻¹' {y : ennreal | a < y},
  {
    simp,
    ext,
    split;intros A3A;simp at A3A;simp;apply A3A,
  },
  rw A3,
  apply is_measurable.union,
  {
    apply A1,
    apply is_ennreal_is_measurable_intro_Ioi,
  },
  {
    apply A2,
    apply is_ennreal_is_measurable_intro_Ioi,
  },
end



--Could remove, but let's leave it here for now.
lemma ennreal.is_measurable_le {Ω:Type*} {M:measurable_space Ω}
  {x y:Ω → ennreal}:measurable x → measurable y →
  is_measurable {ω:Ω|x ω ≤ y ω} :=
begin
  intros A1 A2,
  apply is_measurable_le A1 A2,
end



lemma with_density_le_with_density {Ω:Type*} {M:measurable_space Ω}
  {μ:measure_theory.measure Ω} {x y:Ω → ennreal} 
  {S:set Ω}:
  is_measurable S →
  (∀ ω ∈ S, x ω ≤ y ω) →  
  μ.with_density x S ≤ μ.with_density y S :=
begin
  intros A3 A4,
  rw measure_theory.with_density_apply2 μ x S A3,
  rw measure_theory.with_density_apply2 μ y S A3,
  apply integral.monotone,
  rw le_func_def2,
  intros ω,
  cases (classical.em (ω ∈ S)) with A5 A5,
  {
    rw set.indicator_of_mem A5,
    rw set.indicator_of_mem A5,
    apply A4 _ A5,
  },
  {
    rw set.indicator_of_not_mem A5,
    rw set.indicator_of_not_mem A5,
    apply le_refl _,
  },
end


--TODO(martinz): Remove measurability?
lemma with_density_sup_of_le {Ω:Type*} {M:measurable_space Ω}
  {μ:measure_theory.measure Ω} {x y:Ω → ennreal} 
  {S:set Ω}:measurable x → measurable y →
  is_measurable S →
  (∀ ω ∈ S, x ω ≤ y ω) →  
  μ.with_density (x⊔y) S = μ.with_density y S :=
begin
  intros A1 A2 A3 A4,
  rw measure_theory.with_density_apply2 μ (x ⊔ y) S A3,
  rw measure_theory.with_density_apply2 μ y S A3,
  have A5:set.indicator S (x ⊔ y) = set.indicator S y,
  {
    apply funext,
    intro ω,
    cases (classical.em (ω∈ S)) with A5A A5A,
    {
      rw set.indicator_of_mem A5A,
      rw set.indicator_of_mem A5A,
      rw sup_apply,
      simp,
      apply max_eq_right (A4 _ A5A),
      --simp,
    },
    {
      rw set.indicator_of_not_mem A5A,
      rw set.indicator_of_not_mem A5A,
    },
  },
  rw A5,
end


lemma measure_theory.measure.sup_le_apply {Ω:Type*}
  {M:measurable_space Ω}
  {μ ν m:measure_theory.measure Ω}
  {S:set Ω}:is_measurable S →
  (μ ≤ m) →
  (ν ≤ m) → 
  (μ ⊔ ν) S ≤ m S :=
begin
  intros A1 A2 A3,
  have A4:μ ⊔ ν ≤ m := 
      @sup_le (measure_theory.measure Ω) _ μ ν m A2 A3,
  apply A4,
  apply A1,
end


------------------------------------------------

--No such (sane) set exists, certainly not if μ and ν are finite.
--Note that we don't make the system inconsistent
--by constructing a definition that is possibly unsatisfiable.
--The general idea that we want to prove is that if μ X < ν X,
--then there must be some pure set X'⊆ X, where for all subsets
-- X''⊆ X', μ X'' ≤ ν X'', and μ X' < ν X'. A hahn crazy set
--is a counterexample to this theorem.
def hahn_crazy_set {α:Type*} [M:measurable_space α] 
  (μ ν:measure_theory.measure α) (X:set α):Prop :=
    (μ X < ν X) ∧ 
    is_measurable X ∧ 
    (∀ X':set α,  (X' ⊆ X) → (μ X' < ν X')  →  
    ¬ (le_on_subsets μ ν X'))


lemma hahn_crazy_set_def {α:Type*} [M:measurable_space α] 
  (μ ν:measure_theory.measure α) (X:set α):
  hahn_crazy_set μ ν X =
    ((μ X < ν X) ∧ 
    is_measurable X ∧ 
    (∀ X':set α,  (X' ⊆ X) → (μ X' < ν X')  →  
    ¬ (le_on_subsets μ ν X'))) := rfl



lemma measure_theory.measure_diff' {α:Type*}
    [measurable_space α] {μ:measure_theory.measure α}
    {s₁ s₂:set α}:s₂ ⊆ s₁ →  is_measurable s₁ →
    is_measurable s₂ → μ s₂ < ⊤ →
    μ (s₁ \ s₂) = μ s₁ - μ s₂ :=
begin
  apply measure_theory.measure_diff,
end


lemma with_top.not_none_lt {α:Type*} [preorder α] (a:with_top α):
  ¬(@has_lt.lt (with_top α) _  (none:with_top α) a):=
begin
  intro A1,
  rw lt_iff_le_not_le at A1,
  cases A1 with A1 A2,
  apply A2,
  apply with_top.none_le,
end

lemma with_top.not_none_le_some {α:Type*} [partial_order α] (a:α):
  ¬(@has_le.le (with_top α) _ (none) (some a)):=
begin
  intro A1,
  have B1:(some a) ≠ (none:with_top α),
  {
    simp,
  },
  have B3:(@has_le.le (with_top α) _ (some a) (none)) := with_top.none_le,
  have B4 := @le_antisymm (with_top α) _ (some a) (none) B3 A1,
  apply B1,
  apply B4
end


lemma ennreal.sub_lt_sub_of_lt_of_le {a b c d:ennreal}:a < b →
  c ≤ d →
  d ≤ a →
  a - d < b - c :=
begin
  intros A1 A2 A3,
  have B1:(⊤:ennreal) = none := rfl,
  have B2:∀ n:nnreal,  (some n) = n,
  {
    intro n,
    refl,
  },
  cases a,
  {
    exfalso,
    apply @with_top.not_none_lt nnreal _ b A1,
  },
  cases d,
  {
    exfalso,
    apply @with_top.not_none_le_some nnreal _ a A3,
  },
  cases c,
  {
    exfalso,
    apply @with_top.not_none_le_some nnreal _ d A2,
  },
  cases b,
  {
    simp,
    rw ← ennreal.coe_sub,
    rw B1,
    rw ← B2,
    apply with_top.none_lt_some,
  },
  repeat {rw B2},
  repeat {rw ← ennreal.coe_sub},
  rw ennreal.coe_lt_coe,
  apply nnreal.sub_lt_sub_of_lt_of_le,
  repeat {rw B2 at A1},
  rw ennreal.coe_lt_coe at A1,
  apply A1,
  
  repeat {rw B2 at A2},
  rw ennreal.coe_le_coe at A2,
  apply A2,

  repeat {rw B2 at A3},
  rw ennreal.coe_le_coe at A3,
  apply A3,
end


--The contradiction proofs chip away at this set. This
--theorem shows that when you chip a piece off a crazy set,
--a crazy set remains.
lemma hahn_crazy_set_subset {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α)
  (X:set α) (X':set α):
  hahn_crazy_set μ ν X → 
  X' ⊆ X →
  is_measurable X' →
  --μ X' < ⊤ →
  ν X' ≤ μ X' →
  hahn_crazy_set μ ν (X\X') :=
begin
  intros A1 A2 A3 A5,
  rw hahn_crazy_set_def at A1,
  have A4:μ X' < ⊤,
  {
    have A4A:μ X' ≤ μ X,
    {
      apply measure_theory.measure_mono A2,
    },
    apply lt_of_le_of_lt A4A,
    apply lt_of_lt_of_le A1.left,
    apply @le_top ennreal _,
    --A1.left,
  },
  have B1:is_measurable (X \ X'),
  {
    apply is_measurable.diff A1.right.left A3,
  },
  have B2:μ (X \ X') < ν (X \ X'),
  {
    rw measure_theory.measure_diff' A2 A1.right.left A3 A4, 
    rw measure_theory.measure_diff' A2 A1.right.left A3
       (lt_of_le_of_lt A5 A4),
    -- ⊢ ⇑μ X - ⇑μ X' < ⇑ν X - ⇑ν X'
    apply ennreal.sub_lt_sub_of_lt_of_le,
    { -- ⊢ ⇑μ X < ⇑ν X
      apply A1.left,
    },
    { -- ⊢ ⇑ν X' ≤ ⇑μ X'
      apply A5,
    },
    { -- ⊢ ⇑μ X' ≤ ⇑μ X
      apply (measure_theory.measure_mono A2),
    },
  },
  rw hahn_crazy_set_def,
  apply and.intro B2,
  apply and.intro B1,
  intros X'' C1 C2,
  apply A1.right.right,
  apply @set.subset.trans α X'' (X \ X') X C1,
  apply set.diff_subset,
  apply C2,
end

lemma hahn_crazy_set_self {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α)
  (X:set α):hahn_crazy_set μ ν X →
  ¬le_on_subsets μ ν X :=
begin
  intros A1,
  rw hahn_crazy_set_def at A1,
  apply A1.right.right X (set.subset.refl _) A1.left,
end


--In a hahn_crazy_set μ ν X, you will find sets X'⊆ X where ν X' < μ X',
--even though μ X < ν X. So, by creating X - X', you get an even crazier
--set. In hahn_crazy_diff_big below, we show how we can select an element
--that is big ENOUGH.
def hahn_crazy_diff_set {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α)
  (X:set α):set (set α) := { X':set α|X' ⊆ X ∧ is_measurable X' ∧ 
                      μ X' < ν X'}

lemma hahn_crazy_diff_set_def {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α):hahn_crazy_diff_set μ ν X = 
  { X':set α|X' ⊆ X ∧ is_measurable X' ∧ μ X' < ν X'} := rfl



lemma hahn_crazy_diff_set_nonempty {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α):is_measurable X → 
  ¬le_on_subsets ν μ X →
  (hahn_crazy_diff_set μ ν X).nonempty :=
begin
  intros A1 A2,
  rw set.nonempty_iff_ne_empty,
  intro A3,
  apply A2,
  rw le_on_subsets_def,
  apply and.intro A1,
  intros X' B1 B2,
  rw hahn_crazy_diff_set_def at A3,
  apply @le_of_not_lt ennreal _,
  intro C1,
  apply @set.eq_empty_elim (set α) _ X' A3,
  simp,
  apply and.intro B1 (and.intro B2 C1),
end


lemma hahn_crazy_diff_set_nonempty' {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α): 
  hahn_crazy_set ν μ X →
  (hahn_crazy_diff_set μ ν X).nonempty :=
begin
  intros A1,
  apply hahn_crazy_diff_set_nonempty,
  have A2 := (hahn_crazy_set_def ν μ X).mp A1,
  apply A2.right.left,
  apply hahn_crazy_set_self,
  apply A1,
end


lemma pred_eq_set {α:Type*} {S:set α} {a:α}:
    (S a) = (a∈ S) := rfl


lemma nat.find_spec_set {S : set ℕ} [_inst_1 : decidable_pred S] (H : ∃ (n : ℕ), S n):(nat.find H) ∈ S :=
begin
  rw ← pred_eq_set,
  apply nat.find_spec,
end


lemma nat.Inf_of_nonempty {S:set ℕ}:S.nonempty → Inf S ∈ S :=
begin
  intro A1,
  have A2:= set.contains_of_nonempty A1,
  rw nat.Inf_def A2,
  have A3:decidable_pred S := classical_set ℕ S,
  apply nat.find_spec_set,
end


lemma nat.exists_le_Inf_map 
  {α:Type*} {f:α → ℕ} {S:set α}:S.nonempty → ∃ s∈ S,
  ∀ a∈ S, f s ≤ f a :=
begin
  intro A1,
  let n := Inf (f '' S),
  begin
    have A2:(f '' S).nonempty,
    {
      apply set.nonempty_image_of_nonempty A1,
    },
    have A3 := nat.Inf_of_nonempty A2,
    simp at A3,
    cases A3 with a A3,
    apply exists.intro a,
    apply exists.intro A3.left,
    intros b B1,
    rw A3.right,
    apply nat.Inf_le,
    simp,
    apply exists.intro b,
    apply and.intro B1,
    refl,
  end
end

lemma nat.le_Inf  {S:set ℕ} {a:ℕ}:S.nonempty → (∀ s∈ S,
  a ≤ s) → a ≤ Inf S := 
begin
  intros A1 A2,
  apply A2,
  apply nat.Inf_of_nonempty A1,
end

lemma nat.exists_eq_Inf_map {α:Type*} {f:α → ℕ} {S:set α}:S.nonempty → 
    ∃ s∈ S, f s = Inf (f '' S) :=
begin
  intros A1,
  have B1:(f '' S).nonempty,
  {
    apply set.nonempty_image_of_nonempty A1,
  },

  have B2 := nat.Inf_of_nonempty B1,
  simp at B2,
  cases B2 with a B2,
  cases B2 with B2 B3,
  apply exists.intro a,
  apply exists.intro B2,
  apply B3,
end



--Notice that this function chooses the minimum n that is greater than or equal to the inverse.
--Put another way, this chooses the maximum 1/n that is less than or equal to the value.
noncomputable def floor_simple_fraction (x:ennreal):ℕ  := Inf {n:ℕ|(n:ennreal) ≥ x⁻¹}


--This is a way of selecting a "big" input of a function when it is hard to select a maximum
--input. Because we are mapping the extended non-negative reals onto the naturals with a
--monotonically decreasing function, and for any nonempty set of natural numbers there is
--a minimum, we get a set of "big" inputs to the function, and we apply classical.some, we 
--get one of these values.
-- 
--This is good for showing progress: if we whittle away something, and get smaller and
--smaller results, we eventually grab every nonzero result remaining.
lemma hahn_infi_ennreal {α:Type*} {f:α→ ennreal} (S:set α):S.nonempty → 
  ∃ a∈ S, 
  (floor_simple_fraction ∘ f) a = Inf ((floor_simple_fraction ∘ f) '' S) :=
begin
  intro A1,
  apply nat.exists_eq_Inf_map,
  apply A1,
end 


/-
  When we start with some hahn_crazy_set μ ν X, we know μ X < ν X. We want to
  grab a big chunk X' where ν X' < μ X'. This can only go on for so long.

  NOTE: there WAS a sign mistake here, where I flipped μ and ν in the difference.
-/
def hahn_crazy_diff_big {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):set α :=
  classical.some
  (@hahn_infi_ennreal (set α) (λ X':set α, μ X' - ν X')
  (hahn_crazy_diff_set ν μ X) (hahn_crazy_diff_set_nonempty' ν μ X H))


lemma hahn_crazy_diff_big_def {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):hahn_crazy_diff_big μ ν X H =
  classical.some
  (@hahn_infi_ennreal (set α) (λ X':set α, μ X' - ν X')
  (hahn_crazy_diff_set ν μ X) (hahn_crazy_diff_set_nonempty' ν μ X H)) := rfl


lemma hahn_crazy_diff_big_spec {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):
 (hahn_crazy_diff_big μ ν X H) ∈ 
  (hahn_crazy_diff_set ν μ X) ∧
  (floor_simple_fraction ∘ (λ X':set α, μ X' - ν X')) (hahn_crazy_diff_big μ ν X H)
  = Inf  ((floor_simple_fraction ∘ (λ X':set α, μ X' - ν X'))''(hahn_crazy_diff_set ν μ X)) :=
begin
  let f :=  (λ X':set α, μ X' - ν X'),
  let S := (hahn_crazy_diff_set ν μ X),
  let P := (λ (a:set α), 
       (∃ (H:a∈ hahn_crazy_diff_set  ν μ X),
      (floor_simple_fraction ∘ f)
       a =
      Inf ((floor_simple_fraction ∘ f) '' S))),
  begin
  have A1: f = (λ X':set α, μ X' - ν X') := rfl,
  have A2: S = (hahn_crazy_diff_set ν μ X) := rfl,
  have A3: P = (λ (a:set α), 
       (∃ (H:a∈ hahn_crazy_diff_set  ν μ X),
      (floor_simple_fraction ∘ f)
       a =
      Inf ((floor_simple_fraction ∘ f) '' S))) := rfl,
  have B1:(λ (a:set α), 
       (∃ (H:a∈ hahn_crazy_diff_set  ν μ X),
      (floor_simple_fraction ∘ f)
       a =
      Inf ((floor_simple_fraction ∘ f) '' S))) 
       (hahn_crazy_diff_big μ ν X H),
  {  
    rw hahn_crazy_diff_big_def,

    have B1A:∃ y:set α, P y,
    {
      rw A3,
      apply hahn_infi_ennreal,
      apply hahn_crazy_diff_set_nonempty,
      {
        rw hahn_crazy_set_def at H,
        apply H.right.left,
      },
      {
        apply hahn_crazy_set_self,
        apply H,
      },
    },
    apply @classical.some_spec (set α) P B1A,
  },
  cases B1 with B1 B2,
  split,
  apply B1,
  apply B2
  end
end




lemma hahn_crazy_diff_big_Inf {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):
  (floor_simple_fraction ∘ (λ X':set α, μ X' - ν X')) (hahn_crazy_diff_big μ ν X H)
  = Inf  ((floor_simple_fraction ∘ (λ X':set α, μ X' - ν X'))''(hahn_crazy_diff_set ν μ X)) :=
begin
  have A1 := hahn_crazy_diff_big_spec μ ν X H,
  apply A1.right,
end

lemma hahn_crazy_diff_big_mem {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):
  (hahn_crazy_diff_big μ ν X H) ∈ (hahn_crazy_diff_set ν μ X) := 
begin
  have A1 := hahn_crazy_diff_big_spec μ ν X H,
  apply A1.left,
end


lemma lt_of_hahn_crazy_diff_big {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):
  ν (hahn_crazy_diff_big μ ν X H) < μ (hahn_crazy_diff_big μ ν X H) := 
begin
  have A1 := hahn_crazy_diff_big_mem μ ν X H,
  rw hahn_crazy_diff_set_def at A1,
  simp at A1,
  apply A1.right.right,
end


lemma hahn_crazy_set_of_hahn_crazy_diff_big {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α) (H:hahn_crazy_set μ ν X):
  (hahn_crazy_set μ ν (X \ (hahn_crazy_diff_big μ ν X H))) :=
begin
  have B1:=hahn_crazy_diff_big_mem μ ν X H,
  rw hahn_crazy_diff_set_def at B1,
  simp at B1,
  apply hahn_crazy_set_subset,
  {
    apply H,
  },
  {
    -- ⊢ hahn_crazy_diff_big μ ν X H ⊆ X
    apply B1.left,
  },
  {
    apply B1.right.left,
  },
  {
    apply le_of_lt B1.right.right,
  },
end

--open subtype


def next_hahn_crazy_set {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:subtype (hahn_crazy_set μ ν)):
  subtype (hahn_crazy_set μ ν) := subtype.mk 
      (X.1 \ (hahn_crazy_diff_big μ ν X.1 X.2))
      (hahn_crazy_set_of_hahn_crazy_diff_big μ ν X.1 X.2)



lemma next_hahn_crazy_set_val {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (S:set α) (H:hahn_crazy_set μ ν S):
  ((next_hahn_crazy_set μ ν (subtype.mk S H)):set α) =
      (S \ (hahn_crazy_diff_big μ ν S H)) := rfl


lemma set.diff_diff_eq_of_subset {α:Type*} (S T:set α):S ⊆ T →
  T \ (T \ S) = S :=
begin
  intro A1,
  ext a,split;intros B1,
  {
    rw set.mem_diff at B1,
    cases B1 with B1 B2,
    rw set.mem_diff at B2,
    simp at B2,
    apply B2 B1,
  },
  {
    simp,
    rw set.subset_def at A1,
    apply and.intro (A1 a B1), 
    intro C1,
    apply B1,
  },
end


lemma next_hahn_crazy_set_diff {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (S:set α) (H:hahn_crazy_set μ ν S):
  S \ (next_hahn_crazy_set μ ν (subtype.mk S H)) =
      (hahn_crazy_diff_big μ ν S H) := 
begin
  rw next_hahn_crazy_set_val,
  apply set.diff_diff_eq_of_subset (hahn_crazy_diff_big μ ν S H) S,
  have B1:=hahn_crazy_diff_big_mem μ ν S H,
  rw hahn_crazy_diff_set_def at B1,
  cases B1 with B1 B2,
  apply B1,
end


/-
begin
  refl
end-/
   


def nth_hahn_crazy_set {α:Type*} [measurable_space α]
  (μ ν:measure_theory.measure α) (X:subtype (hahn_crazy_set μ ν)):
  ℕ → subtype (hahn_crazy_set μ ν)
  | 0 := X
  | (nat.succ n) := next_hahn_crazy_set μ ν (nth_hahn_crazy_set n)


lemma neg_monotone_of_succ_le {α:Type*} [partial_order α] {f:ℕ → α}:
  (∀ n:ℕ, f (n.succ) ≤ f n) →
  (∀ i j, i ≤ j → f j ≤ f i) :=
begin
  intros A1,
  intros i j,
  induction j,
  {
    intro B1,
    simp at B1,
    subst i,
  },
  {
    intro C1,
    cases C1 with C1 C1,
    apply le_refl _,
    have C2 := j_ih C1,
    apply le_trans (A1 j_n) C2,
  },
end


lemma measure_Inter_eq_infi_nat' {α:Type*} [measurable_space α]
  {μ:measure_theory.measure α} {f:ℕ → set α}:
  (∀ n:ℕ,  f n.succ ⊆ f n) →
  (∀ n, is_measurable (f n)) →
  (μ (f 0) < ⊤) → 
  μ (⋂ n, f n) =  ⨅ n, μ (f n)  :=
begin
  intros A1 A2 A3,
  apply measure_theory.measure_Inter_eq_infi_nat,
  apply A2,
  {
    intros i j B1,
    have B2:∀ n:ℕ, f (n.succ) ≤ f n,
    {
      intro n,
      apply A1 n,
    },
    apply neg_monotone_of_succ_le B2 i j B1,
  },
  apply exists.intro 0,
  apply A3,
end

lemma measure_monotone_finite {α:Type*} [measurable_space α]
  {μ:measure_theory.measure α} {f:ℕ → set α}:
  (∀ n:ℕ,  f n.succ ⊆ f n) →
  (∀ n, is_measurable (f n)) →
  (μ (f 0) < ⊤) →
  (∀ n, μ (f n) < ⊤) :=
begin
  intros A1 A2 A3,
  intro n,
  induction n,
  {
    apply A3,
  },
  {
    have B1:μ (f (n_n.succ)) ≤ μ (f (n_n)),
    {
      apply measure_theory.measure_mono,
      apply A1,
    },
    apply lt_of_le_of_lt B1,
    apply n_ih,
  },
end

/-
  We need some basic results about sums of extended nonnegative reals to prove
  our results.
 -/




lemma not_top_eq_some {x:ennreal}:x≠ ⊤ → (∃ (y:nnreal), (y:ennreal) = x) :=
begin
  intro A1,
  cases x,
  {
    exfalso,
    simp at A1,
    apply A1,
  },
  apply exists.intro x,
  refl
end


--∀ᶠ
--All of the variants of has_classical_limit follow easily from this.
lemma has_classical_limit_nonneg {β:Type*} [ordered_add_comm_monoid β] [topological_space β]
  [order_topology β]
  [t2_space β] (f:ℕ → β) (v:β):(0≤ f) →
  (∀ z<v, ∃ m,  z < (finset.sum (finset.range m) f))  →
  (∀ m', (finset.sum (finset.range m') f) ≤ v) →
  has_sum f v
  :=
begin
  intros A1 A2 A3,
  unfold has_sum,
  rw tendsto_order,
  split,
  {
    intros x B1,
    rw filter.eventually_iff,
    simp,
    have B2 := A2 x B1,
    cases B2 with m B2,
    apply exists.intro (finset.range m),
    intros T B3,
    apply lt_of_lt_of_le B2,
    apply finset.sum_monotone_of_nonnegative A1 B3,
  },
  {
    intros b C1,
    rw filter.eventually_iff,
    simp,
    apply exists.intro finset.empty,
    intros T C2,
    apply lt_of_le_of_lt _ C1,
    have C3:∃ m, T ⊆ (finset.range m) := finset_range_bound T,
    cases C3 with m C3,
    apply le_trans _ (A3 m),
    apply finset.sum_monotone_of_nonnegative A1 C3,
  },
end


lemma nonnegative_fn {α β:Type*} [preorder β] [has_zero β] {f:α → β}:(is_nonnegative β)
 → 0 ≤ f :=
begin
  intro A1,
  rw le_func_def2,
  intro a,
  apply A1,
end


--Not quite the classical way of thinking about a limit, but
--more practical for nonnegative sums.
--See has_classical_limit_nnreal' 
lemma has_classical_limit_ennreal (f:ℕ → ennreal) (v:ennreal):
  (∀ z<v, ∃ m,  z < (finset.sum (finset.range m) f))  →
  (∀ m', (finset.sum (finset.range m') f) ≤ v) →
  has_sum f v
  :=
begin
  intros A1 A2,
  apply has_classical_limit_nonneg,
  {
    apply nonnegative_fn (nonnegative_ennreal),
  },
  {
    apply A1,
  },
  {
    apply A2,
  },
end


lemma ennreal.eq_add_of_sub_eq {a b c:ennreal}:b ≤ a →
  a - b = c → a = b + c :=
begin
  intros A1 A2,
  cases a;cases b,
  {
    simp,
  },
  {
    cases c,
    {
      simp,
    },
    exfalso,
    simp at A2,
    apply A2,
  },
  {
    exfalso,
    apply with_top.not_none_le_some _ A1,
  },
  simp at A2,
  rw ← ennreal.coe_sub at A2,
  cases c,
  {
    exfalso,
    simp at A2,
    apply A2,
  },
  {
    simp,
    rw ← ennreal.coe_add,
    rw ennreal.coe_eq_coe,
    simp at A2,
    simp at A1,
    apply nnreal.eq_add_of_sub_eq A1 A2,
  },
end


lemma real.sub_add_sub {a b c:real}:(a - b) + (b - c) = a - c :=
begin
  rw ← add_sub_assoc,
  simp,
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


lemma ennreal_telescope_helper2 {f:ℕ → ennreal} {m:ℕ}:
  (∀ n:ℕ,  f n.succ ≤ f n) →
  (f 0) - (f m) = (finset.range m).sum (λ n, (f n) - (f n.succ)) :=
begin
  intros A1,
  induction m,
  {
    simp,
  },
  {
    rw finset.range_succ,
    simp,
    rw ← m_ih,
    rw add_comm,
    symmetry,
    apply ennreal.sub_add_sub,
    apply A1,
    apply neg_monotone_of_succ_le A1,
    simp,
  },
end


lemma real.add_lt_of_lt_sub {a b c:real}:a < b - c → a + c < b :=
begin
  intro A1,
  have B1:a + c < (b - c) + c,
  {
    apply add_lt_add_right,
    apply A1,
  },
  simp at B1,
  apply B1,
end

lemma nnreal.add_lt_of_lt_sub {a b c:nnreal}:a < b - c → a + c < b :=
begin
  cases (classical.em (c ≤ b)) with B1 B1,
  {
    repeat {rw ← nnreal.coe_lt_coe <|> rw nnreal.coe_add},
    rw nnreal.coe_sub B1,
    apply real.add_lt_of_lt_sub,    
  },
  {
    intros A1,
    rw nnreal.sub_eq_zero at A1,
    exfalso,
    simp at A1,
    apply A1,
    apply le_of_not_le B1,
  },
end

lemma ennreal.add_lt_of_lt_sub {a b c:ennreal}:a < b - c → a + c < b :=
begin
  --intros AX A1,
  cases a;cases b;cases c;try {simp},
  {
    rw ← ennreal.coe_add,
    apply with_top.none_lt_some,
  },
  {
    repeat {rw ← ennreal.coe_sub 
            <|> rw ennreal.coe_lt_coe
            <|> rw ← ennreal.coe_add},
    apply nnreal.add_lt_of_lt_sub,
  },
end


lemma real.lt_sub_of_add_lt {a b c:real}:a + c < b → a < b - c :=
begin
  intro A1,
  have B1:a + c + (-c) < b + (-c),
  {
    apply add_lt_add_right,
    apply A1,
  },
  simp at B1,
  apply B1,
end


lemma nnreal.lt_sub_of_add_lt {a b c:nnreal}:a + c < b → a < b - c :=
begin
  intro A1,
  have B1:c ≤ b,
  {
    have B1A := le_of_lt A1,
    have B1B:a + c ≤ a + b,
    {
      have B1BA:b ≤ a + b,
      {
        rw add_comm,
        apply le_add_nonnegative _ _ nonnegative_nnreal,
      },
      apply le_trans B1A B1BA,
    },
    simp at B1B,
    apply B1B,
  },
  revert A1,
  repeat {rw ← nnreal.coe_lt_coe <|> rw nnreal.coe_add},
  rw nnreal.coe_sub B1,
  apply real.lt_sub_of_add_lt,
end


lemma ennreal.lt_sub_of_add_lt {a b c:ennreal}: a + c < b → a < b - c :=
begin
  --intros AX A1,
  cases a;cases b;cases c;try {simp},
  {
    repeat {rw ← ennreal.coe_sub 
            <|> rw ennreal.coe_lt_coe
            <|> rw ← ennreal.coe_add},
    apply nnreal.lt_sub_of_add_lt,
  },
end



lemma Inf_lt {α:Type*} [complete_linear_order α]
   {S:set α} {z:α}:S.nonempty →
  Inf S < z → ∃ s∈ S, s < z :=
begin
  intros A1 A2,
  apply classical.exists_of_not_forall_not,
  intro A3,
  have A4:z ≤ Inf S,
  {
    apply @le_Inf α _ _,
    intros b A4A,
    have A4B := A3 b,
    rw not_exists_iff_forall_not at A4B,
    have A4C := A4B A4A,
    apply le_of_not_lt A4C,
  },
  apply not_lt_of_le A4,
  apply A2,
end 



lemma infi_lt {α β:Type*} [nonempty α] [complete_linear_order β] 
  {f:α → β} {z:β}:
  infi f < z → ∃ a, f a < z :=
begin
  intro A1,
  have B1:(set.range f).nonempty,
  {
    apply set.range_nonempty,
  },
  have B2:(Inf (set.range f)) < z,
  {
    unfold infi at A1,
    apply A1,
  },
  have B3:=Inf_lt B1 B2,
  cases B3 with x B3,
  cases B3 with B3 B4,
  cases B3 with a B3,
  apply exists.intro a,
  subst x,
  apply B4,
end 


lemma ennreal_infi_diff {f:ℕ → ennreal} {z:ennreal}:z < f 0 - infi f →
  ∃ n, z < f 0 - f n := 
begin
  intros A1,
  have B1:infi f ≤ f 0 := @infi_le ennreal _ _ f 0,
  have B2:= ennreal.add_lt_of_lt_sub A1,
  rw add_comm at B2,
  have B3 := ennreal.lt_sub_of_add_lt B2,
  have B4 := infi_lt B3,
  cases B4 with n B4,
  apply exists.intro n,
  apply ennreal.lt_sub_of_add_lt,
  rw add_comm,
  apply ennreal.add_lt_of_lt_sub,
  apply B4,
end


lemma real.le_sub_add {a b c:real}:b ≤ c → 
a ≤ a - b + c := 
begin
  intros A1,
  have B1:a - b + b ≤ a - b + c,
  {
    apply add_le_add_left,
    apply A1,
  },
  simp at B1,
  apply B1,
end

lemma nnreal.le_sub_add {a b c:nnreal}:b ≤ c → c ≤ a → 
a ≤ a - b + c := 
begin
  repeat {rw ← nnreal.coe_le_coe},
  repeat {rw nnreal.coe_add},
  intros A1 A2,
  repeat {rw nnreal.coe_sub},
  apply real.le_sub_add A1,
  apply le_trans A1 A2,
end


lemma ennreal.le_sub_add {a b c:ennreal}:b ≤ c → c ≤ a → 
a ≤ a - b + c := 
begin
  cases a;cases b;cases c;try {simp},
  rw ← ennreal.coe_sub,
  rw ← ennreal.coe_add,
  rw ennreal.coe_le_coe,
  apply nnreal.le_sub_add,
end



lemma ennreal_telescope_helper {f:ℕ → ennreal}:
  (∀ n:ℕ,  f n.succ ≤ f n) →
  (f 0) - (infi f) = (∑' n, (f n) - (f n.succ)) :=
begin
  intro A1,
  symmetry,
  rw ← summable.has_sum_iff (ennreal.summable),
  apply has_classical_limit_ennreal,
  {
    intros z B1,
    have B2 := ennreal_infi_diff B1,
    cases B2 with n B2,
    apply exists.intro n,
    rw ← ennreal_telescope_helper2 A1,
    apply B2,
  },
  {
    intro m,
    rw ← ennreal_telescope_helper2 A1,
    simp,
    apply ennreal.le_sub_add,
    apply @infi_le ennreal ℕ _,
    apply neg_monotone_of_succ_le A1,
    simp,
  },
end

lemma ennreal_telescope {f:ℕ → ennreal}:
  (∀ n:ℕ,  f n.succ ≤ f n) →
  (f 0) = (∑' n, (f n) - (f n.succ)) + (infi f) :=
begin
  intros A1,
  have B1 := ennreal_telescope_helper A1,
  rw add_comm,
  apply ennreal.eq_add_of_sub_eq _ B1,   
  apply @infi_le ennreal _ _,
end


lemma measure_Inter_telescope {α:Type*} [measurable_space α]
  {μ:measure_theory.measure α} {f:ℕ → set α}:
  (∀ n:ℕ,  f n.succ ⊆ f n) →
  (∀ n, is_measurable (f n)) →
  (μ (f 0) < ⊤) →
  μ (f 0) = (∑' n, μ (f n \ (f (n.succ)))) + μ (⋂ n, f n) := 
begin
  intros A1 A2 A3,
  rw measure_Inter_eq_infi_nat' A1 A2 A3,
  have B1:(λ n, μ (f n \ (f (n.succ))))=(λ n, μ (f n) - μ (f (n.succ))),
  {
    apply funext,
    intro n,
    have B1A:μ (f n \ f (n.succ))=μ (f n \ (f (n.succ))) := rfl,
    rw B1A,
    rw measure_theory.measure_diff,
    apply A1,
    apply A2,
    apply A2,
    apply measure_monotone_finite A1 A2 A3,
  },
  rw B1,
  apply @ennreal_telescope (μ ∘ f),
  intro n,
  apply measure_theory.measure_mono,
  apply A1,
end


lemma ennreal.add_sub_cancel {a b:ennreal}:b < ⊤ → a + b - b = a :=
begin
  cases a;cases b;try {simp},
end

lemma measure_Inter_telescope' {α:Type*} [measurable_space α]
  {μ:measure_theory.measure α} {f:ℕ → set α}:
  (∀ n:ℕ,  f n.succ ⊆ f n) →
  (∀ n, is_measurable (f n)) →
  (μ (f 0) < ⊤) →
  μ (⋂ n, f n) =
  μ (f 0) - (∑' n, μ (f n \ (f (n.succ)))) := 
begin
  intros A1 A2 A3,
  have B1 := measure_Inter_telescope A1 A2 A3,
  rw B1,
  rw add_comm,
  simp,
  rw ennreal.add_sub_cancel,
  rw B1 at A3,
  apply lt_of_le_of_lt _ A3,
  apply @le_add_nonnegative ennreal _ _ _ nonnegative_ennreal,
end




lemma exists_coe {x:ennreal}:x < ⊤ → ∃ v:nnreal, x = v :=
begin
  cases x;try {simp},
end

lemma lt_Sup {α:Type*} [complete_linear_order α]
   {S:set α} {z:α}:S.nonempty →
  z < Sup S  → ∃ s∈ S,  z < s :=
begin
  intros A1 A2,
  apply classical.exists_of_not_forall_not,
  intro A3,
  have A4:Sup S ≤ z,
  {
    apply @Sup_le α _ _,
    intros b A4A,
    have A4B := A3 b,
    rw not_exists_iff_forall_not at A4B,
    have A4C := A4B A4A,
    apply le_of_not_lt A4C,
  },
  apply not_lt_of_le A4,
  apply A2,
end 



lemma lt_supr {α β:Type*} [nonempty α] [complete_linear_order β] 
  {f:α → β} {z:β}:
  z < supr f → ∃ a, z < f a :=
begin
  intro A1,
  have B1:(set.range f).nonempty,
  {
    apply set.range_nonempty,
  },
  have B2:z < (Sup (set.range f)),
  {
    unfold supr at A1,
    apply A1,
  },
  have B3:= lt_Sup B1 B2,
  cases B3 with x B3,
  cases B3 with B3 B4,
  cases B3 with a B3,
  apply exists.intro a,
  subst x,
  apply B4,
end 


lemma real.lt_of_le_of_add_le_of_le_of_sub_lt {a b c d e:real}:
    a + b ≤ c → d ≤ b → c - e < a → d < e := 
begin
  intros A1 A2 A3,
  have B1:c < a + e,
  {
    have B1A:(c - e) + e < a + e,
    {
      apply add_lt_add_right,
      apply A3,
    },
    simp at B1A,
    apply B1A,
  },
  have B2:a + b < a + e,
  {
    apply lt_of_le_of_lt A1 B1,
  },
  simp at B2,
  apply lt_of_le_of_lt A2 B2,
end


lemma real.lt_of_lt_of_le_of_add_le_of_le_of_sub_lt {a b c d e:real}:
    c < e → a + b ≤ c → d ≤ b → 0 < a → d < e := 
begin
  intros A1 A2 A3 A4,
  apply lt_of_le_of_lt _ A1,
  apply le_trans A3,
  clear A1 A3,
  have B1:0 + c < a + c,
  {
    simp,
    apply A4,
  },
  rw zero_add at B1,
  have B2 := lt_of_le_of_lt A2 B1,
  simp at B2,
  apply le_of_lt B2, 
end


lemma nnreal.lt_of_add_le_of_le_of_sub_lt {a b c d e:nnreal}:
    a + b ≤ c → d ≤ b → c - e < a → d < e := 
begin
  rw ← nnreal.coe_le_coe,
  rw ← nnreal.coe_le_coe,
  rw ← nnreal.coe_lt_coe,
  rw ← nnreal.coe_lt_coe,
  rw nnreal.coe_add,
  cases (le_or_lt e c) with B1 B1,
  {
    rw nnreal.coe_sub B1,
    rw ← nnreal.coe_le_coe at B1,
    apply real.lt_of_le_of_add_le_of_le_of_sub_lt,
  },
  {   
    rw nnreal.sub_eq_zero (le_of_lt B1),
    rw ← nnreal.coe_lt_coe at B1,
    apply real.lt_of_lt_of_le_of_add_le_of_le_of_sub_lt B1,
  },
end


lemma ennreal.lt_of_add_le_of_le_of_sub_lt {a b c d e:ennreal}:c < ⊤ →
    a + b ≤ c → d ≤ b → c - e < a → d < e := 
begin
  cases c,simp,
  cases a;cases b;cases d;cases e;try {simp},
  rw ← ennreal.coe_add,
  rw ← ennreal.coe_sub,
  rw ennreal.coe_le_coe,
  rw ennreal.coe_lt_coe,
  apply nnreal.lt_of_add_le_of_le_of_sub_lt,
end




lemma ennreal.coe_sub_lt_self {a:nnreal} {b:ennreal}:
     0 < a  → 0 < b →
     (a:ennreal) - b < (a:ennreal) :=
begin
  cases b;simp,
  intros A1 A2,
  rw ← ennreal.coe_sub,
  rw ennreal.coe_lt_coe,
  apply nnreal.sub_lt_self A1 A2,
end 


lemma nnreal.epsilon_half_lt_epsilon {ε:nnreal}: 0 < ε → (ε / 2) < ε :=
begin
  rw ← nnreal.coe_lt_coe,
  rw ← nnreal.coe_lt_coe,
  --rw ← nnreal.coe_two,
  rw nnreal.coe_div,
  apply epsilon_half_lt_epsilon,
end


lemma ennreal.epsilon_half_lt_epsilon {ε:ennreal}: ε < ⊤ → 0 < ε → (ε / 2) < ε :=
begin
  cases ε;simp,
  --rw ennreal.coe_div,
  have B1:((2:nnreal):ennreal) = 2 := rfl,
  rw ← B1,
  rw ← ennreal.coe_div,
  rw ennreal.coe_lt_coe,
  apply nnreal.epsilon_half_lt_epsilon,
  intro C1,
  have C2:(0:nnreal) < (2:nnreal),
  {
    apply zero_lt_two,
  },
  rw C1 at C2,
  simp at C2,
  apply C2,
end

lemma real.lt_of_add_lt_of_pos {a b c:real}:
      b + c ≤ a →
      0 < b →
      c < a :=
begin
  intros A1 A2,
  have A3:0 + c < b + c,
  {
    apply add_lt_add_right A2,
  }, 
  rw zero_add at A3,
  apply lt_of_lt_of_le A3,
  apply A1,
end

lemma nnreal.lt_of_add_lt_of_pos {a b c:nnreal}:
      b + c ≤ a →
      0 < b →
      c < a :=
begin
  --intros A1 A2,
  rw ← nnreal.coe_le_coe,
  rw ← nnreal.coe_lt_coe,
  rw ← nnreal.coe_lt_coe,
  rw nnreal.coe_add,
  apply real.lt_of_add_lt_of_pos,
end

lemma ennreal.lt_of_lt_top_of_add_lt_of_pos {a b c:ennreal}:a < ⊤ →
      b + c ≤ a →
      0 < b →
      c < a :=
begin
  cases a;simp;
  cases b;cases c;simp,
  rw ← ennreal.coe_add,
  rw ennreal.coe_le_coe,
  apply nnreal.lt_of_add_lt_of_pos,
end
     
--This is true WITHOUT the non-negative part. So long as the sum is 
--well-defined, this should be true.
--Revisit later (and search mathlib).
lemma ennreal.tendsto_zero_of_finite_sum (f:ℕ → ennreal):tsum f < ⊤ →
  filter.tendsto f filter.at_top (nhds 0) :=
begin
  intro A1,
  rw tendsto_order,
  split,
  {
    intros a B1,
    exfalso,
    simp at B1,
    apply B1,
  },
  {
    intros x C1,
    rw filter.eventually_iff,
    simp,
    have C2:=exists_coe A1,
    cases C2 with v C2,
    have C5:(⨆  n, (finset.range n).sum f)  = (v:ennreal),
    {
      rw ennreal.lim_finset_sum_eq_tsum,
      apply C2,
    },
    cases (lt_or_le x (v:ennreal)) with C4 C4,
    { -- C4 : a < ↑v
      have D1:(v:ennreal) - x < (⨆ (n : ℕ), (finset.range n).sum f),
      {
        rw C5,
        simp,
        apply ennreal.coe_sub_lt_self,
        have D1A:0 < (v:ennreal),
        {
          apply lt_trans C1 C4,
        },
        simp at D1A,
        apply D1A,
        apply C1,
      },
      have D2 := lt_supr D1,
      cases D2 with b D2,
      apply exists.intro b,
      intros c D3,
      have D4:(finset.range (c.succ)).sum f ≤ (v:ennreal),
      {
        rw ← C5,
        apply @le_supr ennreal ℕ _,
      },
      have D5:0 ≤ b,
      {
        simp,
      },
      have D6:b ≤ c.succ,
      {
        apply le_trans D3,
        apply nat.le_succ,
      },
      rw ← finset.Ico.zero_bot at D4,
      have D7:disjoint (finset.Ico 0 b) (finset.Ico b c.succ),
      {
        apply finset.Ico.disjoint_consecutive,
      },
      rw ← finset.Ico.union_consecutive D5 D6 at D4,
      rw finset.sum_union D7 at D4,
      rw finset.Ico.zero_bot at D4,
      -- b' + c'' ≤ v
      -- c' ≤ c''
      -- v - x < b' 
      -- ⊢ c' < x
      -- Working here.
      have D8:f c ≤ (finset.Ico b c.succ).sum f,
      {
        apply finset.element_le_sum nonnegative_ennreal,
        {
          simp [D3,lt_succ], 
        }, 
        {
          apply nat.decidable_eq,
        },
      },
      have D9:(v:ennreal) < ⊤,
      {
        simp,
      },
      apply ennreal.lt_of_add_le_of_le_of_sub_lt D9 D4 D8 D2,      
    },

    cases (@eq_or_ne nnreal _ v 0) with C6 C6,
    {
      subst v,
      apply exists.intro 0,
      intros n E1,
      simp at C5,
      have E2:(finset.range (n.succ)).sum f ≤ 0,
      {
        rw ← C5,
        apply @le_supr ennreal ℕ _,
      },
      --have E3:
      simp at C1,
      apply lt_of_le_of_lt _ C1,
      apply le_trans _ E2,  
      apply finset.element_le_sum nonnegative_ennreal,
      {
        simp,
      },
      {
        apply nat.decidable_eq,
      },
    },
    {
      have F1:0 < v,
      {
        rw lt_iff_le_and_ne,
        split,
        simp,
        symmetry,
        apply C6,
      },
      have F2:0 < (⨆ (n : ℕ), (finset.range n).sum f),
      {
        rw C5,
        simp,
        apply F1,
      },
      --have F3 := lt_supr F2,
      have F3 := lt_supr F2,
      cases F3 with a F3,
      apply exists.intro a,
      intros b F4,
      apply lt_of_lt_of_le _ C4,
      have F5:(finset.range (b.succ)).sum f ≤ (v:ennreal),
      {
        rw ← C5,
        apply @le_supr ennreal ℕ _,
      },
      have F6:0 ≤ a,
      {
        simp,
      },
      have F7:a ≤ b.succ,
      {
        apply le_trans F4,
        apply nat.le_succ,
      },
      rw ← finset.Ico.zero_bot at F5,
      have F8:disjoint (finset.Ico 0 a) (finset.Ico a b.succ),
      {
        apply finset.Ico.disjoint_consecutive,
      },
      rw ← finset.Ico.union_consecutive F6 F7 at F5,
      rw finset.sum_union F8 at F5,
      rw finset.Ico.zero_bot at F5,
      --apply ennreal.lt_of_add_le_of_le_of_sub_lt D9 D4 D8 D2,      
      have F9:f b ≤ (finset.Ico a b.succ).sum f,
      {
        apply finset.element_le_sum nonnegative_ennreal,
        {
          simp [F4,lt_succ], 
        }, 
        {
          apply nat.decidable_eq,
        },
      },
      have F10:(v:ennreal) < ⊤,
      {
        simp,
      },
      have F11: (finset.range a).sum (λ (x : ℕ), f x) + f b ≤ ↑v,
      {
        apply le_trans _ F5,
        apply add_le_add_left F9,
        --apply add_le_add_of_le,
      },
      apply ennreal.lt_of_lt_top_of_add_lt_of_pos F10 F11 F3,      
    },
  },
end





lemma filter.tendsto_const {α β:Type*} [topological_space β]
    {v:β} {F:filter α}:
    filter.tendsto (λ n:α, v) F (nhds v) :=
begin
  unfold filter.tendsto,
  unfold filter.map,
  unfold nhds,
  simp,
  intros S B1 B2,
  have C1:(λ n:α, v) ⁻¹' S = set.univ,
  {
    ext;split;intro C1A,
    simp,
    simp,
    apply B1,  
  },
  rw C1,
  apply filter.univ_sets,
end



lemma filter.tendsto_le {α β:Type*} [topological_space β]
    [partial_order β] [order_topology β] {F:filter α} 
    {f g h:α  → β} {v:β}:
    f ≤ g →
    g ≤ h →
    filter.tendsto f F (nhds v) →
    filter.tendsto h F (nhds v) →
    filter.tendsto g F (nhds v) :=
begin
  intros A1 A2 A3 A4,
  rw tendsto_order,
  split,
  {
    intros x B1,
    rw filter.eventually_iff,
    rw tendsto_order at A3,
    have B2 := A3.left x B1,
    rw filter.eventually_iff at B2,
    have B4: {x_1 : α | x < f x_1}⊆ {x_1 : α | x < g x_1},
    {
      rw set.subset_def,
      intros a B4A,
      simp at B4A,
      simp,
      apply lt_of_lt_of_le B4A (A1 a),
    },
    apply filter.sets_of_superset F B2 B4,
  },
  {
    intros x B1,
    rw filter.eventually_iff,
    rw tendsto_order at A4,
    have B2 := A4.right x B1,
    rw filter.eventually_iff at B2,
    have B4: {x_1 : α | h x_1 < x}⊆ {x_1 : α | g x_1 < x},
    {
      rw set.subset_def,
      intros a B4A,
      simp at B4A,
      simp,
      apply lt_of_le_of_lt (A2 a) B4A,
    },
    apply filter.sets_of_superset F B2 B4,
  },
end


--Extend to nonnegative type (well, nnreal).
lemma ennreal.tendsto_le {α:Type*} {F:filter α} {g h:α  → ennreal}:
    g ≤ h →
    filter.tendsto h F (nhds 0) →
    filter.tendsto g F (nhds 0) :=
begin
  intros A1 A2,
  let f:α → ennreal := (λ a:α, 0),
  begin
    have B1:f = (λ a:α, 0) := rfl,
    have B2:f ≤ g,
    {
      rw B1,
      intros a,
      simp,
    },
    have B3:filter.tendsto f F (nhds 0),
    {
      apply filter.tendsto_const,
    },
    apply filter.tendsto_le B2 A1 B3 A2,
  end
end


lemma set.preimage_subset_preimage_of_subset {α β:Type*} {S T:set α} {f:β  → α}:
  (S⊆ T)→ set.preimage f S ⊆  set.preimage f T :=
begin
--{x:β |f x ∈ S} ⊆ {x:β |f x ∈ T} :=
  intro A1,
  have B1:set.preimage f S = {x:β |f x ∈ S} := rfl,
  have B2:set.preimage f T = {x:β |f x ∈ T} := rfl,
  rw B1,
  rw B2,
  apply preimage_superset,
  apply A1,
end


--∀ᶠ (b : ℕ) in filter.at_top, f b < x
lemma tendsto_top {α β:Type*} [NE:nonempty β] [SL:semilattice_sup β] {g:α → β} {F:filter α}:filter.tendsto g F filter.at_top ↔ (∀ b:β,  ∀ᶠ (c:α) in F, b ≤ g c) :=
begin
  split;intros A1,
  {
    rw filter.tendsto_iff_eventually at A1,
    intro b,apply A1,
    rw filter.eventually_iff,
    simp,
    apply exists.intro b,
    intros b_1,
    simp,
  },
  {
    rw filter.tendsto_def,
    intros S C1,
    rw filter.mem_at_top_sets at C1,
    cases C1 with a C1,
    have C2 := A1 a,
    rw filter.eventually_iff at C2,
    apply filter.mem_sets_of_superset C2,
    apply set.preimage_subset_preimage_of_subset,
    rw set.subset_def,
    intros b C3,
    apply C1,
    apply C3,
  },
end
 
lemma tendsto_top' {α β:Type*} [NE:nonempty β] [SL:semilattice_sup β] {g:α → β} {F:filter α}:filter.tendsto g F filter.at_top ↔ (∀ b:β, g⁻¹' {c|b≤ c} ∈ F) :=
begin
  rw tendsto_top,
  split;intros A1;intros b;have B1 := A1 b,
  {
    rw filter.eventually_iff at B1,
    apply B1,
  },
  {
    rw filter.eventually_iff,
    apply B1,
  },
end 


lemma eventually_at_top_iff {α:Type*} [nonempty α] [semilattice_sup α] {P:α → Prop}:
  (∀ᶠ (c:α) in filter.at_top,  P c) ↔ ∃ (a : α), ∀ (b : α), b ≥ a → b ∈ {x : α | P x}:=
begin
  rw filter.eventually_iff,
  split;intros A1,
  {
    rw filter.mem_at_top_sets at A1,
    ---cases A1 with a A1,
    apply A1,
  },
  {
    rw filter.mem_at_top_sets,
    apply A1,
  },
end


lemma floor_simple_fraction_def (x:ennreal):floor_simple_fraction x = Inf {n:ℕ|(n:ennreal) ≥ x⁻¹} := rfl


lemma inv_as_fraction {c:ennreal}:(1)/(c) = (c)⁻¹ := 
begin
  rw ennreal.div_def,
  rw one_mul,
end

lemma nnreal.inv_as_fraction {c:nnreal}:(1)/(c) = (c)⁻¹ := 
begin
  rw nnreal.div_def,
  rw one_mul,
end



lemma nnreal.mul_le_mul_of_le_left {a b c:nnreal}:
  a ≤ b → c * a ≤ c * b :=
begin
  intro A1,
  apply ordered_comm_monoid.mul_le_mul_left,
  apply A1,
end

/-
  enneral could be a linear_ordered_comm_group_with_zero,
  and therefore a ordered_comm_monoid.
  HOWEVER, I am not sure how to integrate this.
  I am going to just prove the basic results from the class.
  NOTE that this is strictly more general than
  ennreal.mul_le_mul_left.
-/
lemma ennreal.mul_le_mul_of_le_left {a b c:ennreal}:
  a ≤ b → c * a ≤ c * b :=
begin
  cases a;cases b;cases c;simp;
  try {
    cases (classical.em (c=0)) with B1 B1,
    {
      subst c,
      simp,
    },
    {
      have B2:(c:ennreal) * ⊤ = ⊤,
      {
        rw ennreal.mul_top,
        rw if_neg,
        intro B2A,
        apply B1,
        simp at B2A,
        apply B2A,
      },
      rw B2,
      {apply le_refl _ <|> simp},
    },
  },
  {
    cases (classical.em (b=0)) with B1 B1,
    {
      subst b,
      simp,
    },
    {
      have B2:⊤ * (b:ennreal) = ⊤,
      {
        rw ennreal.top_mul,
        rw if_neg,
        intro B2A,
        apply B1,
        simp at B2A,
        apply B2A,
      },
      rw B2,
      simp,
    },
  },
  rw ← ennreal.coe_mul,
  rw ← ennreal.coe_mul,
  rw ennreal.coe_le_coe,
  apply nnreal.mul_le_mul_of_le_left,
end





lemma ennreal.inverse_le_of_le {a b:ennreal}:
  a ≤ b →
  b⁻¹ ≤ a⁻¹ :=
begin
  intros A2,
  cases (classical.em (a = 0)) with A1 A1,
  {
    subst a,
    simp,
  },

  cases b,
  {
    simp,
  },
  cases (classical.em (b = 0)) with C1 C1,
  {
    subst b,
    simp at A2,
    exfalso,
    apply A1,
    apply A2,
  },
  simp,
  simp at A2,
  have B1: (a⁻¹ * b⁻¹) * a ≤  (a⁻¹ * b⁻¹) * b,
  {
    apply ennreal.mul_le_mul_of_le_left A2,
  },
  rw mul_comm a⁻¹  b⁻¹ at B1,
  rw mul_assoc at B1,
  rw ennreal.inv_mul_cancel at B1,
  rw mul_comm (b:ennreal)⁻¹  a⁻¹ at B1,
  rw mul_assoc at B1,
  rw mul_one at B1,
  rw ennreal.inv_mul_cancel at B1,
  rw mul_one at B1,
  apply A2,
  {
    simp [C1],
  },
  {
    simp,
  },
  {
    apply A1,
  },
  {
    rw ← lt_top_iff_ne_top,
    apply lt_of_le_of_lt A2,
    simp,  
  },
end


lemma ennreal.nat_coe_add {a b:ℕ}:(a:ennreal) + (b:ennreal) = 
    ((@has_add.add nat _ a  b):ennreal) :=
begin
  simp,
end

lemma ennreal.nat_coe_le_coe {a b:ℕ}:(a:ennreal) ≤ (b:ennreal) ↔ (a ≤ b) :=
begin
  have B1:(a:ennreal) = ((a:nnreal):ennreal),
  {
    simp,
  }, 
  have B2:(b:ennreal) = ((b:nnreal):ennreal),
  {
    simp,
  }, 
  rw B1,
  rw B2,
  rw ennreal.coe_le_coe,
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


lemma floor_simple_fraction_bound (b:ℕ) (x:ennreal):0 < x →
x < (1/(b:ennreal)) →
b ≤ floor_simple_fraction x := 
begin
  intros A1 A2,
  cases b,
  {
    simp,
  },
  rw floor_simple_fraction_def,
  
  apply @nat.le_Inf,
  {
    simp,
    cases x,
    {
      simp,
    },
    simp,
    simp at A1,
    have A3 := nnreal.exists_unit_frac_lt_pos A1,
    cases A3 with a A3,
    have A4 := le_of_lt A3,
    rw nnreal.inv_as_fraction at A4,
    have A6 := nnreal.inverse_le_of_le _ A4,
    rw nnreal.inv_inv at A6,
    rw set.nonempty_def,
    apply exists.intro a.succ,
    simp,
    rw ← ennreal.coe_inv,
    have A7:((a + 1:nnreal):ennreal) = (a:ennreal) + 1,
    {
      simp,
    },
    rw ← A7,
    rw ennreal.coe_le_coe,
    apply A6,
    {
      intro B1,
      subst x,
      simp at A1,
      apply A1,
    },
    {
      rw nnreal.inv_pos,
      rw add_comm,
      have B2:(0:nnreal) < (1:nnreal) := zero_lt_one,
      apply lt_of_lt_of_le B2,
      apply le_add_nonnegative _ _ (nonnegative_nnreal),
    },
  },
  {
    intros c C1,
    simp at C1,
    simp at A2,
    have C2:(1:ennreal)/(c:ennreal) ≤ x,
    {
      rw inv_as_fraction,
      rw ← @ennreal.inv_inv x,
      apply ennreal.inverse_le_of_le,
      have C2A:x < ⊤,
      {
        apply lt_trans A2,
        rw inv_as_fraction,
        simp,
        rw add_comm,
        
        apply @lt_of_lt_of_le ennreal _ 0 1 _
              (ennreal.zero_lt_one),
        apply le_add_nonnegative 1 (b:ennreal) 
           nonnegative_ennreal,
      },
      rw lt_top_iff_ne_top at C2A,
      rw ← ennreal.inv_pos at C2A,
      apply C1,
    },
    have C3 := lt_of_le_of_lt C2 A2,
    have C4 := le_of_lt C3,
    rw inv_as_fraction at C4,
    rw inv_as_fraction at C4,
    have C5 := ennreal.inverse_le_of_le C4,
    rw ennreal.inv_inv at C5,
    rw ennreal.inv_inv at C5,
    have C6:((1:nat):ennreal) = (1:ennreal),
    {
      simp,
    },
    rw ← C6 at C5,    
    rw ennreal.nat_coe_add at C5,
    rw ennreal.nat_coe_le_coe at C5,
    apply C5,
  },
end


lemma floor_simple_fraction_limit_top {g:ℕ  → ennreal}:
    (∀ n, 0 < g n) →
    filter.tendsto g filter.at_top (nhds 0) →
    filter.tendsto (floor_simple_fraction∘ g) filter.at_top filter.at_top :=
begin
  intros AX A1,
  rw tendsto_order at A1,
  cases A1 with A1 A2,
  clear A1,
  rw tendsto_top,
  intro b,
  rw eventually_at_top_iff,
  have B1:((1:ennreal)/(b.succ:ennreal)) > 0,
  {
    simp,
    have B1A:(b:ennreal) = ((b:nnreal):ennreal),
    {
      simp,
    },
    rw B1A,
    have B1B:(1:ennreal) = ((1:nnreal):ennreal),
    {
      simp,
    },
    rw B1B,
    rw ← ennreal.coe_add,
    apply ennreal.coe_ne_top,
  },
  have B2 := A2 ((1:ennreal)/(b.succ:ennreal)) B1,
  rw eventually_at_top_iff at B2,
  cases B2 with a B2,
  apply exists.intro a,
  intros c B3,
  have B4 := B2 c B3,
  simp,
  simp at B4,
  have B5:b ≤ b.succ,
  {
    apply nat.le_succ,
  },
  apply le_trans B5,
  apply floor_simple_fraction_bound,
  apply AX,
  apply B4
end

/-
  This is the crux of the hahn decomposition theorem, the key of a proof by induction by
  contradiction. We assume that there is a set X where μ X < ν X and v X < ⊤, and there 
  does not exista a subset X' ⊆ X where μ X' < ν X', where for all X''⊆ X', μ X'' ≤ ν X''.

  The proof follows the contradiction part in An Epsilon of Room. If such a hahn crazy set
  existed, then we could find a set Y ⊆ X where ν Y < μ Y. And if we subtracted this set
  off, we would be back where we started with X-Y being a set where μ (X - Y) < ν (X - Y) 
  and no subset X' ⊆ X - Y where μ X' < ν X' and le_on_subsets μ ν X'. 

  What if we want to grab a set Y which maximizes μ Y - ν Y?
  Unfortunately, we find this as hard as the entire Hahn decomposition
  problem itself. But we don't need to find the biggest one, just one 
  that is big enough. What follows is one of the most unusual mathematical 
  tricks I have seen. We basically chunk the reals into (1,∞],(1/2,1],(1/3,1/2],
  et cetera. Instead of grabbing the absolute largest element, we grab an
  element in the first populated range. Thus, if we do this an infinite number
  of times, either the values we get sum to infinity (which they can't),
  or each range gets eventually depopulated. Thus, after this point, any remaining
  set must have μ Y - ν Y=0, a contradiction.
 -/
lemma hahn_crazy_set_not_finite {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α):
  (hahn_crazy_set μ ν X) →
  ¬(ν.is_finite) :=
begin
  intros A1 A2,
  let h:ℕ → set α :=
      (λ n, (nth_hahn_crazy_set μ ν (subtype.mk X A1) n).val),
  let d:ℕ → (set α) :=
      λ n, h n \ h (n.succ),
  let Z:=⋂ n, (h n),
  begin
    have B1:h =λ n, (nth_hahn_crazy_set μ ν (subtype.mk X A1) n).val := rfl,
    have B2:d = λ n, h (n) \ h (n.succ) := rfl,
    have B3:Z = ⋂ n, (h n) := rfl,
    have B4:(h 0) = X,
    {
      rw B1,
      refl,
    },
    have B5:∀ n:ℕ, nth_hahn_crazy_set μ ν (subtype.mk X A1) (nat.succ n)
           = next_hahn_crazy_set μ ν (nth_hahn_crazy_set μ ν (subtype.mk X A1) (n)),
    {
      intro n,
      refl,
    },
    have B6:∀ n:ℕ, h (n.succ) = next_hahn_crazy_set μ ν (nth_hahn_crazy_set μ ν (subtype.mk X A1) (n)),
    {
      intro n,
      rw B1,
      refl,
    },
    have J0:∀ n:ℕ, (hahn_crazy_set μ ν (h n)),
    {
      intros n,
      rw B1,
      apply (nth_hahn_crazy_set μ ν (subtype.mk X A1) n).property,
    },
    have J0B:∀ n:ℕ, h (n.succ) = next_hahn_crazy_set μ ν  
             (subtype.mk (h n) (J0 n)),
    {
      intro n,
      rw B6,
      refl,
    },
    have J1:∀ n:ℕ, h (n.succ) ⊆ h n,
    {
      intro n,
      rw J0B,
      unfold next_hahn_crazy_set,
      apply set.diff_subset,
    },
    have J2:∀ n:ℕ, is_measurable (h n),
    {
      intro n,
      have J2A := J0 n,
      rw hahn_crazy_set_def at J2A,
      apply J2A.right.left,  
    },
    have C1A:ν  (h 0) < ⊤,
    {
      rw B4,
      apply measure_theory.measure.is_finite_all ν X A2,
    },
    have J4:μ (h 0) < ν (h 0),
    {
       rw B4,
       rw hahn_crazy_set_def at A1,
       apply A1.left,
    },
    have C1:ν Z = ν (h 0) - (∑' n, ν (d n)),
    {
      rw B3,
      rw B2,
      simp,
      apply @measure_Inter_telescope' α M ν h J1 J2 C1A,
    },
      have C2A:μ  (h 0) < ⊤,
      {
        apply lt_trans J4 C1A,
      },

    have C2:μ Z = μ (h 0) - (∑' n, μ (d n)),
    {
      rw B3,
      rw B2,
      apply @measure_Inter_telescope' α M μ h J1 J2 C2A,
    },
    have C3C:(∑' (n : ℕ), μ (d n)) ≤ μ (h 0),
    {  
      rw measure_Inter_telescope J1 J2 C2A,
      have C3B1:(∑' (n : ℕ), μ (d n)) =
                (∑' (n : ℕ), μ (h n \ h n.succ)) := rfl,
      rw ← C3B1,
      apply le_add_nonnegative _ _ nonnegative_ennreal,
    },
    have C3X:(∑' (n : ℕ), ν (d n)) ≤ ν (h 0),
    {  
      rw measure_Inter_telescope J1 J2 C1A,
      have C3B1:(∑' (n : ℕ), ν (d n)) =
                (∑' (n : ℕ), ν (h n \ h n.succ)) := rfl,
      rw ← C3B1,
      apply le_add_nonnegative _ _ nonnegative_ennreal,
    },

    have C3:μ Z < ν Z,
    {
      rw C1,
      rw C2,
      apply ennreal.sub_lt_sub_of_lt_of_le,
      {
        rw B4,
        rw hahn_crazy_set_def at A1,
        apply A1.left,
      },
      {
        apply tsum_le_tsum _ ennreal.summable ennreal.summable,
        intro n,
        rw B2,
        simp,
        rw J0B,
        rw next_hahn_crazy_set_diff,
        have C3A1:= hahn_crazy_diff_big_mem μ ν (h n) (J0 n),
        rw hahn_crazy_diff_set_def at C3A1,
        apply le_of_lt (C3A1.right.right),
      },
      {
        apply C3C,
      },
    },
    have D1:is_measurable Z,
    {
      apply is_measurable.Inter,
      apply J2,
    },
    have D3:Z ⊆ X,
    {
      rw B3,
      rw ← B4,
      simp,
      apply set.Inter_subset,
    },
    have D2:hahn_crazy_set μ ν Z,
    {
      rw hahn_crazy_set_def,
      apply and.intro C3,
      apply and.intro D1,
      intros X' D2A D2B,
      rw hahn_crazy_set_def at A1,
      apply A1.right.right,
      apply set.subset.trans D2A D3,
      apply D2B,
    },
    have D3:filter.tendsto 
      (λ n:ℕ, μ (d n)) filter.at_top (nhds 0),
    {
      --There is a sequence of positive numbers with a finite sum.
      --Thus, their limit must be zero.
      apply ennreal.tendsto_zero_of_finite_sum,
      apply lt_of_le_of_lt C3C C2A,
    },
    have D3B:filter.tendsto 
      (λ n:ℕ, ν (d n)) filter.at_top (nhds 0),
    {
      --This is definitely true, but I am not sure if I need it,
      --or D3 above is what is needed. I need to walk through the
      --rest of this proof.
      apply ennreal.tendsto_zero_of_finite_sum,
      apply lt_of_le_of_lt C3X C1A,
    },
    have D4:filter.tendsto 
      (λ n:ℕ, Inf ((floor_simple_fraction ∘ (λ X':set α, μ X' - ν X'))
       ''(hahn_crazy_diff_set ν μ (h n))))  filter.at_top filter.at_top,
    {
      --I reversed this: I need to figure out if I can make the rest of the proof work.
      --Now, I need to reverse it back.
      have D4A:(λ n:ℕ, Inf ((floor_simple_fraction ∘ (λ X':set α, μ X' - ν X'))
       ''(hahn_crazy_diff_set ν μ (h n)))) = 
         (λ n:ℕ, (floor_simple_fraction ∘ (λ X':set α,  μ X' - ν X'))
                (hahn_crazy_diff_big μ ν (h n) (J0 n))),
      {
        -- J0 n:hahn_crazy_set μ ν (h n)
        apply funext,
        intro n,
        symmetry,
        apply @hahn_crazy_diff_big_Inf α _ μ ν (h n) (J0 n),
        
      },
      have D4B:∀ n, (hahn_crazy_diff_big μ ν (h n) (J0 n)) = d n,
      {
        intro n,
        rw B2,
        simp,
        rw ← next_hahn_crazy_set_diff,
        rw J0B,
      },
      have D4C:(λ n:ℕ, Inf ((floor_simple_fraction ∘ (λ X':set α, μ X' - ν X'))
       ''(hahn_crazy_diff_set ν μ (h n)))) = 
         (λ n:ℕ, (floor_simple_fraction ∘ (λ X':set α,  μ X' - ν X'))
                (d n)),
      {
        rw D4A,
        apply funext,
        intro n,
        rw D4B n,
      },
      have D4E: (λ n:ℕ, (λ X':set α,  μ X' - ν X')
                (d n)) ≤ (λ n:ℕ, μ (d n)),
      {
        intro n,
        simp,
        apply le_add_nonnegative _ _ nonnegative_ennreal,
      },
  
      have D4G:∀ n, ν (d n) < μ (d n),
      {
        intro n,
        rw ← D4B,
        apply @lt_of_hahn_crazy_diff_big α _ μ ν (h n),
      },
      have D4F:filter.tendsto (λ n:ℕ,  (λ X':set α,  μ X' - ν X')
                (d n)) filter.at_top (nhds (0:ennreal)),
      {
        apply ennreal.tendsto_le D4E D3,  
      },
      rw D4C,
      apply floor_simple_fraction_limit_top,
      {
        intro n,
        --rw ← D4B,
        simp,
        rw ← D4B,
        apply @lt_of_hahn_crazy_diff_big α _ μ ν (h n),
        --have D4G:
       -- sorry
      },
      apply D4F,
    },
    have E1:(hahn_crazy_diff_set ν μ Z).nonempty,
    {
      apply hahn_crazy_diff_set_nonempty' ν μ Z D2,
    },
    have E2:∃ S, S∈(hahn_crazy_diff_set ν μ Z),
    {
      apply set.contains_of_nonempty E1,
    },
    cases E2 with S E2,
    rw hahn_crazy_diff_set_def at E2,
    simp at E2,
    --True, but unnecessary
    have F1:0 < μ S - ν S,
    {
      simp,
      apply E2.right.right,
    },
    let n := floor_simple_fraction (μ S - ν S),
    begin
      have G1:n = floor_simple_fraction (μ S - ν S) := rfl,
      have H1: {m:ℕ| n.succ ≤ m} ∈ filter.at_top,
      {
        apply filter.mem_at_top,
      },
      have H2 := filter_tendsto_elim D4 H1,
      simp at H2,
      cases H2 with n2 H2,
      have H3 := H2 n2 (le_refl n2),
      have H4:Inf ((λ (a : set α), floor_simple_fraction (μ a - ν a)) '' hahn_crazy_diff_set ν μ (h n2))
              ≤ n,
      {
        apply nat.Inf_le,
        simp,
        apply exists.intro S,
        split,
        {
          rw hahn_crazy_diff_set_def,
          simp,
          split,
          {
             apply @set.subset.trans α S Z (h n2) E2.left,
             rw B3,
             apply set.Inter_subset,
           },
           apply (E2.right),
         },
         rw G1,
      },
      have H5 := le_trans H3 H4,
      apply not_lt_of_le H5,
      apply nat.lt.base,
    end
  end
end


lemma finite_set_not_hahn_crazy_set {α:Type*} [M:measurable_space α]
  (μ ν:measure_theory.measure α) (X:set α):
  (ν.is_finite) →
  ¬ (hahn_crazy_set μ ν X)  :=
begin
 intros A1 A2,
 apply hahn_crazy_set_not_finite μ ν X A2 A1, 
end

/-
  This theorem is a weak variant of hahn_unsigned_inequality_decomp.
  However, it probably has uses in its own right, beyond that of
  its parent theorem.
 -/
lemma hahn_unsigned_inequality_decomp_junior {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α) {X:set α}:(ν.is_finite) →
    (is_measurable X) →
    (μ X < ν X) → 
    (∃ X':set α, 
      X' ⊆ X ∧
      μ X' < ν X' ∧
      le_on_subsets μ ν X') :=
begin
  intros A1 A2 A3,
  have B1:= finite_set_not_hahn_crazy_set μ ν X A1,
  rw hahn_crazy_set_def at B1,
  simp at B1,
  apply B1 A3 A2, 
end


lemma Sup_apply_eq_supr_apply_of_closed'' {α:Type*}
  [complete_lattice α] {S:set α} (g:α → ennreal):
  (∀ (a∈ S) (b∈ S), a ≤ b → g a ≤ g b) →
  (∀ f:ℕ → α, set.range f ⊆ S → monotone f → (supr f)∈ S) →
  (S.nonempty) →
  (∀ a ∈ S, ∀ b ∈ S, a ⊔ b ∈ S)→
  (∃ f:ℕ → α,
            (∀ n, f n ∈ S) ∧ 
            (monotone f) ∧
            g (supr f) = Sup (g '' S)) :=
begin
  intros A1 AX A2 A3,
  have B1:(g '' S).nonempty,
  {
    apply set.nonempty_image_of_nonempty A2,
  },
  have B1X := ennreal.Sup_eq_supr B1,
  cases B1X with f' B1X,
  have B2:∃ f'':ℕ → α, ∀ n:ℕ, 
          (f'' n)∈ S ∧ g (f'' n) = f' n, 
  {
    apply @classical.some_func ℕ α (λ (n:ℕ) (a:α), 
        a∈ S ∧ g a = f' n),
    intro n,
    have B2A:=(B1X.left) n,
    simp at B2A,
    cases B2A with a B2A,
    apply exists.intro a,
    simp,
    apply B2A,
  },
  cases B2 with f'' B2,
  have C1:∀ (n : ℕ), Sup_so_far f'' n ∈ S,
  {
    apply Sup_so_far_of_closed,
    intro n,
    apply (B2 n).left,
    apply A3,  
  },
  apply exists.intro (Sup_so_far f''),
  split,
  {
    apply C1,
  },
  split,
  {
    apply monotone_Sup_so_far,
  },
  {
    --rw ← AX,
      have D1:(supr (Sup_so_far f''))∈ S,
      {
        apply AX,
        {
          rw set.subset_def,
          intros x D1A,
          --apply C1,
          simp at D1A,
          cases D1A with y D1A,
          subst x,
          apply C1,
        },
        apply monotone_Sup_so_far,
      },
    apply le_antisymm,
    {
      apply @le_Sup ennreal _ _,
      simp,
      apply exists.intro (supr (Sup_so_far f'')),
      apply and.intro D1,
      refl,   
    },
    {
      rw ← B1X.right,
      apply @supr_le ennreal _ _,
      intro i,
      rw ← (B2 i).right,
      apply A1,
      apply (B2 i).left,
      apply D1,
      have D2:f'' i ≤ (Sup_so_far f'') i,
      {
        apply le_Sup_so_far,
      },
      apply le_trans D2,
      apply @le_supr _ ℕ _ (Sup_so_far f'') i,
   },
  },
end


lemma hahn_unsigned_inequality_decomp {α:Type*} [M:measurable_space α]
    (μ ν:measure_theory.measure α):(ν.is_finite) → 
    (∃ X:set α,  le_on_subsets μ ν X ∧ le_on_subsets ν μ (Xᶜ)) :=
begin
  /-
    What we want is the argmax of f on S: this is our candidate for X.
    However, we must first establish that such an argmax exists.
     
    First, we construct an  M that is our candidate for X.
    It is the supremum of 
   -/
  let S:set (set α) := {X:set α|le_on_subsets μ ν X},
  let f:set α → ennreal := (λ T:set α, (ν T) - (μ T)),
  -- M is unused.
  let M:ennreal := Sup (f '' S),
  begin
    intro A1,
    have A2:S = {X:set α|le_on_subsets μ ν X} := rfl,
    have A3:f = (λ T:set α, (ν T) - (μ T)) := rfl,
    have A5:∀ X, le_on_subsets μ ν X → μ X < ⊤,
    {
      intros X A5A,
      apply lt_of_le_of_lt (le_on_subsets_self A5A),
      apply ν.is_finite_all,
      apply A1,
    },
    have A6:∀ T, f T = ν T - μ T,
    {
      intro T,
      refl,
    },
    have B1:∀ (a∈ S) (b∈ S), a ≤ b → f a ≤ f b,
    {
      intros T1 B1A T2 B1B B1C,
      rw A2 at B1A,
      simp at B1A,      
      rw A2 at B1B,
      simp at B1B,
      repeat {rw A6},
      have B1F:le_on_subsets μ ν (T2 \ T1),
      {
        apply le_on_subsets_diff B1B B1A,
      },
      have B1G:T2 = T1 ∪ (T2 \ T1),
      { 
        rw set.union_diff_cancel,
        apply B1C,
      },
      rw B1G,
      rw le_on_subsets_add,
      apply @le_add_of_nonneg_right ennreal _,
      simp,
      {
        apply A5 T1 B1A,
      },
      {
        apply A5 _ B1F,
      },
      apply B1A,
      apply B1F, 
      apply set.disjoint_diff,
    },
    have B2B:(∀ h:ℕ → set α, set.range h ⊆ S → monotone h → (supr h)∈ S),
    {
      intros h B2C B2D,
      rw A2,
      rw supr_eq_Union,
      apply le_on_subsets_m_Union,
      apply B2D,
      intro n,
      have B2E:h n ∈ S,
      {
         apply B2C,
         simp,
      },
      rw A2 at B2E,
      simp at B2E, 
      apply B2E,
    },
    have B3:S.nonempty,
    {
      apply @set.nonempty_of_contains (set α) _ ∅,
      rw A2,
      simp,
      apply le_on_subsets_empty,
    },
    have B4:(∀ (a ∈ S) (b ∈ S), a ⊔ b ∈ S),
    {
      rw A2,
      simp,
      intros a B4A b B4B,
      have B4C:a ⊔ b = a ∪ b := rfl,
      --rw B4C,
      apply le_on_subsets_union B4A B4B,
    },
    have C1:=@Sup_apply_eq_supr_apply_of_closed'' (set α) _ S f B1 B2B B3 B4,
    cases C1 with g C1,
    apply exists.intro (supr g),
    have C2:le_on_subsets μ ν (supr g),
    {
      rw supr_eq_Union,
      apply le_on_subsets_m_Union,
      apply C1.right.left,
      intro n,
      have D1:=C1.left n,
      rw A2 at D1,
      apply D1,
    },
    apply and.intro C2,
    -- ⊢ le_on_subsets ν μ (-supr g)
    rw le_on_subsets_def,
    split,
    {
      apply is_measurable.compl,
      apply le_on_subsets_is_measurable C2,
    },
    {
      intros X' D1 D2,
      apply le_of_not_lt _,
      intro D3,
      have D4:= hahn_unsigned_inequality_decomp_junior μ ν A1 D2 D3,
      cases D4 with X'' D4,
      have D5:f (X'' ∪ supr g) ≤  f (supr g),
      {
        rw C1.right.right,
        apply @le_Sup ennreal _ _,
        simp,
        apply exists.intro (X'' ∪ supr g),
        split,
        {
          apply le_on_subsets_union,
          apply D4.right.right,
          apply C2,
        },
        refl,
      },
      repeat {rw A6 at D5},
      rw le_on_subsets_add at D5,
      repeat {rw ← A6 at D5},
      rw add_comm at D5,
      apply @ennreal.not_add_le_of_lt_of_lt_top (f (supr g)) (f X'') _ _ _,
      {
        rw A6,
        simp,
        apply D4.right.left,
      },
      {
        rw A6,
        have D6:ν (supr g) < ⊤,
        {
          apply ν.is_finite_all,
          apply A1,
        },
        apply lt_of_le_of_lt _ D6,
        simp,
        apply ennreal.le_add,
        apply le_refl _,
      },
      apply D5,
      apply A5 _ D4.right.right,
      apply A5 _ C2,
      apply D4.right.right,
      apply C2,
      {
        apply @disjoint_subset_left _ ((supr g)ᶜ),
        apply set_disjoint_comm,
        apply set.disjoint_compl,
        apply set.subset.trans D4.left D1,
      },
    },
  end
end



lemma ennreal.ne_zero_iff_zero_lt {x:ennreal}:x ≠ 0 ↔ 0 < x :=
begin
  split;intros A1,
  {
    apply lt_of_not_le,
    intro B1,
    apply A1,
    simp at B1,
    apply B1,
  },
  {
    intros C1,
    subst x,
    simp at A1,
    apply A1,
  },
end




lemma simple_restrict_eq_indicator_const {Ω:Type*} {M:measurable_space Ω} 
  (S:set Ω) (x:ennreal):(is_measurable S) →
  ⇑((measure_theory.simple_func.const Ω x).restrict S) = (set.indicator S (λ ω:Ω, x)) :=
begin
  intro A1,
  rw measure_theory.simple_func.coe_restrict,
  rw measure_theory.simple_func.coe_const,
  apply A1,
end

lemma with_density_const_apply {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {k:ennreal} {S:set Ω}:is_measurable S →
   μ.with_density (λ ω:Ω, k) S = k * μ S :=
begin
  intros B1,
  rw measure_theory.with_density_apply2,
  rw ← simple_restrict_eq_indicator_const,
  rw integral_const_restrict_def,
  refl,
  apply B1,
  apply B1,
  apply B1,
end


lemma measure_theory.measure.le_zero_iff {Ω:Type*} [measurable_space Ω]
  (μ:measure_theory.measure Ω):μ ≤ 0 ↔ μ = 0 :=
begin
  split;intros A1,
  {
    apply le_antisymm A1,
    apply measure_theory.measure.zero_le,
  },
  {
    rw A1,
    apply le_refl _,
  },
end

lemma measure_theory.measure.sub_eq_zero_if_le {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω):μ ≤ ν → μ - ν = 0 :=
begin
  intros A1,
  rw ← measure_theory.measure.le_zero_iff,
  rw measure_theory.measure.sub_def,
  apply @Inf_le (measure_theory.measure Ω) _ _,
  simp [A1],
end


lemma measure_theory.measure.sub_apply {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω}:is_measurable S → ν.is_finite →
  ν ≤ μ → (μ - ν) S = μ S - ν S :=
begin
  intros A1 A2 A3,
  rw measure_sub_eq μ ν A3 A2,
  apply measure_sub_apply,
  apply A1,
end


lemma measure_theory.measure.restrict_apply_subset {Ω:Type*} [measurable_space Ω]
  (μ:measure_theory.measure Ω) {S T:set Ω}:is_measurable S →
  S ⊆ T →
  (μ.restrict T) S = μ S :=
begin
  intros A1 A3,
  rw measure_theory.measure.restrict_apply A1,
  simp [set.inter_eq_self_of_subset_left,A3],
end 

lemma measure_theory.measure.restrict_apply_self {Ω:Type*} [measurable_space Ω]
  (μ:measure_theory.measure Ω) {S:set Ω} (H:is_measurable S):
  (μ.restrict S) S = μ S :=
begin
  rw measure_theory.measure.restrict_apply H,
  simp,
end 

lemma restrict_le_restrict_of_le_on_subsets {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω}:
  le_on_subsets μ ν S →
  (μ.restrict S) ≤ ν.restrict S :=
begin
  intros A1,
  rw le_on_subsets_def at A1,
  rw measure_theory.measure.le_iff,
  intros T B1,   
  rw measure_theory.measure.restrict_apply,
  rw measure_theory.measure.restrict_apply,
  apply A1.right,
  simp,
  apply is_measurable.inter,
  apply B1,
  apply A1.left,
  repeat {apply B1},
end

/-
  Not required, but completes the connection between le_on_subsets and restrict.
 -/
lemma le_on_subsets_of_is_measurable_of_restrict_le_restrict {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω}:is_measurable S →
  (μ.restrict S) ≤ ν.restrict S →
  le_on_subsets μ ν S  :=
begin
  intros A1 A2,
  rw measure_theory.measure.le_iff at A2,
  rw le_on_subsets_def,
  apply and.intro A1,
  intros X B1 B2,
  have B3 := A2 X B2,
  rw measure_theory.measure.restrict_apply_subset μ B2 B1 at B3,
  rw measure_theory.measure.restrict_apply_subset ν B2 B1 at B3,
  apply B3,
end

lemma measure_theory.outer_measure.Inf_gen_nonempty3 {α:Type*} (m : set (measure_theory.outer_measure α))
    (t:set α) :m.nonempty →
  measure_theory.outer_measure.Inf_gen m t =
   (⨅ (μ : measure_theory.outer_measure α) (H:μ∈ m), μ t) :=
begin
  intro A1,
  have B1:∃ μ:measure_theory.outer_measure α, μ ∈ m,
  {
    rw set.nonempty_def at A1,
    apply A1,
  },
  cases B1 with μ B1,
  rw measure_theory.outer_measure.Inf_gen_nonempty2 _ μ B1,
end


lemma measure_theory.outer_measure.of_function_def2 
  {α : Type*} (m : set α → ennreal) (m_empty : m ∅ = 0)  (s:set α):
  (measure_theory.outer_measure.of_function m m_empty) s
    = ⨅{f : ℕ → set α} (h : s ⊆ ⋃i, f i), ∑'i, m (f i)  := rfl


lemma set.Union_inter_eq_inter_Union {α
   β:Type*} {f:α → set β} {T:set β}:
    (⋃ (a:α), f a ∩ T) =  T ∩ (⋃ (a:α), f a) :=
begin
  apply set.ext,
  intro b,split;intros B1;simp;simp at B1;
  apply and.intro B1.right B1.left,
end


lemma set.Union_union_eq_union_Union {α
   β:Type*} [NE:nonempty α] {f:α → set β} {T:set β}:
    (⋃ (a:α), f a ∪ T) =  T ∪ (⋃ (a:α), f a) :=
begin
  apply set.ext,
  intro b,split;intros B1;simp;simp at B1,
  {
    cases B1 with a B2,
    cases B2 with B3 B4,
    {
       right,
       apply exists.intro a B3,
    },
    {
      left,
      apply B4,
    },
  },
  {
    cases B1 with C1 C2,
    {
       apply nonempty.elim NE,
       intro a,
       apply exists.intro a,
       right,
       apply C1,
    },
    {
       cases C2 with a C3,
       apply exists.intro a,
       left,
       apply C3,
    },
  },
end

lemma set.subset_union_compl_of_inter_subset {α:Type*} {A B C:set α}:A ∩ B ⊆ C →
    A ⊆ C ∪ Bᶜ :=
begin
  intro D1,
  rw set.subset_def,
  intros x D2,
  rw set.subset_def at D1,
  simp,
  cases (classical.em (x∈ B)) with D3 D3,
  {
    left,
    apply D1,
    simp [D2,D3],
  },
  {
    right,
    apply D3,
  },
end 



lemma infi_le_trans {α β:Type*} [complete_lattice β] (a:α) (f:α → β) 
    (b:β):(f a ≤ b) → (⨅ (c:α), (f c)) ≤ b :=
begin
  intros A1,
  apply le_trans _ A1,
  apply @infi_le _ _ _, 
end

/-
  I saw this pattern a bunch below. It could be more widely used.
 -/
lemma infi_set_le_trans {α β:Type*} [complete_lattice β] (a:α) (P:α → Prop) (f:α → β) 
    (b:β):(P a) → (f a ≤ b) → (⨅ (c:α) (H:P c), f c) ≤ b :=
begin
  intros A1 A2,
  apply infi_le_trans a,
  rw infi_prop_def A1,
  apply A2,
end

lemma infi_set_image {α β γ:Type*} [complete_lattice γ] (S:set α) (f:α → β) 
    (g:β → γ):(⨅ (c∈ (f '' S)), g c) = ⨅  (a∈ S), (g ∘ f) a :=
begin
  apply le_antisymm;simp,
  {
    intros a B1,
    apply infi_le_trans (f a),
    apply infi_le_trans a,
    rw infi_prop_def,
    apply and.intro B1,
    refl,
  },
  {
    intros b a2 C1 C2,
    apply infi_le_trans a2,
    rw infi_prop_def C1,
    rw C2,
  },
end



--Note that this does not hold true for empty S.
--If S2.nonempty, but S2 ∩ T = ∅, then ⊤ (S2 ∩ T) = 0, but ⊤ (S2) = ⊤.
lemma measure_theory.outer_measure.Inf_restrict {Ω:Type*} [measurable_space Ω]
  (S:set (measure_theory.outer_measure Ω)) {T:set Ω}:
  is_measurable T → (S.nonempty) →
  measure_theory.outer_measure.restrict T (Inf S) = Inf ((measure_theory.outer_measure.restrict T) '' S) := 
begin
  intros A1 B1,
  apply measure_theory.outer_measure.ext,
  intros S2,
  rw measure_theory.outer_measure.restrict_apply,
  rw measure_theory.outer_measure.Inf_eq_of_function_Inf_gen,
  rw measure_theory.outer_measure.Inf_eq_of_function_Inf_gen,
  rw measure_theory.outer_measure.of_function_def2,
  rw measure_theory.outer_measure.of_function_def2,
  have E1:((measure_theory.outer_measure.restrict T) '' S).nonempty,
  {
    apply set.nonempty_image_of_nonempty B1,
  },
  apply le_antisymm,
  {
    simp,
    intros f C1,
    let g := λ n, (f n) ∩ T,
    begin
      have C2:g = (λ n, (f n) ∩ T) := rfl,
      have C3: (∑' (i:ℕ), measure_theory.outer_measure.Inf_gen S (g i)) ≤
               ∑' (i : ℕ), measure_theory.outer_measure.Inf_gen (⇑(measure_theory.outer_measure.restrict T) '' S) (f i),
      {
        apply ennreal.tsum_le_tsum,
        intro n,
        rw measure_theory.outer_measure.Inf_gen_nonempty3 _ _ B1,
        rw measure_theory.outer_measure.Inf_gen_nonempty3 _ _ E1,
        simp,
        intros μ' μ C3A C3B,
        subst μ',
        rw measure_theory.outer_measure.restrict_apply,
        rw C2,
        simp,
        have C3C:(⨅ (H : μ ∈ S),
                 μ (f n ∩ T)) ≤ μ (f n ∩ T),
        {
          rw infi_prop_def,
          apply le_refl _,
          apply C3A,
        },
        apply le_trans _ C3C,
        apply @infi_le ennreal _ _,
      },
      apply le_trans _ C3,
      have C4:(⨅ (h : S2 ∩ T ⊆ ⋃ (i : ℕ), g i),
             (∑' (i:ℕ), measure_theory.outer_measure.Inf_gen S (g i))) ≤
             (∑' (i:ℕ), measure_theory.outer_measure.Inf_gen S (g i)),
      {
        rw infi_prop_def,
        apply le_refl _,
        rw C2,
        simp,
        rw set.Union_inter_eq_inter_Union,
        simp,
        apply set.subset.trans _ C1,
        apply set.inter_subset_left,
      },
      apply le_trans _ C4,
      apply @infi_le ennreal _ _,
    end
  },
  {
    simp,
    intros h D1,
    let g := λ n, (h n) ∪ Tᶜ, 
    begin
      have D2:g = λ n, (h n) ∪ Tᶜ := rfl,
      apply @infi_set_le_trans (ℕ → set Ω) ennreal _ g,
      {
        rw D2,
        simp,
        rw set.Union_union_eq_union_Union,
        rw set.union_comm,
        apply set.subset_union_compl_of_inter_subset,
        apply D1,
      },
      {
        apply ennreal.tsum_le_tsum,
        intro n,
        rw measure_theory.outer_measure.Inf_gen_nonempty3 _ _ B1,
        rw measure_theory.outer_measure.Inf_gen_nonempty3 _ _ E1,
        rw infi_set_image,
        simp,
        intros μ D3,
        apply @infi_set_le_trans (measure_theory.outer_measure Ω) ennreal _ μ,
        apply D3,
        {
          rw D2,
          simp,
          rw set.inter_distrib_right,
          simp,
          apply μ.mono,
          simp,
        },
      },
    end
  },
end  


lemma measure_theory.measure.lift_linear_def {α β:Type*} [measurable_space α] [Mβ:measurable_space β]
    (f : measure_theory.outer_measure α →ₗ[ennreal] measure_theory.outer_measure β)
    (H:∀ (μ : measure_theory.measure α), Mβ ≤ (f μ.to_outer_measure).caratheodory) 
    {μ:measure_theory.measure α}:
    (measure_theory.measure.lift_linear f H μ) = (f (μ.to_outer_measure)).to_measure (H μ) :=
begin
  apply measure_theory.measure.ext,
  intros S B1,
  unfold measure_theory.measure.lift_linear,
  simp,
end


lemma measure_theory.outer_measure.to_measure_to_outer_measure_eq_trim {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.outer_measure Ω} (H:M ≤ (μ).caratheodory):
    (μ.to_measure H).to_outer_measure = μ.trim :=
begin
  apply measure_theory.outer_measure.ext,
  intros S,
  unfold measure_theory.outer_measure.to_measure measure_theory.measure.to_outer_measure
    measure_theory.outer_measure.trim
    measure_theory.measure.of_measurable,
  simp,
  refl,
end


lemma infi_prop_false2 {α:Type*} [complete_lattice α]
    {P:Prop} {v:P→ α} (H:¬P):(⨅ (H2:P), v H2) = ⊤ :=
begin
  apply le_antisymm,
  {
    simp,
  },
  {
    apply @le_infi α _ _,
    intro H2,
    exfalso,
    apply H,
    apply H2,
  },
end


lemma measure_theory.extend_top {α : Type*} {P : α → Prop} 
    {m : Π (s : α), P s → ennreal} {s : α}: ( ¬P s)→
    measure_theory.extend m s = ⊤ :=
begin
  intros A1,
  unfold measure_theory.extend,
  rw infi_prop_false2, 
  apply A1,
end


--Unused.
lemma measure_theory.le_extend2 {α:Type*} [measurable_space α] {x:ennreal} 
    {h:Π (s:set α), (is_measurable s)  → ennreal} (s:set α):
  (Π (H:is_measurable s), (x ≤ h s H)) → (x ≤ measure_theory.extend h s) :=
begin
  intros A1,
  cases (classical.em (is_measurable s)) with B1 B1,
  {
    apply le_trans (A1 B1),
    apply measure_theory.le_extend,
  },
  {
    rw measure_theory.extend_top B1, 
    simp,
  },
end 



/-
  This is a result that must be proven directly for restrict, but has
  larger implications.

  I am curious whether this follows from
  lift_linear constraint on the catheodary measurable space of the output outer
  measure of restrict. That would be a more general result, implying that this would
  hold for all places where lift_linear was used.
 -/
lemma measure_theory.outer_measure.restrict_trimmed_of_trimmed {Ω:Type*} [M:measurable_space Ω]
    {μ:measure_theory.outer_measure Ω} {S:set Ω}:is_measurable S → μ.trim = μ →
    (measure_theory.outer_measure.restrict S μ).trim = (measure_theory.outer_measure.restrict S μ) :=
begin
  intros A2 A1,
  apply measure_theory.outer_measure.ext,
  unfold measure_theory.outer_measure.trim,
  unfold measure_theory.induced_outer_measure,
  intros T,
  simp,
  rw measure_theory.outer_measure.of_function_def2,
  apply le_antisymm,
  {
    have B1:μ (T ∩ S) = μ.trim (T ∩ S),
    {
      rw A1,
    },
    rw B1,
    unfold measure_theory.outer_measure.trim,
    unfold measure_theory.induced_outer_measure,
    rw measure_theory.outer_measure.of_function_def2,
    simp,
    intros h B2,
    let g := λ (n:ℕ), (h n) ∪ Sᶜ,
    begin
      have B3:g = λ (n:ℕ), (h n) ∪ Sᶜ := rfl,
      have B4:(∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), 
              μ (s ∩ S)) (g i)) ≤
              ∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), 
             μ s) (h i),
      {
        apply ennreal.tsum_le_tsum,
        intros n,
        apply measure_theory.le_extend2,
        intro B4A,
        rw measure_theory.extend_eq,
        rw B3,
        simp,
        rw set.inter_distrib_right,
        simp,
        apply measure_theory.outer_measure.mono',
        simp,
        rw B3,
        simp,
        apply is_measurable.union B4A (is_measurable.compl A2),
      },
      apply le_trans _ B4,
      clear B4,
      have B5:(⨅ (h : T ⊆ ⋃ (i : ℕ), g i),
              ∑' (i : ℕ), measure_theory.extend 
             (λ (s : set Ω) (_x : is_measurable s), μ (s ∩ S)) (g i)) ≤
              ∑' (i : ℕ), measure_theory.extend 
             (λ (s : set Ω) (_x : is_measurable s), μ (s ∩ S)) (g i),
      {
        rw infi_prop_def,
        apply le_refl _,
        rw B3,
        simp,
        rw set.Union_union_eq_union_Union,
        rw set.union_comm,
        apply set.subset_union_compl_of_inter_subset B2,
      },
      apply le_trans _ B5,
      apply @infi_le ennreal _ _,
    end
  },
  {
    simp,
    intros h C1,
    let g := λ n:ℕ, h n ∩ S,
    begin
      have C2:g = λ n:ℕ, h n ∩ S := rfl,
      have C3:μ (T ∩ S) ≤ μ(set.Union g),
      {
        apply measure_theory.outer_measure.mono',
        rw C2,
        rw set.Union_inter_eq_inter_Union,
        rw set.inter_comm S,
        simp,
        apply set.subset.trans _ C1,
        simp,
      },
      apply le_trans C3,
      have C4:μ(set.Union g) ≤ ∑' (i:ℕ), μ (g i),
      {
        apply measure_theory.outer_measure.Union,
      },
      apply le_trans C4,
      apply ennreal.tsum_le_tsum,
      intro n,
      cases (classical.em (is_measurable (h n))) with C5 C5,
      {
        apply le_trans _ (measure_theory.le_extend _ C5),
        rw C2,
        apply le_refl _,
      },
      {
        rw measure_theory.extend_top C5,
        simp,
      },
    end
  },
end


lemma measure_theory.measure.to_outer_measure.restrict' {Ω:Type*} [measurable_space Ω]
    {μ:measure_theory.measure Ω} {S:set Ω}:is_measurable S →
    (μ.restrict S).to_outer_measure = measure_theory.outer_measure.restrict S (μ.to_outer_measure) :=
begin
  intros A1,
  apply measure_theory.outer_measure.ext,
  intro T,
  rw measure_theory.outer_measure.restrict_apply,
  simp,
  unfold measure_theory.measure.restrict,
  unfold measure_theory.measure.restrictₗ,
  rw measure_theory.measure.lift_linear_def,
  rw measure.apply,
  rw measure_theory.to_measure_to_outer_measure,
  --rw measure_theory.outer_measure.to_measure_to_outer_measure_eq_trim,
  rw measure_theory.outer_measure.restrict_trimmed_of_trimmed A1,
  simp,
  apply measure_theory.measure.trimmed,
end


lemma compose_image {α β γ:Type*} {f:α → β} {g:β → γ} {S:set α}:
  g '' (f '' S) = (g ∘ f) '' S :=
begin
  ext c,
  split;
  intros B1;simp;simp at B1;apply B1,
end


lemma measure_theory.measure.Inf_restrict {Ω:Type*} [measurable_space Ω]
  (S:set (measure_theory.measure Ω)) {T:set Ω}:S.nonempty → is_measurable T →
  (Inf S).restrict T = Inf ((λ μ:measure_theory.measure Ω,μ.restrict T) '' S) := 
begin
  intros AX A1,
  apply measure_theory.measure.ext,
  intros S2 B1,
  rw measure_theory.measure.Inf_apply B1,
  rw measure_theory.measure.restrict_apply B1,
  rw measure_theory.measure.Inf_apply (is_measurable.inter B1 A1),
  have B3:(measure_theory.measure.to_outer_measure '' ((λ (μ : measure_theory.measure Ω), μ.restrict T) '' S))
      = (measure_theory.outer_measure.restrict T) ''( measure_theory.measure.to_outer_measure '' S),
  {
    rw compose_image,
    rw compose_image,
    have B3A:(measure_theory.measure.to_outer_measure ∘ λ (μ : measure_theory.measure Ω), μ.restrict T) = (measure_theory.outer_measure.restrict T) ∘ (measure_theory.measure.to_outer_measure),
    {
      apply funext,
      intro μ,
      simp,
      apply measure_theory.measure.to_outer_measure.restrict',
      apply A1,
    },
    rw B3A,
  },
  rw B3,
  rw ← measure_theory.outer_measure.Inf_restrict _ A1,
  rw measure_theory.outer_measure.restrict_apply,
  apply set.nonempty_image_of_nonempty,
  apply AX,
end  


lemma set.subset_self {α:Type*} (S:set α):S ⊆ S :=
begin
  rw set.subset_def,
  intros x A1,
  apply A1,
end


lemma measure_theory.measure.restrict_le_restrict_of_le {Ω:Type*} [measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω}:
  μ  ≤ ν  → μ.restrict S ≤ ν.restrict S :=
begin
  intros A1,
  apply measure_theory.measure.restrict_mono,
  apply set.subset_self,
  apply A1,
end


lemma measure_theory.measure_partition_apply {Ω:Type*} [M:measurable_space Ω]
    (μ:measure_theory.measure Ω) (S T:set Ω):is_measurable S → is_measurable T →
  μ T = μ (S ∩ T) + μ (Sᶜ ∩ T) :=
begin
  intros A1 A2,
  rw set.inter_comm,
  rw set.inter_comm Sᶜ,

  have B1:T = (T∩ S) ∪ (T∩ Sᶜ),
  {
    rw union_inter_compl,
  },
  --have B2:μ T =
  rw ← @measure_theory.measure_union Ω M μ (T∩ S) _,
  rw ← B1,
  apply disjoint_inter_compl,
  apply is_measurable.inter,
  apply A2,
  apply A1,
  apply is_measurable.inter,
  apply A2,
  apply is_measurable.compl,
  apply A1,
end


lemma measure_theory.measure.le_of_partition {Ω:Type*} [M:measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S T:set Ω}:is_measurable S →
  is_measurable T →
  μ (S ∩ T) ≤ ν (S ∩ T) →
  μ (Sᶜ ∩ T) ≤ ν (Sᶜ ∩ T) →
  μ T ≤ ν T :=
begin
  intros A1 A2 A3 A4,
  rw measure_theory.measure_partition_apply μ S T,
  rw measure_theory.measure_partition_apply ν S T,
  have B1:μ (S ∩ T) + μ (Sᶜ ∩ T) ≤ ν (S ∩ T) + μ (Sᶜ ∩ T),
  {
    apply add_le_add_right A3,
  },
  apply le_trans B1,
  apply add_le_add_left A4,
  repeat {assumption},
end


lemma Inf_le_Inf' {α:Type*} [complete_lattice α] {S T:set α}:(∀ t∈ T, ∃ s∈ S,
  s ≤ t) → Inf S ≤ Inf T :=
begin
  intros A1,
  apply @le_Inf,
  intros t B1,
  have B2 := A1 t B1,
  cases B2 with s B2,
  cases B2 with B2 B3,
  apply le_trans _ B3,
  apply @Inf_le,
  apply B2
end


lemma measure_theory.outer_measure.le_top_caratheodory {Ω:Type*} [M:measurable_space Ω]:
  M ≤ (⊤:measure_theory.outer_measure Ω).caratheodory :=
begin
  rw measure_theory.outer_measure.top_caratheodory,
  simp
end


lemma measure_theory.measure.of_measurable_apply' {α:Type*} [M:measurable_space α]
(m : Π (s : set α), is_measurable s → ennreal)
  (m0 : m ∅ is_measurable.empty = 0)
  (mU : ∀ {{f : ℕ → set α}} (h : ∀i, is_measurable (f i)),
    pairwise (disjoint on f) →
    m (⋃i, f i) (is_measurable.Union h) = (∑'i, m (f i) (h i))) (S:set α):
  measure_theory.measure.of_measurable m m0 mU S = 
  measure_theory.induced_outer_measure m _ m0 S :=
begin
  unfold measure_theory.measure.of_measurable,
  simp,
  rw measure.apply, 
end


lemma measure_theory.outer_measure.top_eq {Ω:Type*} [M:measurable_space Ω]:
    ⇑(⊤:measure_theory.outer_measure Ω) = (λ (s:set Ω), (@ite (s=∅) (classical.prop_decidable (s=∅)) ennreal 0 ⊤)) :=
begin
  apply funext,
  intro S,
  cases (classical.em (S = ∅)) with B1 B1,
  {
    rw if_pos,
    subst S,
    apply measure_theory.outer_measure.empty',
    apply B1,
  },
  {
    rw if_neg,
    apply measure_theory.outer_measure.top_apply,
    rw set.nonempty_iff_ne_empty,
    apply B1,
    apply B1,
  },
end


lemma measure_theory.outer_measure.extend_top {Ω:Type*} [M:measurable_space Ω]:
  (measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), (⊤:measure_theory.outer_measure Ω) s))=(λ (s:set Ω), (@ite (s=∅) (classical.prop_decidable (s=∅)) ennreal 0 ⊤)) :=
begin
  apply funext,
  intro S,
  rw measure_theory.outer_measure.top_eq,
  cases (classical.em (is_measurable S)) with B1 B1,
  {
    unfold measure_theory.extend,
    rw infi_prop_def,
    apply B1,
  },
  {
    unfold measure_theory.extend,
    rw infi_prop_false,
    rw if_neg,
    intros B2,
    apply B1,
    subst S,
    simp,
    apply B1,
  },
end

lemma measure_theory.outer_measure.extend_top' {Ω:Type*} [M:measurable_space Ω]:
  (measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), (⊤:measure_theory.outer_measure Ω) s))=(⊤:measure_theory.outer_measure Ω) :=
begin
  rw measure_theory.outer_measure.extend_top,
  rw measure_theory.outer_measure.top_eq,
end

lemma subst_apply_empty_zero {Ω:Type*} {f g:set Ω → ennreal}:(f = g) → (f ∅ = 0) → (g ∅ = 0) :=
begin
  intros A1 A2,
  subst f,
  apply A2,
end

lemma measure_theory.outer_measure.of_function_subst {Ω:Type*} [M:measurable_space Ω]
   {f g:set Ω → ennreal} {P:f ∅ = 0} (H:f = g):
  measure_theory.outer_measure.of_function f P =
  measure_theory.outer_measure.of_function g (subst_apply_empty_zero H P) :=
begin
  subst g,
end


lemma measure_theory.outer_measure.of_function_eq' {Ω:Type*} [M:measurable_space Ω]
  {μ:measure_theory.outer_measure Ω} (H:μ ∅ = 0): 
  measure_theory.outer_measure.of_function (⇑μ) H = μ :=
begin
  apply measure_theory.outer_measure.ext,
  intro S,
  apply measure_theory.outer_measure.of_function_eq,
  {
    intros T B1,
    apply measure_theory.outer_measure.mono',
    apply B1, 
  },
  {
    intros f,
    apply measure_theory.outer_measure.Union_nat,
  },
end


lemma measure_theory.outer_measure.top_eq_trim {Ω:Type*} [M:measurable_space Ω]:
  (⊤:measure_theory.outer_measure Ω).trim = ⊤ :=
begin
  unfold measure_theory.outer_measure.trim,
  unfold measure_theory.induced_outer_measure,
  have B1:= @measure_theory.outer_measure.extend_top' Ω M,
  rw measure_theory.outer_measure.of_function_subst B1,  
  rw measure_theory.outer_measure.of_function_eq',
end


lemma measure_theory.outer_measure.top_to_measure_to_outer_measure_eq_top {Ω:Type*} [M:measurable_space Ω]:
  ((⊤:measure_theory.outer_measure Ω).to_measure measure_theory.outer_measure.le_top_caratheodory).to_outer_measure  = ⊤ :=
begin
  apply measure_theory.outer_measure.ext,
  intro S,
  unfold measure_theory.outer_measure.to_measure,
  simp,
  rw measure_theory.measure.of_measurable_apply',
  unfold measure_theory.induced_outer_measure,
  have B1:= @measure_theory.outer_measure.extend_top' Ω M,
  rw measure_theory.outer_measure.of_function_subst B1,  
  rw measure_theory.outer_measure.of_function_eq',
end



/-
  One could extract many monotone relationships from this:
  induced_outer_measure, extend, of_function, et cetera.
  However, I wouldn't be surprised to find them in the library.
 -/
lemma measure_theory.outer_measure.trim_monotone {Ω:Type*} [M:measurable_space Ω]
  (μ ν:measure_theory.outer_measure Ω):μ ≤ ν → μ.trim ≤ ν.trim :=
begin
  intros A1,
  rw outer_measure_measure_of_le,
  unfold measure_theory.outer_measure.trim,
  unfold measure_theory.induced_outer_measure,
  unfold measure_theory.outer_measure.of_function,
  intros S,
  simp,
  intros f B1,
  have B2:(∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), μ s) (f i)) ≤
    ∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), ν s) (f i),
  {
    apply ennreal.tsum_le_tsum,
    unfold measure_theory.extend,
    intros n,
    simp,
    intros B2A,
    rw infi_prop_def,
    apply A1,
    apply B2A,
  },
  apply le_trans _ B2,
  have B3:(⨅ (h : S ⊆ ⋃ (i : ℕ), f i),(∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), μ s) (f i))) = ∑' (i : ℕ), measure_theory.extend (λ (s : set Ω) (_x : is_measurable s), μ s) (f i),
  {
    rw infi_prop_def,
    apply B1,
  }, 
  rw ← B3,
  apply @infi_le ennreal _ _,
end


lemma measure_theory.measure.to_outer_measure_eq_top {Ω:Type*} [M:measurable_space Ω]:
   (⊤:measure_theory.measure Ω).to_outer_measure = ⊤ := 
begin
  rw ← measure_theory.measure.trimmed,
  rw ← @top_le_iff (measure_theory.outer_measure Ω) _,
  have B1:((⊤:measure_theory.outer_measure Ω).to_measure measure_theory.outer_measure.le_top_caratheodory).to_outer_measure.trim ≤ (⊤:measure_theory.measure Ω).to_outer_measure.trim,
  {
    apply measure_theory.outer_measure.trim_monotone,
    apply measure_theory.measure.to_outer_measure_le.mpr,
    simp
  }, 
  rw measure_theory.outer_measure.top_to_measure_to_outer_measure_eq_top at B1,
  rw measure_theory.outer_measure.top_eq_trim at B1,
  apply B1,
end


lemma measure_theory.measure.top_apply {Ω:Type*} [M:measurable_space Ω]
   {S:set Ω}:S.nonempty → (⊤:measure_theory.measure Ω)(S) = (⊤:ennreal) :=
begin
  intro A1,
  rw measure.apply,
  rw measure_theory.measure.to_outer_measure_eq_top,
  simp,
  rw measure_theory.outer_measure.top_apply A1,
end


--Unused.
lemma measure_is_nonnegative {Ω:Type*} [M:measurable_space Ω]:is_nonnegative (measure_theory.measure Ω) :=
begin
  unfold is_nonnegative,
  intros μ,
  rw measure_theory.measure.le_iff,
  intros s A1,
  simp,
end


--measure_theory.measure is not an ordered_comm_monoid, or I couldn't find it.
lemma measure_theory.measure.le_add {Ω:Type*} [M:measurable_space Ω] {μ ν:measure_theory.measure Ω}:μ ≤ μ + ν :=
begin
  rw measure_theory.measure.le_iff,
  intros S B1,
  simp,
  apply le_add_nonnegative _ _ (nonnegative_ennreal),
end


lemma measure_theory.measure.sub_restrict_comm {Ω:Type*} [M:measurable_space Ω]
  (μ ν:measure_theory.measure Ω) {S:set Ω}:is_measurable S →
  (μ - ν).restrict S = (μ.restrict S) - (ν.restrict S) :=
begin
  intro A1,
  rw measure_theory.measure.sub_def,
  rw measure_theory.measure.sub_def,
  have G1:{d : measure_theory.measure Ω | μ ≤ d + ν}.nonempty,
  {
    apply @set.nonempty_of_mem _ _ μ,
    simp,
    apply measure_theory.measure.le_add,
  },
  rw measure_theory.measure.Inf_restrict _ G1 A1,
  apply le_antisymm,
  {
    apply @Inf_le_Inf' (measure_theory.measure Ω) _,
    intros t B1,
    simp at B1,
    apply exists.intro (t.restrict S),
    split,
    {
      simp,
      apply exists.intro (t + (⊤:measure_theory.measure Ω).restrict Sᶜ),
      split,
      {
        rw add_assoc,
        rw add_comm _ ν,
        rw ← add_assoc,
        rw measure_theory.measure.le_iff,
        intros T E1,
        have E2:is_measurable (S ∩ T) := is_measurable.inter A1 E1,
        --rw measure_theory.measure.add_apply,
        apply measure_theory.measure.le_of_partition _ _ A1 E1;
          rw measure_theory.measure.add_apply,
        {
          rw measure_theory.measure.restrict_apply E2,
          rw set.inter_assoc,
          rw set.inter_comm _ Sᶜ,
          rw ← set.inter_assoc,
          rw set.inter_compl_eq_empty,
          simp,
          rw measure_theory.measure.le_iff at B1,
          have B2 := B1 (S ∩ T) E2,
          rw measure_theory.measure.add_apply at B2,
          rw measure_theory.measure.restrict_apply E2 at B2,
          rw measure_theory.measure.restrict_apply E2 at B2,
          have E3:S ∩ T ∩ S = S ∩ T,
          {
            rw set.inter_eq_self_of_subset_left,
            apply set.inter_subset_left S T,
          },
          rw E3 at B2,
          apply B2,
        },
        cases (@empty_or_nonempty _ (Sᶜ ∩ T)) with E4 E4,
        {
          rw measure_theory.measure.restrict_apply,
          have E5:Sᶜ ∩ T ∩ Sᶜ = Sᶜ ∩ T,
          {
            rw set.inter_eq_self_of_subset_left,
            apply set.inter_subset_left Sᶜ T,
          },
          rw E5,
          have E6:(⊤:measure_theory.measure Ω)(Sᶜ ∩ T) = (⊤:ennreal),
          {
            apply measure_theory.measure.top_apply,
            apply E4,
          },
          rw E6,
          simp,
          apply is_measurable.inter (is_measurable.compl A1) E1,
        },
        {
          rw E4,
          simp,
        },
      },
      {
        apply measure_theory.measure.ext,
        intros T D1,
        rw measure_theory.measure.restrict_apply D1,
        rw measure_theory.measure.restrict_apply D1,
        rw measure_theory.measure.add_apply,
        rw measure_theory.measure.restrict_apply (is_measurable.inter D1 A1),
        have D2:T ∩ S ∩ Sᶜ = ∅,
        {
          rw set.inter_assoc,
          simp,
        },
        rw D2,
        simp,
      },
    },
    {
      apply measure_theory.measure.restrict_le_self,
    },
  },
  {
    apply @Inf_le_Inf' (measure_theory.measure Ω) _,
    intros s C1,
    simp at C1,
    cases C1 with t C1,
    cases C1 with C1 C2,
    subst s,
    apply exists.intro (t.restrict S),
    split,
    {
      simp,
      rw ← measure_theory.measure.restrict_add,
      apply measure_theory.measure.restrict_le_restrict_of_le,
      apply C1,
    },
    {
      apply le_refl _,
    },
  },
end


lemma jordan_decomposition_junior_zero {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S:set Ω):le_on_subsets μ ν S →
  (μ - ν) S = 0 :=
begin
  intro A1,
  have B1 := le_on_subsets_is_measurable A1,
  rw ← measure_theory.measure.restrict_apply_self _ B1,
  rw measure_theory.measure.sub_restrict_comm,
  rw measure_theory.measure.sub_eq_zero_if_le,
  simp,
  apply restrict_le_restrict_of_le_on_subsets _ _ A1,
  apply B1,
end


--This works with EITHER ν or μ being finite, or even ν S < ⊤.
lemma jordan_decomposition_junior_apply {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S:set Ω):ν.is_finite → le_on_subsets ν μ S →
  (μ - ν) S = μ S - ν S :=
begin
  intros AX A1,
  have B1 := le_on_subsets_is_measurable A1,
  rw ← measure_theory.measure.restrict_apply_self _ B1,
  rw measure_theory.measure.sub_restrict_comm,
  rw measure_theory.measure.sub_apply,
  rw measure_theory.measure.restrict_apply_self,
  rw measure_theory.measure.restrict_apply_self,
  apply B1,
  apply B1,
  apply B1,
  {
    unfold measure_theory.measure.is_finite,
    rw measure_theory.measure.restrict_apply,
    apply measure_theory.measure.is_finite_all _ ,
    apply AX,
    simp,
  },
  {
    --rw le_on_subsets_def at A1,
    apply restrict_le_restrict_of_le_on_subsets,
    apply A1,
  },
  apply B1,
end



/-
  A jordan decomposition of subtraction.
 -/
lemma jordan_decomposition_nonneg_sub {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S T:set Ω):μ.is_finite → 
    is_measurable T → (le_on_subsets μ ν S) → (le_on_subsets ν μ Sᶜ) →
    (ν - μ) T = ν (S ∩ T) - μ (S ∩ T) :=
begin
  intros A1 A3 A4 A5,
  have A2:is_measurable S,
  {
     apply le_on_subsets_is_measurable A4,
  },
  have B1:(ν - μ) T = (ν - μ) (S∩ T) + (ν - μ) (Sᶜ ∩ T),
  {
    rw measure_theory.measure_partition_apply,
    apply A2,
    apply A3,
  },
  have B2:(ν - μ) (S∩ T) = ν (S ∩ T) - μ (S ∩ T),
  {
    apply jordan_decomposition_junior_apply,
    apply A1,
    apply le_on_subsets_subset _ _ _ _ A4,
    simp,
    apply is_measurable.inter A2 A3,
  },
  have B3:(ν - μ) (Sᶜ ∩ T) = 0,
  {
    apply jordan_decomposition_junior_zero,
    apply le_on_subsets_subset _ _ _ _ A5,
    simp,
    apply is_measurable.inter (is_measurable.compl A2) A3,
  },
  rw B1,
  rw B2,
  rw B3,
  rw add_zero,
end


lemma jordan_decomposition_nonneg_sub' {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (S:set Ω) (T:set Ω):μ.is_finite → 
    (le_on_subsets μ ν S) → (le_on_subsets ν μ Sᶜ) →
    (is_measurable T) →
    (ν - μ) T = (ν.restrict S) T - (μ.restrict S) T :=
begin
  intros A1 A2 A3 B1,
  rw jordan_decomposition_nonneg_sub μ ν S T A1 B1 A2 A3,
  rw measure_theory.measure.restrict_apply B1,
  rw measure_theory.measure.restrict_apply B1,
  rw set.inter_comm T,
end

lemma real.sub_le_sub_of_le_of_le_of_le {a b c d:real}:
    a ≤ b → c ≤ d → a ≤ b - c + d :=
begin
  intros A1 A2,
  apply le_trans A1,
  have B1:b - c + c  ≤ b - c + d,
  {
    apply add_le_add,
    apply le_refl _,
    apply A2,
  },
  simp at B1,
  apply B1
end

lemma nnreal.sub_le_sub_of_le_of_le_of_le {a b c d:nnreal}:
    a ≤ b → c ≤ d → d ≤ a → a ≤ b - c + d :=
begin
  intros A1 A2 A3,
  rw ← nnreal.coe_le_coe,
  rw nnreal.coe_add,
  rw nnreal.coe_sub,
  apply real.sub_le_sub_of_le_of_le_of_le,
  {
    rw nnreal.coe_le_coe,
    apply A1,
  },
  {
    rw nnreal.coe_le_coe,
    apply A2,
  },
  apply le_trans A2,
  apply le_trans A3,
  apply le_trans A1,
  apply le_refl _,
end


lemma ennreal.sub_le_sub_of_le_of_le_of_le {a b c d:ennreal}:
    a ≤ b → c ≤ d → d ≤ a → a - d ≤ b - c :=
begin
  cases a;cases b;cases c;cases d;try {simp},
  intros A1 A2 A3,
  have B1:(a:ennreal) ≤ (b:ennreal) - (c:ennreal) + (d:ennreal),
  {
    rw ← ennreal.coe_sub,
    rw ← ennreal.coe_add,
    rw  ennreal.coe_le_coe,
    apply nnreal.sub_le_sub_of_le_of_le_of_le A1 A2 A3,
  },
  apply B1,  
end


lemma measure_theory.measure.add_compl_inter {Ω:Type*} [measurable_space Ω]
  (μ:measure_theory.measure Ω) (S T:set Ω):(is_measurable S) → 
  (is_measurable T) →
  (μ T = μ (S ∩ T) + μ (Sᶜ ∩ T)) :=
begin
  intros A1 A2,
  have A3:T = (S∩ T) ∪ (Sᶜ ∩ T),
  {
    rw ← set.inter_distrib_right,
    rw set.union_compl_self,
    simp,
  },
  have A4:μ T =  μ ( (S∩ T) ∪ (Sᶜ ∩ T)),
  {
    rw ← A3,
  },
  rw A4,
  rw measure_theory.measure_union,
  rw set.inter_comm,
  rw set.inter_comm _ T,
  apply disjoint_inter_compl,
  apply is_measurable.inter A1 A2,
  apply is_measurable.inter (is_measurable.compl A1) A2,
end


lemma le_on_subsets_inter {Ω:Type*} [measurable_space Ω] 
    {μ ν:measure_theory.measure Ω} {T U:set Ω}:is_measurable U →
    le_on_subsets μ ν T → μ (T ∩ U) ≤ ν (T ∩ U) :=
begin
  intros A1 A2,
  rw le_on_subsets_def at A2,
  apply A2.right,
  simp,
  apply is_measurable.inter A2.left A1,
end


--This may be gotten by easier methods.
lemma measure_theory.measure.sub_le_sub {Ω:Type*} [measurable_space Ω] 
    (μ ν:measure_theory.measure Ω) (T:set Ω):μ.is_finite → 
    is_measurable T → (ν T - μ T) ≤ (ν - μ) T :=
begin
  intros A1 A2,
  have B1 := hahn_unsigned_inequality_decomp ν μ A1,
  cases B1 with U B1,
  have C1 := le_on_subsets_is_measurable B1.left,
  rw jordan_decomposition_nonneg_sub μ ν Uᶜ,
  {
    have C2:ν T = ν (U ∩ T) + ν (Uᶜ ∩ T),
    {
      apply measure_theory.measure.add_compl_inter _ _ _  C1 A2,
    },
    rw C2,
    have C3:μ T = μ (U ∩ T) + μ (Uᶜ ∩ T),
    {
      apply measure_theory.measure.add_compl_inter _ _ _  C1 A2,
    },
    rw C3,
    simp,
    rw add_comm (μ (U ∩ T)) (μ (Uᶜ ∩ T)),
    rw ← add_assoc,
    have C4:ν (Uᶜ ∩ T) ≤ ν (Uᶜ ∩ T) - μ (Uᶜ ∩ T) + μ (Uᶜ ∩ T),
    {
      apply ennreal.le_sub_add_self,
    }, 
    have C5 := add_le_add_right C4 (μ (U ∩ T)),
    apply le_trans _ C5,
    rw add_comm,
    apply add_le_add_left _ _,
    apply le_on_subsets_inter A2 B1.left,
  },
  apply A1,
  apply A2,
  apply B1.right,
  simp,
  apply B1.left,
end


lemma measure_theory.measure.is_support_def {α:Type*} [measurable_space α]
    (μ:measure_theory.measure α) (S:set α):
    μ.is_support S = (is_measurable S ∧ μ (Sᶜ) = 0) := rfl

def measure_theory.measure.perpendicular {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):Prop :=
    (∃ S T:set α, μ.is_support S ∧ ν.is_support T ∧  
    disjoint S T)


lemma measure_theory.measure.perpendicular_def {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):μ.perpendicular ν =
    (∃ S T:set α, μ.is_support S ∧ ν.is_support T ∧  
    disjoint S T) := rfl


lemma set_disjoint_def2 {α:Type*} (A B:set α): disjoint A B ↔ (A ∩ B ⊆ ∅) :=
begin
  split;intros A1;apply A1,
end

lemma set_disjoint_def3 {α:Type*} (A B:set α):(A ∩ B = ∅) ↔ disjoint A B :=
begin
  rw set_disjoint_def2,
  split;intros A1,
  {
    rw A1,
  },
  {
    apply set.subset.antisymm A1,
    simp,
  },
end

lemma measure_theory.measure.perpendicular_def2 {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):μ.perpendicular ν ↔
    (∃ S:set α,  is_measurable S ∧ μ S = 0 ∧  ν (Sᶜ) = 0) :=
begin
  rw measure_theory.measure.perpendicular_def,
  split;intros B1,
  {
    cases B1 with S B1,
    cases B1 with T B1,
    cases B1 with B1 B2,
    cases B2 with B2 B3,
    rw measure_theory.measure.is_support_def at B1,
    rw measure_theory.measure.is_support_def at B2,

    apply exists.intro T,
    split,
    {
      apply B2.left,      
    },
    split,
    {
      cases B1 with C1 C2,
      rw ← ennreal.le_zero_iff,
      rw ← ennreal.le_zero_iff at C2,
      apply le_trans _ C2,
      apply measure_theory.measure_mono,
      rw ← set_disjoint_def3 at B3,
      rw set.inter_comm at B3,
      rw ← set.subset_compl_iff_disjoint at B3,
      apply B3,
    },
    {
      apply B2.right,
    },
  },
  {
    cases B1 with S B1,
    apply exists.intro Sᶜ,
    apply exists.intro S,
    split,
    {
      rw measure_theory.measure.is_support_def,
      apply and.intro (is_measurable.compl (B1.left)),
      simp,
      apply B1.right.left,
    },
    split,
    {
      rw measure_theory.measure.is_support_def,
      apply and.intro (B1.left) (B1.right.right),
    },
    {
      rw ← set_disjoint_def3,
      rw ← set.subset_compl_iff_disjoint,
      apply set.subset.refl Sᶜ,
    },
  },
end


lemma measure_theory.measure.perpendicular_intro {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) {S:set α}:is_measurable S → 
    μ S = 0 → ν (Sᶜ) = 0 →
μ.perpendicular ν :=
begin
  intros A1 A2 A3,
  rw measure_theory.measure.perpendicular_def2,
  apply exists.intro S (and.intro A1 (and.intro A2 A3)),
end

lemma measure_theory.measure.not_perpendicular {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α) {S:set α}:(¬(μ.perpendicular ν)) → is_measurable S → 
    μ S = 0 → 0 < ν (Sᶜ)  :=
begin
  intros A1 A2 A3,
  rw zero_lt_iff_ne_zero,
  intros A4,
  apply A1,
  apply measure_theory.measure.perpendicular_intro μ ν A2 A3 A4,
end


lemma measure_theory.measure.perpendicular_symmetric' {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):(μ.perpendicular ν) →
    (ν.perpendicular μ) :=
begin
  
  intro A1,
  rw measure_theory.measure.perpendicular_def2,
  rw measure_theory.measure.perpendicular_def2 at A1,
  cases A1 with S A1,
  apply exists.intro Sᶜ,
  apply and.intro (is_measurable.compl A1.left),
  apply and.intro A1.right.right,
  simp,
  apply A1.right.left,
end


lemma measure_theory.measure.perpendicular_symmetric {α:Type*} [measurable_space α]
    (μ ν:measure_theory.measure α):(μ.perpendicular ν) ↔
    (ν.perpendicular μ) :=
begin
  split;apply measure_theory.measure.perpendicular_symmetric',
end


lemma measure_theory.measure.perpendicular_of_le {α:Type*}
    [measurable_space α] {μ ν ν':measure_theory.measure α}:μ.perpendicular ν →
    ν' ≤ ν → μ.perpendicular ν' :=
begin
  intros A1 A2,
  rw measure_theory.measure.perpendicular_def2,
  rw measure_theory.measure.perpendicular_def2 at A1,
  cases A1 with S A1,
  apply exists.intro S,
  apply and.intro A1.left,
  apply and.intro (A1.right.left),
  rw ← ennreal.le_zero_iff,
  rw ← A1.right.right,
  apply A2,
  apply is_measurable.compl (A1.left),
end

lemma measure_theory.measure.sub_le {α:Type*}
    [measurable_space α] {μ ν:measure_theory.measure α}:μ - ν ≤ μ :=
begin
  rw measure_theory.measure.sub_def,
  apply @Inf_le (measure_theory.measure α) _ _,
  simp,
  apply measure_theory.measure.le_add,
end


lemma measure_theory.measure.perpendicular_of_sub {α:Type*} [measurable_space α]
   {μ ν ν':measure_theory.measure α}:μ.perpendicular ν → (μ.perpendicular (ν - ν')) :=
begin
  intros A1,
  apply measure_theory.measure.perpendicular_of_le A1,
  apply measure_theory.measure.sub_le,
end


lemma measure_theory.measure.smul_finite {α:Type*} [measurable_space α]
   {μ:measure_theory.measure α} {ε:ennreal}:ε ≠ ⊤ → μ.is_finite → (ε• μ).is_finite :=
begin
  unfold measure_theory.measure.is_finite,
  intros A1 A2,
  rw ennreal_smul_measure_apply,
  apply ennreal.mul_lt_top,
  rw lt_top_iff_ne_top,
  apply A1,
  apply A2,
  simp,
end 


lemma nnreal.mul_lt_mul_of_pos_of_lt 
    {a b c:nnreal}:(0 < a) → (b < c) → (a * b < a * c) :=
begin
  intros A1 A2,
  apply mul_lt_mul',
  apply le_refl _,
  apply A2,
  simp,
  apply A1,
end
/-
  It is hard to generalize this.
 -/
lemma nnreal.mul_pos_iff_pos_pos 
    {a b:nnreal}:(0 < a * b) ↔ (0 < a)∧ (0 < b) :=
begin
  split;intros A1,
  {
    rw zero_lt_iff_ne_zero at A1,
    repeat {rw zero_lt_iff_ne_zero},
    split;intro B1;apply A1,
    {
       rw B1,
       rw zero_mul,
    },
    {
      rw B1,
      rw mul_zero,
    },
  },
  {
    have C1:0 ≤ a * 0,
    {
      simp,
    },
    apply lt_of_le_of_lt C1,
    apply nnreal.mul_lt_mul_of_pos_of_lt,
    apply A1.left,
    apply A1.right,
  },
end


lemma nnreal.inv_mul_eq_inv_mul_inv {a b:nnreal}:(a * b)⁻¹=a⁻¹ * b⁻¹ :=
begin
  rw nnreal.mul_inv,
  rw mul_comm,
end


lemma nnreal.le_zero_iff {a:nnreal}:a ≤ 0 ↔ a=0 :=
begin
  simp
end

lemma nnreal.pos_iff {a:nnreal}:0 < a ↔ a ≠ 0 :=
begin
  split;intros B1,
  {
    intros C1,
    subst a,
    simp at B1,
    apply B1,
  },
  {
    apply by_contradiction,
    intros D1,
    apply B1,
    rw ← @nnreal.le_zero_iff a,
    apply le_of_not_lt D1,
  },
end


lemma ennreal.inv_mul_eq_inv_mul_inv {a b:ennreal}:(a≠ 0) → (b≠ 0) → (a * b)⁻¹=a⁻¹ * b⁻¹ :=
begin
  cases a;simp;cases b;simp,
  intros A1 A2,
  rw ← ennreal.coe_mul,
  repeat {rw ← ennreal.coe_inv},
  rw ← ennreal.coe_mul,
  rw ennreal.coe_eq_coe,
  apply @nnreal.inv_mul_eq_inv_mul_inv a b,
  apply A2,
  apply A1,
  rw ← @nnreal.pos_iff (a * b),
  rw nnreal.mul_pos_iff_pos_pos,
  repeat {rw zero_lt_iff_ne_zero},
  apply and.intro A1 A2,
end


lemma ennreal.div_dist {a b c:ennreal}:(b≠ 0) → (c≠ 0) → a/(b * c)=(a/b)/c :=
begin
  intros A1 A2,
  rw ennreal.div_def,
  rw ennreal.inv_mul_eq_inv_mul_inv,
  rw ← mul_assoc,
  rw ennreal.div_def,
  rw ennreal.div_def,
  apply A1,
  apply A2,
end


lemma ennreal.div_eq_zero_iff {a b:ennreal}:a/b=0 ↔ (a = 0) ∨ (b = ⊤) :=
begin
  cases a;cases b;split;simp;intros A1;simp;simp at A1,
end

/-
  Helper function to lift nnreal.exists_unit_frac_lt_pos to ennreal.
 -/
lemma ennreal.exists_unit_frac_lt_pos' {ε:nnreal}:0 < ε → (∃ n:ℕ, (1/((n:ennreal) + 1)) < (ε:ennreal)) :=
begin
  intros A1,
--  simp at A1,
  have C1:= nnreal.exists_unit_frac_lt_pos A1,   
  cases C1 with n A1,
  apply exists.intro n,
  have D1:((1:nnreal):ennreal) = 1 := rfl,
  rw ← D1,
  have D2:((n:nnreal):ennreal) = (n:ennreal),
  {
    simp,
  },
  rw ← D2,
  rw ← ennreal.coe_add,
  rw ← ennreal.coe_div,
  rw ennreal.coe_lt_coe,
  apply A1,
  simp,
end


lemma ennreal.exists_unit_frac_lt_pos {ε:ennreal}:0 < ε → (∃ n:ℕ, (1/((n:ennreal) + 1)) < ε) :=
begin
  cases ε,
  {
     intros A1,
     have B1:(0:nnreal) < (1:nnreal),
     {
       apply zero_lt_one,
     },
     have B1:=ennreal.exists_unit_frac_lt_pos' B1,
     cases B1 with n B1,
     apply exists.intro n,
     apply lt_of_lt_of_le B1,
     simp,
  },
  {
    intros A1,
    simp at A1,
    have C1:= ennreal.exists_unit_frac_lt_pos' A1,   
    apply C1,
  },
end


lemma ennreal.zero_of_le_all_unit_frac {x:ennreal}:
    (∀ (n:ℕ), (x ≤ 1/((n:ennreal) + 1))) →  (x = 0) :=
begin
  intros A1,
  rw ← not_exists_not at A1, 
  apply by_contradiction,
  intros B1,
  apply A1,
  have B2:0 < x,
  {
    rw  zero_lt_iff_ne_zero,
    apply B1,
  },
  have B3:= ennreal.exists_unit_frac_lt_pos B2,
  cases B3 with n B3,
  apply exists.intro n,
  apply not_le_of_lt,
  apply B3,
end



lemma ennreal.unit_frac_pos {n:ℕ}:(1/((n:ennreal) + 1))>0 :=
begin
  simp,
  intros B1,
  rw ennreal.add_eq_top at B1,
  simp at B1,
  apply B1,
end


lemma ennreal.div_eq_top_iff {a b:ennreal}:a/b=⊤ ↔ 
                             ((a = ⊤)∧(b≠ ⊤) )∨ ((a≠ 0)∧(b=0)):=
begin
  rw ennreal.div_def,
  cases a;cases b;simp,
end

lemma ennreal.unit_frac_ne_top {n:ℕ}:(1/((n:ennreal) + 1))≠ ⊤ :=
begin
  intro A1, 
  rw ennreal.div_eq_top_iff at A1,
  simp at A1,
  apply A1,
end



lemma set.compl_Union_eq_Inter_compl {α β:Type*} {f:α → set β}:(⋃ n, f n)ᶜ = (⋂ n, (f n)ᶜ) :=
begin
  ext b,
  split;intros A1;simp;simp at A1;apply A1,
end



lemma le_on_subsets_of_zero {α:Type*} [measurable_space α] {μ:measure_theory.measure α}
   (ν:measure_theory.measure α)  {S:set α}:is_measurable S → μ S = 0 → le_on_subsets μ ν S := 
begin
  intros A1 A2,
  rw le_on_subsets_def,
  apply and.intro A1,
  intros X B1 B2,
  have B3:μ X ≤ μ S,
  {
    apply measure_theory.measure_mono,
    apply B1,
  },
  apply le_trans B3,
  rw A2,
  simp,
end


lemma measure_theory.measure.sub_zero_eq_self {α:Type*} [measurable_space α] {μ ν:measure_theory.measure α} {S:set α}:is_measurable S → μ.is_finite → μ S = 0 → 
  (ν - μ) S = ν S :=
begin
  intros A1 A2 A4,
  have B1 := le_on_subsets_of_zero ν A1 A4,
  rw jordan_decomposition_junior_apply,
  rw A4,
  simp,
  apply A2,
  apply B1,
end


lemma nnreal.mul_le_mul_left' (a b:nnreal) (H:a≤ b) (c:nnreal):
    c * a ≤ c * b :=
begin
  cases (classical.em (c = 0)) with B1 B1,
  {
    subst c,
    simp,
  },
  {
    have C1:0 < c,
    {
      rw zero_lt_iff,
      intro C1A,
      apply B1,
      apply C1A,
    },
    rw mul_le_mul_left,
    apply H,
    apply C1,
  },
end

lemma ennreal.mul_le_mul_left' (a b:ennreal) (H:a≤ b) (c:ennreal):
    c * a ≤ c * b :=
begin
  revert H,
  cases c;cases a;cases b;try {simp},
  {
    intros A1,
    rw ennreal.top_mul,
    rw ennreal.top_mul,
    cases (classical.em (a = 0)) with B1 B1,
    {
       subst a,
       simp,
    },
    {
       have B2:0 < a,
       {
         rw zero_lt_iff_ne_zero,
         intro B2A,
         rw B2A at B1,
         simp at B1,
         apply B1,
       },
       have B3:0 < b,
       {
         apply lt_of_lt_of_le B2 A1,
       },
       have B4:(b:ennreal) ≠ 0,
       {
         rw zero_lt_iff_ne_zero at B3,
         intros B4A,
         apply B3,
         simp at B4A,
         apply B4A,
       },
       rw if_neg B4,
       simp,
    },
  },
  {
     apply le_refl _,
  },
  {
    rw ennreal.mul_top,
    cases (classical.em (c = 0)) with D1 D1,
    {
       subst c,
       simp,
    },
    {
       have E1:¬((c:ennreal) = 0),
       {
         intro E1A,
         apply D1,
         simp at E1A,
         apply E1A,
       },
       rw if_neg E1,
       simp,
    },
  },
  rw ← ennreal.coe_mul,
  rw ← ennreal.coe_mul,
  rw ennreal.coe_le_coe,
  intro F1,
  apply nnreal.mul_le_mul_left',
  apply F1,
end


lemma measure_theory.measure.perpendicular_of {α:Type*} [M:measurable_space α]
   {μ ν:measure_theory.measure α}:μ.is_finite → ν.is_finite → 
   (∀ ε:ennreal,  ε > 0 → μ.perpendicular (ν - (ε • μ)) ) → 
   μ.perpendicular ν  :=
begin
  intros A2 A3 A1,
  have B1:∀ n:ℕ,(∃ S:set α,  is_measurable S ∧ μ S = 0 ∧ 
          (ν - ((1/((n:ennreal) + 1))• μ)) (Sᶜ) = 0),
  {
    intros n,
    have B1A:(1/((n:ennreal) + 1))>0,
    {
      apply ennreal.unit_frac_pos,
    },
    have B1B := A1 _ B1A,
    rw measure_theory.measure.perpendicular_def2 at B1B,
    apply B1B,
  },
  have B2 := classical.some_func B1,
  cases B2 with f B2,
  let T := ⋃ n, f n,
  begin
    have C1:T = ⋃ n, f n := rfl,
    have C2:Tᶜ = ⋂ n, (f n)ᶜ,
    {
      rw C1,
      rw set.compl_Union_eq_Inter_compl,
    },
    have C3:is_measurable T,
    {
      rw C1,
      apply is_measurable.Union,
      intro n,
      apply (B2 n).left,
    },
    have C4:is_measurable Tᶜ,
    {
      apply is_measurable.compl C3,
    },
    have I1:∀ (n:ℕ), Tᶜ ⊆ (f n)ᶜ,
    {
      intro n,
      rw C2,
      apply @set.Inter_subset α ℕ (λ n, (f n)ᶜ),
    },
    have I2:∀ (n:ℕ), μ Tᶜ ≤ μ (f n)ᶜ,
    {
      intro n,      
      apply @measure_theory.measure_mono α M μ _ _ (I1 n),
    },
       
    apply @measure_theory.measure.perpendicular_intro α _ μ ν T,
    {
      apply is_measurable.Union,
      intro n,
      apply (B2 n).left,
    },
    {
       rw C1,
       rw ← ennreal.le_zero_iff,
       have D1:=@measure_theory.measure.Union_nat α _ μ f,
       apply le_trans D1,
       rw ennreal.le_zero_iff,
       have E1:(λ n, μ (f n)) = (λ (n:ℕ), (0:ennreal)),
       {
         apply funext,
         intro n,
         apply (B2 n).right.left,
       },
       rw E1,
       simp,
    },
    {
       --rw C2,       
       have H1:ν (Tᶜ)/(μ (Tᶜ)) = 0,
       {
          apply ennreal.zero_of_le_all_unit_frac,
          intro n,
          apply ennreal.div_le_of_le_mul,
          --have H1B := H1A n,
          have H1B:(ν) Tᶜ - ((1 / ((n:ennreal) + 1)) • μ) Tᶜ ≤ 
                   (ν - (1 / ((n:ennreal) + 1)) • μ) Tᶜ,
          {
            apply measure_theory.measure.sub_le_sub,
            {
              apply measure_theory.measure.smul_finite,
              {
                apply ennreal.unit_frac_ne_top,
              },
              {
                apply A2,
              },
            },
            apply C4,
          },

          have H1C:(ν) Tᶜ - ((1 / ((n:ennreal) + 1)) • μ) Tᶜ = 0, 
          --have H1B:(ν - (1 / ((n:ennreal) + 1)) • μ) Tᶜ = 0,
          {
            rw ← ennreal.le_zero_iff,
            apply le_trans H1B,
            rw ← (B2 n).right.right,
            apply measure_theory.measure_mono (I1 n), 
          },
          rw ennreal_smul_measure_apply at H1C,
          apply ennreal.le_of_sub_eq_zero,
          apply H1C,
          apply C4,
       },
       rw ennreal.div_eq_zero_iff at H1,
       cases H1 with H1 H1,
       {
         apply H1,
       },
       {
         exfalso,
         apply measure_theory.measure.is_finite_all_ne μ A2 H1,
       },
    },
  end
end


lemma measure_theory.measure.exists_of_not_perpendicular {α:Type*} [measurable_space α]
   (μ:measure_theory.measure α) {ν:measure_theory.measure α}:μ.is_finite → ν.is_finite →
   (¬ (μ.perpendicular ν)) → 
   (∃ ε:ennreal,  ε > 0  ∧  ¬μ.perpendicular (ν - (ε • μ)) ) :=
begin
  intros A1 A2 A3,
  apply classical.exists_of_not_forall_not,
  intros B1,
  apply A3,
  apply measure_theory.measure.perpendicular_of A1 A2,
  intros ε C1,
  have C2 := B1 ε,
  simp at C2,
  apply C2,
  apply C1,
end


lemma measure_theory.measure.sub_add_cancel_of_le {α:Type*} [measurable_space α] {μ ν:measure_theory.measure α}:μ.is_finite →
  μ ≤ ν → ν - μ + μ = ν :=
begin
  intros A2 A1,
  apply measure_theory.measure.ext,
  intros S B1,
  rw measure_theory.measure.add_apply,
  rw jordan_decomposition_junior_apply,
  rw ennreal.sub_add_cancel_of_le,
  apply A1,
  apply B1,
  apply A2,
  rw le_on_subsets_def,
  apply and.intro B1,
  intros X' C1 C2,
  apply A1,
  apply C2,
end


/- 
  This is taken from a step in Tao's proof of the Lebesgue-Radon-Nikodym Theorem.
  By the Hahn Decomposition Theorem, we can find a set where μ ≤ ν and μ S > 0.
 -/
lemma measure_theory.measure.perpendicular_sub_elim {α:Type*} [measurable_space α]
    (μ:measure_theory.measure α) {ν:measure_theory.measure α}: 
    ν.is_finite → 
    ¬(μ.perpendicular (ν - μ)) → 
    ∃ (S:set α), is_measurable S ∧ le_on_subsets μ ν S ∧ 0 < μ S :=
begin
  intros A2 A3,
  have B1:=hahn_unsigned_inequality_decomp μ ν A2,
  cases B1 with X B1,
  have B2 := jordan_decomposition_junior_zero ν μ Xᶜ B1.right,
  have B3 := le_on_subsets_is_measurable B1.right,
  have B4:¬((ν - μ).perpendicular μ),
  {
    intro B4A,
    apply A3,
    apply measure_theory.measure.perpendicular_symmetric',
    apply B4A,
  },
  have B5 := measure_theory.measure.not_perpendicular (ν - μ) μ B4 B3 B2,
  simp at B5,
  apply exists.intro X,
  apply and.intro (le_on_subsets_is_measurable B1.left) 
       (and.intro B1.left B5),
end


lemma ennreal_smul_smul_measure_assoc {Ω:Type*} [N:measurable_space Ω] 
    (μ:measure_theory.measure Ω) {a b:ennreal}:(a * b) • μ = a • (b • μ) :=
begin
  apply measure_theory.measure.ext,
  intros S B1,
  repeat {rw ennreal_smul_measure_apply _ _ S B1},
  rw mul_assoc,
end


lemma measure_theory.measure.perpendicular_zero {Ω:Type*} [N:measurable_space Ω] (μ:measure_theory.measure Ω): 
  (μ.perpendicular 0) :=
begin
  rw measure_theory.measure.perpendicular_def2,
  apply exists.intro (∅:set Ω),
  split,
  apply is_measurable.empty,
  split,
  apply measure_theory.measure_empty,
  simp,
end

lemma measure_theory.measure.perpendicular_smul' {Ω:Type*} [N:measurable_space Ω] (μ ν:measure_theory.measure Ω) {k:ennreal}: 
  (μ.perpendicular ν) → (k • μ).perpendicular ν :=
begin
  intros A2,
  rw measure_theory.measure.perpendicular_def2,
  rw measure_theory.measure.perpendicular_def2 at A2,
  cases A2 with S A2,
  apply exists.intro S,
  apply and.intro (A2.left),
  apply and.intro _ A2.right.right,
  rw ennreal_smul_measure_apply,
  rw A2.right.left,
  simp,
  apply A2.left,
end


lemma measure_theory.measure.perpendicular_smul {Ω:Type*} [N:measurable_space Ω] (μ ν:measure_theory.measure Ω) {k:ennreal}: 0 < k → 
  (k • μ).perpendicular ν → μ.perpendicular ν :=
begin
  intros A1 A2,
  rw measure_theory.measure.perpendicular_def2,
  rw measure_theory.measure.perpendicular_def2 at A2,
  cases A2 with S A2,
  apply exists.intro S,
  apply and.intro A2.left,
  apply and.intro _ A2.right.right,
  have B1 := A2.right.left,
  rw ennreal_smul_measure_apply _ _ _ A2.left at B1,
  simp at B1,
  cases B1 with B1 B1,
  {
    exfalso,
    rw zero_lt_iff_ne_zero at A1,
    apply A1,
    apply B1,
  },
  {
    apply B1,
  },
end


lemma measure_theory.measure.restrict_integral_eq_integral_indicator {Ω:Type*} [M:measurable_space Ω] 
    (μ:measure_theory.measure Ω) {S:set Ω} {f:Ω → ennreal}:
    (is_measurable S) →
    (μ.restrict S).integral f = μ.integral (S.indicator f) :=
begin
  intros A1,
  
  unfold measure_theory.measure.integral,
  rw measure_theory.lintegral_indicator,
  apply A1,
end


lemma integral_eq {Ω:Type*} [M:measurable_space Ω] 
    (μ:measure_theory.measure Ω) {f g:Ω → ennreal}:(f = g) →
    μ.integral f = μ.integral g :=
begin
  intros A1,
  rw A1,
end

lemma with_density_indicator_eq_restrict {Ω:Type*} [M:measurable_space Ω] 
    (μ:measure_theory.measure Ω) {S:set Ω} {f:Ω → ennreal}:
    (is_measurable S) → 
    μ.with_density (set.indicator S f) = (μ.restrict S).with_density f :=
begin
  intros A1,
  apply measure_theory.measure.ext,
  intros T B1,
  rw measure_theory.with_density_apply2,
  rw measure_theory.with_density_apply2,
  rw measure_theory.measure.restrict_integral_eq_integral_indicator,
  {
    rw set.indicator_indicator,
    rw set.indicator_indicator,
    rw set.inter_comm,
  },
  {
    apply A1,
  },
  {
    apply B1,
  },
  {
    apply B1,
  },
end

lemma scalar_as_with_density {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {k:ennreal}:
  (k•μ) = μ.with_density (λ ω:Ω, k) :=
begin
  apply measure_theory.measure.ext,
  intros S B1,
  rw with_density_const_apply,
  rw ennreal_smul_measure_apply,
  apply B1,
  apply B1,
end


lemma with_density_indicator_eq_restrict_smul {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) {S:set Ω} {k:ennreal}:(is_measurable S) → μ.with_density (set.indicator S (λ ω:Ω, k)) = k • μ.restrict S :=
begin
  intro A1,
  rw with_density_indicator_eq_restrict,
  rw scalar_as_with_density,
  apply A1,
end


lemma smul_restrict_comm {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) {S:set Ω} {k:ennreal}:(is_measurable S) → (k • μ).restrict S = k • μ.restrict S :=
begin
  intros A1,
  apply measure_theory.measure.ext,
  intros T B1,
  rw ennreal_smul_measure_apply _ _ _ B1,
  rw measure_theory.measure.restrict_apply B1,
  rw measure_theory.measure.restrict_apply B1,
  rw ennreal_smul_measure_apply _ _ _ (is_measurable.inter B1 A1),
end


/-
  In the full version of Lebesgue-Radon-Nikodym theorem, μ is an unsigned 
  σ-finite measure, and ν is a signed σ-finite measure.

  The first stage of the proof focuses on finite, unsigned measures
  (see lebesgue_radon_nikodym_unsigned_finite). In that proof,
  there is a need to prove that if two measures are not perpendicular, then there
  exists some nontrivial f where μ.with_density f set.univ > 0 and 
  μ.with_density f ≤ ν. In Tao's An Epsilon of Room, this is to show that
  taking the f which maximizes μ.with_density f set.univ subject to
  μ.with_density f ≤ ν, when subtracted from ν, leaves a measure perpendicular to μ.
 -/
lemma lebesgue_radon_nikodym_junior {Ω:Type*} [N:measurable_space Ω] 
  (μ ν:measure_theory.measure Ω):
  (μ.is_finite) →
  (ν.is_finite) →
  ¬(μ.perpendicular ν) →
  ∃ f:Ω → ennreal, 
  measurable f ∧
  μ.with_density f ≤ ν ∧
  0 < μ.with_density f (set.univ) :=
begin
  intros A1 A2 A3,
  have B1 := measure_theory.measure.exists_of_not_perpendicular μ A1 A2 A3,
  cases B1 with ε B1,
  have B2:¬((ε • μ).perpendicular (ν - ε • μ)),
  {
    intro B2A,
    apply B1.right,
    apply measure_theory.measure.perpendicular_smul _ _ B1.left,
    apply B2A,
  },
  have B3 := measure_theory.measure.perpendicular_sub_elim _ A2 B2,
  cases B3 with S B3,
  let f := (set.indicator S (λ ω:Ω, ε)),
  begin
    have C1:f = (set.indicator S (λ ω:Ω, ε)) := rfl,
    apply exists.intro f,
    split,
    {
      apply measurable_set_indicator,
      apply B3.left,
      apply measurable_const,
    },
    split,
    {
      rw C1,
      rw with_density_indicator_eq_restrict_smul _ B3.left,
      rw ← smul_restrict_comm _ B3.left,
      apply le_trans _ (@measure_theory.measure.restrict_le_self _ _ _ S),
      apply restrict_le_restrict_of_le_on_subsets,
      apply B3.right.left,
    },
    {
      have C2:0 < μ S,
      {
        have C2A := B3.right.right,
        rw ennreal_smul_measure_apply _ _ _ B3.left at C2A,
        simp at C2A,
        apply C2A.right,
      },
      rw C1,
      rw with_density_indicator_eq_restrict_smul _ B3.left,
      rw ennreal_smul_measure_apply _ _ _ (is_measurable.univ),
      rw measure_theory.measure.restrict_apply is_measurable.univ,
      simp,
      apply and.intro (B1.left) C2,
    },
  end
end


lemma set.indicator_sup {Ω:Type*} {x y:Ω → ennreal} {S:set Ω}:
   (∀ ω∈ S,  x ω ≤ y ω) → 
   set.indicator S (x ⊔ y) = set.indicator S y :=
begin
  intros A1,
  apply funext,
  intro ω,
  cases (classical.em (ω ∈ S)) with B1 B1,
  {
    repeat {rw set.indicator_of_mem B1},
    simp,
    rw max_eq_right,
    apply A1,
    apply B1,
  },
  {
    repeat {rw set.indicator_of_not_mem B1},
  },
end


lemma sup_indicator_partition {α:Type*} {x y:α → ennreal}:
   (x ⊔ y) = set.indicator {ω|y ω < x ω} x + set.indicator {ω|x ω ≤ y ω} y  :=
begin
  apply funext,
  intro a,
  simp,
  cases (classical.em (x a ≤ y a)) with B1 B1,
  {
    rw max_eq_right B1,
    rw set.indicator_of_not_mem,
    rw set.indicator_of_mem,
    simp,
    apply B1,
    simp,
    apply B1,
  },
  {
    have B2:=lt_of_not_le B1,
    have B3:=le_of_lt B2,
    rw max_eq_left B3,
    rw set.indicator_of_mem,
    rw set.indicator_of_not_mem,
    simp,
    apply B1,
    apply B2,
  },
end


lemma with_density_le_sup_apply {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal} {S:set Ω}:
    (is_measurable S) →
    (∀ ω∈ S,  x ω ≤ y ω) → 
    μ.with_density (x ⊔ y) S =
    μ.with_density y S :=
begin
  intros A3 A4,
  rw measure_theory.with_density_apply2 _ _ _ A3,
  rw measure_theory.with_density_apply2 _ _ _ A3,
  rw set.indicator_sup A4,
end


lemma le_on_subsets_with_density_of_le {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal} {S:set Ω}:
    (is_measurable S) →
    (∀ ω∈ S,  x ω ≤ y ω) → 
    le_on_subsets (μ.with_density x) (μ.with_density y) S :=
begin
  intros A3 A4,
  rw le_on_subsets_def,
  apply and.intro A3,
  intros X' B1 B2,
  apply with_density_le_with_density B2,
  intros ω C1,
  apply A4 ω,
  apply B1,
  apply C1,
end


lemma measure_theory.measure.sup_def {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}:μ ⊔ ν = Inf {d|μ ≤ d ∧ ν ≤ d} := rfl


lemma measure_theory.measure.le_sup {Ω:Type*} [measurable_space Ω] {μ ν d:measure_theory.measure Ω}:(∀ c, μ ≤ c → ν ≤ c → d ≤ c) → d ≤ μ ⊔  ν :=
begin
  rw measure_theory.measure.sup_def,
  intro A1,
  apply @le_Inf (measure_theory.measure Ω) _,
  intros c B1,
  apply A1;simp at B1,
  apply B1.left,
  apply B1.right, 
end


lemma measure_theory.measure.le_restrict_add_restrict {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}
  {S:set Ω}:le_on_subsets μ ν S → le_on_subsets ν μ Sᶜ → 
   μ ≤ μ.restrict Sᶜ + ν.restrict S :=
begin
  intros A1 A2,
  have B1:is_measurable S := le_on_subsets_is_measurable A1,
  rw measure_theory.measure.le_iff,
  intros T C1,
  rw measure_theory.measure_partition_apply μ S T B1 C1,
  rw measure_theory.measure.add_apply,
  rw add_comm,
  apply @add_le_add ennreal _,
  {
    rw measure_theory.measure.restrict_apply C1,
    rw set.inter_comm,
    apply le_refl _,
  },
  {
    rw measure_theory.measure.restrict_apply C1,
    rw set.inter_comm,
    rw le_on_subsets_def at A1,
    apply A1.right,
    apply set.inter_subset_right,
    apply is_measurable.inter C1 B1,
  },
end

lemma measure_theory.measure.sup_eq {Ω:Type*} [measurable_space Ω] {μ ν:measure_theory.measure Ω}
  (S:set Ω):le_on_subsets μ ν S → le_on_subsets ν μ Sᶜ → 
   (μ ⊔ ν) = μ.restrict Sᶜ + ν.restrict S :=
begin
  intros A1 A2,
  have D1:is_measurable S := le_on_subsets_is_measurable A1,
  apply le_antisymm,
  {
    apply @sup_le (measure_theory.measure Ω) _,
    {
      apply measure_theory.measure.le_restrict_add_restrict A1 A2,
    },
    {
      rw add_comm,
      have B1:ν.restrict Sᶜᶜ = ν.restrict S,
      {
        simp,
      },
      rw ← B1,
  
      apply measure_theory.measure.le_restrict_add_restrict,
      apply A2,
      simp,
      apply A1,
    },
  },
  {
     apply measure_theory.measure.le_sup,
     intros c C1 C2,
     rw measure_theory.measure.le_iff,
     intros T C3,
     simp,
     rw measure_theory.measure.restrict_apply C3,
     rw measure_theory.measure.restrict_apply C3,
     rw measure_theory.measure_partition_apply c S,
     rw add_comm,
     apply @add_le_add ennreal _,
     rw set.inter_comm,
     apply C2,
     apply is_measurable.inter D1 C3,
     rw set.inter_comm,
     apply C1,
     apply is_measurable.inter (is_measurable.compl D1) C3,
     apply D1,
     apply C3,
  },
end


lemma set.indicator_add_comm {α β:Type*} [ordered_add_comm_monoid β] {f g:α → β} {S:set α}:
    S.indicator (f + g) = S.indicator f + S.indicator g :=
begin
  apply funext,
  intros a,
  simp,
  cases (classical.em (a∈ S)) with B1 B1,
  {
    repeat {rw set.indicator_of_mem B1},
    simp,
  },
  {
    repeat {rw set.indicator_of_not_mem B1},
    simp,
  },
end


lemma measure_theory.measure.with_density_restrict_comm {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω)
  {x:Ω → ennreal} {S:set Ω}:is_measurable S → (μ.with_density x).restrict S = (μ.restrict S).with_density x := 
begin
  intros A1,
  apply measure_theory.measure.ext,
  intros T B1,
  rw measure_theory.with_density_apply2,
  rw measure_theory.measure.restrict_integral_eq_integral_indicator,
  rw measure_theory.measure.restrict_apply,
  rw set.indicator_indicator,
  rw set.inter_comm,
  rw measure_theory.with_density_apply2,
  repeat {assumption <|> apply is_measurable.inter},
end

lemma measure_theory.measure.with_density_add {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal}:measurable x → measurable y → μ.with_density (x + y) = μ.with_density x + μ.with_density y :=
begin
  intros A1 A2,
  apply measure_theory.measure.ext,
  intros S B1,
  rw measure_theory.measure.add_apply,
  rw measure_theory.with_density_apply2 ,
  rw measure_theory.with_density_apply2 ,
  rw measure_theory.with_density_apply2 ,
  rw set.indicator_add_comm,
  rw measure_theory.measure.integral_add,
  repeat{assumption <|> apply measurable_set_indicator},
end


lemma lt_eq_le_compl {δ α:Type*}
  [linear_order α] {f g : δ → α}:{a | f a < g a} ={a | g a ≤ f a}ᶜ :=
begin
    apply set.ext,
    intros ω;split;intros A3A;simp;simp at A3A;apply A3A,
end


lemma is_measurable_lt {δ α:Type*} [measurable_space δ] [measurable_space α] [topological_space α]
  [opens_measurable_space α]
  [linear_order α] [order_closed_topology α] [topological_space.second_countable_topology α]
  {f g : δ → α} (hf : measurable f) (hg : measurable g) :
  is_measurable {a | f a < g a} :=
begin
  rw lt_eq_le_compl,
  apply is_measurable.compl,
  apply is_measurable_le,
  repeat {assumption},
end


lemma with_density_sup' {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal}:measurable x → measurable y → 
    μ.with_density (x ⊔ y) =
    (μ.with_density x).restrict {ω:Ω|y ω < x ω} 
    +
    (μ.with_density y).restrict {ω:Ω|x ω ≤ y ω} :=
begin
  intros A1 A2,
  rw sup_indicator_partition,
  rw measure_theory.measure.with_density_add,
  rw with_density_indicator_eq_restrict,
  rw with_density_indicator_eq_restrict,
  rw measure_theory.measure.with_density_restrict_comm,
  rw measure_theory.measure.with_density_restrict_comm,
  repeat {assumption <|> apply is_measurable_le <|> apply is_measurable_lt <|> apply measurable_set_indicator},
end


--Oh dear. This may not be true: instead it might be an inequality.
lemma with_density_sup {Ω:Type*} {M:measurable_space Ω} (μ:measure_theory.measure Ω)
  {x y:Ω → ennreal}:measurable x → measurable y → 
    μ.with_density (x ⊔ y) =
    measure_theory.measure.with_density μ x ⊔ measure_theory.measure.with_density μ y :=
begin
  intros A1 A2,
  rw with_density_sup' μ A1 A2,
  rw measure_theory.measure.sup_eq {ω:Ω|x ω ≤ y ω},
  rw lt_eq_le_compl,
  {
    apply le_on_subsets_with_density_of_le,
    apply is_measurable_le A1 A2,
    simp,
  },
  {
    apply le_on_subsets_with_density_of_le,
    apply is_measurable.compl (is_measurable_le A1 A2),
    simp,
    intros ω B3,
    apply le_of_lt B3,
  },
end


lemma ennreal.lt_add_self {a b:ennreal}:a < ⊤ → 0 < b → a < a + b :=
begin
  cases a;cases b;simp,
  intros A1,
  rw ← ennreal.coe_add,
  rw ennreal.coe_lt_coe,
  simp,
  apply A1,
end


lemma lebesgue_radon_nikodym_finite_unsigned {Ω:Type*} {N:measurable_space Ω} (μ ν:measure_theory.measure Ω):
  (μ.is_finite) →
  (ν.is_finite) →
  ∃ f:Ω → ennreal, 
  ∃ μ₂:measure_theory.measure Ω,
  measurable f ∧ 
  ν = μ.with_density f + μ₂ ∧
  μ.perpendicular μ₂ :=
begin
  intros A1 A2,
  let S := {f:Ω → ennreal|measurable f ∧ (μ.with_density f ≤ ν)},
  let M := Sup ((λ f, μ.with_density f set.univ) '' S),
  begin
    have A4:S = {f:Ω → ennreal|measurable f ∧ (μ.with_density f ≤ ν)} := rfl,
    have B2:M = Sup ((λ f, μ.with_density f set.univ) '' S)
            := rfl,
    have B3:M < ⊤,
    {
     
      -- Because μ is finite.
      -- Or, because ν is finite, and μ... is less than ν.
      have B3A:M ≤ ν set.univ,
      {
        rw B2,
        apply @Sup_le ennreal _,
        intros b B3A1,
        simp at B3A1,
        cases B3A1 with f B3A1,
        cases B3A1 with B3A1 B3A2,
        subst b,
        apply B3A1.right,
        apply is_measurable.univ,
      },
      apply lt_of_le_of_lt B3A,
      rw ← measure_theory.measure.is_finite_def,
      apply A2,
    },
    have B1:∃ h:ℕ → Ω → ennreal, 
            (∀ n, h n ∈ S) ∧ 
            (monotone h) ∧
            (μ.with_density (supr h) set.univ) = M,
    {
--      have B1A:=
      apply @Sup_apply_eq_supr_apply_of_closed' (Ω → ennreal) 
          _ S (λ f:Ω → ennreal, μ.with_density f set.univ) _ _, 
      --cases B1A with h B1A,
      { -- ⊢ S.nonempty
        apply @set.nonempty_of_contains (Ω → ennreal) S 0,
        rw A4,
        simp,
        split,
        apply @measurable_const ennreal Ω _ N 0,
        rw with_density.zero,
        apply measure_theory.measure.zero_le,
      },
      { -- ⊢ ∀ a ∈ S, ∀  b ∈ S, a ⊔ b ∈ S
        intros a B1B1 b B1B2,
        cases B1B1 with B1B1 B1B3,
        cases B1B2 with B1B2 B1B4,
        simp,
        split,
        {
          apply measurable_sup B1B1 B1B2,
        },
        {
          rw (with_density_sup μ B1B1 B1B2),
          simp,
          apply and.intro B1B3 B1B4,
        },
      },
      { -- ⊢ ∀ a ∈ S,∀ b ∈ S,a ≤ b → 
        -- (μ.with_density a set.univ ≤ μ.with_density b set.univ),
        intros a B1C b B1D B1E,
        simp,
        rw A4 at B1C,
        rw A4 at B1D,
        apply with_density_le_with_density,
        simp,
        intros ω B1F,
        apply B1E,
      },
      {
        -- ⊢ ∀ (f : ℕ → Ω → ennreal),
        -- set.range f ⊆ S →
        -- monotone f →
        -- supr ((λ (f : Ω → ennreal), ⇑(μ.with_density f) set.univ) ∘ f) =
        -- (λ (f : Ω → ennreal), ⇑(μ.with_density f) set.univ) (supr f)
        intros f B1G B1H,
        simp,
        rw supr_with_density_apply_eq_with_density_supr_apply _ _ B1H,
        simp,
        intros n,
        rw A4  at B1G,
        unfold set.range at B1G,
        rw set.subset_def at B1G,
        simp at B1G,
        apply (B1G (f n) n _).left,
        refl,
        
      },
    },
    cases B1 with h B1,
    have B4:∀ n, measurable (h n),
    {
      intros n,
      have B4A := (B1.left n),
      rw A4 at B4A,
      apply B4A.left,
    },
    let g := supr h,
    begin
      apply exists.intro g,
      /-
        At this point, we have declared that g is the derivative.
        First of all, there are several questions that need to be resolved.
        Is g measurable?
        -- The supremum of a countable set of measurable
           functions is measurable. 
        Is μ.with_density g ≤ ν?
        -- This is true iff  μ.with_density g S ≤ ν S.
        -- For each n, μ.with_density (h n) ≤ ν. Considering a particular
        -- measurable set S, μ.with_density (h n) ≤ ν S. However, HERE IS
        -- THE RUB. We have to be careful about the difference between the
        -- supremum of h and the supremum of μ.with_density h.
        -- The second question is whether ν ≤ μ.with_density g. Let us choose
        -- a specific measurable set S. Suppose that μ.with_density g S < ν S.
        -- Then, since μ.with_density g (-S) ≤ ν S,
        -- μ.with_density g set.univ < ν set.univ.
        -- This implies  
       -/
      have A5:g = supr h := rfl,
      have A6:μ.with_density g set.univ = M,
      {
        rw A5,
        rw ← B1.right.right,
      },
      have A7:μ.with_density g ≤ ν,
      {
        -- For each measurable set S:
        -- (λ f, μ.with_density f S) is continuous.
        -- So, μ.with_density g S ≤ 
        --       supr (λ n, μ.with_density h n S)
        -- supr (λ n, μ.with_density h n S) ≤ ν S,
        -- because for all n, μ.with_density h n S ≤ ν S.
        --WORKING HERE
        rw measure_theory.measure.le_iff,
        intros S A7A,
        rw ← supr_with_density_apply_eq_with_density_supr_apply,
        apply @supr_le ennreal _ _,
        intros i,
        have A7B := (B1.left i),
        simp at A7B,
        apply A7B.right,
        apply A7A,
        apply A7A,
        apply B4,
        apply B1.right.left,
      },
      apply exists.intro (ν - μ.with_density g),
      have C4:ν = μ.with_density g + (ν - μ.with_density g),
      {
        rw add_comm,
        rw measure_theory.measure.sub_add_cancel_of_le,
        rw measure_theory.measure.is_finite_def,
        apply lt_of_le_of_lt (A7 set.univ is_measurable.univ),
        rw measure_theory.measure.is_finite_def at A2,
        apply A2,
        apply A7,       
      }, 
      have C5:measurable g,
      {
        rw A5,
        apply @measurable_supr_of_measurable,
        apply B4,
      },
      apply and.intro C5,
      apply and.intro C4,
      {
        apply by_contradiction,
        intros C1,
        have C2 := lebesgue_radon_nikodym_junior μ (ν - μ.with_density g) A1 _ C1,
        cases C2 with f C2,
        have D1:M < μ.with_density (f + g) set.univ,
        {
          rw measure_theory.measure.with_density_add,
          rw measure_theory.measure.add_apply,
          rw A6,
          rw add_comm,
          apply ennreal.lt_add_self,
          apply B3,
          apply C2.right.right,
          apply C2.left,
          apply C5,
        },
        apply not_le_of_lt D1,
        rw B2,
        apply @le_Sup ennreal _,
        simp,
        apply exists.intro (f  + g),
        split,
        split,
        {
          apply measurable.add,
          apply C2.left,
          apply C5,
        },
        {
          rw C4,
          rw measure_theory.measure.with_density_add,
          rw add_comm,
          apply measure_theory.measure.add_le_add,
          apply le_refl _,
          apply C2.right.left,
          apply C2.left,
          apply C5,    
          --apply @add_le_add (measure_theory.measure Ω) _,
        },
        refl,
        apply measure_theory.measure.is_finite_le,
        apply measure_theory.measure.sub_le,
        apply A2,
      },
    end
  end
end

