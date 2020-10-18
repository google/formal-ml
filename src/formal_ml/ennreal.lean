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
import data.real.ennreal
import formal_ml.nat
import formal_ml.nnreal

-- ennreal is a canonically_ordered_add_monoid
-- ennreal is not a decidable_linear_ordered_semiring
-- Otherwise (0 < c) → (c * a) ≤ (c * b) → (a ≤ b),
-- but this does not hold for c =⊤, a = 1, b = 0. 
-- This is because ennreal is not an ordered_cancel_add_comm_monoid.
-- Nor is it an ordered_cancel_comm_monoid
-- This implies it is also not an ordered_semiring



lemma ennreal_coe_eq_lift {a:ennreal} {b:nnreal}:a = b → (a.to_nnreal = b) :=
begin
  intro A1,
  have A2:(a.to_nnreal)=(b:ennreal).to_nnreal,
  {
    rw A1,
  },
  rw ennreal.to_nnreal_coe at A2,
  exact A2,
end

/-
  This is one of those complicated inequalities that is probably too rare to justify a
  lemma. However, since it shows up, we give it the canonical name and move on.
-/
lemma ennreal_le_to_nnreal_of_ennreal_le_of_ne_top {a:nnreal} {b:ennreal}:
    b≠ ⊤ → (a:ennreal) ≤ b → (a ≤ b.to_nnreal) :=
begin
  intros A1 A2,
  cases b,
  {
    simp at A1,
    exfalso,
    apply A1,
  },
  {
    have A3:(b:ennreal) = (some b) := rfl,
    rw ← A3,
    rw (@ennreal.to_nnreal_coe b),
    rw ← ennreal.coe_le_coe,
    rw A3,
    apply A2,
  }
end


lemma ennreal_add_monoid_smul_def{n:ℕ} {c:ennreal}: n •ℕ c = ↑(n) * c := 
begin
  induction n,
  {
    simp,
  },
  {
    simp,
  }
end


lemma ennreal_lt_add_ennreal_one (x:nnreal):(x:ennreal) < (1:ennreal) + (x:ennreal) :=
begin
  apply ennreal.coe_lt_coe.mpr,
  simp,
  apply canonically_ordered_semiring.zero_lt_one,
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

lemma ennreal.forall_epsilon_le_iff_le : ∀{a b : ennreal}, (∀ε:nnreal, 0 < ε → b < ⊤ → a ≤ b + ε) ↔ a ≤ b :=
begin
  intros a b,
  split,
  apply ennreal.le_of_forall_epsilon_le, 
  intros A1 ε B1 B2,
  --apply le_trans A1,
  apply le_add_right A1,
end

lemma ennreal.lt_of_add_le_of_pos {x y z:ennreal}:x + y ≤ z → 0 < y → x < ⊤ → x < z :=
begin
  cases x;cases y;cases z;try {simp},
  {repeat {rw ← ennreal.coe_add},rw ennreal.coe_le_coe,apply nnreal.lt_of_add_le_of_pos},
end

lemma ennreal.iff_infi_le {α:Type*} {f:α → ennreal} {b : ennreal}:
   (∀ (ε : nnreal), 0 < ε → b < ⊤ → (∃a, f a  ≤ b + ↑ε)) ↔ infi f ≤ b :=
begin
  --intro A1,
  --rw ← @ennreal.forall_epsilon_le_iff_le (infi f) b,
  split,
  apply ennreal.infi_le,
  intro A1,
  intros ε A2 A3,
  apply classical.by_contradiction,
  intro A4,
  apply not_lt_of_ge A1,
  have A5:b + ↑ε ≤ infi f,
  { apply @le_infi ennreal _ _, intro a,
    have A5:=(forall_not_of_not_exists A4) a,
    simp at A5,
    apply le_of_lt A5,
  },
  apply ennreal.lt_of_add_le_of_pos A5,
  simp,apply A2,
  apply A3,
end

#check classical.some
lemma ennreal.exists_le_infi_add {α:Type*} (f:α → ennreal) [N:nonempty α] {ε:nnreal}:0 < ε → (∃ a, f a ≤ infi f + ε) :=
begin
  intros A1,
  have A2:infi f ≤ infi f,
  {apply le_refl _},
  rw ← ennreal.iff_infi_le at A2,
  cases (decidable.em (infi f < ⊤)) with A3 A3,
  apply A2 ε  A1 A3,
  simp only [not_lt, top_le_iff] at A3,
  --cases N,
  have a := classical.choice N,
  apply exists.intro a,
  rw A3,
  simp,
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

/-This isn't true. Specifically, for any non-finite sets, one can construct a counterexample.
  Using ℕ as an example, f:ℕ → ℕ → ennreal := λ a b, if (a < b) then 1 else 0.
lemma ennreal.supr_infi_eq_infi_supr {α β:Type*} [nonempty α] [nonempty β] [partial_order β] {f:α → β → ennreal}:(∀ a:α, monotone (f a)) →
  (⨅ (a:α), ⨆ (b:β), f a b )= ( ⨆ (b:β), ⨅ (a:α), f a b) :=
begin

 -/

