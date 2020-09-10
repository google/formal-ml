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
