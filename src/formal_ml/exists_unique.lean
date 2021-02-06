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
import tactic.simp_rw


namespace exists_unique
@[simp]
lemma proof_iff {P Q:Prop}:
  (∃! (H:P), Q) ↔ (P ∧ Q) :=
begin
  split;intros h,
  have h_exists := exists_of_exists_unique h,
  cases h_exists with hP hQ,
  apply and.intro hP hQ,
  cases h with hP hQ,
  apply exists_unique.intro hP hQ,
  intros hP' hQ',
  refl,
end

@[simp]
lemma in_set_iff {α:Type*} {s:set α} 
  {P:α → Prop}:
  (∃! a∈s, P a) ↔ (∃! a, a∈s ∧ P a) :=
begin
  simp_rw [exists_unique.proof_iff],
end

/--Technically, `∃! (b∈s), P s` reads "there exists a unique b such that
   there exists a unique proof of `(b∈s)` such that `P s`."
   A more natural interpretation is there exists a unique b such that 
   b∈s and P s. This performs the translation. -/
lemma intro_set {α:Type*} {s:set α} 
  {P:α → Prop} (a : α) (h : a∈ s) (hPa : P a) (h_unique: ∀ b∈ s, P b → b = a):
  ∃! c∈s, P c :=
begin
  rw exists_unique.in_set_iff,
  apply exists_unique.intro a (and.intro h hPa),
  intros y hy_in_s_and_Py,
  apply h_unique y hy_in_s_and_Py.left hy_in_s_and_Py.right,
end

end exists_unique

