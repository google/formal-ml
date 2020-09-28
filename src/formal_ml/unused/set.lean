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

import data.set.disjointed data.set.countable
import data.set.lattice data.set.finite
import formal_ml.nat
import formal_ml.set

/-
  Theorems about sets. The best repository of theorems about sets is
  /mathlib/src/data/set/basic.lean. 
 -/


lemma subset_preimage_image (α β:Type*) (A:set α) (f:α → β):
A⊆ (set.preimage f (set.image f A)) :=
begin
  rw set.subset_def,
  intros,
  unfold set.preimage,
  simp,
  apply exists.intro x,
  split,
  {
    assumption,
  },
  {
    refl,
  }
end

-- Note: currently unused.
lemma subset_image_preimage (α β:Type*) (B:set β) (f:α → β):
(set.image f (set.preimage f B))⊆ B :=
begin
  rw set.subset_def,
  intros,
  unfold set.image at a,
  simp at a,
  cases a,
  cases a_h,
  rw a_h_right at a_h_left,
  assumption,
end

--Unused.
lemma sUnion_subset_funion (α β:Type*) (f:α → set β) (Y:set α):
  set.sUnion (f '' Y) ⊆ (⋃ i, f i) :=
begin
  simp,
  rw set.subset_def,
  intros x B1,
  simp at B1,
  cases B1 with i B1,
  simp,
  apply exists.intro i B1.right,
end


--Unused
lemma Union_eq_sUnion_univ (α β:Type*) (f:α → set β):
  (⋃ i, f i) = set.sUnion (f '' set.univ) :=
begin
  simp,
end

lemma sUnion_subset_comm (α:Type*) (X:set (set α)) (Y:set (set α)):
  (X⊆ Y) → (set.sUnion X)⊆ (set.sUnion Y) :=
begin
  intros A1,
  simp,
  intros x X' B1 B2,
  apply exists.intro X',
  split,
  {
    apply A1,
    apply B1,
  },
  {
    apply B2,
  },
end

/-
  Rename this.
  Basically, this argues that if set T is in the image of S, then
  I can construct a set S2 where set T is EXACTLY the image of S2.
  This is true in intuitionistic logic.
  -/
lemma preimage_choice {α β:Type*} (f:α → β) (S:set α) (T:set β):
  T⊆ (set.image f S) →
  ∃ S2:set α, S2 ⊆ S ∧ set.image f S2 = T :=
begin
  intros,
  apply exists.intro ({a:α| (a∈ S) ∧ (f a) ∈ T}),
  split,
  {
    rw set.subset_def,
    simp,
    intros A1 A2 A3,
    exact A2,
  },
  {
    ext,split;intros A4,
    {
      simp at A4,
      cases A4 with a2 A5,
      cases A5 with X4 X5,
      subst x,
      apply X4.right,
    },
    {
      simp,
      rw set.subset_def at a,
      have S1:x∈ f '' S,
      {
        apply a,
        exact A4,
      },
      cases S1 with x2 S2,
      cases S2 with S3 S4,
      subst x,
      apply exists.intro x2,
      split,
      {
        split;assumption,
      },
      {
        refl,
      }
    }
  }
end

lemma set.diff_inter_comm (α:Type*) (S T U:set α):(S ∩ T) \ U = (S \ U) ∩ T :=
begin
  ext,
  split;intros,
  {
    cases a,
    cases a_left,
    split,
    {
      rw set.mem_diff;split;assumption,
    },
    exact a_left_right,
  },
  {
    cases a,
    cases a_left,
    rw set.mem_diff,
    split,
    split,
    repeat {assumption},
  }
end

--Novel?
--Translation of inf_bot_eq:x ⊓ ⊥ = ⊥
lemma set.inter_empty_eq_empty (α:Type*) (T:set α):T∩ ∅ = ∅ :=
begin
  ext,
  split,
  {
    intros,
    rw set.mem_inter_eq at a,
    cases a,
    apply a_right,
  },
  {
    intros,
    exfalso,
    apply a,
  }
end

--Novel?
lemma union_not_mem_intro (α:Type*) (A B:set α) (x:α):
  (x∉ A) → (x∉ B) → (x∉  A ∪ B) :=
begin
  intros A1 A2 A3,
  rw set.mem_union at A3,
  cases A3 with A3 A3,
  apply A1 A3,
  apply A2 A3,
end

--Novel? Not used.
lemma mem_of_union_not_mem_left (α:Type*) (A B:set α) (x:α):
  (x∉ A) → (x∈ A∪ B) → (x∈  B) :=
begin
  intros,
  cases a_1,
  {
    exfalso,
    apply a,
    exact a_1,
  },
  {
    exact a_1,
  }
end

--I have not seen this theorem literally, but there are a
--lot of theorems in /mathlib/src/data/set/basic.lean that
--are very close.
--However, this is a nice lemma, even if unused.
lemma set.neg_def {α:Type*} {S:set α}:
  Sᶜ = (λ a:α, a∉ S) := 
begin
  refl,
end

--Unused.
lemma univ_has_Union (α:Type*):∀ (f:ℕ → set α ),
  (∀ (n:ℕ), (f n)∈(@set.univ (set α))) →  @set.univ (set α) (⋃ (n:ℕ),f n) :=
begin
  intros,
  unfold set.univ,
end

--A small variant on set.prod_subset_prod_iff.
lemma set.prod_subset {α:Type*} (A₁ A₂:set α) {β:Type*} (B₁ B₂:set β) (a:α) (b:β):
  (a ∈ A₁) →
  (b∈ B₁) →
  ((set.prod A₁ B₁)  ⊆ (set.prod A₂  B₂) ↔ (A₁ ⊆ A₂) ∧ (B₁ ⊆ B₂)) :=
begin
  intros A1 A2,
  rw set.prod_subset_prod_iff,
  split;intros B1,
  {
    cases B1,
    apply B1,
    exfalso,
    cases B1;rw set.eq_empty_iff_forall_not_mem at B1;apply B1,
    apply A1,
    apply A2,
  },
  {
    left,
    apply B1,
  },
end
