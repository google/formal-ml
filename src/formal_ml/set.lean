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

/-
  Theorems about sets. The best repository of theorems about sets is
  /mathlib/src/data/set/basic.lean. 
 -/

--Novel, used: move to mathlib?
--Alternately, look into topological_space.lean, and see what is necessary.
lemma set.preimage_fst_def {α β:Type*} {Bα:set (set α)}:
    (@set.preimage (α × β) α (@prod.fst α β) '' Bα) =
    {U : set (α × β) | ∃ (A : set α) (H : A ∈ Bα), U = @set.prod α β A (@set.univ β)} :=
begin
  ext,split;intros A1A,
  {
    simp at A1A,
    cases A1A with A A1A,
    cases A1A with A1B A1C,
    subst x,
    split,
    simp,
    split,
    apply A1B,
    unfold set.prod,
    simp,
    refl,
  },
  {
    simp at A1A,
    cases A1A with A A1A,
    cases A1A with A1B A1C,
    subst x,
    split,
    split,
    apply A1B,
    unfold set.prod,
    simp,
    refl
  }
end


--Novel, used.
lemma set.preimage_snd_def {α β:Type*} {Bβ:set (set β)}:
    (@set.preimage (α × β) β (@prod.snd α β) '' Bβ) =
    {U : set (α × β) | ∃ (B : set β) (H : B ∈ Bβ), U = @set.prod α β (@set.univ α) B} :=
begin
    ext,split;intros A1A,
    {
      simp at A1A,
      cases A1A with A A1A,
      cases A1A with A1B A1C,
      subst x,
      split,
      simp,
      split,
      apply A1B,
      unfold set.prod,
      simp,
      refl,
    },
    {
      simp at A1A,
      cases A1A with A A1A,
      cases A1A with A1B A1C,
      subst x,
      split,
      split,
      apply A1B,
      unfold set.prod,
      simp,
      refl
    }
end


--Novel, used.
--Similar, but not identical to set.preimage_sUnion.
--Could probably replace it.
lemma set.preimage_sUnion' {α β:Type*} (f:α → β) (T:set (set β)):
 (f ⁻¹' ⋃₀ T)=⋃₀ (set.image (set.preimage f)  T) :=
begin
  rw set.preimage_sUnion,  
  ext,split;intros A1;simp;simp at A1;apply A1,
end



--Novel, used.
lemma set.prod_sUnion_right {α:Type*} (A:set α) {β:Type*} (B:set (set β)):
  (set.prod A (⋃₀ B)) = ⋃₀  {C:set (α× β)|∃ b∈ B, C=(set.prod A b)} :=
begin
  ext,split;intro A1,
  {
    cases A1 with A2 A3,
    cases A3 with b A4,
    cases A4 with A5 A6,
    simp,
    apply exists.intro (set.prod A b),
    split,
    {
      apply exists.intro b,
      split,
      exact A5,
      refl,
    },
    {
      split;assumption,
    }
  },
  {
    cases A1 with Ab A2,
    cases A2 with A3 A4,
    cases A3 with b A5,
    cases A5 with A6 A7,
    subst Ab,
    cases A4 with A8 A9,
    split,
    {
      exact A8,
    },
    {
      simp,
      apply exists.intro b,
      split;assumption,
    }
  }
end


--Novel, used.
lemma set.prod_sUnion_left {α:Type*} (A:set (set α)) {β:Type*} (B:set β):
  (set.prod (⋃₀ A) B) = ⋃₀  {C:set (α× β)|∃ a∈ A, C=(set.prod a B)} :=
begin
  ext,split;intro A1,
  {
    cases A1 with A2 A3,
    cases A2 with a A4,
    cases A4 with A5 A6,
    simp,
    apply exists.intro (set.prod a B),
    split,
    {
      apply exists.intro a,
      split,
      exact A5,
      refl,
    },
    {
      split;assumption,
    }
  },
  {
    cases A1 with Ab A2,
    cases A2 with A3 A4,
    cases A3 with b A5,
    cases A5 with A6 A7,
    subst Ab,
    cases A4 with A8 A9,
    split,
    {
      simp,
      apply exists.intro b,
      split;assumption,
    },
    {
      exact A9,
    }
  }
end

--Novel, used.
lemma union_trichotomy {β:Type*} [decidable_eq β] {b:β} {S S2:finset β}:
  b∈ (S ∪ S2) ↔ (
      ((b∈  S) ∧ (b∉ S2)) ∨ 
      ((b∈ S) ∧ (b ∈ S2)) ∨ 
      ((b∉ S) ∧ (b∈ S2))) :=
begin
  have B1:(b∈ S)∨ (b∉ S),
  {
    apply classical.em,
  },
  have B2:(b∈ S2)∨ (b∉ S2),
  {
    apply classical.em,
  },
  split;intro A1,
  {
    simp at A1,
    cases A1,
    {
      cases B2,
      {
        right,left,
        apply and.intro A1 B2,  
      },
      {
        left,
        apply and.intro A1 B2,
      },
    },
    {
      right,
      cases B1,
      {
        left,
        apply and.intro B1 A1,
      },
      {
        right,
        apply and.intro B1 A1,
      },
    },
  },
  {
    simp,
    cases A1,
    {
      left,
      apply A1.left,
    },
    cases A1,
    {
      left,
      apply A1.left,
    },
    {
      right,
      apply A1.right,
    },
  },
end

/-
  There are theorems about disjoint properties, but not about disjoint sets.
  It would be good to figure out a long-term strategy of dealing with 
  disjointedness, as it is pervasive through measure theory and probability
  theory. Disjoint is defined on lattices, and sets are basically the canonical
  complete lattice. However, the relationship between complementary sets and
  disjointedness is lost, as complementarity doesn't exist in a generic complete
  lattice.

  SIDE NOTE: lattice.lean now has a ton of theorems. Follow set.disjoint_compl_right
 -/
--Replace with disjoint.symm


lemma set.disjoint.symm {α:Type*} {A B:set α}:disjoint A B → disjoint B A :=
begin
  apply @disjoint.symm (set α) _,
end

--Unused, but there are parallels in mathlib for finset and list.
--Too trivial now.
lemma set.disjoint_comm {α:Type*} {A B:set α}:disjoint A B ↔ disjoint B A :=
begin
  apply @disjoint.comm (set α) _,
end

lemma set.disjoint_inter_compl {α:Type*} (A B C:set α):disjoint (A ∩ B) (C∩ Bᶜ) :=
begin
  apply set.disjoint_of_subset_left (set.inter_subset_right A B),
  apply set.disjoint_of_subset_right (set.inter_subset_right C Bᶜ),
  apply set.disjoint_compl_right,
end


--In general, disjoint A C → disjoint (A ⊓ B) C
lemma set.disjoint_inter_left {α:Type*} {A B C:set α}:
  disjoint A C →
  disjoint (A ∩ B) (C) :=
begin
  intros A1,
  apply set.disjoint_of_subset_left _ A1,
  apply set.inter_subset_left,
end


--In general, disjoint A C → disjoint A (B ⊓ C)
lemma set.disjoint_inter_right {α:Type*} {A B C:set α}:
  disjoint A C →
  disjoint A (B ∩ C) :=
begin
  intros A1,
  apply set.disjoint_of_subset_right _ A1,
  apply set.inter_subset_right,
end

/-
  The connection between Union and supremum comes in 
  useful in measure theory. The next three theorems
  do this directly.
 -/
lemma set.le_Union {α:Type*} {f:ℕ → set α} {n:ℕ}:
    f n ≤ set.Union f :=
begin
  rw set.le_eq_subset,
  rw set.subset_def,
  intros a A3,
  simp,
  apply exists.intro n A3,
end


lemma set.Union_le {α:Type*} {f:ℕ → set α} {S:set α}:
    (∀ i, f i ≤ S) → 
    set.Union f ≤ S :=
begin
  intro A1,
  rw set.le_eq_subset,
  rw set.subset_def,
  intros x A2,
  simp at A2,
  cases A2 with n A2,
  apply A1 n A2,
end


lemma supr_eq_Union {α:Type*}
    {f:ℕ → set α}:
    supr f = set.Union f :=
begin
  apply le_antisymm,
  {
    apply @supr_le (set α) _ _,
    intro i,
    apply set.le_Union,
  },
  {
    apply set.Union_le,
    intros n,
    apply @le_supr (set α) _ _,
  },
end


lemma empty_of_subset_empty {α:Type*} (X:set α):
    X ⊆ ∅ → X = ∅ :=
begin
  have A1:(∅:set α) = ⊥ := rfl,
  rw A1,
  rw ← set.le_eq_subset,
  intro A2,
  rw le_bot_iff at A2,
  apply A2,
end

lemma subset_empty_iff {α:Type*} (X:set α):
    X ⊆ ∅ ↔ X = ∅ :=
begin
  have A1:(∅:set α) = ⊥ := rfl,
  rw A1,
  rw ← set.le_eq_subset,
  apply le_bot_iff,
end


lemma set.eq_univ_iff_univ_subset {α:Type*} {S:set α}:
  set.univ ⊆ S ↔ S = set.univ :=
begin
  have A1:@set.univ α = ⊤ := rfl,
  rw A1,
  rw ← set.le_eq_subset,
  apply top_le_iff,
end

lemma preimage_if {α β:Type*}
  {E:set α} {D:decidable_pred E}
  {X Y:α → β} {S:set β}:
  set.preimage (λ a:α, if (E a) then (X a) else (Y a)) S =
  (E ∩ set.preimage X S) ∪ (Eᶜ ∩ set.preimage Y S) :=
begin
  ext a;split;intros A1,
  {
    cases (classical.em (a∈ E)) with A2 A2,
    {
      rw set.mem_preimage at A1,
      rw if_pos at A1,
      apply set.mem_union_left,
      apply set.mem_inter A2,
      rw set.mem_preimage,
      apply A1,
      rw set.mem_def at A2,
      apply A2,
    },
    {
      rw set.mem_preimage at A1,
      rw if_neg at A1,
      apply set.mem_union_right,
      apply set.mem_inter,
      apply set.mem_compl,
      apply A2,
      rw set.mem_preimage,
      apply A1,
      rw set.mem_def at A2,
      apply A2,
    },
  },
  {
    rw set.mem_preimage,
    rw set.mem_union at A1,
    cases A1 with A1 A1;
    rw set.mem_inter_eq at A1;
    cases A1 with A2 A3;
    rw set.mem_preimage at A3;  
    rw set.mem_def at A2,
    {
      rw if_pos,
      apply A3,
      apply A2,
    },
    {
      rw if_neg,
      apply A3,
      apply A2,
    },
  },
end
