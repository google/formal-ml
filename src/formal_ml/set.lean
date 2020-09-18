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


--Appears "novel", used: move to mathlib?
lemma set.union_inter_compl (α:Type*) (A B:set α):(A∩ B)∪ (A∩ Bᶜ)=A :=
begin
  rw ← set.inter_union_distrib_left,
  rw set.union_compl_self,
  simp,
end


--Used: Move to mathlib?
lemma set.range_eq_image_compl (α β:Type*) (S:(set α)) (f:α → β):(set.range f) = (set.image f S) ∪ (set.image f (Sᶜ)) :=
begin
  rw ← set.image_univ,
  rw ← set.union_compl_self,
  apply set.image_union,
end


----Used, and surprisingly novel. Move to mathlib?
lemma set.nonempty_image_of_nonempty {α β:Type*} {f:α → β} {T:set α}:T.nonempty → 
  (f '' T).nonempty  :=
begin
  intro A1,
  have B1:=set.nonempty_def.mp A1,
  cases B1 with a B1,
  have B2:(f a ∈ f '' T),
  {
    simp,
    apply exists.intro a,
    split,
    apply B1,
    refl,
  },
  apply set.nonempty_of_mem B2,
end


--Novel, used: move to mathlib?
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
 -/
lemma set.disjoint.symm {α:Type*} {A B:set α}:disjoint A B → disjoint B A :=
begin
  rw set.disjoint_iff_inter_eq_empty,
  rw set.disjoint_iff_inter_eq_empty,
  rw set.inter_comm,
  simp,
end

--Unused, but there are parallels in mathlib for finset and list.
lemma set.disjoint_comm {α:Type*} {A B:set α}:disjoint A B ↔ disjoint B A :=
begin
  split;intros A1;apply set.disjoint.symm A1,
end

lemma set.disjoint_inter_compl {α:Type*} (A B C:set α):disjoint (A ∩ B) (C∩ Bᶜ) :=
begin
  apply set.disjoint_of_subset_left (set.inter_subset_right A B),
  apply set.disjoint_of_subset_right (set.inter_subset_right C Bᶜ),
  apply set.disjoint_compl,
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


---------------------- Unused theorems --------------------------------------------

/-

  These theorems were useful to work out to understand the tendsto
  operator for limits. Ultimately, I didn't use them.

  You would think set.image f A = B and (set.preimage f B = A) were
  equivalent. However, consider:
  f a_1 = b_1
  f a_2 = b_2
  f a_3 = b_2

  If A = {a_1,a_2,a_3} and B = {b_1,b_2,b_3}, then:
  preimage f {b_1,b_2,b_3} = {a_1,a_2,a_3}, but
  image f {a_1,a_2,a_3} = {b_1,b_2}
  so ∃ B, ∃ f, image f (preimage f B) ≠ B
  Can we prove a weaker statement:
  image f (preimage f B) ⊆ B?

  Similarly, for the other direction:
  image f {a_1,a_2} = {b_1,b_2}
  preimage f {b_1,b_2} = {a_1,a_2,a_3}
  so ∃ A, ∃ f, preimage f (image f A) ≠ A

  However A ⊆ preimage f (image f A)?
-/
-- Note: currently unused.
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
