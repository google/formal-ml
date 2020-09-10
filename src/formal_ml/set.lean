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
  This is a weird definition. First of all, it is clear that one cannot ask
  a question such as, "what is expected value of (1/n^2), conditioned on
  n being a program that terminates." Nonetheless, if we don't declare
  that some sets are decidable, we can run into problems.
-/
noncomputable def classical_set (T:Type*) (S:set T):(@decidable_pred T S) :=
  λ t, classical.prop_decidable (S t)


noncomputable def classical.decidable_pred {β:Type*} (P:β → Prop):decidable_pred P:=
  (λ b:β, classical.prop_decidable (P b))

noncomputable def classical.decidable_eq (β:Type*):decidable_eq β:=
  (λ b c:β, classical.prop_decidable (b=c))


def union_def (α β:Type*) (f:α → set β):=set.sUnion ((λ S:set β, (∃ a:α , f a = S)))

lemma set.neg_def {α:Type*} {S:set α}:
  Sᶜ = (λ a:α, a∉ S) := 
begin
  refl,
end

lemma mem_set_univ_intro (α:Type*) (x:α):x∈ (@set.univ α) :=
begin
  unfold set.univ,
end
lemma union_def_helper (α β:Type*) (f:α → set β) (a_w:α):
  (λ (S : set β), ∃ (a : α), f a = S) (f a_w) :=
begin
  apply (exists.intro a_w),
  refl,
end

lemma union_def_correct (α β:Type*) (f:α → set β):union_def α β f = ⋃ (a:α), f a :=
begin
  intros,
  unfold union_def,
  unfold set.sUnion,
  intros,
  ext,

  simp,
  split,
  {
    intros,
    cases a,
    cases a_h,
    cases a_h_left,
    apply (exists.intro a_h_left_w),
    rw a_h_left_h,
    assumption,
  },
  {
    intros,
    cases a,
    apply (exists.intro (f a_w)),
    split,
    {
      apply union_def_helper
    },
    {
      assumption,
    }
  }
end


lemma sUnion_member_intro (β:Type*) (X:set (set β)) (x:β) (S:set β):
  x ∈ S →  S ∈ X → (x∈ (set.sUnion X)) :=
begin
  intros,
  unfold set.sUnion,
  simp,
  apply (exists.intro S),
  split; assumption
end




--TODO:remove
lemma funion_member_elim (α β:Type*) (f:α → set β) (x:β):
  (x∈ (⋃ a:α , f a)) → (∃ (a:α), x ∈ f a) :=
begin
  intros A1,
  simp at A1,
  apply A1,
end

lemma funion_helper (α β:Type*) (f:α → set β) (a:α):
  ((λ S, ∃ (a:α), f a = S) (f a)) :=
begin
  apply exists.intro a, simp,
end

lemma funion_member_intro (α β:Type*) (f:α → set β) (x:β) (a:α):
   (x ∈ f a)→ (x∈ (⋃ a:α , f a)):=
begin
  intros,
  have A1:(⋃ a:α , f a) = (union_def α β f),
  apply union_def_correct,
  rw A1,
  unfold union_def,
  apply sUnion_member_intro,
  {
    apply a_1,
  },
  {
    apply funion_helper,
  },
end


lemma emptyset_intro (α:Type*) (S: set α):
  (∀ a ∈ S, false)→ (S = ∅) :=
begin
  intros,
  ext,
  split,
  {
    intros,
    exfalso,
    apply a,
    apply a_1,
  },
  {
    intros,
    exfalso,
    apply a_1,
  }
end


lemma inter_defn (α:Type*) (A B:set α):
  ({a | a ∈ A ∧ a ∈ B} = A ∩ B) :=
begin
  refl,
end

lemma inter_member_elim (α:Type*) (A B:set α) (x:α):
  (x∈ A ∩ B) → (x∈ A) ∧  (x∈  B)  :=
begin
  intros,
  rw ← inter_defn at a,
  split,
  {
    cases a,
    assumption,
  },
  {
    cases a,
    assumption,
  }
end

lemma inter_member_intro (α:Type*) (A B:set α) (x:α):
  (x∈ A) → (x∈  B) → (x∈ A ∩ B) :=
begin
  intros,
  rw ← inter_defn,
  split; assumption
end


lemma union_defn (α:Type*) (A B:set α):
  ({a | a ∈ A ∨ a ∈ B} = A ∪ B) :=
begin
  refl,
end

lemma union_member_elim (α:Type*) (A B:set α) (x:α):
  (x∈ A ∪ B) → (x∈ A) ∨ (x∈  B)  :=
begin
  intros,
  rw ← union_defn at a,
  cases a,
  {
    apply or.inl,
    assumption,
  },
  {
    apply or.inr,
    assumption,
  }
end


lemma union_member_intro1 (α:Type*) (A B:set α) (x:α):
  (x∈ A) → (x∈ A ∪ B) :=
begin
  apply set.mem_union_left,
end

lemma union_member_intro2 (α:Type*) (A B:set α) (x:α):
  (x∈ B) → (x∈ A ∪ B) :=
begin
  apply set.mem_union_right,
end



lemma compl_member_intro (α:Type*) (A:set α) (x:α):
  ¬ (x∈ A) → (x∈ Aᶜ) :=
begin
  intros,
  apply a,
end

lemma notin_false_elim (α:Type*) (A:set α) (x:α):
  (x∉ A) → (x∈ A)→ false :=
begin
  intros,
  apply a,
  apply a_1,
end

-- law of the excluded middle
lemma in_or_notin (α:Type*) (A:set α) (x:α):
   (x∈ A) ∨ (x∉ A):=
begin
  have A1:(x∈ A)→ (x∈ A) ∨ (x∉ A),
  {
    apply or.inl,
  },
  have A2:(x∉  A)→ (x∈ A) ∨ (x∉ A),
  {
    apply or.inr,
  },
  apply (classical.by_cases A1 A2),
end

lemma eq_or_noteq (α:Type*) (A B:set α):
  (A = B) ∨ (A ≠ B):=
begin
  have A1:(A = B)→ (A=B) ∨ (A ≠ B),
  {
    apply or.inl,
  },
  have A2:(A ≠ B)→ (A=B) ∨ (A ≠ B),
  {
    apply or.inr,
  },
  apply classical.by_cases A1 A2,
end



lemma empty_or_contains (α:Type*) (A:set α):
  (A = ∅) ∨ (∃ x,x∈ A) :=
begin
  have A1:(∃ x,x∈ A)→(A = ∅) ∨ (∃ x,x∈ A),
  {
    apply or.inr,
  },
  have A2:¬(∃ x,x∈ A)→(A = ∅) ∨ (∃ x,x∈ A),
  {
    intros,
    left,
    have A2A:∀ x, x∉ A,
    {
      intros,
      intro,
      apply a,
      apply exists.intro x,
      apply a_1,
    },
    ext,
    split,
    {
      intro,
      exfalso,
      have A2B:x∉ A,
      {
        apply A2A,
      },
      apply A2B,
      apply a_1,
    },
    {
      intro,
      exfalso,
      apply a_1,
    }
  },
  apply classical.by_cases A1 A2,
end

lemma notin_false_intro (α:Type*) (A:set α) (x:α):
  ((x∈ A)→ false) → (x∉ A) :=
begin
  intros,
  have A1:(x∈ A) ∨ (x∉ A),
  apply in_or_notin,
  cases A1,
  {
    exfalso,
    apply a,
    assumption,
  },
  {
    assumption,
  }
end


lemma compl_member_elim (α:Type*) (A:set α) (x:α):
   (x∈ Aᶜ) → ¬ (x∈ A) :=
begin
  intros,
  apply a,
end

lemma not_compl_member_elim (α:Type*) (A:set α) (x:α):
  ¬ (x∈ Aᶜ) → (x∈ A) :=
begin
  intros,
  have A1:(x∈ A) ∨ (x∉ A),
  apply in_or_notin,
  cases A1,
  {
    apply A1,
  },
  {
    exfalso,
    apply a,
    apply compl_member_intro,
    apply A1,
  }
end

lemma not_compl_member_intro (α:Type*) (A:set α) (x:α):
  (x∈ A)→ ¬ (x∈ Aᶜ) :=
begin
  intros,
  intro,
  have A1:¬ (x∈ A),
  {
    apply compl_member_elim,
    apply a_1,
  },
  apply A1,
  apply a,
end

lemma double_neg_set (α:Type*) (A:set α):A = ((Aᶜ)ᶜ) :=
begin
  ext,
  split;intros,
  {
    apply compl_member_intro,
    apply not_compl_member_intro,
    apply a,
  },
  {
    apply not_compl_member_elim,
    apply compl_member_elim,
    apply a,
  }
end

lemma set_univ_compl (α:Type*):(∅)ᶜ=(@set.univ α) :=
begin
  ext,
  split,
  {
    intros,
    simp,
  },
  {
    intros,
    rw set.neg_def,
    simp,
  }
end

lemma union_compl_set_univ (α:Type*) (A:set α):A∪ (Aᶜ)=(@set.univ α) :=
begin
  ext,split;intro A1,
  {
    simp,
  },
  {
    have A2:x∈ A ∨ x∉ A,
    {
      apply in_or_notin,
    },
    cases A2,
    {
      apply set.mem_union_left,
      apply A2,
    },
    {
      apply set.mem_union_right,
      intro A3,
      apply A2,
      apply A3,
    }
  }
end

lemma union_inter_compl (α:Type*) (A B:set α):(A∩ B)∪ (A∩ Bᶜ)=A :=
begin
  ext x,split;intro A1,
  {
    cases A1,
    {
      cases A1 with A2 A3,
      exact A2,
    },
    {
      cases A1 with A4 A5,
      exact A4,
    },
  },
  {
    have A6:x∈ B∨ x∉ B,
    {
      apply in_or_notin,
    },
    cases A6,
    {
      left,
      split;assumption,
    },
    {
      right,
      split;assumption,
    }
  }
end

lemma inter_union_compl (α:Type*) (A B:set α): (A ∩ B = ((Aᶜ) ∪ (Bᶜ))ᶜ) :=
begin
  intros,
  ext,
  split,
  {
    intros,
    cases a,
    apply compl_member_intro,
    apply notin_false_intro,
    intros,
    have A1:(x∈ Aᶜ) ∨ (x∈ Bᶜ),
    {
      apply union_member_elim,
      assumption,
    },
    cases A1,
    {
      apply notin_false_elim α A; assumption,
    },
    {
      apply notin_false_elim α B; assumption,
    },
  },
  {
    intros,
    have A2:x∉ ((Aᶜ) ∪ (Bᶜ)),
    {
      apply compl_member_elim,
      assumption
    },
    have A3:x∈ A ∨ (x∉ A),
    {
      apply in_or_notin,
    },
    have A4:x∈ B ∨ (x∉ B),
    {
      apply in_or_notin,
    },
    cases A3,
    {
      cases A4,
      {
        apply inter_member_intro;assumption,
      },
      {
        exfalso,
        have A5:(x ∈ (Aᶜ) ∪ (Bᶜ)),
        {
          apply or.inr,
          apply A4,
        },
        {
          apply notin_false_elim α ((Aᶜ) ∪ (Bᶜ));assumption,
        }
      }
    },
    {
      exfalso,
      have A5:(x ∈ (Aᶜ) ∪ (Bᶜ)),
      {
        apply or.inl,
        assumption,
      },
      apply notin_false_elim α ((Aᶜ) ∪ (Bᶜ));assumption
    }
  }
end


lemma in_univ (α:Type*):∀ a:α, a ∈ (@set.univ  α) :=
begin
  intros,
  unfold set.univ,
end


lemma univ_has_empty (α:Type*):∅ ∈ (@set.univ (set α)) := in_univ (set α) ∅


lemma univ_has_compl (α:Type*):∀ (E:set α), E ∈ (@set.univ (set α)) →  (E)ᶜ∈ (@set.univ (set α)) :=
begin
  intros,
  apply in_univ (set α),
end

lemma univ_has_Union (α:Type*):∀ (f:ℕ → set α ),
  (∀ (n:ℕ), (f n)∈(@set.univ (set α))) →  @set.univ (set α) (⋃ (n:ℕ),f n) :=
begin
  intros,
  unfold set.univ,
end

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


lemma set_range_set_image (α β:Type*) (f:α → β):(set.range f) = (set.image f set.univ) :=
begin
  ext,
  split; intros,
  {
    unfold set.range at a,
    cases a,
    split,
    {
      split,
      {
        have A1:a_w ∈ set.univ,
        {
          apply mem_set_univ_intro,
        },
        apply A1,
      },
      {
        apply a_h,
      }
    }
  },
  {
    unfold set.image at a,
    cases a,
    cases a_h,
    unfold set.range,
    split,
    {
      apply a_h_right,
    },
  }
end

lemma set_image_union (α β:Type*) (S T:(set α)) (f:α → β):(set.image f (S ∪ T)) = (set.image f S) ∪ (set.image f T) :=
begin
  ext,
  unfold set.image,
  simp,
  split;intros,
  {
    cases a,
    cases a_h,
    cases a_h_left,
    {
      left,
      apply exists.intro a_w,
      split;assumption,
    },
    {
      right,
      apply exists.intro a_w,
      split;assumption,
    },
  },
  {
    cases a,
    {
      cases a,
      apply exists.intro a_w,
      split,
      {
        left,
        exact a_h.left,
      },
      {
        exact a_h.right,
      }
    },
    {
      cases a,
      apply exists.intro a_w,
      split,
      {
        right,
        exact a_h.left,
      },
      {
        exact a_h.right,
      }
    },
  }
end

lemma set_univ_eq_set_compl (α:Type*) (S:(set α)):set.univ = S ∪ Sᶜ :=
begin
  ext,
  split;intros,
  {
    rw set.neg_def,
    simp,
    cases classical.em (x∈ S) with A1 A1,
    {
      apply or.inl A1,
    },
    {
      right,
      apply A1,
    },
  },
  {
    simp,
  }
end

lemma set_range_split (α β:Type*) (S:(set α)) (f:α → β):(set.range f) = (set.image f S) ∪ (set.image f (Sᶜ)) :=
begin
  rw set_range_set_image,
  rw (set_univ_eq_set_compl _ S),
  apply set_image_union,
end

lemma image_substh (α β:Type*) (S:(set α)) (f g:α → β):
(∀ s∈ S, f s = g s)→
(set.image f S)⊆ (set.image g S) :=
begin
  intros,
  rw set.subset_def,
  intros,
  {
    cases a_1,
    have A1:f a_1_w = g a_1_w,
    {
      apply a,
      apply a_1_h.left,
    },
    split,
    {
      split,
      apply a_1_h.left,
      rw ← A1,
      apply a_1_h.right,
    },
  }
end

lemma image_subst (α β:Type*) (S:(set α)) (f g:α → β):
(∀ s∈ S, f s = g s)→
(set.image f S)= (set.image g S) :=
begin
  intros,
  have A1:(set.image f S)⊆ (set.image g S),
  {
    apply image_substh,
    apply a,
  },
  have A2:(set.image g S)⊆ (set.image f S),
  {
    apply image_substh,
    intros,
    symmetry,
    apply a,
    exact H,
  },
  apply set.subset.antisymm;assumption,

end
lemma subset_elim (α:Type*) (S T:set α) (x:α):
  (S⊆ T)→ (x∈ S)→ (x∈ T) :=
begin
  intros,
  have A1:∀ y, y∈ S→ y∈ T,
  {
    rw ← set.subset_def,
    apply a,
  },
  apply A1,
  assumption,
end

--{x : finset ℕ | sum x f ∈ b} ∈ filter.at_top
lemma preimage_superset (α β:Type*) (S T:set α) (f:β  → α):
  (S⊆ T)→ {x:β |f x ∈ S} ⊆ {x:β |f x ∈ T} :=
begin
  intros,
  rw set.subset_def,
  intros,
  simp,
  simp at a_1,
  apply subset_elim,
  apply a,
  apply a_1,
end


lemma set_inter_empty_eq_empty (α:Type*) (T:set α):T∩ ∅ = ∅ :=
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



lemma set_diff_def (α:Type*) (S T:set α):S \ T = {x∈ S| x∉ T} :=
begin
  refl
end

lemma set_mem_diff_elim1 (α:Type*) (S T:set α) (x:α):x ∈ S \ T → x∈ S :=
begin
  rw set_diff_def,
  intros,
  simp at a,
  cases a,
  apply a_left,
end

lemma set_mem_diff_elim2 (α:Type*) (S T:set α) (x:α):x ∈ S \ T → x∉ T :=
begin
  rw set_diff_def,
  intros,
  simp at a,
  cases a,
  apply a_right,
end

lemma set_mem_diff_intro (α:Type*) (S T:set α) (x:α):x ∈ S → x∉ T →  x∈ S \ T:=
begin
  rw set_diff_def,
  intros,
  simp,
  split;assumption,
end

lemma set_diff_empty (α:Type*) (T:set α):T \ ∅ = T :=
begin
  ext,
  split,
  {
    intros,
    apply set_mem_diff_elim1,
    apply a,
  },
  {
    intros,
    apply set_mem_diff_intro,
    {
      apply a,
    },
    {
      intro,
      apply a_1,
    }
  }
end

lemma set_diff_compl (α:Type*) (S T:set α):(S \ (Tᶜ))=(S ∩ T) :=
begin
  ext,
  split;intros,
  {
    apply set.mem_inter,
    {
       apply set_mem_diff_elim1,
       apply a,
    },
    {
       apply not_compl_member_elim,
       apply set_mem_diff_elim2,
       {
         apply a,
       }
    }
  },
  {
    cases a,
    apply set_mem_diff_intro,
    {
      apply a_left,
    },
    {
      apply not_compl_member_intro,
      apply a_right,
    }
  }
end

lemma set_diff_compl2 (α:Type*) (S T:set α):(S ∩ (Tᶜ))=(S \ (T)) :=
begin
  have A1:(S \ ((Tᶜ)ᶜ))=(S ∩ (T)ᶜ),
  {
    apply set_diff_compl,
  },
  rw ← (double_neg_set α T) at A1,
  symmetry,
  exact A1
end

lemma set_diff_inter_comm (α:Type*) (S T U:set α):(S ∩ T) \ U = (S \ U) ∩ T :=
begin
  ext,
  split;intros,
  {
    cases a,
    cases a_left,
    split,
    {
      apply set_mem_diff_intro;assumption,
    },
    exact a_left_right,
  },
  {
    cases a,
    cases a_left,
    apply set_mem_diff_intro,
    split;assumption,
    exact a_left_right,
  }
end

lemma set_diff_inter_union (α:Type*) (S T:set α):(S ∩ T) ∪ (S \ T) = S :=
begin
  ext,
  split;intros,
  {
    cases a,
    {
      exact a.left,
    },
    {
      exact a.left,
    }
  },
  {
    have A1:(x∈ T∨ x ∉ T),
    {
      apply in_or_notin,
    },
    cases A1,
    {
      apply union_member_intro1,
      apply inter_member_intro;assumption,
    },
    {
      apply union_member_intro2,
      apply set_mem_diff_intro;assumption,
    }
  }
end

lemma union_not_mem_intro (α:Type*) (A B:set α) (x:α):
  (x∉ A) → (x∉ B) → (x∉  A ∪ B) :=
begin
  intros,
  rw ← union_defn,
  simp,
  intro,
  cases a_2,
  {
    apply a,
    exact a_2,
  },
  {
    apply a_1,
    exact a_2,
  }
end

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


lemma diff_union_eq_diff_diff (α:Type*) (S T U:set α):S \ (T ∪ U) = S\ T \ U :=
begin
  intros,
  ext,
  split;intros,
  {
    have A1:x∉ (T∪  U),
    {
      apply set_mem_diff_elim2,
      apply a,
    },

    apply set_mem_diff_intro,
    {
      apply set_mem_diff_intro,
      {
        apply set_mem_diff_elim1,
        apply a,
      },
      {
        intro,
        apply A1,
        left,
        apply a_1,
      }
    },
    {
      intro,
      apply A1,
      right,
      apply a_1,
    }
  },
  {
    cases a,
    cases a_left,
    apply set_mem_diff_intro,
    {
      assumption,
    },
    {
      intro,
      cases a,
      {
        apply a_left_right,
        apply a,
      },
      {
        apply a_right,
        apply a,
      }
    }
  }
end

def inter_Set {β:Type*} (X:set (set β)) (S:set β):set (set β) :=
  {T:set β|∃ V∈ X, T=S∩ V}

lemma inter_sUnion (β:Type*) (X:set (set β)) (S:set β):
  (S∩ (set.sUnion X))= (set.sUnion (inter_Set X S)) :=
begin
  ext,
  unfold inter_Set,
  simp,
  split;intros,
  {
    cases a,
    cases a_right,
    apply exists.intro (S∩ a_right_w),
    cases a_right_h,
    split,
    {
      apply exists.intro a_right_w,
      split,
      {
        apply a_right_h_left,
      },
      {
        refl,
      }
    },
    {
      split;assumption,
    }
  },
  {
    cases a,
    cases a_h,
    cases a_h_left,
    cases a_h_left_h,
    subst a_w,
    cases a_h_right,
    split,
    {
      exact a_h_right_left,
    },
    {
      apply exists.intro a_h_left_w,
      split,
      {
        apply a_h_left_h_left,
      },
      {
        apply a_h_right_right,
      }
    }
  }
end

def set_none_to_emptyset (β:Type*):(option (set β)) → set β
  | (option.some S) := S
  | (option.none) := ∅



def encodable_set_fn (α β:Type*) [Y:encodable β] (f : β → (set α)) (i: ℕ):set α :=
  set_none_to_emptyset α ((option.map f)  (encodable.decode2 β i))

lemma option_map_none (α β:Type*) (f:α → β):
  option.map f none = none :=
begin
  intros,
  unfold option.map,
  unfold option.bind,
end

lemma encodable_set_fn_none_empty (α β:Type*) [Y:encodable β] (f : β → (set α)) (i: ℕ):
  (encodable.decode2 β i = option.none)→
  encodable_set_fn α β f i = ∅ :=
begin
  intros,
  unfold encodable_set_fn,
  rw a,
  rw option_map_none,
  unfold set_none_to_emptyset,
end

lemma encodable_set_fn_encode (α β:Type*) [Y:encodable β] (f : β → (set α)) (b: β):
  (encodable_set_fn α β f (encodable.encode b)) = f b :=
begin
  intros,
  unfold encodable_set_fn,
  have A1:encodable.decode2 β (encodable.encode b) = some b,
  {
    apply (@encodable.mem_decode2 β _ (encodable.encode b) b).mpr,
    refl,
  },
  rw A1,
  unfold option.map,
  unfold option.bind,
  unfold set_none_to_emptyset,
end





/-
  See encodable.decode2
  Okay, this is harder to prove than it should be.
  Let's get back to basics.
  Suppose that (x ≠ encodable.encode v).
  A -> 0
  B -> 1
  C -> 2
  0 -> some A
  1 -> some B
  2 -> some C
  3 -> some A ???
  4 -> none
  ...
  So, that violates these three theorems.
  lemma encodable_decode_conditional_injh (β:Type*) [X:encodable β] (x:ℕ) (v:β):
      (encodable.decode β x = some v)→
      (encodable.encode v = x) :=

  lemma encodable_decode_conditional_inj (β:Type*) [encodable β] (x y:ℕ) (v:β):
      (encodable.decode β x = encodable.decode β y)→
      (encodable.decode β x = some v)→
      x= y  :=

  lemma encodable_b (α β:Type*) [encodable β] (f : β → (set α)) (x:α) (n:ℕ):
      x ∈ set_none_to_emptyset α (option.map f (encodable.decode β n))→
      ∃ b:β, n = encodable.encode b :=
-/

--x ∈ encodable_set_fn α β f A1_w
lemma encodable_b (α β:Type*) [encodable β] (f : β → (set α)) (x:α) (n:ℕ):
    x ∈ encodable_set_fn α β f n→
    ∃ b:β, (encodable_set_fn α β f (encodable.encode b))
    = encodable_set_fn α β f n :=
begin
  let z:=encodable.decode2 β n,
begin
  have A1:z=encodable.decode2 β n,
  {
    refl,
  },
  intros,
  --rw ← A1,
  cases (encodable.decode2 β n),
  {
    exfalso,
    have A2:encodable_set_fn α β f n = ∅,
    {
      apply encodable_set_fn_none_empty,
      rw ← A1,
    },
    rw A2 at a,
    apply a,
  },
  {
    intros,
    apply exists.intro val,
    unfold encodable_set_fn,
    have A3:encodable.decode2 β (encodable.encode val) = encodable.decode2 β n,
    {
      rw encodable.encodek2,
      rw ←  A1,
    },
    rw A3,
  }
end

end


lemma not_encodable_none {α β:Type*} [encodable β] (f:β → (set α)):
∀ i ∉ (set.range (@encodable.encode β _)), encodable_set_fn α β f i = ∅ :=
begin
  intros,
  let z:=(@encodable.decode β _ i),
  begin
  have A1:(encodable.decode2 β i = option.none),
  {
    unfold encodable.decode2,
    -- ⊢ option.bind (encodable.decode β i) (option.guard (λ (a : β), encodable.encode a = i)) = none
    cases (@encodable.decode β _ i),
    { -- ⊢ option.bind none (option.guard (λ (a : β), encodable.encode a = i)) = none
      unfold option.bind,
    },
    { -- ⊢ option.bind (some val) (option.guard (λ (a : β), encodable.encode a = i)) = none
      unfold option.bind,
      unfold option.guard,
      apply if_neg,
      { -- ⊢ ¬ (encodable.encode val = i)
        intro,
        apply H,
        split,
        apply a,
      }
    },
  },
  unfold encodable_set_fn,
  rw A1,
  rw option_map_none,
  unfold set_none_to_emptyset,
  end
end




lemma encodable_set_fn_equivalent
(α β:Type*) [encodable β] (f : β → (set α)):
    (⋃ (i:ℕ), ((encodable_set_fn α β f) i)) = (⋃b, (f b)) :=
begin
  intros,
  ext,
  split;intros,
  {
    have A1:(∃ (a:ℕ), x ∈ encodable_set_fn α β f a),
    {
      apply funion_member_elim,
      apply a,
    },
    cases A1,
    have A2:∃ b:β, (encodable_set_fn α β f (encodable.encode b))
    = encodable_set_fn α β f A1_w,
    {
      apply encodable_b,
      apply A1_h,
    },
    cases A2,
    rw ← A2_h at A1_h,
    unfold encodable_set_fn at A1_h,
    unfold option.map at A1_h,
    rw encodable.encodek2 at A1_h,
    unfold option.bind at A1_h,
    unfold set_none_to_emptyset at A1_h,
    apply funion_member_intro,
    {
      apply A1_h,
    }
  },
  {
    cases a,
    cases a_h,
    cases a_h_w,
    have A2:encodable.decode2 β (encodable.encode a_h_w_w) = some a_h_w_w,
    {
      apply encodable.encodek2,
    },
    have A3:encodable_set_fn α β f (encodable.encode a_h_w_w) = a_w,
    {
      unfold encodable_set_fn,
      rw A2,
      unfold option.map,
      unfold option.bind,
      unfold set_none_to_emptyset,
      apply a_h_w_h,
    },
    rw ← A3 at a_h_h,
    apply funion_member_intro,
    {
      apply a_h_h,
    }
  }
end

lemma union_equivalent_Union
(α:Type*) (A B:set α):
    (⋃ (i:ℕ), ((encodable_set_fn α bool (λ b, cond b A B)) i)) = A ∪ B :=
begin
  rw encodable_set_fn_equivalent,
  rw set.union_eq_Union,
end




lemma nat_bound_insert (n:ℕ):{i:ℕ|i < nat.succ n} = insert n {i:ℕ|i < n} :=
begin
  ext,
  split;intros,
  {
    simp,
    simp at a,
    cases a,
    {
      left,
      refl,
    },
    {
      right,
      apply a_a,
    }
  },
  {
    simp,
    simp at a,
    cases a,
    {
      subst x,
      apply lt_succ,
    },
    {
      apply lt_succ_of_lt,
      apply a
    }
  }
end

lemma finite_nat_bound (n:ℕ):set.finite {i:ℕ|i < n} :=
begin
  induction n,
  {
    have A1:{i:ℕ|i < 0} = ∅,
    {
      apply emptyset_intro,
      intros,
      simp at H,
      apply nat.not_lt_zero,
      apply H,
    },
    rw A1,
    apply set.finite_empty,
  },
  {
    rw nat_bound_insert,
    apply set.finite.insert,
    exact n_ih,
  }
end

--TODO:remove
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

lemma sUnion_subset_funion (α β:Type*) (f:α → set β) (Y:set α):
  set.sUnion (f '' Y) ⊆ (⋃ i, f i) :=
begin
  rw Union_eq_sUnion_univ,
  have A1:(λ (i : α), f i) = f,
  {
    refl,
  },
  rw A1,
  apply sUnion_subset_comm,
  apply set.image_subset,
  simp,
end


lemma preimage_fst_def {α β:Type*} {Bα:set (set α)}:
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


lemma preimage_snd_def {α β:Type*} {Bβ:set (set β)}:
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



lemma preimage_sUnion {α β:Type*} (f:α → β) (T:set (set β)):
 (f ⁻¹' ⋃₀ T)=⋃₀ (set.image (set.preimage f)  T) :=
begin
  ext,split;intros A1,
  {
    cases A1 with S A2,
    cases A2 with A3 A4,
    split,
    {
      simp,
      split,
      {
        apply exists.intro S,
        split,
        {
          exact A3,
        },
        refl,

      },
      {
        apply A4,
      }
    },
  },
  {
    cases A1 with S A2,
    cases A2 with A3 A4,
    cases A3 with R A5,
    cases A5 with A5 A6,
    subst S,
    split,
    {
      simp,
      split,
      {
        apply A5,
      },
      {
        apply A4,
      },
    }
  }
end

lemma preimage_univ {α β:Type*} (f:α → β):set.preimage f set.univ = set.univ :=
begin
  ext,
  split;intros A1,
  {
    simp,
  },
  {
    simp,
  }
end

lemma preimage_inter {α β:Type*} (f:α → β) (B1 B2:set β):
  set.preimage f (B1 ∩ B2) = (set.preimage f B1) ∩ (set.preimage f B2) :=
begin
  refl,
end

lemma preimage_union {α β:Type*} (f:α → β) (B1 B2:set β):
  set.preimage f (B1 ∪ B2) = (set.preimage f B1) ∪  (set.preimage f B2) :=
begin
  refl,
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


lemma set_disjoint_def {α:Type*} (A B:set α):(A ∩ B ⊆ ∅)→ disjoint A B :=
begin
  intro A1,
  unfold disjoint,
  apply A1,
end

lemma set_disjoint_intro {α:Type*} (A B:set α):
    (∀x:α,(x∈ A)→(x∈ B)→ false) →  disjoint A B :=
begin
  intro A1,
  apply set_disjoint_def,
  rw set.subset_def,
  intros x A2,
  exfalso,
  apply A1 x A2.left A2.right,
end

lemma set_disjoint_elim {α:Type*} {A B:set α}:disjoint A B  → (A ∩ B = ∅):=
begin
  intro A1,
  unfold disjoint at A1,
  have A2:A∩ B⊆ ∅,
  {
    apply A1,
  },
  apply le_antisymm,
  apply A2,
  apply set.empty_subset,
end

lemma set_disjoint_comm {α:Type*} {A B:set α}:disjoint A B → disjoint B A :=
begin
  intro A1,
  apply set_disjoint_intro,
  intros x A2 A3,
  have A4:(A ∩ B = ∅),
  {
    apply set_disjoint_elim A1,
  },
  have A5:x∈ A∩ B,
  {
    apply and.intro A3 A2,
  },
  rw A4 at A5,
  apply A5,
end

lemma set_not_disjoint_def {α:Type*} (A B:set α) (x:α):(x∈ A ∩ B)→ ¬ (disjoint A B) :=
begin
  intros A1 A2,
  have A3:(A∩ B=∅),
  {
    apply set_disjoint_elim,
    apply A2,
  },
  rw A3 at A1,
  apply A1,
end

lemma set.inter_compl_eq_empty {α:Type*} {A:set α}:(A ∩ Aᶜ)=∅ :=
begin
  ext a,
  split;intros A1,
  {
    exfalso,
    simp at A1,
    cases A1 with A1 A2,
  },
  {
    exfalso,
    apply A1,
  },
end


lemma disjoint_inter_compl' {α:Type*} (A B C:set α):disjoint (A ∩ B) (C∩ Bᶜ) :=
begin
  apply set_disjoint_def,
  have A1:A ∩ B ∩ (C ∩ Bᶜ) ⊆ B ∩ (C ∩ Bᶜ),
  {
    apply set.inter_subset_inter_left,
    apply set.inter_subset_right,
  },
  apply set.subset.trans,
  apply A1,
  have A2:B ∩ (C ∩ Bᶜ)⊆ B ∩ (Bᶜ),
  {
    apply set.inter_subset_inter_right,
    apply set.inter_subset_right C (Bᶜ),
  },
  apply set.subset.trans,
  apply A2,
  rw set.inter_compl_eq_empty,
end

lemma disjoint_inter_compl {α:Type*} (A B:set α):disjoint (A ∩ B) (A∩ Bᶜ) :=
begin
  apply disjoint_inter_compl',
end


lemma set_prod_inter {α:Type*} (A₁ A₂:set α) {β:Type*} (B₁ B₂:set β):
  (set.prod A₁ B₁)  ∩  (set.prod A₂  B₂) =
  (set.prod (A₁ ∩ A₂)  (B₁ ∩ B₂)) :=
begin
  apply set.prod_inter_prod,
end

lemma set_prod_subset {α:Type*} (A₁ A₂:set α) {β:Type*} (B₁ B₂:set β) (a:α) (b:β):
  (a ∈ A₁) →
  (b∈ B₁) →
  ((set.prod A₁ B₁)  ⊆ (set.prod A₂  B₂) ↔ (A₁ ⊆ A₂) ∧ (B₁ ⊆ B₂)) :=
begin
  intros A1 A2,
  rw set.subset_def,
  rw set.subset_def,
  rw set.subset_def,
  split;intro A3,
  {
    split;intro x,
    {
      intro A3A,
      have A3B:(prod.mk x b)∈ (set.prod A₂ B₂),
      {
        apply A3,
        split,
        simp,
        apply A3A,
        apply A2,
      },
      cases A3B with A3C A3D,
      simp at A3C,
      exact A3C,
    },
    {
      intro A3A,
      have A3B:(prod.mk a x)∈ (set.prod A₂ B₂),
      {
        apply A3,
        split,
        simp,
        apply A1,
        apply A3A,
      },
      cases A3B with A3C A3D,
      simp at A3D,
      exact A3D,
    },
  },
  {
    intros x B1,
    cases B1 with B4 B5,
    cases A3 with B2 B3,
    split,
    {
      apply B2,
      apply B4,
    },
    {
      apply B3,
      apply B5,
    }
  }
end

lemma set_prod_sUnion_right {α:Type*} (A:set α) {β:Type*} (B:set (set β)):
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

lemma set_prod_sUnion_left {α:Type*} (A:set (set α)) {β:Type*} (B:set β):
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


lemma upper_bounds_def {α:Type*} [preorder α] (s : set α) : upper_bounds s = { x | ∀ ⦃a⦄, a ∈ s →  a ≤ x } := rfl

lemma upper_bounds_def2 {α:Type*} [preorder α] (s : set α) {x y:α} : 
  x ∈ upper_bounds s →  (y∈ s) →  y≤ x :=
begin
  intros A1 A2,
  rw upper_bounds_def at A1,
  simp at A1,
  apply A1 A2,
end


lemma set.contains_of_nonempty {α:Type*} {T:set α}:T.nonempty → (∃ a, a∈ T) :=
begin
  apply set.nonempty_def.mp,
end


lemma set.nonempty_of_contains {α:Type*} {T:set α} {a:α}:(a∈ T)  → T.nonempty :=
begin
  intros A1,
  rw set.nonempty_def,
  apply exists.intro a A1,
end


lemma set.image_const {α β:Type*} {f:α → β} {T:set α} {b:β}:T.nonempty → 
  (∀ a:α, f a = b) → (f '' T = {b}) :=
begin
  intros A1 A2,
  ext,split;intros A3;simp at A3;simp,
  {
    cases A3 with a A3,
    cases A3 with A3 A4,
    subst x,
    apply A2,
  },
  {
    subst x,
    have B1:=set.contains_of_nonempty A1,
    cases B1 with a B1,
    apply exists.intro a,
    apply and.intro B1 (A2 a),
  },
end


lemma set.nonempty_image_of_nonempty {α β:Type*} {f:α → β} {T:set α}:T.nonempty → 
  (f '' T).nonempty  :=
begin
  intro A1,
  have B1:=set.contains_of_nonempty A1,
  cases B1 with a B1,
  have B2:(f a ∈ f '' T),
  {
    simp,
    apply exists.intro a,
    split,
    apply B1,
    refl,
  },
  apply set.nonempty_of_contains B2,
end


lemma set_disjoint_def' {α:Type*} (A B:set α):(A ∩ B ⊆ ∅) = disjoint A B := rfl

lemma disjoint_subset_left {α:Type*} {A B C:set α}:
  disjoint A C →
  B ⊆ A →
  disjoint B C :=
begin
  intros A1 A2,
  rw ← set_disjoint_def',
  rw ← set_disjoint_def' at A1,
  apply set.subset.trans _ A1,
  simp,
  apply set.subset.trans _ A2,
  apply set.inter_subset_left,  
end

lemma disjoint_subset_right {α:Type*} {A B C:set α}:
  disjoint A C →
  B ⊆ C →
  disjoint A B :=
begin
  intros A1 A2,
  apply set_disjoint_comm,
  have A3 := set_disjoint_comm A1,
  apply disjoint_subset_left A3 A2,
end


lemma disjoint_inter_left {α:Type*} {A B C:set α}:
  disjoint A C →
  disjoint (A ∩ B) (C) :=
begin
  intros A1,
  apply disjoint_subset_left A1,
  apply set.inter_subset_left,
end

lemma disjoint_inter_right {α:Type*} {A B C:set α}:
  disjoint A C →
  disjoint A (B ∩ C) :=
begin
  intros A1,
  apply disjoint_subset_right A1,
  apply set.inter_subset_right,
end

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

lemma empty_or_nonempty {α:Type*} {S:set α}:
  S.nonempty ∨ S = ∅ :=
begin
  have A1:(∃ x:α, x∈ S) ∨ (¬ ∃ x:α,x ∈ S) := classical.em (∃ x:α, x∈ S),
  cases A1,
  {
    left,
    apply A1,
  },
  {
    right,
    ext,
    split;intro A2,
    {
      exfalso,
      apply A1,
      apply exists.intro x A2,
    },
    {
      exfalso,
      apply A2,
    }
  },
end
