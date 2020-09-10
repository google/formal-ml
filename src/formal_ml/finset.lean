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
import order.filter.basic
import topology.bases
import order.bounded_lattice
import formal_ml.set
import data.real.basic
import data.finset
open finset

--Noncomputability is probably unavoidable, one way or another.
noncomputable def set_fintype_finset (T:Type) (F:fintype T) (S:set T):finset T :=
  @finset.filter T S (classical_set T S) F.elems

lemma set_fintype_finset_mem (T:Type) (F:fintype T) (S:set T) (a:T):
  a∈ S ↔  a∈ (set_fintype_finset T F S) :=
begin
  unfold set_fintype_finset,
  apply iff.symm,
  apply iff.trans,
  apply finset.mem_filter,
  split,
  {
     intros,
     cases a_1,
     assumption,
  },
  {
    intros,
    split,
    {
      apply F.complete,
    },
    {
      assumption,
    }
  }
end

lemma empty_set_to_empty_finset (T:Type) (F:fintype T):
  set_fintype_finset T F ∅ = ∅ :=
begin
  ext,
  apply iff.symm,
  apply (set_fintype_finset_mem T F ∅),
end

lemma finset_zero:range 0 = ∅  :=
begin
  apply finset.range_zero,
end

lemma mem_finset_intro (n m:ℕ) :(n < m) → n ∈ range (m)  :=
begin
  apply (@finset.mem_range m n).mpr,
end

lemma mem_finset_elim (n m:ℕ) :n ∈ range (m) → (n < m) :=
begin
  apply (@finset.mem_range m n).mp,
end


--This is exactly finset.range_succ
lemma finset_succ (n:ℕ):range (nat.succ n) = insert n (range n)  :=
begin
  apply finset.range_succ,
end

lemma finset_bot_eq_empty (T:Type) (D:decidable_eq T):
  @semilattice_inf_bot.bot (finset T) _ = ∅ :=
begin
  refl
end

lemma not_new_insert (P:Type) (D:decidable_eq P) (S:finset P) (p p':P):
  (p'∈ insert p S) → (p ≠ p') → (p' ∈ S) :=
begin
  intros,
  rw finset.insert_def at a,
  rw finset.mem_def,
  rw finset.mem_def at a,
  simp at a,
  cases a,
  {
    exfalso,
    apply a_1,
    symmetry,
    apply a,
  },
  {
    assumption
  }
end

lemma insert_or (P:Type) (D:decidable_eq P) (S:finset P) (p p':P):
  (p'∈ insert p S) → (p' = p) ∨ (p' ∈ S) :=
begin
  intros,
  rw finset.insert_def at a,
  rw finset.mem_def at a,
  simp at a,
  cases a,
  {
    left,
    assumption,
  },
  {
    right,
    rw finset.mem_def,
    assumption
  }
end

lemma insert_intro (P:Type*) (D:decidable_eq P) (S:finset P) (p p':P):
  (p' ∈ S) → (p'∈ insert p S) :=
begin
  intros,
  rw finset.insert_def,
  simp,
  right,
  apply a,
end

lemma insert_intro2 (P:Type*) (D:decidable_eq P) (S:finset P) (p:P):
  (p∈ insert p S) :=
begin
  intros,
  rw finset.insert_def,
  simp,
end

lemma finset_disjoint_def (T:Type*) (D:decidable_eq T)  (A B:finset T):
  disjoint A B ↔ A ∩ B ⊆ ∅ :=
begin
  refl,
end

lemma finset_disjoint_def_fwd (T:Type*) (D:decidable_eq T)  (A B:finset T):
  disjoint A B → A ∩ B ⊆ ∅ :=
begin
  have A1:(disjoint A B ↔ A ∩ B ⊆ ∅),
  apply finset_disjoint_def,
  cases A1,
  assumption
end

lemma finset_disjoint_def_bck (T:Type*) (D:decidable_eq T)  (A B:finset T):
  A ∩ B ⊆ ∅ → disjoint A B :=
begin
  have A1:(disjoint A B ↔ A ∩ B ⊆ ∅),
  apply finset_disjoint_def,
  cases A1,
  assumption
end


def finset_max (A:finset ℕ):ℕ :=
  (@finset.fold ℕ ℕ max _ _  0  id A)

lemma finset_max_def (A:finset ℕ):
  (finset_max A)  = (fold  max 0  id A) :=
begin
  refl,
end

lemma finset_max_limit (A:finset ℕ) (a:ℕ):
  (a∈ A)→ (a ≤ (finset_max A)) :=
begin
  apply finset.induction_on A,
  {
    simp,
  },
  {
    intros,
    have A1:a = a_1 ∨ a∈ s,
    {
      apply insert_or,
      apply a_4,
    },
    rw finset_max_def,
    rw finset.fold_insert_idem,
    rw ← finset_max_def,
    simp,
    cases A1,
    {
      subst a_1,
      left,
      refl,
    },
    {
      right,
      apply a_3,
      apply A1,
    }
  }
end


lemma finset_range_bound (A:finset ℕ):∃ n, (A⊆ finset.range n) :=
begin
  apply exists.intro (nat.succ (finset_max A)),
  rw finset.subset_iff,
  intros,
  apply mem_finset_intro,
  have A1:x ≤ finset_max A,
  {
    apply finset_max_limit,
    apply a,
  },
  apply lt_of_le_of_lt,
  {
    apply A1,
  },
  {
    apply nat.lt_succ_self,
  }
end

lemma finset_range_monotonic (m n:ℕ):(m ≤ n) → (finset.range m ⊆ finset.range n) :=
begin
  intros,
  rw finset.subset_iff,
  intros,
  apply mem_finset_intro,
  have A1:x < m,
  {
    apply mem_finset_elim,
    apply a_1,
  },
  apply lt_of_lt_of_le,
  {
    apply A1,
  },
  {
    apply a,
  }
end





lemma finset_disjoint_intro {α:Type*} [decidable_eq α] (S T:finset α):(∀ a∈ S, a∉ T)→ (disjoint S T) :=
begin
  intros,
  apply (finset_disjoint_def α _ S T).mpr,
  apply (@subset_iff α (S ∩ T) ∅).mpr,
  intros,
  exfalso,
  have A1:x∉  T,
  {
    apply a,
    apply finset.mem_of_mem_inter_left,
    apply a_1,
  },
  apply A1,
  apply finset.mem_of_mem_inter_right,
  apply a_1,
end

lemma finset_subseteq_emptyset {α:Type*} [decidable_eq α] (S:finset α) (a:α): (a∈ S)→ (S⊆ ∅) → false :=
begin
  intros,
  rw @subset_iff at a_2,
  have A1:a∈ (@has_emptyc.emptyc (finset α) _) ,
  {
    apply a_2,
    apply a_1,
  },
  have A2:a∉ (@has_emptyc.emptyc (finset α) _) ,
  {
    apply finset.not_mem_empty,
  },
  apply A2,
  apply A1,
end

lemma finset_comp_elim {α:Type*} (T:finset α) (a:α):((a∈ T)→ false)→ (a∉ T) :=
begin
  intros,
  intro,
  apply a_1,
  apply a_2,
end

lemma finset_disjoint_symm {α:Type*} [decidable_eq α] (S T:finset α):(disjoint S T)→ (disjoint T S) :=
begin
  intros,
  apply (finset_disjoint_def α _ T S).mpr,
  rw finset.inter_comm,
  apply (finset_disjoint_def α _ S T).mp,
  assumption
end

lemma finset_disjoint_elim {α:Type*} [X:decidable_eq α] {S T:finset α} (a:α):(disjoint S T)→
    (a∈ S)→ (a∉ T) :=
begin
  intros,
  have A1:S∩ T⊆ ∅,
  {
    apply (finset_disjoint_def α _ S T).mp,
    apply a_1,
  },
  have A2:(a∈T) → false,
  {
    intros,

    apply (@finset_subseteq_emptyset α X),
    {
      have A3:(a∈ S∩ T),
      {
        apply finset.mem_inter_of_mem;assumption,
      },
      apply A3,
    },
    apply A1,
  },
  intro,
  apply A2,
  apply a_3,
end



lemma insert_disjoint_imp_disjoint {α:Type*} [decidable_eq α] (S T:finset α) (a:α):
  disjoint T (insert a S) → disjoint T S :=
begin
  intros,
  apply finset_disjoint_intro,
  intros,
  have A2:a_2∉ (insert a S),
  {
    apply finset_disjoint_elim,
    apply a_1,
    apply H,
  },
  intro,
  apply A2,
  apply insert_intro,
  assumption,
end



lemma sum_insert_add {α β:Type*} [decidable_eq α] [add_comm_monoid β] (f:α → β) (S:finset α) (a:α):
  (a∉ S)→
  (((insert a S).sum  f)=(f a) + (S.sum f)) :=
begin
  intros,
  apply fold_insert,
  apply a_1,
end

lemma sdiff_subset {α:Type*} [decidable_eq α] (S T:finset α):(S \ T) ⊆ S :=
begin
  rw finset.subset_iff,
  intro x,
  intro A1,
  simp at A1,
  apply A1.left,
end

lemma sum_disjoint_add {α β:Type*} [decidable_eq α] [add_comm_monoid β] (f:α → β) (S T:finset α):
  disjoint S T →
  ((S.sum f) + (T.sum f)=(S∪ T).sum  f) :=
begin
  apply finset.induction_on T,
  {
    simp,
  },
  {
    intros,
    simp,
    have A1:disjoint S s,
    {
      apply insert_disjoint_imp_disjoint,
      apply a_3,
    },
    have A2:a∉ S,
    {
      have A3:disjoint (insert a s) S,
      {
        apply finset_disjoint_symm,
        apply a_3,
      },
      apply finset_disjoint_elim,
      apply A3,
      apply insert_intro2,
    },
    rw sum_insert_add,
    rw sum_insert_add,
    have A2:S.sum f + s.sum f =  (S ∪ s).sum f,
    {
      apply a_2,
      apply A1,
    },
    rw ← A2,
    rw ← add_assoc,
    rw add_comm _ (f a),
    simp,
    apply add_assoc,
    rw finset.mem_union,
    intro,
    cases a_4,
    {
      apply A2,
      apply a_4,
    },
    {
      apply a_1,
      apply a_4,
    },
    assumption,
  }
end



def finset_set {α:Type*} (S:finset α) (a:α):Prop := a∈ S


--def finset_type {α:Type*} (S:finset α):Type* := subtype (λ a:α, a ∈ S)

lemma finset_fintype_complete {α:Type*} (S:finset α):∀ a:{a:α|a∈ S}, a∈ (finset.attach S) :=
begin
  intros,
  unfold attach,
  simp,
end

def finset_fintype {α:Type*} (S:finset α):fintype {a:α|a∈ S} := {
  elems := finset.attach S,
  complete :=  finset_fintype_complete S,
}

lemma finite_finset {α:Type*} (S:finset α):set.finite {a:α| a∈ S} :=
begin
  unfold set.finite,
  apply nonempty.intro (finset_fintype S),
end
