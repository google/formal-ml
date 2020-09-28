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
import formal_ml.classical

open finset

/-
  There are more theorems about finsets in mathlib in data.finset.basic
-/
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

--TODO:replace with finset.range_zero
lemma finset_zero:range 0 = ∅  :=
begin
  apply finset.range_zero,
end

--TODO:replace with finset.mem_range
lemma mem_finset_intro (n m:ℕ) :(n < m) → n ∈ range (m)  :=
begin
  apply (@finset.mem_range m n).mpr,
end

--TODO:replace with finset.mem_range
lemma mem_finset_elim (n m:ℕ) :n ∈ range (m) → (n < m) :=
begin
  apply (@finset.mem_range m n).mp,
end


--TODO:replace with finset.range_succ
lemma finset_succ (n:ℕ):range (nat.succ n) = insert n (range n)  :=
begin
  apply finset.range_succ,
end

--Trivial, but novel?
lemma finset_bot_eq_empty (T:Type) (D:decidable_eq T):
  @semilattice_inf_bot.bot (finset T) _ = ∅ :=
begin
  refl
end

--Novel?
lemma not_new_insert (P:Type) (D:decidable_eq P) (S:finset P) (p p':P):
  (p'∈ insert p S) → (p ≠ p') → (p' ∈ S) :=
begin
  intros A1 A2,
  rw finset.mem_insert at A1,
  cases A1 with A1 A1,
  {exfalso, apply A2, rw A1},
  {apply A1},
end

--TODO:replace with finset.mem_insert
lemma insert_or (P:Type) (D:decidable_eq P) (S:finset P) (p p':P):
  (p'∈ insert p S) → (p' = p) ∨ (p' ∈ S) :=
begin
  apply finset.mem_insert.mp,
end

--TODO:replace with finset.mem_insert_of_mem
lemma insert_intro (P:Type*) (D:decidable_eq P) (S:finset P) (p p':P):
  (p' ∈ S) → (p'∈ insert p S) :=
begin
  apply finset.mem_insert_of_mem,
end

--TODO:replace with finset.mem_insert_self
lemma insert_intro2 (P:Type*) (D:decidable_eq P) (S:finset P) (p:P):
  (p∈ insert p S) :=
begin
  intros,
  rw finset.insert_def,
  simp,
end

--TODO:replace with finset.disjoint_iff_inter_eq_empty or disjoint_iff.
lemma finset_disjoint_def (T:Type*) (D:decidable_eq T)  (A B:finset T):
  disjoint A B ↔ A ∩ B ⊆ ∅ :=
begin
  refl,
end

--TODO:replace with finset.disjoint_iff_inter_eq_empty.
lemma finset_disjoint_def_fwd (T:Type*) (D:decidable_eq T)  (A B:finset T):
  disjoint A B → A ∩ B ⊆ ∅ :=
begin
  rw finset.disjoint_iff_inter_eq_empty,
  intros A1,
  rw A1,
  simp,
end

lemma finset_disjoint_def_bck (T:Type*) (D:decidable_eq T)  (A B:finset T):
  A ∩ B ⊆ ∅ → disjoint A B :=
begin
  rw finset.disjoint_iff_inter_eq_empty,
  intro A1,
  apply finset.subset.antisymm,
  apply A1,
  simp,
end

--TODO: replace with finset.max (but defn slightly different).
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


--This seems useful. It is probably in mathlib somewhere.
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

--TODO: replace with finset.range_subset.mpr
lemma finset_range_monotonic (m n:ℕ):(m ≤ n) → (finset.range m ⊆ finset.range n) :=
begin
  apply finset.range_subset.mpr,
end




--TODO: replace with finset.disjoint_left
lemma finset_disjoint_intro {α:Type*} [decidable_eq α] (S T:finset α):(∀ a∈ S, a∉ T)→ (disjoint S T) :=
begin
  intros A1,
  rw finset.disjoint_left,
  apply A1,
end



--If this doesn't exist, it should definitely be added.
lemma finset_disjoint_symm {α:Type*} [decidable_eq α] (S T:finset α):(disjoint S T)→ (disjoint T S) :=
begin
  intros,
  apply (finset_disjoint_def α _ T S).mpr,
  rw finset.inter_comm,
  apply (finset_disjoint_def α _ S T).mp,
  assumption
end


--TODO: replace with finset.disjoint_left or finset.disjoint_right
lemma finset_disjoint_elim {α:Type*} [X:decidable_eq α] {S T:finset α} (a:α):(disjoint S T)→
    (a∈ S)→ (a∉ T) :=
begin
  rw finset.disjoint_left,
  intros A1 A2,
  apply A1 A2,
end


--TODO: replace with finset.disjoint_insert_right
lemma insert_disjoint_imp_disjoint {α:Type*} [decidable_eq α] (S T:finset α) (a:α):
  disjoint T (insert a S) → disjoint T S :=
begin
  intros A1,
  rw finset.disjoint_insert_right at A1,
  apply A1.right,
end



lemma sum_insert_add {α β:Type*} [decidable_eq α] [add_comm_monoid β] (f:α → β) (S:finset α) (a:α):
  (a∉ S)→
  (((insert a S).sum  f)=(f a) + (S.sum f)) :=
begin
  intros,
  apply fold_insert,
  apply a_1,
end

--TODO: replace with finset.sdiff_subset
lemma sdiff_subset {α:Type*} [decidable_eq α] (S T:finset α):(S \ T) ⊆ S :=
begin
  apply finset.sdiff_subset,
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


def finset.Union {α:Type*} [decidable_eq α] (S:finset (finset α)):finset α :=
  finset.fold (@has_union.union (finset α) _) (∅:finset α) id S


def finset.Union_insert {α:Type*} [decidable_eq α] (S:finset (finset α)) (t:finset α):
  finset.Union (insert t S) = t ∪ finset.Union S :=
begin
  unfold finset.Union,
  simp,
end

lemma finset.mem_Union {α:Type*} [decidable_eq α] (S:finset (finset α)) {a:α}:
  a ∈ S.Union  ↔ (∃ (T:finset α), a∈ T ∧ T ∈ S) :=
begin
  split,
  {
    apply finset.induction_on S,
    {
      unfold finset.Union,simp,
    },
    {
      intros T S',
      intros C1 C2 C3,
      rw finset.Union_insert at C3,
      simp at C3,
      cases C3 with C3 C3,
      {
        apply exists.intro T,
        simp [C3],
      },
      {
        have C4 := C2 C3,
        cases C4 with T C4,
        apply exists.intro T,
        simp [C4],
      },
    },
  },
  {
    apply finset.induction_on S,
    {
      --intros A1,
      simp,
    },
    {
      intros T S' D1 D2 D3,
      rw finset.Union_insert,
      cases D3 with T' D3,
      cases D3 with D3 D4,
      simp at D4,
      cases D4 with D4 D4,
      {
        subst T',
        simp [D3],
      },
      {
        simp,
        right,
        apply D2,
        apply exists.intro T',
        apply and.intro D3 D4,
      },
    },
  },
end



--Cool, but unused.
/-
  Constructs a finset {u:finset α|∃ s∈ S, t∈ T, u = s ∪ t}
 -/
def finset.pairwise_union {α:Type*} [decidable_eq α] (S T:finset (finset α)):finset (finset α)
  := finset.Union (finset.image (λ s:finset α, finset.image (λ t:finset α, s ∪ t) T) S) 

lemma finset.mem_pairwise_union {α:Type*} [decidable_eq α] (S T:finset (finset α)) (z:finset α):
  z ∈ finset.pairwise_union S T ↔ ∃ (s t:finset α), s∈ S ∧ t ∈ T ∧ z = s ∪ t :=
begin
  unfold finset.pairwise_union,
  rw finset.mem_Union,
  split;intros B1,
  {
    cases B1 with T' B1,
    cases B1 with B1 B2,
    simp at B2,
    cases B2 with s B2,
    cases B2 with B2 B3,
    subst T',
    simp at B1,
    cases B1 with t B1,
    
    apply exists.intro s,
    apply exists.intro t,
    simp [B1,B2],
  },
  {
    cases B1 with s B1,
    cases B1 with t B1,
    apply exists.intro (finset.image (λ (t : finset α), s ∪ t) T),
    simp,    
    split,
    {
      apply exists.intro t,
      simp [B1],
    },
    {
      apply exists.intro s,
      simp [B1],
    },
  },
end

lemma finset.mem_union_pairwise_union_of_mem {α:Type*} [decidable_eq α] (S T:finset (finset α)) 
  (s t:finset α):(s∈ S) → (t ∈ T) → (s ∪ t) ∈ finset.pairwise_union S T :=
begin
  intros A1 A2,
  rw finset.mem_pairwise_union,
  apply exists.intro s,
  apply exists.intro t,
  simp [A1,A2],
end

lemma finset.pairwise_union.comm {α:Type*} [decidable_eq α] (A B:finset (finset α)):
  finset.pairwise_union A B = finset.pairwise_union B A :=
begin
  ext a,
  rw finset.mem_pairwise_union,
  rw finset.mem_pairwise_union,
  split;
  {
    intros B1,cases B1 with s B1,cases B1 with t B1,
    apply exists.intro t,apply exists.intro s,simp [B1,finset.union_comm],
  },
end

lemma finset.pairwise_union.assoc {α:Type*} [decidable_eq α] (A B C:finset (finset α)):
 finset.pairwise_union (finset.pairwise_union A B) C =
  finset.pairwise_union A (finset.pairwise_union B C) :=
begin
  ext x,
  --rw finset.mem_pairwise_union,
  --rw finset.mem_pairwise_union,
  split,
  {
    intro B1,
    rw finset.mem_pairwise_union at B1,
    cases B1 with ab B1,
    cases B1 with c B1,
    cases B1 with B1 B2,
    cases B2 with B2 B3,
    subst x,
    rw finset.mem_pairwise_union at B1,
    cases B1 with a B1,
    cases B1 with b B1,
    cases B1 with B1 B3,
    cases B3 with B3 B4,
    subst ab,
    rw finset.union_assoc,
    repeat {apply finset.mem_union_pairwise_union_of_mem},
    repeat {assumption},
  },
  {
    intros B1,
    rw finset.mem_pairwise_union at B1,
    cases B1 with a B1,
    cases B1 with bc B1,
    cases B1 with B1 B2,
    cases B2 with B2 B3,
    subst x,
    rw finset.mem_pairwise_union at B2,
    cases B2 with b B2,
    cases B2 with c B2,
    cases B2 with B2 B3,
    cases B3 with B3 B4,
    subst bc,
    rw ← finset.union_assoc,
    repeat {apply finset.mem_union_pairwise_union_of_mem},
    repeat {assumption},
  },
end





instance finset.pairwise_union.is_commutative {α:Type*} [D:decidable_eq α]:
  is_commutative (finset (finset α)) (@finset.pairwise_union α D) := {
  comm := finset.pairwise_union.comm
}

instance finset.pairwise_union.is_associative {α:Type*} [D:decidable_eq α]:
  is_associative (finset (finset α)) (@finset.pairwise_union α D) := {
  assoc := finset.pairwise_union.assoc
}

lemma finset.union_diff {α:Type*} [decidable_eq α] {S T:finset α}:S⊆T → 
  S ∪ T \ S = T :=
begin
  intros A1,
  ext a,
  split;intros B1,
  {
    simp at B1,
    cases B1,
    apply A1,
    apply B1,
    apply B1,
  },
  {
    simp,
    apply or.inr B1,
  },
end

lemma finset.diff_subset_insert {α:Type*} [decidable_eq α] {T S:finset α} {a:α}:T ⊆ insert a S  → 
   (T \ {a}) ⊆ S := 
begin
  intros A1,
  rw finset.subset_iff,
  rw finset.subset_iff at A1,
  intros x B1,
  simp at B1,
  have B2 := A1 B1.left,
  simp at B2,
  simp [B1] at B2,
  apply B2,
end


lemma finset.subset_insert_of_not_mem {α:Type*} [decidable_eq α] {T S:finset α} {a:α}:a∉ T →
   T ⊆ insert a S  → T ⊆ S := 
begin
  intros A1 A2,
  rw finset.subset_iff,
  intros x B1,
  --simp at A2,
  have B2 := A2 B1,
  simp at B2,
  cases B2,
  {
    subst x,
    exfalso,
    apply A1 B1,
  },
  {
    apply B2,
  },
end

--Probably already exists.
lemma finset.singleton_union_eq_insert {α:Type*} [D:decidable_eq α] {a:α} {S:finset α}:{a} ∪ S =
  insert a S :=
begin
  refl
end


lemma finset.Union_insert' {α β:Type*} [E:encodable β]
    [D:decidable_eq β] {f:β → set α} {b:β} {S:finset β}:
   (⋃ (b':β) (H:b'∈ (insert b S)), f b') = 
   (f b) ∪ (⋃ (b':β) (H:b'∈ S), f b') := 
begin
  simp
end
