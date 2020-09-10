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
import data.real.nnreal
import topology.instances.real
import topology.instances.nnreal
import topology.instances.ennreal

import topology.algebra.infinite_sum
import formal_ml.set
import formal_ml.finset
import formal_ml.nat
import formal_ml.ennreal
import formal_ml.nnreal
import data.finset
import order.complete_lattice
import formal_ml.real

open finset

lemma filter_le_intro (α:Type*) (A B:filter α):
  (∀ a, a∈ B → a∈ A)→ (A≤ B)  :=
begin
  intros,
  apply (@filter.le_def α A B).mpr,
  assumption,
end


lemma filter_le_intro2 (α:Type*) (A B:filter α):
  (B.sets ⊆ A.sets)→ (A≤ B)  :=
begin
  intros,
  apply (@filter.le_def α A B).mpr,
  have A1:((B.sets ⊆ A.sets) ↔ (∀ a∈ B.sets, a∈ A.sets)),
  {
     refl,
  },
  assumption,
end


lemma filter_le_elim {α:Type*} {A B:filter α} {a:set α}:
   (A≤ B) → (a∈ B)→ (a∈ A) :=
begin
  intros,
  apply (@filter.le_def α A B).mp;assumption,
end


/-
  filter.map f A is the pre-image of the pre-image of the sets in A.
  --set.preimage f has type (set β)→ (set α)
  --set.preimage f B = {x:f x ∈ B}
  --set.preimage (set.preimage f) has type (set (set α)) → (set (set β))
  --set.preimage (set.preimage f) AF = {y:(set.preimage f) y ∈ AF}
  --set.preimage (set.preimage f) AF = {y:{x:f x∈ y} ∈ AF}

-/
lemma filter_map_def (α β:Type*) (A:filter α) (f:α → β):
  (filter.map f A).sets = set.preimage (set.preimage f) A.sets :=
begin
  refl,
end

lemma filter_mem_def (α:Type*) (A:filter α) (a:set α):
  (a∈ A) = (a ∈ A.sets) :=
begin
  refl,
end


lemma filter_map_intro (α β:Type*) (A:filter α) (f:α → β) (X:set α) (Y:set β):
  (X∈ A) → (X=set.preimage f Y)→ (Y∈ filter.map f A)  :=
begin
  intros,
  rw filter_mem_def,
  rw filter_map_def,
  unfold set.preimage,
  simp,
  rw filter_mem_def at a,
  unfold set.preimage at a_1,
  rw ← a_1,
  assumption,
end

lemma filter_map_elim (α β:Type*) (A:filter α) (f:α → β) (Y:set β):
  (Y∈ filter.map f A)→ (∃ (X∈ A), (X=set.preimage f Y))   :=
begin
  intros,
  rw filter_mem_def at a,
  rw filter_map_def at a,
  --unfold set.preimage,
  simp,
  unfold set.preimage at a,
  simp at a,
  apply a,
end

lemma filter_tendsto_intro (α β:Type*)   (f:α → β) (A:filter α) (B:filter β):
  (∀ b∈ B, set.preimage f b ∈ A) → (@filter.tendsto α β  f A B)  :=
begin
  intros,
  unfold filter.tendsto,
  apply filter_le_intro,
  intros,
  apply filter_map_intro,
  have A1:a_1 ∈ B → f ⁻¹' a_1 ∈ A,
  {
    apply a,
  },

  have A2:f ⁻¹' a_1 ∈ A,
  {
     apply A1,
     apply a_2,
  },
  apply A2,
  refl,
end

lemma filter_tendsto_elim {α β:Type*} {f:α → β} {A:filter α} {B:filter β} {s:set β}:
   (@filter.tendsto α β  f A B) →(s∈ B)→  (set.preimage f s ∈ A) :=
begin
  intros,
  unfold filter.tendsto at a,
  have A1:s∈ filter.map f A,
  {
    apply filter_le_elim,
    apply a,
    apply a_1,
  },

  have A2:(∃ (X∈ A), (X=set.preimage f s)),
  {
    apply (filter_map_elim),
    apply A1,
  },
  cases A2,
  cases A2_h,
  subst A2_w,
  exact A2_h_w,
end


lemma filter_principal_intro {α:Type*} (a:finset α) (b:set (finset α)):
  ({c : finset α | a ⊆ c} ⊆ b) → b ∈ (filter.principal  {c:finset α | a⊆ c}):=
begin
  --apply b∈ (filter.principal  {c:finset ℕ | a⊆ c}),
  intros,
  unfold filter.principal,
  have A1:b ∈ {t : set (finset α) | {c : finset α | a ⊆ c} ⊆ t},
  {
    simp,
    apply a_1,
  },
  apply A1,
end


lemma filter_principal_elim {α:Type*} (a:finset α) (b:set (finset α)):
  b ∈ (filter.principal  {c:finset α | a⊆ c}) → ({c : finset α | a ⊆ c} ⊆ b) :=
begin
  intros,
  apply (@filter.mem_principal_sets (finset α) b {c:finset α | a⊆ c}).mp,
  apply a_1,
end



lemma filter_principal_intro2 {α:Type*} (a:finset α) (b:set (finset α)):
  (∀ c:finset α, a⊆ c → c∈ b) → b ∈ (filter.principal  {c:finset α | a⊆ c}):=
begin
  intros,
  apply filter_principal_intro,
  rw set.subset_def,
  intros,
  simp at a_2,
  apply a_1,
  apply a_2,
end


lemma filter_principal_intro3 {α:Type*} (a b:set α):
  (a⊆ b) → b ∈ filter.principal  a:=
begin
  unfold filter.principal,
  simp,
end


lemma filter_principal_elim2 {α:Type*} (a:finset α) (b:set (finset α)) (c:finset α):
  b ∈ (filter.principal  {c:finset α | a⊆ c}) → (a ⊆ c) → (c∈ b) :=
begin
  intros,
  apply (@filter_principal_elim α a b),
  {
    apply a_1,
  },
  apply a_2,
end

lemma filter_principal_elim3 {α:Type*} (a b:set α):
  b ∈ filter.principal  a → (a⊆ b):=
begin
  unfold filter.principal,
  simp,
end




/-
  Let's walk through a simple example.
  b={1,2}
  c={2,3}
  filter.principal {{1,2},{1,2,3},{1,2,3,4}, {1,2,4}} ⊓
  filter.principal {{1,3},{1,2,3},{1,2,3,4}, {1,3,4}} =
  filter.principal {{1,2,3}, {1,2,3,4}}



 -/


lemma principal_inf
    (α:Type*) (A B:set α):
    (filter.principal A ⊓ filter.principal B = filter.principal (A∩B)) :=
begin
  simp,
end


lemma principal_inf_sets2 {α:Type*} [semilattice_sup_bot α] (b c:α):
   filter.principal {d:α |b ≤ d} ⊓ filter.principal {d: α |c ≤ d}
   = filter.principal {d:α |(b ⊔ c) ≤ d} :=
begin
  have A1:{d:α |b ≤ d} ∩ {d:α |c ≤ d} = {d: α |(b ⊔ c) ≤ d},
  {
    ext,
    split;intros,
    {
      cases a,
      simp at a_left,
      simp at a_right,
      simp,
      split;assumption,
    },
    {
      simp at a,
      cases a with A2 A3,
      split;simp;assumption,
    }
  },
  rw ← A1,
  apply principal_inf,
end

-- Use apply principal_inf_sets2,
lemma principal_inf_sets {α:Type*} [decidable_eq α] (b c:finset α):
   filter.principal {d:finset α |b ≤ d} ⊓ filter.principal {d:finset α |c ≤ d}
   = filter.principal {d:finset α |(b ∪ c) ≤ d} :=
begin
  apply principal_inf_sets2,
end



-- src/data/set/lattice.lean
lemma set_Inf_def (α:Type*) (S:set (set α)):
(Inf S) = {a | ∀ t ∈ S, a ∈ t } :=
begin
  refl,
end


lemma set_Inf_intro (α:Type*) (S:set (set α)) (x:α):
   (∀ X∈ S, x∈ X) → x∈ Inf S :=
begin
  intros,
  rw set_Inf_def,
  simp,
  exact a,
end


lemma set_Inf_range_intro (α β:Type*) (f:α → set (β)) (x:β):
   (∀ y:α, x∈ f y) →  x∈ Inf (set.range  (λ (a : α), f a)) :=
begin
  intros,
  apply set_Inf_intro,
  intros,
  unfold set.range at H,
  simp at H,
  cases H,
  rw ← H_h,
  apply a,
end

lemma glb_intro {α β:Type*} (f:α → set (β)) (x:β):
(∀ a:α, x∈ f a) → x ∈  ⨅ a, f a :=
begin
  intros,
  unfold infi,
  unfold Inf,
  apply set_Inf_range_intro,
  assumption,
end


lemma le_Inf_simp : ∀ (α:Type*) (s : set (filter α)) (a : filter α),
    (∀ (b : filter α ), b ∈ s → a ≤ b) → a ≤ complete_lattice.Inf s :=
begin
  intros,
  apply (complete_lattice.le_Inf s),
  apply a_1,
end


lemma Inf_le_simp : ∀ (α : Type*)  (s : set (filter α)) (a : filter α),
  a ∈ s → complete_lattice.Inf s ≤ a :=
begin
  intros,
  apply (complete_lattice.Inf_le s),
  assumption,
end

lemma mem_Inf_intro {α : Type*}  {s : set (filter α)} {a : filter α} {t:set α}:
  t ∈ a → a ∈ s → t∈  complete_lattice.Inf s :=
begin
  intros,
  apply (complete_lattice.Inf_le s),
  assumption,
  assumption
end

-- This is equivalent to filter.mem_infi (or a mem_Inf variant of mem_infi)

def inf_filter_sets_def (α:Type*) (S : set (filter α)):set (set α) :=
  {s:set α | ∃ f∈ S, s∈ f}

lemma inf_filter_sets_of_superset2 (α:Type*) (S : set (filter α)) (s t:set α):
  s∈ (inf_filter_sets_def α S) → s⊆ t → t∈ (inf_filter_sets_def α S) :=
begin
  intro,
  unfold inf_filter_sets_def,
  simp,
  unfold inf_filter_sets_def at a,
  simp at a,
  cases a,
  cases a_h,
  intros,
  apply exists.intro a_w,
  split,
  {
    assumption,
  },
  {
    apply filter.sets_of_superset,
    apply a_h_right,
    assumption,
  }
end

--This suggests the definition is overly simplistic.
def inf_filter_sets_inter_sets2 (α:Type*) (S : set (filter α))
  (H:∀ a b:filter α, a∈ S→ b∈ S→ a⊓b∈ S)  (s t:set α):
  s∈ (inf_filter_sets_def α S) →
  t∈ (inf_filter_sets_def α S) →
  s ∩ t ∈ (inf_filter_sets_def α S) :=
begin
  unfold inf_filter_sets_def,
  simp,
  intros,
  apply (exists.intro (x⊓x_1)),
  split,
  {
    apply H;assumption,
  },
  {
     rw ← filter_mem_def,
     have B1:(s ∩ t) ∈ x ⊓ x_1 ↔ ∃t₁∈x, ∃t₂∈x_1, t₁ ∩ t₂ ⊆ (s ∩ t),
     apply filter.mem_inf_sets,
     apply B1.mpr,
     apply exists.intro s,
     apply exists.intro a_1,
     apply exists.intro t,
     apply exists.intro a_3,
     refl,
  }
end

lemma inf_filter_univ_sets2 (α:Type*) (S : set (filter α)) (b:filter α):
  (b∈ S) → set.univ ∈ (inf_filter_sets_def α S) :=
begin
  unfold inf_filter_sets_def,
  simp,
  intros,
  apply exists.intro b,
  split,
  assumption,
  apply filter.univ_sets,
end

def inf_filter_def2 (α:Type*) (S : set (filter α)) (b:filter α) (H:b∈ S)
  (H2:∀ a b:filter α, a∈ S→ b∈ S→ a⊓b∈ S):filter α := {
  sets := inf_filter_sets_def α S,
  sets_of_superset := inf_filter_sets_of_superset2 α S,
  univ_sets := (inf_filter_univ_sets2 α S b H),
  inter_sets := inf_filter_sets_inter_sets2 α S H2,
}

/-
  This definition is a little weak, as it assumes S is
  nonempty and closed under (binary) infimum.

  However, given these two constraints, the result is more
  elegant, and it corresponds to the generic result about
  filters, filter.eq_Inf_of_mem_sets_iff_exists_mem.
-/
lemma Inf_filter_def (α:Type*) (S : set (filter α))
(b:filter α) (H:b∈ S)
  (H2:∀ a b:filter α, a∈ S→ b∈ S→ a⊓b∈ S) (s:set α):
(s ∈ Inf S)↔ (∃ t∈ S, s∈ t) :=
begin
  have A1:(inf_filter_def2 α  S b H H2) = Inf S,
  {
     apply filter.eq_Inf_of_mem_sets_iff_exists_mem,
     intros,
     unfold inf_filter_def2,
     simp,
     unfold inf_filter_sets_def,
     simp,
  },
  rw ← A1,
  unfold inf_filter_def2,
  simp,
  unfold inf_filter_sets_def,
  simp,
end


lemma eq_Inf_of_mem_sets_iff_exists_mem {α:Type} {S : set (filter α)} {l : filter α}
  (h : ∀ {s}, s ∈ l ↔ ∃ f ∈ S, s ∈ f) : l = Inf S :=
le_antisymm (le_Inf $ λ f hf s hs, h.2 ⟨f, hf, hs⟩)
  (λ s hs, let ⟨f, hf, hs⟩ := h.1 hs in (Inf_le hf : Inf S ≤ f) hs)


--def filter_from_element (α:Type) (a:α):filter α  := filter.principal (λ a', a=a')

--filter.principal s contains all the supersets of s.
--if s is in F, then F also contains
lemma le_principal (F:filter (finset ℕ)) (s:set (finset ℕ)):
  (s∈ F)→ (F ≤ filter.principal s) :=
begin
  intros,
  apply (filter_le_intro2 (finset ℕ) F (filter.principal s)),
  rw set.subset_def,
  intros,

  unfold filter.principal at a_1,
  simp at a_1,
  apply filter.sets_of_superset,
  {
    apply a,
  },
  {
    assumption,
  }
end



/-

What is a neighborhood of x? First, for every open set containing x,
consider the principal filter (set of all supersets). Now, let's consider the
infimum of all those settings, keeping in mind that for a set, the
inf (filter.principal S) (filter.principal T)=(filter.principal S∪T) (at this point,
we should be able to write a proof for this). Since the
union of two open sets containing X itself is an open set containing X, and every
element has at least one neighborhood that contains it, we are OK.

Thus, a neighborhood of x is a superset of an open set containing x.

--a more standard definition of neighborhood.
lemma mem_nhds_def (x:nnreal) (b:set nnreal):
  (b∈ nhds x)↔ (∃ u:set nnreal, (u⊆ b) ∧ is_open u ∧ x∈ u) :=

-/
lemma mem_nhds_elim_real_rat (b:set real) (x:real): b∈ nhds x →
(∃ p q:ℚ, (p < q) ∧ ((set.Ioo p q:set ℝ) ⊆ b) ∧ ((p:ℝ) < x) ∧ (x < (q:ℝ)))
  :=
begin
  let rat_basis := (⋃ (a b : ℚ) (h : a < b), {set.Ioo ↑a ↑b}),
  begin
  intros,
  have A1:topological_space.is_topological_basis rat_basis,
  {
    apply real.is_topological_basis_Ioo_rat,
  },
  have A2: (b ∈ nhds x ↔ ∃ (t : set real) (H : t ∈ rat_basis), x ∈ t ∧ t ⊆ b),
  {
    apply @topological_space.mem_nhds_of_is_topological_basis,
    apply A1,
  },
  have A3: (∃ (t : set real) (H : t ∈ rat_basis), x ∈ t ∧ t ⊆ b),
  {
    apply A2.mp,
    apply a,
  },
  /-
    Now that we have proven A3, we are basically done. We just rewrite A3
    into the statement of the theorem.
  -/
  cases A3,
  cases A3_h,
  simp at A3_h_w,
  cases A3_h_w,
  cases A3_h_w_h,
  cases A3_h_w_h_h,
  subst A3_w,
  cases A3_h_h,
  apply exists.intro A3_h_w_w,
  apply exists.intro A3_h_w_h_w,
  unfold set.Ioo at A3_h_h_left,
  simp at A3_h_h_left,
  cases A3_h_h_left,
  split,
  {
    assumption,
  },
  split,
  {
    assumption,
  },
  split,
  {
    assumption,
  },
  {
    assumption,
  },
  end
end

------ Move theorems here to where they belong -----------------------------------

lemma induced_topological_basis {α β:Type*} [Tα:topological_space α] 
  [Tβ:topological_space β]
  {f:α → β} {S:set (set β)}:(inducing f) → 
  (topological_space.is_topological_basis S) →
  (topological_space.is_topological_basis (set.image (set.preimage f) S)) :=
begin
  intros A1 A2,
  rw A1.induced,
  unfold topological_space.is_topological_basis,
  split,
  {
    intros t₁ A3 t₂ A4 x A5,
    cases A3 with u₁ A3,
    cases A4 with u₂ A4,
    cases A5 with A6 A7,
    cases A3 with A8 A9,
    cases A4 with A10 A11,
    subst t₁,
    subst t₂,
    simp at A6,
    simp at A7,
    have A12:f x ∈ u₁ ∩ u₂,
    {
      simp,
      apply and.intro A6 A7,
    },
    unfold topological_space.is_topological_basis at A2,
    have A13 := A2.left u₁ A8 u₂ A10 (f x) A12,
    cases A13 with u₃ A13,
    cases A13 with A14 A15,
    cases A15 with A16 A17,
    apply exists.intro (f ⁻¹' u₃),
    have A18:f ⁻¹' u₃ ∈ set.preimage f '' S,
    {
      simp,
      apply exists.intro u₃,
      split,
      apply A14,
      refl,
    },
    apply exists.intro A18,
    split,
    apply A16,
    {
      rw set.subset_inter_iff at A17,
      apply set.subset_inter;apply set.preimage_mono,
      apply A17.left,
      apply A17.right,
    },
  },
  split,
  {
    ext a,split;intro A3;simp,
    unfold topological_space.is_topological_basis at A2,
    have A4:f a ∈ ⋃₀ S, 
    {
      rw A2.right.left,
      simp,
    },
    cases A4 with X A5,    
    cases A5 with A6 A7,
    apply exists.intro X,
    apply and.intro A6 A7,  
  },
  {
    unfold topological_space.is_topological_basis at A2,
    have A3 := A2.right.right,
    rw A3,
    apply induced_generate_from_eq,
  }
end

lemma nnreal_topological_space_def:
   nnreal.topological_space = @topological_space.induced nnreal real 
   (@coe nnreal real _) (@uniform_space.to_topological_space real _) := rfl


lemma inducing_nnreal_topological_space:
   inducing (@coe nnreal real _) := {
  induced := nnreal_topological_space_def,
}


lemma nnreal_nhds {x:nnreal}:
   nhds x = filter.comap (@coe nnreal real _) (nhds x.val) :=
begin
  apply inducing.nhds_eq_comap,
  apply inducing_nnreal_topological_space,
end

lemma nnreal_nhds2 {x:nnreal} {B:set nnreal}:
   B ∈ nhds x ↔ 
   (∃ C∈ nhds (x.val),set.preimage (@coe nnreal real _) C⊆ B)  :=
begin
  rw nnreal_nhds,
  apply filter.mem_comap_sets,
end

lemma coe_nnreal_real_val:(@coe nnreal real _) = subtype.val := rfl

lemma mem_nhds_elim_real {b:set real} {x:real}: b∈ nhds x →
(∃ p q:ℝ, (p < q) ∧ ((set.Ioo p q) ⊆ b) ∧ (p < x) ∧ (x < q))
  :=
begin
  intros,
  have A1:(∃ prat qrat:ℚ, (prat < qrat) ∧ ((set.Ioo prat qrat:set ℝ) ⊆ b) ∧ ((prat:ℝ) < x) ∧ (x < (qrat:ℝ))),
  {
    apply mem_nhds_elim_real_rat,
    apply a,
  },
  cases A1,
  cases A1_h,
  cases A1_h_h,
  cases A1_h_h_right,
  cases A1_h_h_right_right,

  apply exists.intro (A1_w:ℝ),
  apply exists.intro (A1_h_w:ℝ),
  split,
  {
    apply (@rat.cast_lt real _ A1_w A1_h_w).mpr,
    apply A1_h_h_left,
  },
  {
    split,
    {
      assumption,
    },
    split,
    {
      apply A1_h_h_right_right_left,
    },
    {
      apply A1_h_h_right_right_right,
    }
  },
end


lemma mem_nhds_elim_nnreal {b:set nnreal} {x:nnreal}: b∈ nhds x →
(∃ p q:ℝ, (p < q) ∧ 
          (set.preimage  (@coe nnreal real _) (set.Ioo p q) ⊆ b) ∧ 
          (p < ↑x) ∧ (↑x < q))
  :=
begin
  intro A1,
  rw nnreal_nhds2 at A1,
  cases A1 with C A1,
  cases A1 with A2 A3,
  have A4 := mem_nhds_elim_real A2,
  cases A4 with p A4,
  cases A4 with q A4,
  cases A4 with A5 A6,
  cases A6 with A7 A8,
  --cases A8 with A9 A10,
  apply exists.intro p,
  apply exists.intro q,
  split,
  apply A5,
  split,
  apply set.subset.trans,
  {
    apply set.preimage_mono,
    apply A7,
  },
  {
    apply A3,
  },
  apply A8,
end

lemma preimage_coe_Ioo {p q:ℝ}:(p < 0) → (0 ≤ q) →
    set.preimage (@coe nnreal real _) (set.Ioo p q) = set.Iio (nnreal.of_real q) :=
begin
  intro A1,
  intro A2,
  unfold set.Ioo set.Iio,
  ext,split;intro A3;simp at A3;simp,
  {
    cases A3 with A4 A5,
    rw ← nnreal.coe_lt_coe,
    rw nnreal.coe_of_real,
    apply A5,
    apply A2,
  },
  {
    split,
    {
      apply lt_of_lt_of_le,
      apply A1,
      apply x.property,
    },
    {
      rw ← nnreal.coe_of_real q,
      rw nnreal.coe_lt_coe,
      apply A3,
      apply A2,
    },
  },
end

lemma preimage_coe_Ioo2 {p q:ℝ}:(0 ≤ p) → (p < q) →
    set.preimage (@coe nnreal real _) (set.Ioo p q) = set.Ioo (nnreal.of_real p) (nnreal.of_real q) :=
begin
  intro A1,
  intro A2,
  have B1:0 ≤ q,
  {
    apply le_trans,
    apply A1,
    apply le_of_lt,
    apply A2,
  },
  unfold set.Ioo,
  ext,split;intro A3;simp at A3;simp,
  {
    cases A3 with A4 A5,
    split;rw ← nnreal.coe_lt_coe;rw nnreal.coe_of_real,
    apply A4,
    apply A1,
    apply A5,
    apply B1,
  },
  {
    cases A3 with A4 A5,
    split,
    {
      rw ← nnreal.coe_of_real p,
      rw nnreal.coe_lt_coe,
      apply A4,
      apply A1,
    },
    {
      rw ← nnreal.coe_of_real q,
      rw nnreal.coe_lt_coe,
      apply A5,
      apply B1,
    },
  },
end




lemma mem_nhds_elim_nnreal2 {b:set nnreal} {x:nnreal}:x ≠ 0 →  b∈ nhds x →
(∃ p q:nnreal, (p < q) ∧ 
          ((set.Ioo p q) ⊆ b) ∧ 
          (p < x) ∧ (x < q))
  :=
begin
  intros A1 A2,
  have A3 := mem_nhds_elim_nnreal A2,
  cases A3 with p A3,
  cases A3 with q A3,
  cases A3 with A4 A5,
  cases A5 with A6 A7,
  cases A7 with A8 A9,
  have A10:p < 0 ∨ 0 ≤ p := lt_or_le p 0,
  have A11:0 < x := bot_lt_iff_ne_bot.mpr A1,
  have A12:(@coe nnreal real _ 0) = (0:real) := rfl,
  have A13:x.val = (@coe nnreal real _ x) := rfl,
  have A14:0 < x.val,
  {
    rw A13,
    rw ← A12,
    rw nnreal.coe_lt_coe,
    apply A11,
  },
  have A15:0 ≤ q,
  {
    apply le_trans,
    apply x.property,
    apply le_of_lt,
    apply A9,
  },
  have A16:x < nnreal.of_real q,
  {
    rw ← nnreal.coe_lt_coe,
    rw nnreal.coe_of_real,
    apply A9,
    apply A15,
  },
  cases A10,
  {
    apply exists.intro (0:nnreal),
    apply exists.intro (nnreal.of_real q),
    split,
    {
      rw ← nnreal.coe_lt_coe,
      rw A12,
      apply lt_trans,
      apply A14,
      rw A13,
      apply lt_of_lt_of_le,
      apply A9,
      rw nnreal.coe_of_real,
      apply A15,
    },
    split,
    {
      have B2:set.Ioo 0 (nnreal.of_real q) ⊆ 
              (set.preimage (@coe nnreal real _) (set.Ioo p q)),
      {
        rw preimage_coe_Ioo,
        rw set.subset_def,
        intros y B2A,
        unfold set.Iio,
        unfold set.Ioo at B2A,
        simp at B2A,
        simp,
        apply B2A.right,
        apply A10,
        apply A15,
      },
      apply set.subset.trans B2 A6,
    },
    split,
    {
      apply A11,
    },
    {
      apply A16,
    },
  },
  {
    apply exists.intro (nnreal.of_real p),
    apply exists.intro (nnreal.of_real q),
    have B1:nnreal.of_real p < x,
    {
      rw ← nnreal.coe_lt_coe,
      rw nnreal.coe_of_real,
      apply A8,
      apply A10,
    },
    split,
    {
      apply lt_trans B1 A16,
    },
    split,
    {
      rw ← preimage_coe_Ioo2,
      apply A6,
      apply A10,
      apply A4,
    },
    split,
    {
      apply B1,
    },
    {
      apply A16,
    },
  },
end

lemma mem_nhds_elim_real_bound (b:set real) (x:real): b∈ nhds x →
(∃ r>0, (set.Ioo (x-r) (x+r)) ⊆ b)
  :=
begin
  intros,
  have A1:(∃ p q:ℝ, (p < q) ∧ ((set.Ioo p q) ⊆ b) ∧ (p < x) ∧ (x < q)),
  {
    apply mem_nhds_elim_real,
    apply a,
  },
  cases A1,
  cases A1_h,
  cases A1_h_h,
  cases A1_h_h_right,
  cases A1_h_h_right_right,

  let r := min (x - A1_w) (A1_h_w -x),
  begin
  apply exists.intro r,
  have A2:r>0,
  {
    apply lt_min,
    {
       apply (@lt_sub real _ 0 x A1_w).mpr,
       simp,
       assumption,
    },
    {
       apply (@lt_sub real _ 0 A1_h_w x).mpr,
       simp,
       assumption,
    }
  },
  apply exists.intro A2,
  have A3:set.Ioo (x-r) (x+r) ⊆ set.Ioo A1_w A1_h_w,
  {
    unfold set.Ioo,
    simp,
    intros,
    split,
    {
      apply lt_of_le_of_lt,
      show x - r < a_1,
      {
        assumption,
      },
      {
        have A4:r <= x - A1_w,
        apply min_le_left,
        apply (@le_sub real _ r x A1_w).mp,
        assumption,
      }
    },
    {
      apply lt_of_lt_of_le,
      {
        apply a_3,
      },
      { -- prove x + r ≤ A1_h_w
        have A6:r <= A1_h_w - x,
        apply min_le_right,
        --rw A7,
        apply (@le_neg_add_iff_add_le real _ x r A1_h_w).mp,
        have A7:((-x)+A1_h_w=A1_h_w-x),
        {
          apply real.decidable_linear_ordered_comm_ring.add_comm,
        },
        rw A7,
        assumption,
      }
    },
  },
  apply set.subset.trans,
  apply A3,
  assumption,
  end
end

lemma nnreal_sub_le_sub_of_le2 {a b c:nnreal}:a ≤ b → a - c ≤ b - c :=
begin
  intro A1,
  have A2:(c ≤ a) ∨ (a ≤ c) := le_total c a,
  cases A2,
  {
    rw ← add_le_add_iff_right c,
    rw nnreal.sub_add_cancel_of_le A2,
    rw nnreal.sub_add_cancel_of_le (le_trans A2 A1),
    apply A1,
  },
  {
    rw nnreal.sub_eq_zero A2,
    apply bot_le,
  },
end

lemma nnreal_le_sub_of_le_sub_of_le {p x r:nnreal}:p ≤ x → r ≤ x - p → p ≤ x - r :=
begin
  intros A1 A2,
  rw ← add_le_add_iff_right p at A2,
  rw nnreal.sub_add_cancel_of_le A1 at A2,
  have A3:(r + p) - r ≤ x - r := nnreal_sub_le_sub_of_le2 A2,
  rw add_comm r p at A3,
  rw nnreal.add_sub_cancel at A3,
  apply A3,
end

--TODO: remove dependence on x≠0
lemma mem_nhds_elim_nnreal_bound (b:set nnreal) (x:nnreal):x ≠ 0 →  b∈ nhds x →
(∃ r>0, (set.Ioo (x-r) (x+r)) ⊆ b)
  :=
begin
  intros AX a,
  have A1:(∃ p q:nnreal, (p < q) ∧ ((set.Ioo p q) ⊆ b) ∧ (p < x) ∧ (x < q)),
  {
    apply mem_nhds_elim_nnreal2,
    apply AX,
    apply a,
  },
  cases A1 with p A1,
  cases A1 with q A1,
  cases A1 with B1 B2,
  cases B2 with B2 B3,
  cases B3 with B3 B4,

  let r := min (x - p) (q -x),
  begin
  apply exists.intro r,
  have A2:r>0,
  {
    apply lt_min;rw nnreal.sub_pos,
    {
       apply B3,
    },
    {
       apply B4,
    }
  },
  apply exists.intro A2,
  have A3:set.Ioo (x-r) (x+r) ⊆ set.Ioo p q,
  {
    apply set.Ioo_subset_Ioo,
    {
      have A4:r <= x - p := min_le_left (x-p) (q - x),
      apply nnreal_le_sub_of_le_sub_of_le (le_of_lt B3) A4,
    },
    {
      have A4:r <= q - x := min_le_right (x-p) (q - x),
      rw ← add_le_add_iff_left x at A4,
      apply le_trans A4,
      rw add_comm x,
      rw nnreal.sub_add_cancel_of_le (le_of_lt B4),
    },
  },
  apply set.subset.trans,
  apply A3,
  assumption,
  end
end


--This is filter.at_top_def
lemma filter_at_top_def3 {α:Type*} [preorder α]:
filter.at_top = ⨅ a:α, filter.principal {b | a ≤ b} := rfl

lemma filter_at_top_def (α:Type*):
  (@filter.at_top (finset α) _)=  ⨅ (a:(finset α)),
   filter.principal  {b:finset α | a⊆  b} := rfl

--This is (roughly) filter.at_top_mem_sets
lemma mem_filter_at_top_def2 {α:Type*}  [SL:semilattice_sup_bot α] {S:set α}:
  (S∈ @filter.at_top α _)↔
  (∃ a:α, {b:α|a ≤ b}⊆ S) :=
begin
  have B1:order_bot α := semilattice_sup_bot.to_order_bot α,
  have B2:has_bot α := order_bot.to_has_bot α,
  rw filter_at_top_def3,
  unfold infi,
  have A1:(∀ X Y:filter α,
  X ∈ (set.range (λ (a :α), filter.principal {b : α | a ≤ b})) →
  Y ∈ (set.range (λ (a : α), filter.principal {b : α | a ≤ b})) →
  X ⊓ Y ∈ (set.range (λ (a : α), filter.principal {b : α | a ≤ b}))),
  {
    intros,
    simp at a,
    cases a,
    subst X,
    simp at a_1,
    cases a_1,
    subst Y,
    --simp,
    apply exists.intro (a_w ⊔ a_1_w),
    symmetry,
    apply principal_inf_sets2,
  },
  have A2:filter.principal {b : α | ⊥ ≤  b} ∈
   (set.range (λ (a : α), filter.principal {b : α | a ≤ b})),
  {
    rw set.mem_range,
    apply exists.intro ⊥,
    refl,
  },
  have A3:(S ∈ Inf (set.range (λ (a : α), filter.principal {b :  α | a ≤ b})))↔
          (∃ t∈ (set.range (λ (a : α), filter.principal {b : α | a ≤ b})), S∈ t),
  {
    apply (@Inf_filter_def (α)
          (set.range (λ (a : α), filter.principal {b : α | a ≤ b}))
          (filter.principal {b : α | ⊥ ≤ b})
          A2
          A1
          ),
  },
  apply iff.trans,
  apply A3,
  split;intros,
  {
    cases a,
    cases a_h,
    simp at a_h_w,
    cases a_h_w,
    apply exists.intro a_h_w_w,
    simp,
    subst a_w,
    simp at a_h_h,
    exact a_h_h,
  },
  {
    cases a,
    apply exists.intro (filter.principal  {b : α | a_w ≤ b}),
    have A4:filter.principal {b : α | a_w ≤ b} ∈
        set.range (λ (a : α), filter.principal {b : α | a ≤ b}),
    {
      simp,
      apply exists.intro a_w,
      refl,
    },
    apply exists.intro A4,
    apply a_h,
  }
end


lemma filter_at_top_def2 (α:Type*) [decidable_eq α] (S:set (finset α)):
  (S∈ @filter.at_top (finset α) _)↔
  (∃ a:finset α, {b:finset α|a ≤ b}⊆ S) :=
begin
  apply mem_filter_at_top_def2,
end


--See alternatives below.
lemma filter_at_top_intro {α:Type*} (b:set (finset α)) (c:finset α):
  (b∈ (filter.principal {d:finset α |c ≤ d} )) →
  (b ∈ (@filter.at_top (finset α) _)) :=
begin
  intros,
  rw filter_at_top_def,
  unfold infi,
  apply Inf_le_simp,
  {
    have A1:(filter.principal {d:finset α |c ≤ d} ) ∈
    set.range (λ (a : finset α), filter.principal {b : finset α | a ⊆ b}),
    {
      unfold set.range,
      simp,
      apply exists.intro c,
      refl,
    },
    apply A1,
  },
  {
    assumption,
  }
end

lemma filter_at_top_elim {α:Type*} [decidable_eq α] {S:set (finset α)} :
  (S ∈ (@filter.at_top (finset α) _))→
  (∃ a:(finset α), {b:finset α|a ≤ b}⊆ S) :=
begin
  apply (filter_at_top_def2 α S).mp,
end

lemma filter_at_top_intro2 {α:Type*} (b:set (finset α)) (c:finset α):
  ({d:finset α |c ≤ d} ⊆ b) →
  (b ∈ (@filter.at_top (finset α) _)) :=
begin
  intros,
  have A1:b∈ filter.principal {d:finset α |c ≤ d},
  {
    unfold filter.principal,
    simp,
    apply a,
  },
  apply filter_at_top_intro,
  apply A1,
end


lemma filter_contains_preimage_superset (α β:Type) (B:filter β) (S T:set α) (f:β  → α):
  (S⊆ T)→ ({x:β |f x ∈ S}∈ B) → ({x:β |f x ∈ T}∈ B) :=
begin
  intros,
  have A1:{x:β |f x ∈ S} ⊆ {x:β |f x ∈ T},
  {
    apply preimage_superset,
    assumption,
  },
  apply B.sets_of_superset,
  apply a_1,
  assumption,
end

lemma filter_at_top_intro3  {α β:Type*} (c:finset α) (S:set β) (f:finset α → β):
  (∀ d ≥ c, f d ∈ S) →
  ({x:finset α|f x∈ S} ∈ (@filter.at_top (finset α) _)) :=
begin
  intros,
  have A1:({d:finset α |c ≤ d} ⊆ {x:finset α|f x∈ S}),
  {
    rw set.subset_def,
    intros,
    simp,
    simp at a_1,
    apply a,
    apply a_1,
  },
  apply filter_at_top_intro2,
  apply A1,
end




lemma mem_filter_at_top_intro {α:Type*} [P:semilattice_sup_bot α] {S:set α} {x:α}:
  {y|x≤ y}⊆ S →
  S∈ (@filter.at_top α _) :=
begin
  intro A1,
  rw mem_filter_at_top_def2,
  apply exists.intro x,
  apply A1,
end



lemma mem_filter_at_top_elim {α:Type*} [P:semilattice_sup_bot α] {S:set α} :
  (S ∈ (@filter.at_top α _))→
  (∃ a:α, {b:α|a ≤ b}⊆ S) :=
begin
  apply (mem_filter_at_top_def2).mp,
end

lemma in_own_Ioo {x ε:ℝ}:(0 < ε)→ x ∈ set.Ioo (x -ε) (x + ε) :=
begin
  apply x_in_Ioo,
end


/-
  Unused.
-/
lemma mem_nhds_elim_helper (b:set nnreal) (x:nnreal) (s:set nnreal)
  (H2 : s ∈ {s : set nnreal | x ∈ s ∧ is_open s}):
 (set.range (λ (H : s ∈ {s : set nnreal | x ∈ s ∧ is_open s}), filter.principal s))
 = {x:filter nnreal| x=filter.principal s}
  :=
begin
  unfold set.range,
  simp,
  ext,
  split,
  {
    simp,
    intros,
    symmetry,
    exact a_2,
  },
  {
    simp,
    intros,
    split,
    {
      apply H2,
    },
    {
      symmetry,
      exact a,
    }
  }
end

/-
  Unused.
-/
lemma mem_nhds_elim_helper2 (b:set nnreal) (x:nnreal) (s:set nnreal)
  (H2 : s ∉ {s : set nnreal | x ∈ s ∧ is_open s}):
 (set.range (λ (H : s ∈ {s : set nnreal | x ∈ s ∧ is_open s}), filter.principal s)) = ∅
  :=
begin
  unfold set.range,
  simp,
  apply emptyset_intro,
  intros,
  simp at H,
  simp at H2,
  cases H,
  cases H_left,
  have A1:(¬ is_open s),
  {
    apply H2,
    assumption,
  },
  apply A1,
  apply H_left_right
end




lemma lim_Inf_filter_empty (α:Type*):
  (@Inf (filter α) _ ∅) = ⊤ :=
begin
  simp,
end

lemma set_in_lattice_infih (α:Type*) (s:set α) (S:set (set α))
  (H2 : s ∉ S):
 (set.range (λ (H : s ∈ S), filter.principal s)) = ∅
  :=
begin
  unfold set.range,
  simp,
  apply emptyset_intro,
  intros,
  simp at H,
  apply H2,
  apply H.left
end

lemma set_in_lattice_infih2 (α:Type*) (s:set α) (S:set (set α))
  (H2 : s ∈ S):
 (set.range (λ (H : s ∈ S), filter.principal s))
 = {filter.principal s}
  :=
begin
  unfold set.range,
  simp,
  ext,
  split,
  {
    simp,
    intros,
    symmetry,
    exact a_1,
  },
  {
    simp,
    intros,
    split,
    {
      apply H2,
    },
    {
      symmetry,
      exact a,
    }
  }
end



lemma lower_bounds_top (α:Type*) (S:set (filter α)):lower_bounds S = lower_bounds (S ∪ {⊤}) :=
begin
  ext,
  unfold lower_bounds,
  split;intros;simp;simp at a;intros,
  {
    cases a_2,
    {
      rw a_2,
      simp,
    },
    {
      apply a,
      apply a_2,
    }
  },
  {
    apply a,
    right,
    apply a_2,
  }
end

lemma Inf_union_top (α:Type*) (S:set (filter α)):
Inf (S∪ {⊤}) = Inf S :=
begin
  have A2:is_glb S (Inf S),
  {
    apply is_glb_Inf,
  },
  have A3:is_glb (S∪ {⊤}) (Inf S),
  {
    cases A2,
    split,
    {
      rw ← lower_bounds_top,
      exact A2_left,
    },
    {
      rw ← lower_bounds_top,
      exact A2_right,
    }
  },
  apply is_glb.Inf_eq A3,
end





/-
  If we unfold infi in nhds, we get a doubly-nested Infimum that is hard to
  work with. This rewrites it more simply.
 -/
lemma set_in_lattice_infi (α:Type*) (S:set (set α)):
(⨅ (s∈ S), (filter.principal s)) = Inf  (set.image (filter.principal) S) :=
begin
  unfold infi,
  rw (set_range_split (set α) _ S),
  have A1:(λ (s : set α), Inf (set.range (λ (H : s ∈ S), filter.principal s))) '' (S)ᶜ =
    (λ (s : set α), ⊤) '' Sᶜ,
  {
    rw image_subst,
    intros,
    have A1AA:set.range (λ (H : s ∈ S), filter.principal s) = ∅,
    {
      apply set_in_lattice_infih,
      apply H,
    },
    rw A1AA,
    rw lim_Inf_filter_empty,
  },
  rw A1,
  have A2:(λ (s : set α), Inf (set.range (λ (H : s ∈ S), filter.principal s))) '' (S) =
    (λ (s : set α), filter.principal s) '' S,
  {
    rw image_subst,
    intros,
    have A2A:set.range (λ (H : s ∈ S), filter.principal s) = {filter.principal s},
    {
      apply set_in_lattice_infih2,
      apply H,
    },
    rw A2A,
    simp,
  },
  rw A2,

  have A4:(Sᶜ = ∅)∨(∃ x, x ∈ Sᶜ), --eq_or_noteq (set α) Sᶜ ∅),
  {
    apply empty_or_contains,
  },
  cases A4,
  {
    rw A4,
    simp,
  },
  {
    cases A4,
    have A4A:∀ k:filter α,(λ (s : set α), k) '' Sᶜ = {k},
    {
      intros,
      ext,
      split;intros,
      {
        cases a,
        cases a_h,
        simp at a_h_right,
        rw a_h_right,
        apply (set.mem_singleton),
      },
      {
        split,
        {
          split,
          apply A4_h,
          simp,
          simp at a,
          rw a,
        }
      }
    },
    have A4B:(λ (s : set α), ⊤) '' Sᶜ = {⊤},
    {
      apply (A4A ⊤),
    },
    rw A4B,
    apply Inf_union_top,
  }
end


lemma open_nhds_inter
    (α:Type*) [topological_space α] (x:α) (A B:set α):
    (A∈ {s:set α|x∈ s∧ is_open s}) →
    (B∈ {s:set α|x∈ s∧ is_open s}) →
    ((A∩ B) ∈ {s:set α|x∈ s∧ is_open s}) :=
begin
  intros,
  cases a,
  cases a_1,
  split,
  {
    split;assumption,
  },
  {
    apply is_open_inter;assumption,
  },
end


/-
lemma Inf_filter_def (α:Type) (S : set (filter α))
(b:filter α) (H:b∈ S)
  (H2:∀ a b:filter α, a∈ S→ b∈ S→ a⊓b∈ S) (s:set α):
(s ∈ Inf S)↔ (∃ t∈ S, s∈ t) :=
-/

lemma nhds_def1 (α:Type*) [topological_space α] (x:α):
nhds x = Inf  (set.image (filter.principal) {S:set α|x∈ S ∧ is_open S}) :=
begin
  unfold nhds,
  unfold infi,
  apply set_in_lattice_infi,
end


/-
   This holds for an arbitrary topology.
   See @mem_nhds_sets_iff
 -/
lemma mem_nhds_intro_real2 {b U:set real} {x:real}:
x∈ U →
is_open U →
U ⊆ b →
b∈ nhds x :=
begin
  intros A1 A2 A3,
  rw nhds_def1,
  have A4:b∈ filter.principal U,
  {
    apply filter_principal_intro3,
    apply A3,
  },
  apply mem_Inf_intro A4,
  {
    simp,
    split;assumption,
  },
end


/- This holds for a (closed) order topology (I think) -/
lemma mem_nhds_intro_real (b:set real) (x y z:real):
x∈ set.Ioo y z →
set.Ioo y z ⊆ b →
b∈ nhds x :=
begin
  intros A1 A2,
  apply mem_nhds_intro_real2 A1 _ A2,
  apply @is_open_Ioo ℝ _ _ _ y z,
end


lemma mem_nhds_filter_principal_intro (α:Type*) [topological_space α] (x:α) (V:set α):
  V∈ {S:set α|x∈ S ∧ is_open S}→ filter.principal V ∈ (set.image (filter.principal) {S:set α|x∈ S ∧ is_open S}) :=
begin
  intros,
  simp,
  apply a,
end


lemma mem_nhds_filter_principal_elim (α:Type*) [topological_space α] (x:α) (V:set α):
  filter.principal V ∈ (set.image (filter.principal) {S:set α|x∈ S ∧ is_open S}) →
  V∈ {S:set α|x∈ S ∧ is_open S} :=
begin
  intros,
  simp at a,
  apply a,
end


lemma mem_nhds_filter_principal_elim2 (α:Type*) [topological_space α] (x:α) (Z:filter α):
  Z ∈ (set.image (filter.principal) {S:set α|x∈ S ∧ is_open S}) →
  (∃ V:set α, V∈ {S:set α|x∈ S ∧ is_open S} ∧ filter.principal V = Z) :=
begin
  intros,
  simp at a,
  apply a,
end


lemma has_open_neighborhood (α:Type*) [topological_space α] (x:α):∃ U:set α, x∈ U ∧ is_open U :=
begin
  apply exists.intro set.univ,
  split,
  {
    simp,
  },
  {
    apply topological_space.is_open_univ,
  }
end


lemma nhds_def2 (α:Type*) [topological_space α] (x:α) (S:set α):
S ∈ nhds x ↔
(∃ u:set α, (u⊆ S) ∧ is_open u ∧ (x∈ u)) :=
begin
  rw nhds_def1,
  have H:∃ U:set α, x∈ U ∧ is_open U,
  apply has_open_neighborhood,
  cases H,
  cases H_h,

  apply iff.trans,
  {
    apply Inf_filter_def,
    {
      apply mem_nhds_filter_principal_intro,
      simp,
      split,
      {
        apply H_h_left,
      },
      {
        apply H_h_right,
      }
    },
    {
      intros,
      have A1:(∃ V:set α, V∈ {S:set α|x∈ S ∧ is_open S} ∧ filter.principal V = a),
      {
        apply mem_nhds_filter_principal_elim2,
        apply a_1,
      },
      cases A1,
      cases A1_h,
      subst a,
      have A2:(∃ V:set α, V∈ {S:set α|x∈ S ∧ is_open S} ∧ filter.principal V = b),
      {
        apply mem_nhds_filter_principal_elim2,
        apply a_2,
      },
      cases A2,
      cases A2_h,
      subst b,
      have A3:((A1_w ∩ A2_w) ∈ {s:set α|x∈ s∧ is_open s}),
      {
        apply open_nhds_inter;assumption,
      },
      rw principal_inf,
      split,
      {
        split,
        {
          apply A3,
        },
        {
          refl,
        }
      }
    }
  },
  {
    split;intros,
    {
      cases a,
      cases a_h,
      have A4:(∃ V:set α, V∈ {S:set α|x∈ S ∧ is_open S} ∧ filter.principal V = a_w),
      {
        apply mem_nhds_filter_principal_elim2,
        apply a_h_w,
      },
      cases A4,
      cases A4_h,
      subst a_w,
      apply exists.intro A4_w,
      cases A4_h_left,
      split,
      {
        assumption,
      },
      split;assumption,
    },
    {
      cases a,
      cases a_h,
      cases a_h_right,
      apply exists.intro (filter.principal a_w),
      {
        have A5:filter.principal a_w ∈ filter.principal '' {S : set α | x ∈ S ∧ is_open S},
        {
          apply mem_nhds_filter_principal_intro,
          split;assumption,
        },
        apply exists.intro A5,
        apply filter_principal_intro3,
        assumption,
      }
    }
  }
end


lemma nhds_contain_point (α:Type*) [topological_space α] (x:α) (S:set α):
S ∈ nhds x → x∈ S :=
begin
  intros,
   have A1:(∃ u:set α, (u⊆ S) ∧ is_open u ∧ (x∈ u)),
   {
     apply (nhds_def2 α x S).mp a,
   },
   cases A1,
   cases A1_h,
   rw set.subset_def at A1_h_left,
   apply A1_h_left,
   apply A1_h_right.right,
end


lemma Ioo_nbhd {x ε:ℝ}:(0 < ε)→ set.Ioo (x -ε) (x + ε) ∈ nhds x :=
begin
  intro A1,
  apply mem_nhds_intro_real,
  apply in_own_Ioo A1,
  apply set.subset.refl,
end


--Remove dependency on not equal to zero.
lemma set_Ioo_in_nhds_of_ne_zero {x:nnreal} {ε:nnreal}:x ≠ 0 → ε >0 → set.Ioo (x - ε) (x + ε) ∈ nhds x :=
begin
  intros A1 A2,
  rw @mem_nhds_sets_iff,
--  have A3:(ε≤x) ∨ (x < ε) := le_or_lt ε x,
  apply exists.intro (set.Ioo (x - ε) (x + ε)),
  split,
  apply @complete_lattice.le_refl (set nnreal) (@set.lattice_set nnreal),
  split,
  apply is_open_Ioo,
  simp,
  split,
  {
    apply nnreal.sub_lt_self,
    {  
      apply bot_lt_iff_ne_bot.mpr,
      apply A1,
    },
    {
      apply A2,
    },
  },
  {
    apply A2,
  },
end

--TODO: remove dependence on x ≠ 0
lemma set_Iio_in_nhds_of_lt {x y:nnreal}:x ≠ 0 → x < y → set.Iio y ∈ nhds x :=
begin
  intros AX A1,
  rw @mem_nhds_sets_iff,
  apply exists.intro (set.Ioo 0 y),
  split,
  {
    apply set.Ioo_subset_Iio_self,  
  },
  split,
  {
    apply is_open_Ioo,
  },
  simp,
  split,
  {
    apply bot_lt_iff_ne_bot.mpr,
    apply AX,
  },
  {
    apply A1,
  },
end

