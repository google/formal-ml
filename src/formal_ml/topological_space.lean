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
import topology.basic
import topology.order
import topology.constructions
import topology.bases
import data.set.countable
import formal_ml.set

import topology.instances.nnreal
import topology.instances.ennreal

/- The nnreal and ennreal are only needed for two methods.
   Could move those to a separate file.
-/

lemma topological_space_le_def {α:Type*} (S T:topological_space α):
  S ≤ T ↔
  (T.is_open ≤ S.is_open) :=
begin
  refl,
end

lemma topological_space_generate_from_refl {α:Type*} (T:topological_space α):
  (topological_space.generate_from (T.is_open)) = T :=
begin
  apply complete_lattice.le_antisymm,
  {
    rw topological_space_le_def,
    intros U A1,
    unfold topological_space.generate_from,
    simp,
    apply topological_space.generate_open.basic,
    exact A1,
  },
  {
    apply (@le_generate_from_iff_subset_is_open α (T.is_open) T).mpr,
    apply set.subset.refl,
  }
end

lemma topological_space_induced_is_open {α β:Type*} (f:α → β) (T:topological_space β):
  (topological_space.induced f T).is_open = (λs, ∃s', T.is_open s' ∧ f ⁻¹' s' = s) :=
begin
  refl,
end

lemma topological_space_induced_is_open2 {α β:Type*} (f:α → β) (T:topological_space β):
  (topological_space.induced f T).is_open = (set.image (set.preimage f) T.is_open) :=
begin
  refl,
end

lemma topological_space_generate_from_is_open {α:Type*} {B:set (set α)}:
  (topological_space.generate_from B).is_open = topological_space.generate_open B :=
begin
  refl,
end




lemma topological_space_induced_def {α β:Type*} {Bβ:set (set β)} (f:α → β):
  topological_space.induced f (@topological_space.generate_from β Bβ) =
  @topological_space.generate_from α (set.image (set.preimage f) Bβ) :=
begin
  rw @induced_generate_from_eq,
end

lemma topological_space_induced_fst_def {α β:Type*} {Bα:set (set α)}:
  topological_space.induced (@prod.fst α β) (@topological_space.generate_from α Bα) =
  @topological_space.generate_from (α × β) {U:set (α × β)|∃ A∈ Bα, U = set.prod A set.univ} :=
begin
  rw topological_space_induced_def,
  rw set.preimage_fst_def,
end

lemma topological_space_induced_snd_def {α β:Type*} {Bβ:set (set β)}:
  topological_space.induced (@prod.snd α β) (@topological_space.generate_from β Bβ) =
  @topological_space.generate_from (α × β) {U:set (α × β)|∃ B∈ Bβ, U = set.prod set.univ B} :=
begin
  rw topological_space_induced_def,
  rw set.preimage_snd_def,
end










lemma semilattice_inf_inf_intro {α:Type*}
  [SL:semilattice_inf α] (x y z:α):
  (z ≤ x) →
  (z ≤ y) →
  (∀ w, (w≤ x)→ (w≤ y)→ (w≤ z))→
  (x ⊓ y = z) :=
begin
  intros A1 A2 A3,
  apply semilattice_inf.le_antisymm,
  { -- x ⊓ y ≤ z
    apply A3,
    {
      apply semilattice_inf.inf_le_left,
    },
    {
      apply semilattice_inf.inf_le_right,
    }
  },
  {  -- ⊢ z ≤ x ⊓ y
    apply semilattice_inf.le_inf,
    {
      apply A1,
    },
    {
      apply A2,
    }
  }
end



lemma topological_space_inf_def {α:Type*} {S:set (set α)} {T:set (set α)}:
   (@topological_space.generate_from α S) ⊓ (@topological_space.generate_from α T)=
   (@topological_space.generate_from α (S∪ T)) :=
begin
  apply semilattice_inf_inf_intro,
  {
    apply generate_from_mono,
    apply set.subset_union_left
  },
  {
    apply generate_from_mono,
    apply set.subset_union_right
  },
  {
    intros w a a_1,
    have A1:S ⊆ w.is_open,
    {
      apply (@le_generate_from_iff_subset_is_open α S w).mp a,
    },
    have A2:T ⊆ w.is_open,
    {
      apply (@le_generate_from_iff_subset_is_open α T w).mp a_1,
    },
    have A2:S ∪ T ⊆ w.is_open,
    {
      apply set.union_subset;assumption,
    },
    apply (@le_generate_from_iff_subset_is_open α (S∪T) w).mpr A2,
  }
end

lemma prod_topological_space_def {α β:Type*} {Bα:set (set α)}
  {Bβ:set (set β)}:@prod.topological_space α β
  (topological_space.generate_from Bα) (topological_space.generate_from Bβ) =
  topological_space.generate_from
  ({U:set (α × β)|∃ A∈ Bα, U = set.prod A set.univ} ∪
  {U:set (α × β)|∃ B∈ Bβ, U = set.prod set.univ B})
  :=
begin
  have A1:(@prod.topological_space α β
  (@topological_space.generate_from α Bα) (@topological_space.generate_from β Bβ)) =
  topological_space.induced prod.fst (@topological_space.generate_from α Bα) ⊓
  topological_space.induced prod.snd (@topological_space.generate_from β Bβ),
  {
    refl,
  },
  rw (@topological_space_induced_fst_def α β Bα) at A1,
  rw (@topological_space_induced_snd_def α β Bβ) at A1,
  rw topological_space_inf_def at A1,
  apply A1,
end



/-
  We have to be careful about continuous and measurable functions when it
  comes to functions with two variables. Specifically, if we say a function like f:α → β → γ
  is continuous, this implies it is a continuous function from α to β → γ, which is usually
  not what we want. This would ignore the topological space of β.
  Instead, we want to consider a related function f:(α × β) → γ, and ask if the preimage
  of an open set in γ is an open set in (α × β). This is a stronger statement (I think).

  This little definition takes care of this. Note that if you look at the
  topological_semiring definition below, it matches this definition of continuity.
 -/
def continuous2 {α β γ:Type*} [topological_space α] [topological_space β]
    [topological_space γ] (f:α → β → γ):Prop :=
    continuous (λ p:α × β, f (p.fst) (p.snd))


lemma continuous2_def {α β γ:Type*} [topological_space α] [topological_space β]
    [topological_space γ] (f:α → β → γ):continuous2 f ↔
    continuous (λ p:α × β, f (p.fst) (p.snd)) :=
begin
  refl
end


lemma continuous2_of_has_continuous_mul {α:Type*} [T:topological_space α]
    [HM:has_mul α]:@has_continuous_mul α T HM ↔
    (@continuous2 α α α T T T (@has_mul.mul α _)) :=
begin
  split;intros A1,
  {
    rw continuous2_def,
    apply @continuous_mul α T HM A1,
  },
  {
    rw continuous2_def at A1,
    have A2:@has_continuous_mul α T HM := {
      continuous_mul := A1,
    }, 
    apply A2,
  },
end

lemma has_continuous_add_iff_continuous2 {α:Type*} [T:topological_space α]
    [HM:has_add α]:@has_continuous_add α T HM ↔
    (@continuous2 α α α T T T (@has_add.add α _)) :=
begin
  split;intros A1,
  {
    rw continuous2_def,
    apply @continuous_add α T HM A1,
  },
  {
    rw continuous2_def at A1,
    have A2:@has_continuous_add α T HM := {
      continuous_add := A1,
    }, 
    apply A2,
  },
end


lemma continuous2_nnreal_add: continuous2 nnreal.has_add.add :=
begin
  rw ← has_continuous_add_iff_continuous2,
  apply nnreal.topological_semiring.to_has_continuous_add,
end

lemma continuous2_real_add: continuous2 real.linear_ordered_comm_ring.add :=
begin
  have A1:real.linear_ordered_comm_ring.add = (@has_add.add ℝ _) := rfl,
  rw A1,
  rw ← has_continuous_add_iff_continuous2,
  apply real.topological_semiring.to_has_continuous_add,
end

lemma continuous2_ennreal_add: continuous2 ennreal.canonically_ordered_comm_semiring.add :=
begin
  have A1:ennreal.canonically_ordered_comm_semiring.add = (@has_add.add ennreal _) := rfl,
  rw A1,
  rw ← has_continuous_add_iff_continuous2,
  apply ennreal.has_continuous_add,
end


-- Topological basis is the true topological basis, as would be found in Munkres.
-- The important distinction is that any open set can be formed via a union of elements of the
-- basis.




--Trivial: do not use
lemma contains_nbhd_of_basis {α:Type*} [Tα:topological_space α] {Gα:set (set α)} {x:α} {V:set α}:
      (@topological_space.is_topological_basis α Tα  Gα) →
      (is_open V) →
      (x∈ V) →
      (∃ S∈ Gα, x∈ S∧ S⊆V) :=
begin
  intros A1 A2 A3,
  apply @topological_space.mem_basis_subset_of_mem_open α Tα Gα A1 x V A3 A2,
end

--Trivial: do not use
lemma union_basis_of_is_open {α:Type*} [Tα:topological_space α] {Gα:set (set α)}  {V:set α}:
      (@topological_space.is_topological_basis α Tα  Gα) →
      (is_open V) →
      (∃ S⊆ Gα, V = set.sUnion S) :=
begin
  intros A1 A2,
  apply topological_space.sUnion_basis_of_is_open,
  apply A1,
  apply A2,
end


--set_option pp.implicit true
lemma continuous_intro {α β:Type*} {Tα:topological_space α} {Tβ:topological_space β} {Gβ:set (set β)}  (f:α → β):
      (@topological_space.is_topological_basis β Tβ Gβ) →
      (∀ U∈ Gβ, is_open (f⁻¹' U)) →
      (@continuous α β Tα Tβ f) :=
begin
  rw continuous_def,
  intros A1 A2 S A3,
  --unfold topological_space.is_topological_basis at A1,
  have A4:(∃ X⊆ Gβ, S = set.sUnion X),
  {
    apply topological_space.sUnion_basis_of_is_open,
    apply A1,
    apply A3,
  },
  cases A4 with X A5,
  cases A5 with A6 A7,
  rw A7,
  rw set.preimage_sUnion',
  apply is_open_sUnion,
  intro T,
  intro A8,
  cases A8 with T2 A9,
  cases A9 with A10 A11,
  subst T,
  apply A2,
  rw set.subset_def at A6,
  apply A6,
  exact A10,
end





lemma sUnion_eq_univ_intro {β:Type*} {Gβ:set (set β)}:
      (∀ x:β, ∃ B∈ Gβ, x∈ B) → (⋃₀ Gβ = set.univ) :=
begin
  intro A1,
  ext,split;intros A2,
  {
    simp,
  },
  {
    have A3: ∃ (B : set β) (H : B ∈ Gβ), x ∈ B,
    {
      apply A1,
    },
    cases A3 with B A4,
    cases A4 with A5 A6,


    simp,
    apply exists.intro B,
    split,
    exact A5,
    exact A6,
  }
end

/-
  This theorem uses a middle definition of basis.
  Specifically, every point must be in some set in the basis.
  Note that this is equivalent to the union of the sets in the basis being the universe.
-/
lemma continuous_intro2 {α β:Type*} {Tα:topological_space α}
    {Gβ:set (set β)} (f:α → β):
      (∀ x:β, ∃ B∈ Gβ, x∈ B) →
      (∀ U∈ Gβ, is_open (f⁻¹' U)) →
      (@continuous α β Tα (topological_space.generate_from Gβ) f) :=
begin
  intros A0 A1,
  rw continuous_def,
  intros U A2,
  have A3:@topological_space.generate_open β Gβ U,
  {
    rw ← topological_space_generate_from_is_open,
    apply A2,
  },
  clear A2,
  induction A3,
  {
    apply A1,
    exact A3_H,
  },
  {
    have A4:(⋃₀ Gβ = set.univ),
    {
      apply sUnion_eq_univ_intro,
      apply A0,
    },
    {
      rw ← A4,
      rw set.preimage_sUnion',
      apply is_open_sUnion,
      intros t A5,
      cases A5 with B A6,
      cases A6 with A7 A8,
      subst t,
      apply A1,
      exact A7,
    },
  },
  {
    rw set.preimage_inter,
    apply is_open_inter;assumption,
  },
  {
    rw set.preimage_sUnion',
    apply is_open_sUnion,
    intros t A5,
    cases A5 with B A6,
    cases A6 with A7 A8,
    subst t,
    apply A3_ih,
    exact A7,
  }
end

lemma generate_from_le_generate_from {α:Type*} {A B:set (set α)}:
  (∀ b∈ B, topological_space.generate_open A b) →
  (topological_space.generate_from A ≤ topological_space.generate_from B) :=
begin
  intro A1,
  apply le_generate_from_iff_subset_is_open.mpr,
  rw set.subset_def,
  unfold topological_space.generate_from,
  intros x A3,
  apply A1,
  exact A3,
end

lemma generate_from_eq_generate_from {α:Type*} {A B:set (set α)}:
  (∀ a∈ A, topological_space.generate_open B a) →
  (∀ b∈ B, topological_space.generate_open A b) →
  (topological_space.generate_from A = topological_space.generate_from B) :=
begin
  intros A1 A2,
  apply le_antisymm,
  {
    apply generate_from_le_generate_from,
    exact A2,
  },
  {
    apply generate_from_le_generate_from,
    exact A1,
  },
end



lemma prod_topological_space_def2 {α β:Type*}
  {Tα:topological_space α} {Tβ:topological_space β} {Bα:set (set α)}
  {Bβ:set (set β)}:
  (@topological_space.is_topological_basis α Tα Bα) →
  (@topological_space.is_topological_basis β Tβ Bβ) →
  (@topological_space.is_topological_basis (α × β)
  (@prod.topological_space α β Tα Tβ)
  ({U:set (α × β)|∃ A∈ Bα, ∃ B∈ Bβ, U = set.prod A B}))
  :=
begin
  intros A1 A2,
  unfold topological_space.is_topological_basis at A1,
  cases A1 with A3 A4,
  cases A4 with A5 A6,
  rw A6,
  unfold topological_space.is_topological_basis at A2,
  cases A2 with A7 A8,
  cases A8 with A9 A10,
  rw A10,
  rw prod_topological_space_def,
  unfold topological_space.is_topological_basis,
  split,
  {
    intros t₁ B1 t₂ B2 x B3,
    cases B1 with tA₁ B4,
    cases B4 with B5 B6,
    cases B6 with tB₁ B7,
    cases B7 with B7 B8,
    subst t₁,
    --unfold set.prod at B3,
    cases B2 with tA₂ B9,
    cases B9 with B10 B11,
    cases B11 with tB₂ B12,
    cases B12 with B13 B14,
    subst t₂,
    rw set.prod_inter_prod at B3,
    cases B3 with B15 B16,
    have B17:(∃ (tA₃ : set α) (H : tA₃ ∈ Bα), x.fst ∈ tA₃ ∧ tA₃ ⊆ tA₁ ∩ tA₂),
    {
      apply A3,
      exact B5,
      exact B10,
      exact B15,
    },
    have B18:(∃ (tB₃ : set β) (H : tB₃ ∈ Bβ), x.snd ∈ tB₃ ∧ tB₃ ⊆ tB₁ ∩ tB₂),
    {
      apply A7,
      exact B7,
      exact B13,
      exact B16,
    },
    cases B17 with tA₃ B19,
    cases B19 with B20 B21,
    cases B21 with B22 B23,
    cases B18 with tB₃ B24,
    cases B24 with B25 B26,
    cases B26 with B27 B28,
    apply exists.intro (set.prod tA₃ tB₃),
    split,
    {
      simp,
      apply exists.intro tA₃,
      split,
      exact B20,
      apply exists.intro tB₃,
      split,
      exact B25,
      refl,
    },
    {
      split,
      {
        split,
        apply B22,
        apply B27,
      },
      {
        rw set.prod_inter_prod,
        rw set.prod_subset_prod_iff,
        left,split;assumption,
      }
    }
  },
  {
    split,
    {
      ext;split;intro C1,
      {
        simp,
      },
      {
         simp,
         have C2:x.fst ∈ ⋃₀ Bα,
         {
           rw A5,
           simp,
         },
         cases C2 with S C3,
         cases C3 with C4 C5,
         have C6:x.snd ∈ ⋃₀ Bβ,
         {
           rw A9,
           simp,
         },
         cases C6 with T C7,
         cases C7 with C8 C9,
         apply exists.intro (@set.prod α β S T),
         simp,
         split,
         {
           apply (exists.intro S),

           split,
           exact C4,
           apply (exists.intro T),
           split,
           {
             exact C8,
           },
           {
             refl,
           }
         },
         {
           split,
           {
             exact C5,
           },
           {
             exact C9,
           }
         }
      }
    },
    {
      apply generate_from_eq_generate_from,
      {
         intros X D1,
         cases D1,
         {
           cases D1 with S D2,
           cases D2 with D3 D4,
           rw ← A9 at D4,
           rw set.prod_sUnion_right at D4,
           subst X,
           apply topological_space.generate_open.sUnion,
           intros ST D5,
           cases D5 with T D6,
           cases D6 with D7 D8,
           subst ST,
           apply topological_space.generate_open.basic,
           simp,
           apply exists.intro S,
           split,
           exact D3,
           apply exists.intro T,
           split,
           exact D7,
           refl,
         },
         {
           cases D1 with T D2,
           cases D2 with D3 D4,
           rw ← A5 at D4,
           rw set.prod_sUnion_left at D4,
           subst X,
           apply topological_space.generate_open.sUnion,
           intros ST D5,
           cases D5 with S D6,
           cases D6 with D7 D8,
           subst ST,
           apply topological_space.generate_open.basic,
           simp,
           apply exists.intro S,
           split,
           exact D7,
           apply exists.intro T,
           split,
           exact D3,
           refl,
         }
      },
      {
        intros X E1,
        cases E1 with S E2,
        cases E2 with E2 E3,
        cases E3 with T E4,
        cases E4 with E5 E6,
        have E7:X = (set.prod S set.univ) ∩ (set.prod set.univ T),
        {
          rw E6,
          rw set.prod_inter_prod,
          simp,
        },
        subst X,
        apply topological_space.generate_open.inter;apply topological_space.generate_open.basic,
        {
          left,
          apply exists.intro S,
          split,
          {
            exact E2,
          },
          {
            unfold set.prod,
            simp,refl,
          }
        },
        {
          right,
          apply exists.intro T,
          split,
          {
            exact E5,
          },
          {
            unfold set.prod,
            simp,refl,
          }
        }
      }
    }
  },
end

