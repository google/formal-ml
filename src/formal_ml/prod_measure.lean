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
import measure_theory.measurable_space

import measure_theory.measure_space
import measure_theory.outer_measure
import measure_theory.lebesgue_measure
import measure_theory.integration

import measure_theory.borel_space
import data.set.countable
import formal_ml.nnreal
import formal_ml.ennreal
import formal_ml.sum
import formal_ml.lattice
import formal_ml.measurable_space
import formal_ml.classical
import formal_ml.core
import formal_ml.characteristic
import formal_ml.measure
import data.equiv.list


noncomputable def prod.outer_measure {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.outer_measure α) (μβ:measure_theory.outer_measure β):measure_theory.outer_measure (α × β) := 
  measure_theory.outer_measure.of_function
  (λ P:set (α × β), μα (prod.fst '' P) * μβ (prod.snd '' P))
begin
  simp,
end 

noncomputable def prod.measure {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.measure α) (μβ:measure_theory.measure β):measure_theory.measure (α × β) := 
  (prod.outer_measure μα.to_outer_measure μβ.to_outer_measure).to_measure 
begin
  unfold prod.measurable_space,
  simp,
  split;
  intros P A1;
  unfold measurable_space.comap at A1;
  cases A1 with s A1;
  cases A1 with A1 A2;
  subst P;
  apply measure_theory.outer_measure.of_function_caratheodory;
  simp,
  {intros t,
   have B1:μα (prod.fst '' t ∩ s) + μα (prod.fst '' t \ s) = μα (prod.fst '' t),
   {rw ← measure_theory.measure_eq_inter_diff', apply A1},
   rw ← B1,
   clear B1,
   rw right_distrib,
   apply @add_le_add ennreal _;apply ennreal.mul_le_mul;try {apply measure_theory.measure_mono};simp;rw set.subset_def;
   intros p B2;cases p;simp at B2;simp [B2];
   try {apply exists.intro p_snd,simp [B2]};
   {apply exists.intro p_fst,simp [B2]}},
  {intros t,
   have B1:μβ (prod.snd '' t ∩ s) + μβ (prod.snd '' t \ s) = μβ (prod.snd '' t),
   {rw ← measure_theory.measure_eq_inter_diff', apply A1},
   rw ← B1,
   clear B1,
   rw left_distrib,
   apply @add_le_add ennreal _;apply ennreal.mul_le_mul;try {apply measure_theory.measure_mono};simp;rw set.subset_def;
   intros p B2;cases p;simp at B2;simp [B2];
   try {apply exists.intro p_snd,simp [B2]};
   {apply exists.intro p_fst,simp [B2]}},
end

@[simp]
lemma set.prod_fst_image_of_prod {α:Type*} {β:Type*} (A:set α) (B:set β) (h:B.nonempty):(prod.fst '' (A.prod B)) = A :=
begin
  ext p;split;intros A1,
  simp at A1,simp [A1],
  simp [A1],
  apply h,
end

@[simp]
lemma set.prod_snd_image_of_prod {α:Type*} {β:Type*} (A:set α) (B:set β) (h:A.nonempty):(prod.snd '' (A.prod B)) = B :=
begin
  ext p;split;intros A1,
  simp at A1,simp [A1],
  simp [A1],
  apply h,
end

lemma prod.outer_measure.Inf_sum {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.outer_measure α) (μβ:measure_theory.outer_measure β) {P:set (α × β)}:
  prod.outer_measure μα μβ P = 
  ⨅ (f:ℕ → set α) (g:ℕ → set β) (h₁: P ⊆ ⋃ n, (f n).prod (g n)), ∑' n, μα (f n) * μβ (g n) :=
begin
  unfold prod.outer_measure measure_theory.outer_measure.of_function,
  rw ← measure_theory.outer_measure.measure_of_eq_coe,
  simp,
  apply le_antisymm,
  simp,
  intros f g B1,
  apply @infi_le_of_le ennreal  _ _ _ _ (λ (n:ℕ), (f n).prod (g n)),
  apply @infi_le_of_le ennreal  _ _ _ _ _,
  apply ennreal.tsum_le_tsum,
  intros a,
  cases (set.eq_empty_or_nonempty (f a)) with B2 B2,
  {simp [B2]},
  cases (set.eq_empty_or_nonempty (g a)) with B3 B3,
  {simp [B3]},
  {simp [B2,B3,le_refl]},
  {simp [B1]},
  simp,
  intros h C1,
  apply @infi_le_of_le ennreal _ _ _ _ (λ n, prod.fst '' (h n)),
  apply @infi_le_of_le ennreal _ _ _ _ (λ n, prod.snd '' (h n)),
  apply @infi_le_of_le ennreal  _ _ _ _ _,
  simp,
  apply le_refl _,
  simp,
  apply @set.subset.trans (α × β) P (set.Union h) (⋃ (n : ℕ), (prod.fst '' h n).prod (prod.snd '' h n)) C1,
  apply set.Union_subset_Union,
  intro i,
  rw set.subset_def,
  intros a C2,cases a,simp,
  apply and.intro (exists.intro a_snd C2) (exists.intro a_fst C2),
end

lemma set.prod_subset_prod {α:Type*} {β:Type*} {A A':set α} {B B':set β}:A ⊆ A' → B ⊆ B' →
A.prod B ⊆ A'.prod B' := begin
  intros hA hB,
  intros p hp,
  split,
  simp at hp,
  apply hA,
  apply hp.left,
  apply hB,
  apply hp.right,
end

lemma prod.outer_measure.Inf_sum2 {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.measure α) (μβ:measure_theory.measure β) {P:set (α × β)}:
  prod.outer_measure μα.to_outer_measure μβ.to_outer_measure P = 
  ⨅ (f:ℕ → set α) (g:ℕ → set β) 
    (h₁ : ∀ n, measurable_set (f n)) 
    (h₂ : ∀ n, measurable_set (g n)) 
   (h₃: P ⊆ ⋃ n, (f n).prod (g n)), ∑' n, μα (f n) * μβ (g n) :=
begin
  rw prod.outer_measure.Inf_sum,
  apply le_antisymm,
  { simp,
    intros f g h₁ h₂ h₃,
    apply @infi_le_trans (ℕ→ set α) ennreal _ f,
    apply @infi_le_trans (ℕ→ set β) ennreal _ g,
    rw infi_prop_def,
    apply le_refl _,
    apply h₃ },
  { simp,
    intros f g h₃,
    have h4 := λ n, measure_theory.measurable_eq μα (f n),
    rw classical.skolem at h4,
    cases h4 with f' h4,
    have h5 := λ n, measure_theory.measurable_eq μβ (g n),
    rw classical.skolem at h5,
    cases h5 with g' h5,


    apply @infi_le_trans (ℕ→ set α) ennreal _ f',
    apply @infi_le_trans (ℕ→ set β) ennreal _ g',
    rw infi_prop_def,
    rw infi_prop_def,
    rw infi_prop_def,
    apply ennreal.tsum_le_tsum,
    intro n,
    rw (h4 n).right.left,
    rw (h5 n).right.left,
    apply le_refl _,
    apply @set.subset.trans _ P (⋃ (n : ℕ), (f n).prod (g n)) 
          (⋃ (n : ℕ), (f' n).prod (g' n)) h₃,
    apply set.Union_subset_Union,
    intro n,
    apply set.prod_subset_prod,
    apply (h4 n).right.right,
    apply (h5 n).right.right,
    { intro n, apply (h5 n).left },
    { intro n, apply (h4 n).left },
    },
 -- sorry
  
end


/-
  If we can make this into an equality, we're home free. 
  See https://www.math.ucdavis.edu/~hunter/measure_theory/measure_notes_ch5.pdf
  Those notes focus on measurable sets. We could theoretically do the same. However,
  it would make the rest of the analysis much more complex.
  I wonder if using an "outer measure lower integral" would make this useful. 
-/
lemma prod.outer_measure.apply_prod_le {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.outer_measure α) (μβ:measure_theory.outer_measure β) {A:set α} {B:set β}:
  prod.outer_measure μα μβ (A.prod B) ≤ μα A * μβ B :=
begin
  rw prod.outer_measure.Inf_sum,
  {apply @infi_le_of_le ennreal _ _ _ _ (λ (n:ℕ), ite (n = 0) A ∅),
  apply @infi_le_of_le ennreal _ _ _ _ (λ (n:ℕ), ite (n = 0) B ∅),
  apply @infi_le_of_le ennreal _ _ _ _ _,
  rw tsum_eq_single 0,
  {simp [le_refl]},
  intros b' B1,
  simp [B1],
  apply ennreal.t2_space,
  rw set.subset_def,
  intros p B2,
  simp,
  apply exists.intro 0,
  {simp at B2,simp [B2]}},
end

--measure_theory.lintegral_characteristic
/- The primary focus is on measures, instead of outer measures. This establishes an
    inequality when the sets are measurable and we are looking at a product of two 
    measures. -/
lemma prod.outer_measure.le_apply_prod {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.measure α) (μβ:measure_theory.measure β) {A:set α} {B:set β}:
  (measurable_set A) → (measurable_set B) →
  μα A * μβ B  ≤ prod.outer_measure μα.to_outer_measure μβ.to_outer_measure (A.prod B) :=
begin
  intros A4 A5,
  rw prod.outer_measure.Inf_sum2,
  simp,
  intros f g A2 A3 A1,
  have h2:(A.prod B).characteristic ≤ ∑' (n : ℕ), ((f n).prod (g n)).characteristic,
  { apply function.le_trans (set.characteristic.subset A1),
    apply set.characteristic.Union,
     },
  have h3:∀ (a:α) (b:β), (A.characteristic a) * (B.characteristic b)  ≤ 
          ∑' (n : ℕ), ((f n).characteristic a * (g n).characteristic b),
  { intros a b,
    rw ← set.characteristic.prod,
    have h3a: (λ n, ((f n).characteristic a * (g n).characteristic b)) =
              (λ n, ((f n).prod (g n)).characteristic (a, b)),
    { ext n, rw set.characteristic.prod },
    rw h3a,
    have h3b:((∑' (n : ℕ), ((f n).prod (g n)).characteristic) (a, b)) =
        (∑' (n : ℕ), ((f n).prod (g n)).characteristic (a, b)) ,
    { apply ennreal.tsum_apply }, 
    rw ← h3b,
    apply h2 },
  have h4:∀ (b:β), measure_theory.lintegral μα  (λ a, A.characteristic a * (B.characteristic b))  ≤ measure_theory.lintegral μα (λ a, 
            ∑' (n : ℕ), ((f n).characteristic a) * (g n).characteristic b),
  { intro b,
    have h4a: ∀ (a:α), (A.characteristic a) * (B.characteristic b)  ≤ 
          ∑' (n : ℕ), ((f n).characteristic a * (g n).characteristic b),
    { intro a, apply h3 },
    apply measure_theory.lintegral_mono, apply h4a },
  have h5:∀ (b:β), μα A * (B.characteristic b)  ≤ 
            ∑' (n : ℕ), ((μα (f n)) * (g n).characteristic b),
  { intro b,
    have h5a := h4 b,
    rw measure_theory.lintegral_mul_const at h5a,
    rw measure_theory.lintegral_characteristic at h5a,

    rw measure_theory.lintegral_tsum at h5a,
    have h5b : (λ i, (∫⁻ (a : α), (f i).characteristic a * (g i).characteristic b ∂μα)) =
               (λ i, μα (f i) * (g i).characteristic b),
    { ext1 i,
      rw measure_theory.lintegral_mul_const,
      --rw set.characteristic_integral,
      rw measure_theory.lintegral_characteristic,
      apply A2,
      apply measurable.characteristic,
      apply A2 },
    rw h5b at h5a,
      apply h5a,
    { intro i, apply measurable.ennreal_mul,
      apply measurable.characteristic,
      apply A2,
      apply measurable_const },
    { apply A4 },
    { apply measurable.characteristic, apply A4 } },
  have h6:∫⁻ (b : β),   (μα A) * B.characteristic b ∂μβ ≤
          ∫⁻ (b : β), ( ∑' (n : ℕ), (μα (f n)) * (g n).characteristic b)  ∂μβ,
  { apply measure_theory.lintegral_mono,
    apply h5, },
  rw measure_theory.lintegral_const_mul at h6,
  rw measure_theory.lintegral_characteristic at h6, -- set.characteristic_integral at h6,
  rw measure_theory.lintegral_tsum at h6,
  have h7: (λ i, ∫⁻ (b : β), μα (f i) * (g i).characteristic b ∂μβ) =
           (λ i,  μα (f i) *  μβ (g i)),
  {  ext1 i,
     rw measure_theory.lintegral_const_mul,
     rw measure_theory.lintegral_characteristic, -- set.characteristic_integral,
     apply A3, apply measurable.characteristic,
     apply A3 },
  rw h7 at h6,
  apply h6,
  { intro i, apply measurable.ennreal_mul,
    apply measurable_const,
    apply measurable.characteristic,
    apply A3 },
  { apply A5 },
  { apply measurable.characteristic, apply A5 },
end





lemma prod.measure_apply {α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.measure α) (μβ:measure_theory.measure β) (S:set (α × β)):measurable_set S →
  prod.measure μα μβ S = 
  prod.outer_measure μα.to_outer_measure μβ.to_outer_measure S :=
begin
  intro h,
  simp [prod.measure],
  rw measure_theory.to_measure_apply,
  apply h,
end

lemma prod.measure.apply_prod
{α:Type*} {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β] 
  (μα:measure_theory.measure α) (μβ:measure_theory.measure β) (A:set α) (B:set β):measurable_set A →
  measurable_set B → 
  (prod.measure μα μβ) (A.prod B) = (μα A) * (μβ B)  :=
begin
  intros A1 A2,
  rw prod.measure_apply,
  apply le_antisymm,
  { apply prod.outer_measure.apply_prod_le,
     },
  apply prod.outer_measure.le_apply_prod,
  apply A1,
  apply A2,
  apply measurable_set.prod A1 A2,
end
