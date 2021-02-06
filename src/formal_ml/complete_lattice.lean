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
import order.complete_lattice
import order.basic



lemma Sup_image_le {α β:Type*} [complete_lattice β] {f:α → β} {S:set α} {x:β}:
  (∀ s∈ S, f s ≤ x) → (Sup (f '' S)≤ x) :=
begin
  intro A1,
  apply Sup_le,
  intros b A2,
  cases A2 with a A2,
  rw ← A2.right,
  apply (A1 a A2.left),
end

lemma le_Sup_image {α β:Type*} [complete_lattice β] {f:α → β} {S:set α} {a:α}:
  (a∈ S) →
  (f a) ≤ Sup (f '' S) :=
begin
  intro A1,
  apply le_Sup,
  simp,
  apply exists.intro a,
  split,
  apply A1,
  refl,
end

lemma Sup_Sup_image_image_le {α β γ:Type*} [complete_lattice γ] {f:α → β → γ} {S:set α}
    {T:set β} {x:γ}:
    (∀ a∈ S, ∀ b∈T, f a b ≤ x) →
    (Sup ((λ a:α, Sup  ((f a) '' T)) '' S) ≤ x) :=
begin
  intro A1,
  apply Sup_image_le,
  intros a A2,
  apply Sup_image_le,
  intros b A3,
  apply A1 a A2 b A3,
end

lemma le_Sup_Sup_image_image {α β γ:Type*} [complete_lattice γ] {f:α → β → γ} 
    {S:set α} {T:set β} {a:α} {b:β}:
    (a∈ S) → (b∈ T) → 
    (f a b) ≤ (Sup ((λ a:α, Sup  ((f a) '' T)) '' S)) :=
begin
  intros A1 A2,
  apply le_trans,
  apply @le_Sup_image β γ _ (f a) T b A2,
  apply @le_Sup_image α γ _ ((λ a:α, Sup  ((f a) '' T))) S a A1,
end

lemma Sup_le_Sup_of_monotone {α β:Type*} [complete_lattice α]
    [complete_lattice β] 
    {f:α → β} {s:set α}:
   (monotone f) →
    Sup (f '' s) ≤ f (Sup s) :=
begin
  intro A1,
  apply Sup_le,
  intros b A2,
  simp at A2,
  cases A2 with x A2,
  cases A2 with A2 A3,
  subst b,
  apply A1,
  apply le_Sup,
  apply A2,
end

lemma supr_le_supr_of_monotone {α β γ:Type*} [complete_lattice α]
    [complete_lattice β] 
    {f:α → β} {g:γ → α}:
   (monotone f) →
    supr (f ∘ g) ≤ f (supr g) :=
begin
  intro A1,
  apply Sup_le,
  intros b A2,
  simp at A2,
  cases A2 with x A2,
  subst b,
  apply A1,
  apply le_Sup,
  simp,
end

lemma infi_le_infi_of_monotone {α β γ:Type*} [complete_lattice α]
    [complete_lattice β] 
    {f:α → β} {g:γ → α}:
   (monotone f) →
     f (infi g) ≤ infi (f ∘ g) :=
begin
  intro A1,
  apply le_infi,
  intros b,
  apply A1,
  apply infi_le,
end

lemma Inf_le_Inf_of_monotone {α β:Type*} [complete_lattice α]
    [complete_lattice β] 
    {f:α → β} {s:set α}:
   (monotone f) →
     f (Inf s) ≤ Inf (f '' s) :=
begin
  intro A1,
  apply le_Inf,
  intros b A2,
  simp at A2,
  cases A2 with b' A2,
  cases A2 with A2 A3,
  subst b,
  apply A1,
  apply Inf_le,
  apply A2,
end


lemma supr_prop_def {α:Type*} [complete_lattice α]
    {v:α} {P:Prop} (H:P):(⨆ (H2:P), v) = v :=
begin
  apply le_antisymm,
  {
    apply supr_le,
    intro A1,
    apply le_refl v,
  },
  {
    apply @le_supr α P _ (λ H2:P, v),
    apply H,
  },
end

lemma infi_prop_def {α:Type*} [complete_lattice α]
    {v:α} {P:Prop} (H:P):(⨅ (H2:P), v) = v :=
begin
  apply le_antisymm,
  {
    apply infi_le,
    apply H,
  },
  {
    apply @le_infi,
    intro A1,
    apply le_refl v,
  },
end


lemma supr_prop_false {α:Type*} [complete_lattice α]
    {v:α} {P:Prop} (H:¬P):(⨆ (H2:P), v) = ⊥ :=
begin
  apply le_antisymm,
  {
    apply supr_le,
    intro A1,
    exfalso,
    apply H,
    apply A1,
  },
  {
    apply bot_le,
  },
end

lemma infi_prop_false {α:Type*} [complete_lattice α]
    {v:α} {P:Prop} (H:¬P):(⨅ (H2:P), v) = ⊤ :=
begin
  apply le_antisymm,
  {
    apply le_top,
  },
  {
    apply le_infi,
    intro A1,
    exfalso,
    apply H,
    apply A1,
  },
end
