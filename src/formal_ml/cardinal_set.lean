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
import data.finset
import topology.metric_space.basic
import formal_ml.finset
import set_theory.cardinal_ordinal


namespace set


def prod_equiv_mul {α β:Type*} (s:set α) (t:set β):
  (s.prod t) ≃ s × t := {
  to_fun := (λ p, (subtype.mk p.val.fst p.property.left, subtype.mk p.val.snd p.property.right) ),
  inv_fun := (λ p, subtype.mk (p.fst.val, p.snd.val) (set.mk_mem_prod p.fst.property 
    p.snd.property)) ,
  left_inv :=
  begin
     simp [function.left_inverse],
  end,
  right_inv :=
  begin
    simp [function.right_inverse, function.left_inverse],
  end,
}

lemma mem_of_mem_union_of_not_mem_left {α:Type*} {s:set α} {t:set α} {a:α} (h : a ∉ s)
  (hu : a ∈ s ∪ t) : (a ∈ t) :=
begin
  simp [h] at hu,
  apply hu,
end

noncomputable def disjoint_union_equiv_add {α:Type*} (s:set α) (t:set α) (h:disjoint s t):
  (s ∪ t:set α) ≃ s ⊕ t := {
  to_fun := (λ a, (@dite (a.val ∈ s) (classical.prop_decidable _) (s ⊕ t)  
   (λ h,  sum.inl (subtype.mk  a.val  h) ) (λ h, sum.inr (subtype.mk a.val
     (set.mem_of_mem_union_of_not_mem_left h a.property))))), 
  inv_fun := (λ a, match a with
  | sum.inl b := subtype.mk b.val (set.mem_union_left t b.property)
  | sum.inr b := subtype.mk b.val (set.mem_union_right s b.property)
  end),
  left_inv :=
  begin
     simp [function.left_inverse],
     intros x h2,
     cases h2,
     simp [h2],
     refl,
     have h3 : x ∉ s := (set.disjoint_right.mp h) h2,
     simp [h3],
     refl,
  end,
  right_inv :=
  begin
    simp [function.right_inverse, function.left_inverse],
    split,
    intros x h2,
    have A1:(disjoint_union_equiv_add._match_1 s t (sum.inl (subtype.mk x h2))).val = x,
    { refl },
    simp [A1,h2], refl,
    intros x h2,
    have A2:(disjoint_union_equiv_add._match_1 s t (sum.inr (subtype.mk x h2))).val = x := rfl,
    have A3:(disjoint_union_equiv_add._match_1 s t (sum.inr (subtype.mk x h2))).val ∉ s,
    { rw A2, apply (set.disjoint_right.mp h) h2},
    simp [A2, A3, h2],
    refl,
  end,
}



def card {α:Type*} (s:set α):cardinal :=
  cardinal.mk s

lemma card_def {α:Type*} (s:set α):s.card = cardinal.mk s := rfl

lemma card_prod {α β:Type*} (s:set α) (t:set β):
 (s.prod t).card = s.card * t.card :=
begin
  unfold set.card,
  rw cardinal.mul_def,
  rw cardinal.eq,
  apply nonempty.intro,
  apply set.prod_equiv_mul,  
end

lemma card_union {α:Type*} (s:set α) (t:set α) (h:disjoint s t):
  ((s ∪ t).card) = (s.card + t.card) :=
begin
  have A1:(s.card + t.card) = (cardinal.mk (s ⊕ t)),
  { unfold set.card,  refl },
  rw A1,
  unfold set.card,
  rw cardinal.eq,
  apply nonempty.intro,
  apply disjoint_union_equiv_add s t h,
end

@[simp]
lemma card_empty (α:Type*):
  (∅:set α).card = 0 :=
begin
  unfold set.card,
  simp,
end

@[simp]
lemma card_singleton' (α:Type*) {a:α}:
  ({a}:set α).card = 1 :=
begin
  unfold set.card,
  simp,
end

lemma card_insert' {α:Type*} (s:set α) (a:α) (h:a∉ s):
  (insert a s).card = s.card + 1 :=
begin
  rw set.insert_eq,
  rw card_union,
  rw card_singleton',
  rw add_comm,
  rw set.disjoint_left,
  intros b h2,
  simp at h2,
  subst b,
  apply h,
end

lemma disjoint_inter_diff {α : Type*} {s t : set α} : disjoint (t ∩ s) (t \ s) :=
begin
  rw set.disjoint_left, simp, intros a A2 A3 A4, apply A3
end

lemma card_add_card_diff {α : Type*} (s t : set α) : s.card + (t \ s).card = (s ∪ t).card :=
begin
  rw ← card_union,
  rw set.union_diff_self,
  apply set.disjoint_diff
end

lemma card_diff_add_card_inter {α : Type*} (s t : set α) : t.card = (t ∩ s).card + (t \ s).card :=
begin
  rw ← card_union,
  rw set.inter_union_diff,
  apply set.disjoint_inter_diff,
end

lemma card_union_inter {α : Type*} {s t : set α} :
  s.card + t.card = (s ∪ t).card + (s ∩ t).card :=
begin
  have A1 := card_diff_add_card_inter s t,
  rw add_comm at A1,
  rw A1,
  rw ← add_assoc,
  have A2 := card_add_card_diff s t,
  rw A2,
  rw set.inter_comm,
end

lemma card_subset {α:Type*} {s t : set α}  (h : s ⊆ t) : s.card ≤ t.card :=
begin
  rw card_diff_add_card_inter s t,
  rw set.inter_eq_self_of_subset_right h,
  have A2 : s.card + 0 ≤ s.card + (t \ s).card,
  { apply add_le_add, apply le_refl _, apply zero_le },
  rw add_zero at A2,
  apply A2
end

end set

lemma nat.Iio_zero_eq_empty:set.Iio 0 = ∅ :=
begin
  ext; split; simp
end

lemma nat.Iio_succ_eq_insert (n : ℕ) : set.Iio (n.succ) = insert n (set.Iio n) :=
begin
  ext; split; simp,
  { intros A1, 
    have A2:= nat.le_of_lt_succ A1,
    rw le_iff_lt_or_eq at A2,
    cases A2,
    { apply set.mem_insert_of_mem, apply A2 },
    cases A2,
    { apply set.mem_insert } },
  { intros A1,
    have A3 : n < nat.succ n :=  nat.lt_succ_of_le (le_refl _),
    cases A1,
    subst x, apply A3, apply lt_trans A1 A3, },
end

lemma nat.plus_one_eq_succ {n:ℕ} : (n:cardinal) + 1 = (n:cardinal).succ :=
begin
  apply le_antisymm,
  apply cardinal.add_one_le_succ,
  rw cardinal.succ_le,
  have A1:(1:cardinal) = ((1:ℕ):cardinal),
  {  simp  },
  rw A1,
  rw ← nat.cast_add,
  rw cardinal.nat_cast_lt,
  simp,
end

lemma nat.card_Iio (n : ℕ) : (set.Iio n).card = n :=
begin
  induction n,
  { rw nat.Iio_zero_eq_empty, simp },
  { rw nat.Iio_succ_eq_insert,
    have A1 : n_n ∉ (set.Iio n_n),
    { simp },
    rw set.card_insert' (set.Iio n_n) n_n A1, rw n_ih, simp,--rw ← nat.cast_succ,
    rw nat.plus_one_eq_succ },
end

lemma cardinal_eq_of_bijective {α β:Type*} (f:α → β) (h:function.bijective f) : (cardinal.mk α = cardinal.mk β) :=
begin
  haveI E := equiv.of_bijective f h,
  rw cardinal.eq,
  apply nonempty.intro E,  
end

lemma card_eq_of_bijective {α β : Type*} {s : set α} {t : set β} (f : s → t) (h : function.bijective f) : 
  (s.card = t.card) :=
begin
  unfold set.card,
  apply cardinal_eq_of_bijective f h
end

lemma map_card {α β:Type*} {f:α → β} {s:set α} (h_inj : function.injective f):
   (f '' s).card = s.card :=
begin
  let g:s → (f '' s) := (λ (x:s), subtype.mk (f x.val) begin 
    simp,
    apply exists.intro (x.val),
    apply and.intro (x.property),
    refl
  end),
  begin
    symmetry,
    apply card_eq_of_bijective g,
    { simp [g, function.bijective],
      split,
      intros a₁ a₂ A1A,
      simp at A1A,
      apply subtype.eq,
      apply h_inj,
      -- rw A0,
      apply A1A,
      intros x, have A1B := x.property,
      simp at A1B,
      cases A1B with y A1B, existsi  (subtype.mk y (A1B.left)),
      simp, apply subtype.eq, apply A1B.right, },
  end
end

@[simp]
lemma not_lt_refl (c:cardinal) :¬ (c < c)  :=
begin
  simp,
end

lemma equiv_inj {α β : Type*} {s : set α} {t : set β} : s.card = t.card → 0 < t.card →
  ∃ f:α → β, f '' s = t := 
begin
  intros A1 A2,
  have A3 : t ≠ ∅,
  { intro contra, rw contra at A2, simp at A2, apply A2 },
  unfold set.card at A1,
  rw cardinal.eq at A1,
  have A4 := classical.choice A1,
  rw set.ne_empty_iff_nonempty at A3,
  rw set.nonempty_def at A3,
  cases A3 with b A3,
  existsi (λ (a:α), @dite (a ∈ s) (classical.prop_decidable _) β 
   (λ h, A4.to_fun (subtype.mk a h)) 
   (λ h, b) ),  
  simp,
  ext,split; intros B1,
  simp at B1,
  cases B1 with a B1,
  cases B1 with B1 B2,
  subst x,
  rw dif_pos,
  simp,
  apply B1,
  simp,
  have B3 := (A4.inv_fun (subtype.mk x B1)).property,
  apply exists.intro (A4.inv_fun (subtype.mk x B1)).val,
  apply and.intro B3,
  rw dif_pos,
  simp,
  apply B3,
end

inductive set.finite' {α:Type*} : set α → Prop
| empty : set.finite' ∅
| insert (a:α) (s:set α) (hs:set.finite' s) : set.finite' (insert a s)

lemma finite'_of_eq_finset {α:Type*} (f : finset α) : ∀ (s:set α), (s = ↑f) → (s.finite') :=
begin
  haveI := classical.decidable_eq α,
  apply finset.induction_on f,
  { intros s A1, simp at A1, subst s,
    apply set.finite'.empty },
  { intros a s B1 B2 t B4, simp at B4,
    subst t, 
    apply set.finite'.insert a (↑s), apply B2, refl },
end

lemma finite'_of_finite {α:Type*} (s : set α) (h:s.finite) : (s.finite') :=
begin
  haveI := classical.decidable_eq α,
  unfold set.finite at h,
  haveI A1 := classical.choice h,
  have A2:s = ↑(finset.image subtype.val A1.elems),
  { ext; split; intros A2A, 
    { simp, apply exists.intro A2A, apply A1.complete },
    { simp at A2A, cases A2A with A2A A2B, apply A2A } },
  apply finite'_of_eq_finset _ s A2
end


def finset.attach' {α : Type*} [decidable_eq α] (s : finset α) (t : set α) (h : ↑s ⊆ t) : 
  finset t := (finset.image (λ (x : {x //  x∈ s}), subtype.mk (x.val) 
    (set.subset_def.mp h (x.val) x.property)) s.attach) 

noncomputable def fintype_of_insert {α: Type*} [decidable_eq α] (s : set α) (h : s.finite) 
  (a : α) : fintype (insert a s:set α) := {
  elems := (insert a h.to_finset).attach' (insert a s) begin
    rw set.subset_def,
    intros x A1,
    simp at A1,
    simp,
    apply A1, 
  end,
  complete :=
  begin
    intros x,
    simp [finset.attach', finset.attach],
    existsi x.val,
    split,
    apply subtype.eq,
    refl,    
    have A1 := x.property,
    simp at A1,
    simp [A1],
  end
}

lemma finite_of_finite' {α:Type*} (s : set α) (h:s.finite') : (s.finite) :=
begin
  haveI := classical.decidable_eq α,
  induction h,
  { simp },
  { unfold set.finite, apply nonempty.intro, 
    apply fintype_of_insert h_s h_ih h_a },
end

lemma nat_cardinal_of_finite' {α : Type*} (s : set α) (h : s.finite') : ∃ (n:ℕ), s.card = n :=
begin
  induction h,
  existsi 0,
  simp,
  cases h_ih with n h_ih,
  cases (classical.em (h_a ∈ h_s)) with A1 A1,
  apply exists.intro n,
  rw set.insert_eq_of_mem A1,
  apply h_ih,
  apply exists.intro n.succ,
  rw set.card_insert' _ _ A1,
  rw h_ih,
  rw nat.plus_one_eq_succ,
  simp,
end

lemma nat_cardinal_of_finite {α : Type*} (s : set α) (h : s.finite) : ∃ (n:ℕ), s.card = n :=
begin
  apply nat_cardinal_of_finite' s (finite'_of_finite s h)
end

lemma empty_iff_card_eq_zero {α : Type*} (s : set α) : (s.card = 0) ↔ s = ∅ :=
begin
  split; intros A1,
  { have A2 : (∅:set α).card = 0, 
    { simp },
    rw ← A1 at A2,
    unfold set.card at A2,
    
    rw cardinal.eq at A2,
    have A3 := classical.choice A2,
    rw ← set.subset_empty_iff,
    rw set.subset_def,
    intros x A4,
    have A5 := (A3.inv_fun (subtype.mk x A4)).property,
    exfalso,
    simp at A5,
    apply A5,
  },
  { subst s, simp }
end

def set.special_image {α β : Type*} (s : set α) (f : Π (a:α) , (a ∈ s) → β) : set β :=
  { b | ∃ (a:α) (h:a ∈ s), b = f a h }  


lemma set.mem_special_image {α β : Type*} (s : set α) (f : Π (a : α), (a ∈ s) → β) (a : α) (h : a ∈ s) :
  f a h ∈ (s.special_image f) :=
begin
  unfold set.special_image,
  rw set.mem_set_of_eq,
  existsi [a, h],
  refl,
end

lemma set.special_image_card {α β : Type*} (s : set α) (f : Π (a:α) , (a ∈ s) → β)  
  (h_inj : ∀ (a₁  a₂ : α) (h1 : a₁ ∈ s) (h2 : a₂ ∈ s), (f a₁ h1 = f a₂ h2) → (a₁ = a₂)) :
  (s.special_image f).card = s.card :=
begin
  unfold set.special_image, 
  let g : s → (s.special_image f) := (λ (a:s), subtype.mk (f a.val a.property) (set.mem_special_image s f a.val a.property)),
  begin
    symmetry,
    apply card_eq_of_bijective g,
    split,
    { intros a₁ a₂ A1,
      simp [g] at A1,
      apply subtype.eq,
      apply h_inj a₁ a₂ a₁.property a₂.property A1 },
    { intros b,
      have B1 := b.property,
      simp [set.special_image] at B1,
      cases B1 with a B1,
      cases B1 with h B1,
      existsi (subtype.mk a h),
      apply subtype.eq,
      simp [g, set.special_image],
      rw B1,
    }
  end
end

def set.attach {α : Type*} (s : set α) : (set s) :=
  s.special_image subtype.mk


lemma set.attach_complete {α : Type*} (s : set α)  (a : s) :
  a ∈ (set.attach s) :=
begin
  simp [set.attach, set.special_image],
  existsi [a.val, a.property],
  apply subtype.eq,
  simp,
end

lemma subtype.val_eq_val {α :Type*} {P : α → Prop} {a b : subtype P} (h : a = b) : a.val = b.val :=
begin
  rw h,
end

lemma set.attach_card {α : Type*} (s : set α) : (s.attach.card = s.card) :=
begin
  unfold set.attach,
  apply set.special_image_card,
  intros a₁ a₂ h1 h2 A1,
  apply subtype.val_eq_val A1,
end

lemma le_cardinal {α : Type*} {s:set α} {c:cardinal} :
  (c ≤ s.card) ↔ (∃ t:set α, t ⊆ s ∧ t.card = c) :=
begin
  rw set.card_def s,
  rw cardinal.le_mk_iff_exists_set,
  --have A2:(∃ (p : set ↥s), cardinal.mk ↥p = c) ↔ 
  split; intros A1; cases A1 with t A1,
  apply exists.intro ((λ (x:s), (x:α)) '' t),
  split,
  rw set.subset_def,
  intros x B1,
  simp at B1,
  cases B1 with B1 B2,
  apply B1,
  rw map_card,
  simp [set.card, A1],
  intros i j C1,
  apply subtype.eq,
  simp at C1,
  apply C1,
  apply exists.intro (t.special_image (λ (a:α) (h:a ∈ t), 
    @subtype.mk α (λ a, a ∈ s) a ((@set.subset_def α t s).mp A1.left a h))),
  cases A1 with A1 A2,
  subst c,
  rw ← set.card_def,
  rw set.special_image_card,
  intros a₁ a₂ h1 h2 h3,
  have h4 := subtype.val_eq_val h3,
  simp at h4,
  apply h4,
end 

lemma not_is_some {α : Type*} {a : option α} : (¬(option.is_some a)) ↔ (a = none) :=
begin
  cases a;simp [option.is_some],
end 

lemma card_finite_add_one {α β : Type*} {s : set α} {t : set β} (h_finite : s.finite) 
(h_card : t.card = s.card + 1) :
  (∃ (a : β) (s' : set β), t = insert a s' ∧ (a ∉ s') ∧ s'.card = s.card) :=
begin
  have A1 : cardinal.mk (option s) = t.card,
  { rw h_card, rw cardinal.mk_option, refl },
  unfold set.card at A1,
  rw cardinal.eq at A1,
  have A2 := classical.choice A1,
  existsi [(A2.to_fun option.none).val, ((λ (a:s), (A2.to_fun (option.some a)).val) '' (s.attach))],
  split,
  ext, split; intros A3,
  simp,
  have A4 := A2.right_inv (subtype.mk x A3),
  cases (classical.em (option.is_some (A2.inv_fun (subtype.mk x A3)))) with A5 A5,
  { right, existsi [(option.get A5).val, (option.get A5).property], split, apply set.attach_complete,
    simp },
  { left, rw not_is_some at A5, rw A5 at A4, have A6 := subtype.val_eq_val A4, simp at A6, rw A6 },
  simp at A3,
  cases A3,
  { subst x, apply (A2 none).property },
  { cases A3 with y A3, cases A3 with A3 A4, cases A4 with A4 A5,
    subst x, apply (A2 (some (subtype.mk y A3))).property, },
  simp,
  split,
  intros x D1 D2,
  cases D2 with D2 D3,
  have D4 := A2.injective,
  have D5 := subtype.eq D3,
  have D6 := A2.injective (subtype.eq D3),
  simp at D6,
  apply D6,
  rw map_card,
  apply set.attach_card,
  intros a₁ a₂ E1,
  simp at E1,
  have E2 := A2.injective (subtype.eq E1),
  simp at E2,
  apply E2,
end

lemma finite'_of_nat_cardinal {α : Type*} (n : ℕ) : ∀ (s : set α), (s.card = n) →
  (s.finite') :=
begin
  induction n,
  { intros s A1,
    simp at A1, rw empty_iff_card_eq_zero at A1, subst s, apply finite'.empty },
  { intros t B1, simp at B1, rw ← nat.plus_one_eq_succ at B1, 
    have B2 : ↑n_n ≤ t.card,
    { rw B1, 
      have B2A : (n_n:cardinal) + 0 ≤ (n_n:cardinal) + 1, 
      { apply add_le_add (le_refl _), simp },
      rw add_zero at B2A,
      apply B2A }, 
    rw le_cardinal at B2,
    cases B2 with u B2,
    cases B2 with B2 B3,
    have B4 := n_ih u B3,
    have B5 := finite_of_finite' u B4,
    rw  ← B3 at B1,
    have B6 := card_finite_add_one B5 B1,
    
    --have B6 := card_finite_add_one B2 B5 B1,
    cases B6 with a B6,
    cases B6 with s' B6,
    cases B6 with B6 B7,
    cases B7 with B7 B8,
    rw B3 at B8,
    have B9 := n_ih s' B8,
    subst t,
    apply finite'.insert a s' B9 },
end

lemma finite_of_nat_cardinal {α : Type*} (n : ℕ) (s : set α) (h : s.card = n) :
  (s.finite) :=
begin
  have A1 := finite'_of_nat_cardinal n s h,
  apply finite_of_finite' s A1,
end




lemma set.finite_insert {α:Type*} {s:set α} (a:α) (h:s.finite) : (insert a s).finite :=
begin
  haveI D : decidable_eq α := classical.decidable_eq α, 
  cases (classical.em (a ∈ s)) with A1 A1,
  { have A2 : insert a s = s := set.insert_eq_of_mem A1, rw A2, 
    apply h },
  { haveI Fs : fintype s := classical.choice h,
    haveI Fas : fintype (insert a s:set α) := set.fintype_insert' s A1,
    apply nonempty.intro Fas },
end

/-
lemma card_add_one {α : Type*} {β : Type*} {s : set α} {t : set β}  
(h : t.card = s.card + 1) :
  (∃ (b : β) (f : s → (t \ {b} : set β)), function.bijective f) :=
begin
  sorry
end
-/

