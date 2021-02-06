import order.complete_lattice


lemma le_supr'' {α : Type*} {ι : Sort*} [_inst_1 : complete_lattice α] (s : ι → α) (i : ι) (x:α):
  (x ≤ s i) → x ≤ supr s :=
begin
  intro A1,
  apply le_trans A1,
  apply le_supr,
end 


lemma infi_prop_def {α:Type*} [complete_lattice α]
    {v:α} {P:Prop} (H:P):(⨅ (H2:P), v) = v :=
begin
  apply le_antisymm,
  { apply infi_le, apply H },
  { apply @le_infi, intro A1, apply le_refl v },
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

lemma infi_le_trans {α β:Type*} [complete_lattice β] (a:α) (f:α → β) 
    (b:β):(f a ≤ b) → (⨅ (c:α), (f c)) ≤ b :=
begin
  intros A1,
  apply le_trans _ A1,
  apply @infi_le _ _ _, 
end

/-
  I saw this pattern a bunch below. It could be more widely used.
 -/
lemma infi_set_le_trans {α β:Type*} [complete_lattice β] (a:α) (P:α → Prop) (f:α → β) 
    (b:β):(P a) → (f a ≤ b) → (⨅ (c:α) (H:P c), f c) ≤ b :=
begin
  intros A1 A2,
  apply infi_le_trans a,
  rw infi_prop_def A1,
  apply A2,
end

lemma infi_set_image {α β γ:Type*} [complete_lattice γ] (S:set α) (f:α → β) 
    (g:β → γ):(⨅ (c∈ (f '' S)), g c) = ⨅  (a∈ S), (g ∘ f) a :=
begin
  apply le_antisymm;simp,
  {
    intros a B1,
    apply infi_le_trans (f a),
    apply infi_le_trans a,
    rw infi_prop_def,
    apply and.intro B1,
    refl,
  },
  {
    intros b h_b,
    apply infi_le_of_le b,
    apply infi_le_of_le h_b,
    apply le_refl,
  },
end
