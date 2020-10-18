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


lemma infi_le'' {α : Type*} {ι : Sort*} [_inst_1 : complete_lattice α] (s : ι → α) (i : ι) (x:α):
  (s i ≤ x) → infi s ≤ x :=
begin
  intro A1,
  apply le_trans _ A1,
  apply infi_le,
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

