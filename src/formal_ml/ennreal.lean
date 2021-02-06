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
import data.real.ennreal
import formal_ml.nat
import formal_ml.nnreal
import formal_ml.with_top
import formal_ml.lattice

-- ennreal is a canonically_ordered_add_monoid
-- ennreal is not a decidable_linear_ordered_semiring
-- Otherwise (0 < c) → (c * a) ≤ (c * b) → (a ≤ b),
-- but this does not hold for c =⊤, a = 1, b = 0. 
-- This is because ennreal is not an ordered_cancel_add_comm_monoid.
-- Nor is it an ordered_cancel_comm_monoid
-- This implies it is also not an ordered_semiring



lemma ennreal_coe_eq_lift {a:ennreal} {b:nnreal}:a = b → (a.to_nnreal = b) :=
begin
  intro A1,
  have A2:(a.to_nnreal)=(b:ennreal).to_nnreal,
  {
    rw A1,
  },
  rw ennreal.to_nnreal_coe at A2,
  exact A2,
end

/-
  This is one of those complicated inequalities that is probably too rare to justify a
  lemma. However, since it shows up, we give it the canonical name and move on.
-/
lemma ennreal_le_to_nnreal_of_ennreal_le_of_ne_top {a:nnreal} {b:ennreal}:
    b≠ ⊤ → (a:ennreal) ≤ b → (a ≤ b.to_nnreal) :=
begin
  intros A1 A2,
  cases b,
  {
    simp at A1,
    exfalso,
    apply A1,
  },
  {
    have A3:(b:ennreal) = (some b) := rfl,
    rw ← A3,
    rw (@ennreal.to_nnreal_coe b),
    rw ← ennreal.coe_le_coe,
    rw A3,
    apply A2,
  }
end


lemma ennreal_add_monoid_smul_def{n:ℕ} {c:ennreal}: n •ℕ c = ↑(n) * c := 
begin
  induction n,
  {
    simp,
  },
  {
    simp,
  }
end


lemma ennreal_lt_add_ennreal_one (x:nnreal):(x:ennreal) < (1:ennreal) + (x:ennreal) :=
begin
  apply ennreal.coe_lt_coe.mpr,
  simp,
  apply canonically_ordered_semiring.zero_lt_one,
end

lemma ennreal.infi_le {α:Sort*} {f:α → ennreal} {b : ennreal}:
   (∀ (ε : nnreal), 0 < ε → b < ⊤ → (∃a, f a  ≤ b + ↑ε)) → infi f ≤ b :=
begin
  intro A1,
  apply @ennreal.le_of_forall_pos_le_add,
  intros ε A2 A3,
  have A4 := A1 ε A2 A3,
  cases A4 with a A4,
  apply le_trans _ A4,
  apply @infi_le ennreal _ _,
end

lemma ennreal.forall_epsilon_le_iff_le : ∀{a b : ennreal}, (∀ε:nnreal, 0 < ε → b < ⊤ → a ≤ b + ε) ↔ a ≤ b :=
begin
  intros a b,
  split,
  apply ennreal.le_of_forall_pos_le_add, 
  intros A1 ε B1 B2,
  apply le_add_right A1,
end

lemma ennreal.lt_of_add_le_of_pos {x y z:ennreal}:x + y ≤ z → 0 < y → x < ⊤ → x < z :=
begin
  cases x;cases y;cases z;try {simp},
  {repeat {rw ← ennreal.coe_add},rw ennreal.coe_le_coe,apply nnreal.lt_of_add_le_of_pos},
end

lemma ennreal.iff_infi_le {α:Sort*} {f:α → ennreal} {b : ennreal}:
   (∀ (ε : nnreal), 0 < ε → b < ⊤ → (∃a, f a  ≤ b + ↑ε)) ↔ infi f ≤ b :=
begin
  --intro A1,
  --rw ← @ennreal.forall_epsilon_le_iff_le (infi f) b,
  split,
  apply ennreal.infi_le,
  intro A1,
  intros ε A2 A3,
  apply classical.by_contradiction,
  intro A4,
  apply not_lt_of_ge A1,
  have A5:b + ↑ε ≤ infi f,
  { apply @le_infi ennreal _ _, intro a,
    have A5:=(forall_not_of_not_exists A4) a,
    simp at A5,
    apply le_of_lt A5,
  },
  apply ennreal.lt_of_add_le_of_pos A5,
  simp,apply A2,
  apply A3,
end

lemma ennreal.exists_le_infi_add {α:Type*} (f:α → ennreal) [N:nonempty α] {ε:nnreal}:0 < ε → (∃ a, f a ≤ infi f + ε) :=
begin
  intros A1,
  have A2:infi f ≤ infi f,
  {apply le_refl _},
  rw ← ennreal.iff_infi_le at A2,
  cases (decidable.em (infi f < ⊤)) with A3 A3,
  apply A2 ε  A1 A3,
  simp only [not_lt, top_le_iff] at A3,
  --cases N,
  have a := classical.choice N,
  apply exists.intro a,
  rw A3,
  simp,
end


lemma ennreal.le_supr {α:Type*} {f:α → ennreal} {b : ennreal}:(∀ (ε : nnreal), 0 < ε → (supr f < ⊤) → (∃a,  b ≤ f a + ε)) → b ≤ supr f :=
begin
  intro A1,
  apply @ennreal.le_of_forall_pos_le_add,
  intros ε A2 A3,
  have A4 := A1 ε A2 A3,
  cases A4 with a A4,
  apply le_trans A4,
  have A5:=@le_supr ennreal _ _ f a,
  apply add_le_add A5,
  apply le_refl _, 
end

/-This isn't true. Specifically, for any non-finite sets, one can construct a counterexample.
  Using ℕ as an example, f:ℕ → ℕ → ennreal := λ a b, if (a < b) then 1 else 0.
lemma ennreal.supr_infi_eq_infi_supr {α β:Type*} [nonempty α] [nonempty β] [partial_order β] {f:α → β → ennreal}:(∀ a:α, monotone (f a)) →
  (⨅ (a:α), ⨆ (b:β), f a b )= ( ⨆ (b:β), ⨅ (a:α), f a b) :=
begin

 -/

lemma ennreal.not_add_le_of_lt_of_lt_top {a b:ennreal}:
   (0 < b) → (a < ⊤) → ¬(a + b) ≤ a :=
begin
  intros A1 A2 A3,
  have A4:(⊤:ennreal) = none := rfl,
  cases a,
  {
    simp at A2,
    apply A2,
  },
  cases b,
  {
    rw ←A4 at A3,
    rw with_top.add_top at A3,
    rw top_le_iff at A3,
    simp at A3,
    apply A3,
  },
  simp at A3,
  rw ← ennreal.coe_add at A3,
  rw ennreal.coe_le_coe at A3,
  simp at A1,
  apply nnreal.not_add_le_of_lt A1,
  apply A3,
end


lemma ennreal.lt_add_of_pos_of_lt_top {a b:ennreal}:
   (0 < b) → (a < ⊤) → a < a + b :=
begin
  intros A1 A2,
  apply lt_of_not_ge,
  apply ennreal.not_add_le_of_lt_of_lt_top A1 A2,
end

lemma ennreal.infi_elim {α:Sort*} {f:α → ennreal} {ε:nnreal}:
   (0 < ε) → (infi f < ⊤) → (∃a, f a  ≤ infi f + ↑ε) :=
begin
  intros A1 A2,
  have A3:¬(infi f+(ε:ennreal)≤ infi f),
  {
    apply ennreal.not_add_le_of_lt_of_lt_top _ A2,
    simp,
    apply A1,
  },
  apply (@classical.exists_of_not_forall_not α (λ (a  : α), f a ≤ infi f + ↑ε)),
  intro A4,
  apply A3,
  apply @le_infi ennreal α _,
  intro a,
  cases  (le_total (infi f + ↑ε) (f a)) with A5 A5,
  apply A5,
  have A6 := A4 a,
  exfalso,
  apply A6,
  apply A5,
end


lemma ennreal.zero_le {a:ennreal}:0 ≤ a :=
begin
  simp,
end


lemma ennreal.sub_top {a:ennreal}:a - ⊤ = 0 :=
begin
  simp,
end


lemma ennreal.sub_lt_of_pos_of_pos {a b:ennreal}:(0 < a) → 
    (0 < b) → (a ≠ ⊤) → (a - b) < a :=
begin
  intros A1 A2 A3,
  cases a,
  {
    exfalso,
    simp at A3,
    apply A3,
  },
  cases b,
  {
    rw ennreal.none_eq_top,
    rw ennreal.sub_top,
    apply A1,  
  },
  simp,
  rw ← ennreal.coe_sub,
  rw ennreal.coe_lt_coe,
  apply nnreal.sub_lt_of_pos_of_pos,
  {
    simp at A1,
    apply A1,
  },
  {
    simp at A2,
    apply A2,
  },
end

lemma ennreal.Sup_elim {S:set ennreal} {ε:nnreal}:
   (0 < ε) → (S.nonempty)  → (Sup S ≠ ⊤) → (∃s∈S, (Sup S) - ε ≤ s) :=
begin
  intros A1 A2 A3,
  cases classical.em (Sup S = 0) with A4 A4,
  {
    rw A4,
    have A5:= set.nonempty_def.mp A2,
    cases A5 with s A5,
    apply exists.intro s,
    apply exists.intro A5,
    simp,
  },
  have A5:(0:ennreal) = ⊥ := rfl,
  have B1:(Sup S) - ε < (Sup S),
  {
    apply ennreal.sub_lt_of_pos_of_pos,
    rw A5,
    rw bot_lt_iff_ne_bot,
    rw ← A5,
    apply A4,
    simp,
    apply A1,
    apply A3,
  },
  rw lt_Sup_iff at B1,
  cases B1 with a B1,
  cases B1 with B2 B3,
  apply exists.intro a,
  apply exists.intro B2,
  apply le_of_lt B3,
end

lemma ennreal.top_of_infi_top {α:Type*} {g:α → ennreal} {a:α}:((⨅ a', g a') = ⊤) → 
  (g a = ⊤) :=
begin
  intro A1,
  rw ← top_le_iff,
  rw ← A1,
  apply @infi_le ennreal α _,
end



lemma of_infi_lt_top {P:Prop} {H:P→ ennreal}:infi H < ⊤ → P :=
begin
  intro A1,
  cases (classical.em P) with A2 A2, 
  {
    apply A2,
  },
  {
    exfalso,
    unfold infi at A1,
    unfold set.range at A1,
    have A2:{x : ennreal | ∃ (y : P), H y = x}=∅,
    {
      ext;split;intro A2A,
      simp at A2A,
      exfalso,
      cases A2A with y A2A,
      apply A2,
      apply y,
      exfalso,
      apply A2A,
    },
    rw A2 at A1,
    simp at A1,
    apply A1,
  },
end

/-
lemma ennreal.add_le_add_left {a b c:ennreal}:
   b ≤ c → a + b ≤ a + c :=
begin
  intro A1,
  cases a,
  {
    simp,
  },
  cases b,
  {
    simp at A1,
    subst c,
    simp,
  },
  cases c,
  {
    simp,
  },
  simp,
  simp at A1,
  repeat {rw ← ennreal.coe_add},
  rw ennreal.coe_le_coe,
  apply @add_le_add_left nnreal _,
  apply A1,
end
-/

lemma ennreal.le_of_add_le_add_right 
    {a b c:ennreal}:(c < ⊤)→
   (a + c ≤ b + c) → (a ≤ b) :=
begin
  rw add_comm a c,
  rw add_comm b c,
  apply ennreal.le_of_add_le_add_left
end




lemma ennreal.le_add {a b c:ennreal}:a ≤ b → a ≤ b + c :=
begin
  intro A1,
  apply @le_add_of_le_of_nonneg ennreal _,
  apply A1,
  simp,
end


lemma ennreal.add_lt_add_of_lt_of_le_of_lt_top {a b c d:ennreal}:d < ⊤ → c ≤ d → a < b → a + c < b + d :=
begin
  intros A1 A2 A3,
  rw le_iff_lt_or_eq at A2,
  cases A2 with A2 A2,
  {
    apply ennreal.add_lt_add A3 A2,
  },
  subst d,
  rw with_top.add_lt_add_iff_right,
  apply A3,
  apply A1,
end 

lemma ennreal.le_of_sub_eq_zero {a b:ennreal}:
    a - b = 0 → a ≤ b :=
begin
  intros A1,
  simp at A1,
  apply A1,
end

--Used once in hahn.lean.
lemma ennreal.sub_add_sub {a b c:ennreal}:c ≤ b → b ≤ a → (a - b) + (b - c) = a - c :=
begin
  cases c;cases b;cases a;try {simp},
  repeat {rw ← ennreal.coe_sub <|> rw ← ennreal.coe_add <|> rw ennreal.coe_eq_coe},
  apply nnreal.sub_add_sub,
end


-- TODO: everything used below here.
lemma ennreal.inv_as_fraction {c:ennreal}:(1)/(c) = (c)⁻¹ := 
begin
  rw div_eq_mul_inv,
  rw one_mul,
end

lemma ennreal.add_lt_of_lt_sub {a b c:ennreal}:a < b - c → a + c < b :=
begin
  cases a;cases b;cases c;try {simp},
  {
    repeat {rw ← ennreal.coe_sub 
            <|> rw ennreal.coe_lt_coe
            <|> rw ← ennreal.coe_add},
    apply nnreal.add_lt_of_lt_sub,
  },
end


lemma ennreal.lt_sub_of_add_lt {a b c:ennreal}: a + c < b → a < b - c :=
begin
  --intros AX A1,
  cases a;cases b;cases c;try {simp},
  {
    repeat {rw ← ennreal.coe_sub 
            <|> rw ennreal.coe_lt_coe
            <|> rw ← ennreal.coe_add},
    apply nnreal.lt_sub_of_add_lt,
  },
end



lemma ennreal.eq_zero_or_zero_lt {x:ennreal}:¬(x=0) → (0 < x) :=
begin
  intro A1,
  have A2:= @lt_trichotomy ennreal _ x 0,
  cases A2,
  {
    exfalso,
    apply @ennreal.not_lt_zero x,
    apply A2,
  },
  cases A2,
  {
    exfalso,
    apply A1,
    apply A2,
  },
  {
    apply A2,
  },
end

--TODO: everything used below here.

lemma ennreal.sub_eq_of_add_of_not_top_of_le {a b c:ennreal}:a = b + c →
  c ≠ ⊤ →
  c ≤ a → a - c = b :=
begin
  intros A1 A4 A2,
  cases c,
  {
    exfalso,
    simp at A4,
    apply A4,
  },
  cases a,
  {
    simp,
    cases b,
    {
      refl,
    },
    exfalso,
    simp at A1,
    rw ← ennreal.coe_add at A1,
    apply ennreal.top_ne_coe A1,
  },
  cases b,
  {
    simp at A1,
    exfalso,
    apply A1,
  },
  {
    repeat {rw ennreal.some_eq_coe},
    rw ← ennreal.coe_sub,
    rw ennreal.coe_eq_coe,
    repeat {rw ennreal.some_eq_coe at A1},
    rw ← ennreal.coe_add at A1,
    rw ennreal.coe_eq_coe at A1,
    repeat {rw ennreal.some_eq_coe at A2},
    rw ennreal.coe_le_coe at A2,
    apply nnreal.sub_eq_of_add_of_le A1 A2,
  },
end

lemma ennreal.eq_add_of_sub_eq {a b c:ennreal}:b ≤ a →
  a - b = c → a = b + c :=
begin
  intros A1 A2,
  cases a;cases b,
  {
    simp,
  },
  {
    cases c,
    {
      simp,
    },
    exfalso,
    simp at A2,
    apply A2,
  },
  {
    exfalso,
    apply with_top.not_none_le_some _ A1,
  },
  simp at A2,
  rw ← ennreal.coe_sub at A2,
  cases c,
  {
    exfalso,
    simp at A2,
    apply A2,
  },
  {
    simp,
    rw ← ennreal.coe_add,
    rw ennreal.coe_eq_coe,
    simp at A2,
    simp at A1,
    apply nnreal.eq_add_of_sub_eq A1 A2,
  },
end


lemma ennreal.sub_lt_sub_of_lt_of_le {a b c d:ennreal}:a < b →
  c ≤ d →
  d ≤ a →
  a - d < b - c :=
begin
  intros A1 A2 A3,
  have B1:(⊤:ennreal) = none := rfl,
  have B2:∀ n:nnreal,  (some n) = n,
  {
    intro n,
    refl,
  },
  cases a,
  {
    exfalso,
    apply @with_top.not_none_lt nnreal _ b A1,
  },
  cases d,
  {
    exfalso,
    apply @with_top.not_none_le_some nnreal _ a A3,
  },
  cases c,
  {
    exfalso,
    apply @with_top.not_none_le_some nnreal _ d A2,
  },
  cases b,
  {
    simp,
    rw ← ennreal.coe_sub,
    rw B1,
    rw ← B2,
    apply with_top.some_lt_none,
  },
  repeat {rw B2},
  repeat {rw ← ennreal.coe_sub},
  rw ennreal.coe_lt_coe,
  apply nnreal.sub_lt_sub_of_lt_of_le,
  repeat {rw B2 at A1},
  rw ennreal.coe_lt_coe at A1,
  apply A1,
  
  repeat {rw B2 at A2},
  rw ennreal.coe_le_coe at A2,
  apply A2,

  repeat {rw B2 at A3},
  rw ennreal.coe_le_coe at A3,
  apply A3,
end


lemma ennreal.le_sub_add {a b c:ennreal}:b ≤ c → c ≤ a → 
a ≤ a - b + c := 
begin
  cases a;cases b;cases c;try {simp},
  rw ← ennreal.coe_sub,
  rw ← ennreal.coe_add,
  rw ennreal.coe_le_coe,
  apply nnreal.le_sub_add,
end

lemma ennreal.le_sub_add' {a b:ennreal}:a ≤ a - b + b :=
begin
  cases a; cases b; simp,
  rw ← ennreal.coe_sub,
  rw ← ennreal.coe_add,
  rw ennreal.coe_le_coe,
  apply nnreal.le_sub_add',
end



lemma ennreal.add_sub_cancel {a b:ennreal}:b < ⊤ → a + b - b = a :=
begin
  cases a;cases b;try {simp},
end


lemma ennreal.exists_coe {x:ennreal}:x < ⊤ → ∃ v:nnreal, x = v :=
begin
  cases x;try {simp},
end



lemma ennreal.lt_of_add_le_of_le_of_sub_lt {a b c d e:ennreal}:c < ⊤ →
    a + b ≤ c → d ≤ b → c - e < a → d < e := 
begin
  cases c,simp,
  cases a;cases b;cases d;cases e;try {simp},
  rw ← ennreal.coe_add,
  rw ← ennreal.coe_sub,
  rw ennreal.coe_le_coe,
  rw ennreal.coe_lt_coe,
  apply nnreal.lt_of_add_le_of_le_of_sub_lt,
end


lemma ennreal.coe_sub_lt_self {a:nnreal} {b:ennreal}:
     0 < a  → 0 < b →
     (a:ennreal) - b < (a:ennreal) :=
begin
  cases b;simp,
  intros A1 A2,
  rw ← ennreal.coe_sub,
  rw ennreal.coe_lt_coe,
  apply nnreal.sub_lt_self A1 A2,
end 

lemma ennreal.lt_of_lt_top_of_add_lt_of_pos {a b c:ennreal}:a < ⊤ →
      b + c ≤ a →
      0 < b →
      c < a :=
begin
  cases a;simp;
  cases b;cases c;simp,
  rw ← ennreal.coe_add,
  rw ennreal.coe_le_coe,
  apply nnreal.lt_of_add_lt_of_pos,
end


/-
  ennreal could be a linear_ordered_comm_group_with_zero,
  and therefore a ordered_comm_monoid.
  HOWEVER, I am not sure how to integrate this.
  I am going to just prove the basic results from the class.
  NOTE that this is strictly more general than
  ennreal.mul_le_mul_left.
-/
lemma ennreal.mul_le_mul_of_le_left {a b c:ennreal}:
  a ≤ b → c * a ≤ c * b :=
begin
  cases a;cases b;cases c;simp;
  try {
    cases (classical.em (c=0)) with B1 B1,
    {
      subst c,
      simp,
    },
    {
      have B2:(c:ennreal) * ⊤ = ⊤,
      {
        rw ennreal.mul_top,
        rw if_neg,
        intro B2A,
        apply B1,
        simp at B2A,
        apply B2A,
      },
      rw B2,
      {apply le_refl _ <|> simp},
    },
  },
  {
    cases (classical.em (b=0)) with B1 B1,
    {
      subst b,
      simp,
    },
    {
      have B2:⊤ * (b:ennreal) = ⊤,
      {
        rw ennreal.top_mul,
        rw if_neg,
        intro B2A,
        apply B1,
        simp at B2A,
        apply B2A,
      },
      rw B2,
      simp,
    },
  },
  rw ← ennreal.coe_mul,
  rw ← ennreal.coe_mul,
  rw ennreal.coe_le_coe,
  apply nnreal.mul_le_mul_of_le_left,
end


lemma ennreal.inverse_le_of_le {a b:ennreal}:
  a ≤ b →
  b⁻¹ ≤ a⁻¹ :=
begin
  intros A2,
  cases (classical.em (a = 0)) with A1 A1,
  {
    subst a,
    simp,
  },

  cases b,
  {
    simp,
  },
  cases (classical.em (b = 0)) with C1 C1,
  {
    subst b,
    simp at A2,
    exfalso,
    apply A1,
    apply A2,
  },
  simp,
  simp at A2,
  have B1: (a⁻¹ * b⁻¹) * a ≤  (a⁻¹ * b⁻¹) * b,
  {
    apply ennreal.mul_le_mul_of_le_left A2,
  },
  rw mul_comm a⁻¹  b⁻¹ at B1,
  rw mul_assoc at B1,
  rw ennreal.inv_mul_cancel at B1,
  rw mul_comm (b:ennreal)⁻¹  a⁻¹ at B1,
  rw mul_assoc at B1,
  rw mul_one at B1,
  rw ennreal.inv_mul_cancel at B1,
  rw mul_one at B1,
  apply A2,
  {
    simp [C1],
  },
  {
    simp,
  },
  {
    apply A1,
  },
  {
    rw ← lt_top_iff_ne_top,
    apply lt_of_le_of_lt A2,
    simp,  
  },
end


lemma ennreal.nat_coe_add {a b:ℕ}:(a:ennreal) + (b:ennreal) = 
    ((@has_add.add nat _ a  b):ennreal) :=
begin
  simp,
end

lemma ennreal.nat_coe_le_coe {a b:ℕ}:(a:ennreal) ≤ (b:ennreal) ↔ (a ≤ b) :=
begin
  have B1:(a:ennreal) = ((a:nnreal):ennreal),
  {
    simp,
  }, 
  have B2:(b:ennreal) = ((b:nnreal):ennreal),
  {
    simp,
  }, 
  rw B1,
  rw B2,
  rw ennreal.coe_le_coe,
  split;intros A1,
  {
    simp at A1,
    apply A1,
  },
  {
    simp,
    apply A1,
  },
end


------------- from Radon-Nikodym --------


lemma ennreal.inv_mul_eq_inv_mul_inv {a b:ennreal}:(a≠ 0) → (b≠ 0) → (a * b)⁻¹=a⁻¹ * b⁻¹ :=
begin
  cases a;simp;cases b;simp,
  intros A1 A2,
  rw ← ennreal.coe_mul,
  repeat {rw ← ennreal.coe_inv},
  rw ← ennreal.coe_mul,
  rw ennreal.coe_eq_coe,
  apply @nnreal.inv_mul_eq_inv_mul_inv a b,
  apply A2,
  apply A1,
  rw ← @nnreal.pos_iff (a * b),
  rw nnreal.mul_pos_iff_pos_pos,
  repeat {rw canonically_ordered_add_monoid.zero_lt_iff_ne_zero},
  apply and.intro A1 A2,
end


lemma ennreal.div_dist {a b c:ennreal}:(b≠ 0) → (c≠ 0) → a/(b * c)=(a/b)/c :=
begin
  intros A1 A2,
  rw div_eq_mul_inv,
  rw ennreal.inv_mul_eq_inv_mul_inv,
  rw ← mul_assoc,
  repeat {rw div_eq_mul_inv},
  apply A1,
  apply A2,
end


lemma ennreal.div_eq_zero_iff {a b:ennreal}:a/b=0 ↔ (a = 0) ∨ (b = ⊤) :=
begin
  cases a;cases b;split;simp;intros A1;simp;simp at A1,
end

/-
  Helper function to lift nnreal.exists_unit_frac_lt_pos to ennreal.
 -/
lemma ennreal.exists_unit_frac_lt_pos' {ε:nnreal}:0 < ε → (∃ n:ℕ, (1/((n:ennreal) + 1)) < (ε:ennreal)) :=
begin
  intros A1,
--  simp at A1,
  have C1:= nnreal.exists_unit_frac_lt_pos A1,   
  cases C1 with n A1,
  apply exists.intro n,
  have D1:((1:nnreal):ennreal) = 1 := rfl,
  rw ← D1,
  have D2:((n:nnreal):ennreal) = (n:ennreal),
  {
    simp,
  },
  rw ← D2,
  rw ← ennreal.coe_add,
  rw ← ennreal.coe_div,
  rw ennreal.coe_lt_coe,
  apply A1,
  simp,
end


lemma ennreal.exists_unit_frac_lt_pos {ε:ennreal}:0 < ε → (∃ n:ℕ, (1/((n:ennreal) + 1)) < ε) :=
begin
  cases ε,
  {
     intros A1,
     have B1:(0:nnreal) < (1:nnreal),
     {
       apply zero_lt_one,
     },
     have B1:=ennreal.exists_unit_frac_lt_pos' B1,
     cases B1 with n B1,
     apply exists.intro n,
     apply lt_of_lt_of_le B1,
     simp,
  },
  {
    intros A1,
    simp at A1,
    have C1:= ennreal.exists_unit_frac_lt_pos' A1,   
    apply C1,
  },
end


lemma ennreal.zero_of_le_all_unit_frac {x:ennreal}:
    (∀ (n:ℕ), (x ≤ 1/((n:ennreal) + 1))) →  (x = 0) :=
begin
  intros A1,
  rw ← not_exists_not at A1, 
  apply by_contradiction,
  intros B1,
  apply A1,
  have B2:0 < x,
  {
    rw canonically_ordered_add_monoid.zero_lt_iff_ne_zero,
    apply B1,
  },
  have B3:= ennreal.exists_unit_frac_lt_pos B2,
  cases B3 with n B3,
  apply exists.intro n,
  apply not_le_of_lt,
  apply B3,
end



lemma ennreal.unit_frac_pos {n:ℕ}:(1/((n:ennreal) + 1))>0 :=
begin
  simp,
end


lemma ennreal.div_eq_top_iff {a b:ennreal}:a/b=⊤ ↔ 
                             ((a = ⊤)∧(b≠ ⊤) )∨ ((a≠ 0)∧(b=0)):=
begin
  rw div_eq_mul_inv,
  cases a;cases b;simp,
end

lemma ennreal.unit_frac_ne_top {n:ℕ}:(1/((n:ennreal) + 1))≠ ⊤ :=
begin
  intro A1, 
  rw ennreal.div_eq_top_iff at A1,
  simp at A1,
  apply A1,
end

lemma lt_eq_le_compl {δ α:Type*}
  [linear_order α] {f g : δ → α}:{a | f a < g a} ={a | g a ≤ f a}ᶜ :=
begin
    apply set.ext,
    intros ω;split;intros A3A;simp;simp at A3A;apply A3A,
end

lemma ennreal.lt_add_self {a b:ennreal}:a < ⊤ → 0 < b → a < a + b :=
begin
  cases a;cases b;simp,
  intros A1,
  rw ← ennreal.coe_add,
  rw ennreal.coe_lt_coe,
  simp,
  apply A1,
end

lemma ennreal.lt_add_pos {x ε:ennreal}: (x < ⊤) → (0 < ε) → (x < x + ε)  :=
begin
  cases ε; cases x; simp,
  rw ← ennreal.coe_add,
  rw ennreal.coe_lt_coe,
  apply nnreal.lt_add_pos,  
end

lemma ennreal.add_pos_le_false {x ε:ennreal}: (x < ⊤) → (0 < ε) → (x + ε ≤ x) → false :=
begin
  cases ε; cases x; simp,
  rw ← ennreal.coe_add,
  rw ennreal.coe_le_coe,
  apply nnreal.add_pos_le_false,
end 


lemma ennreal.le_of_infi {α:Sort*} {f:α → ennreal} {ε:nnreal}: 
((⨅ (a:α), f a) < ⊤) → (0 < ε) → (∃ (a:α), f a ≤ ( (⨅ (a:α), f a) + ε)) :=
begin
  intros h1 h2,
  have h3:infi f ≤ (⨅ (a:α), f a),
  { apply le_refl _, },
  rw ← @ennreal.iff_infi_le α at h3,
  apply h3 ε h2 h1,
end

lemma ennreal.infi_prop_le_elim (P:Prop) (x:ennreal): 
(⨅ (hp:P), x) < ⊤ → P :=
begin
  intro h1,
  cases classical.em P with h2 h2,
  apply h2,
  rw infi_prop_false at h1,
  simp at h1,
  apply false.elim h1,
  apply h2,
end

lemma ennreal.add_pos_of_pos {x y:ennreal}:(0 < y) → (0 < x + y) :=
begin
  intros h,
  apply lt_of_lt_of_le h,
  rw add_comm,
  apply ennreal.le_add,
  apply le_refl _,
end

--Replace with one_div
lemma ennreal.one_div (x:ennreal):1/x = x⁻¹ := begin
  simp,
end


lemma ennreal.coe_infi {α:Sort*} [nonempty α] {f:α → nnreal}:
  @coe nnreal ennreal _ (⨅ i, f i) = (⨅ i,  @coe nnreal ennreal _ (f i)) := begin
  simp only [infi],
  rw ennreal.coe_Inf,
  apply le_antisymm,
  { simp, intros a, apply @infi_le_of_le ennreal nnreal _ _ _ (f a),
    apply @infi_le_of_le ennreal α _ _ _ a,
    rw infi_pos, apply le_refl _, refl },
  { simp, intros a, apply @Inf_le ennreal _ _ _,
    simp, apply exists.intro a, refl },
  apply set.range_nonempty,
end

lemma ennreal.coe_supr {α:Sort*} [nonempty α] {f:α → nnreal}:
  (bdd_above (set.range f)) →
  @coe nnreal ennreal _ (⨆ i, f i) = (⨆ i,  @coe nnreal ennreal _ (f i)) := begin
  intros h1,
  simp only [supr],
  rw ennreal.coe_Sup,
  apply le_antisymm,
  { simp, intros a, apply @le_Sup ennreal _ _ _,
    simp, apply exists.intro a, refl },
  { simp, intros a, apply @le_supr_of_le ennreal nnreal _ _ _ (f a),
    apply @le_supr_of_le ennreal α _ _ _ a,
    rw supr_pos, apply le_refl _, refl },
  apply h1,
end

/- These are tricky to place, because they depend upon ennreal. -/

lemma nnreal.mul_infi {ι:Sort*} [nonempty ι] {f : ι → nnreal} {x : nnreal}  :
  x * infi f = ⨅i, x * f i :=
begin   
  rw ← ennreal.coe_eq_coe,
  rw ennreal.coe_mul,
  rw ennreal.coe_infi,
  rw ennreal.mul_infi,
  rw ennreal.coe_infi,
  have h1:(λ i, @coe nnreal ennreal _ (x * f i)) = (λ i, (↑ x) * (↑ (f i))),
  { ext1 i, rw ennreal.coe_mul },
  rw h1,
  simp,
end

lemma nnreal.mul_supr {ι:Sort*} [nonempty ι] {f : ι → nnreal} {x : nnreal} 
  (h:bdd_above (set.range f))  :
  x * supr f = ⨆i, x * f i :=
begin   
  rw ← ennreal.coe_eq_coe,
  rw ennreal.coe_mul,
  rw ennreal.coe_supr,
  rw ennreal.mul_supr,

  rw ennreal.coe_supr,
  have h1:(λ i, @coe nnreal ennreal _ (x * f i)) = (λ i, (↑ x) * (↑ (f i))),
  { ext1 i, rw ennreal.coe_mul },
  rw h1,
  { simp [bdd_above], rw set.nonempty_def,
    simp [bdd_above] at h,
    rw set.nonempty_def at h,
    cases h with y h,
    rw mem_upper_bounds at h,
    apply exists.intro (x * y),
    rw mem_upper_bounds,
    intros z h_z,
    simp at h_z,
    cases h_z with i h_z,
    subst z,
    have h_mem:(f i) ∈ set.range f,
    { simp },
    have h_z' := h (f i) h_mem,
    
    apply mul_le_mul,
    apply le_refl _,
    apply h_z',
    simp, 
    simp },
  { apply h },
end
