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
import data.rat
import formal_ml.int

lemma rat.nonpos_of_num_nonpos {q:ℚ}:q.num ≤ 0 → q ≤ 0  :=
begin
  intro A1,
  have A3:(0:ℤ) < (((0:rat).denom):ℤ),
  {
    simp,
    apply (0:rat).pos,     
  },
  rw ← @rat.num_denom q,
  rw ← @rat.num_denom 0,
  rw rat.le_def,
  simp,
  have A4:(0:ℤ) < (((q:rat).denom):ℤ),
  {
    simp,
    apply (q:rat).pos,     
  },
  apply mul_nonpos_of_nonpos_of_nonneg,
  apply A1,
  apply le_of_lt,
  apply A3,
  {
    simp,
    apply q.pos,
  },
  apply A3,    
end


lemma rat.num_nonneg_of_nonneg {q:ℚ}:q≤ 0 → q.num ≤ 0 :=
begin
  intro A1,
  have A3:(0:ℤ) < (((0:rat).denom):ℤ),
  {
    simp,
    apply (0:rat).pos,     
  },
  have A4:(0:ℤ) < (((q:rat).denom):ℤ),
  {
    simp,
    apply (q:rat).pos,     
  },  
  rw ← @rat.num_denom q at A1,
  rw ← @rat.num_denom 0 at A1,
  rw rat.le_def at A1,
  simp at A1,
  apply nonpos_of_mul_nonpos_right A1 A3,
  apply A4,
  apply A3,
end


lemma rat.nonpos_iff_num_nonpos {q:ℚ}:q.num ≤ 0 ↔ q ≤ 0  :=
begin
  have A3:(0:ℤ) < (((0:rat).denom):ℤ),
  {
    simp,
    apply (0:rat).pos,     
  },
  have A4:(0:ℤ) < (((q:rat).denom):ℤ),
  {
    simp,
    apply (q:rat).pos,     
  },

  rw ← @rat.num_denom q,
  rw ← @rat.num_denom 0,
  rw rat.le_def,
  simp,
  split;intros A1,
  {
    apply mul_nonpos_of_nonpos_of_nonneg,
    apply A1,
    apply le_of_lt,
    apply A3,
  },
  {
    have B1:(0:ℤ) * ↑((0:ℚ).denom) = (0:ℤ) := zero_mul _,
    rw ← B1 at A1,
    apply le_of_mul_le_mul_right,
    apply A1,
    apply A3,
  },
  apply A4,
  apply A3,
end

lemma rat.num_pos_of_pos {q:ℚ}:0 < q → 0 < q.num :=
begin
  intro A1,
  apply lt_of_not_ge,
  rw lt_iff_not_ge at A1,
  intro A2,
  apply A1,
  apply rat.nonpos_of_num_nonpos A2,
end

lemma rat.pos_iff_num_pos {q:ℚ}:0 < q ↔ 0 < q.num :=
begin
  split;intro A1,
  {
    apply lt_of_not_ge,
    rw lt_iff_not_ge at A1,
    intro A2,
    apply A1,
    apply rat.nonpos_of_num_nonpos A2,
  },
  {
    apply lt_of_not_ge,
    rw lt_iff_not_ge at A1,
    intro A2,
    apply A1,
    apply rat.num_nonneg_of_nonneg A2,
  },
end



def monoid_hom_int_rat:monoid_hom int rat := {
  to_fun := rat.of_int,
  map_mul' := begin
    intros x y,
    repeat {rw rat.of_int_eq_mk},
    rw rat.mul_def one_ne_zero one_ne_zero,
    simp,
  end,
  map_one' := rfl,
}

def add_monoid_hom_int_rat:add_monoid_hom int rat := {
  to_fun := rat.of_int,
  map_add' := begin
    intros x y,
    repeat {rw rat.of_int_eq_mk},
    rw rat.add_def one_ne_zero one_ne_zero,
    simp,
  end,
  map_zero' := rfl,
}


def ring_hom_int_rat:ring_hom int rat := {
  ..monoid_hom_int_rat,
  ..add_monoid_hom_int_rat,
}

lemma ring_hom_int_rat_to_fun_def {n:ℤ}:
    ring_hom_int_rat.to_fun n = rat.of_int n := rfl


lemma ring_hom_int_rat_to_fun_def2 {n:ℤ}:
    ring_hom_int_rat.to_fun n = n :=
begin
  rw rat.coe_int_eq_of_int,
  rw ring_hom_int_rat_to_fun_def,
end


lemma ring_hom_int_rat_eq {a b:ℤ}:(ring_hom_int_rat.to_fun a)=(ring_hom_int_rat.to_fun b) ↔ (a = b) :=
begin
  repeat {rw ring_hom_int_rat_to_fun_def2},
  simp,
end




def ring_hom_nat_rat:=
  ring_hom.comp ring_hom_int_rat ring_hom_nat_int




lemma ring_hom_nat_rat_to_fun_def {n:ℕ}:
    ring_hom_nat_rat.to_fun n = ring_hom_int_rat.to_fun ( ring_hom_nat_int.to_fun n) :=
begin
  refl,
end

lemma ring_hom_nat_rat_to_fun_def2 {n:ℕ}:
    ring_hom_nat_rat.to_fun n = n :=
begin
  rw ring_hom_nat_rat_to_fun_def,
  rw ring_hom_nat_int_to_fun_def,
  rw ring_hom_int_rat_to_fun_def2,
  simp,
end


lemma ring_hom_nat_rat_eq {a b:ℕ}:(ring_hom_nat_rat.to_fun a)=(ring_hom_nat_rat.to_fun b) ↔ a = b :=
begin
  repeat {rw ring_hom_nat_rat_to_fun_def},
  rw ring_hom_int_rat_eq,
  rw ring_hom_nat_int_eq,
end

lemma nat.one_le_iff_zero_lt {a:ℕ}:1 ≤ a ↔ 0 < a :=
begin
  rw ← nat.succ_le_iff_lt,
end

lemma rat.exists_unit_frac_le_pos {q:ℚ}:0 < q → (∃ n:ℕ, (1/((n:rat) + 1)) ≤ q) := 
begin
  intro A1,
  have A3 := @rat.num_denom q,
  rw ← A3,
  
  apply exists.intro (q.denom.pred),
  
  have A2:(((nat.pred q.denom):rat) + 1) = q.denom,
  {
    have A2A:((@has_one.one ℕ _):ℚ) = 1 := rfl,
    rw ← A2A,
    repeat {rw ← ring_hom_nat_rat_to_fun_def2},
    rw ← ring_hom_nat_rat.map_add',
    rw ring_hom_nat_rat_eq,
    have A2B:nat.pred q.denom + 1 = nat.succ (nat.pred q.denom) := rfl,
    rw A2B,
    rw nat.succ_pred_eq_of_pos,
    apply q.pos,
  },
  rw A2,
  have A3:(1/(q.denom:rat))= rat.mk 1 q.denom,
  {
    have A3A:((1:nat):rat) = 1 := rfl,
    have A3B:((1:ℤ):rat)/((q.denom:ℤ):rat)=1/(q.denom:rat),
    {
      refl,
    },
    rw ← A3B,
    rw ← rat.mk_eq_div,
  },
  rw A3,
  rw rat.le_def,
  {
    simp,
    rw le_mul_iff_one_le_left,
    have B1:(int.succ 0) = 1 := rfl,
    rw ← B1,
    rw @int.succ_le_iff 0 q.num,
    apply rat.num_pos_of_pos A1,
    simp,
    apply q.pos,
  },
  repeat {
    simp,
    apply q.pos,
  },
end

lemma rat.mk_pos_denom {p:ℤ} {n:pnat}:(rat.mk p (n:ℤ))=
  rat.mk_pnat p n :=
begin
  cases n,
  rw rat.mk_pnat_eq,
  simp,
end


lemma rat.pos_mk {p q:ℤ}:(0 < p) → (1 ≤ q) → 
  0 < (rat.mk p q) :=
begin
  intros A1 A2,
  cases q,
  {
    cases q,
    {
      -- q cannot be zero.
      exfalso,
      simp at A2,
      apply not_lt_of_le A2,
      apply zero_lt_one,
    },
    let n := q.succ_pnat,
    begin
      have B1:(n:ℤ) = int.of_nat q.succ := rfl,
      rw ← B1,
      rw rat.mk_pos_denom,
      rw ← rat.num_pos_iff_pos,
      rw rat.mk_pnat_num,
      simp,
      cases p,
      {
        simp, 
        rw ← int.coe_nat_div,
        have B2:((0:ℕ):ℤ) = (0:ℤ) := rfl,
        rw ← B2,
        rw int.coe_nat_lt, 
        apply nat.div_pos,
        apply nat.gcd_le_left,
        simp at A1,
        apply A1,
        apply nat.gcd_pos_of_pos_right,
        simp,
      },
      {
        -- p cannot be negative.
        exfalso,
        apply not_le_of_lt A1,
        apply le_of_lt,
        apply int.neg_succ_of_nat_lt_zero p,
      },
    end 
  },
  -- q cannot be negative.
  rw ← rat.num_pos_iff_pos,
  unfold rat.mk,
  {
    exfalso,
    apply not_le_of_lt (int.neg_succ_of_nat_lt_zero q),
    apply le_of_lt,
    apply lt_of_lt_of_le,
    apply zero_lt_one,
    apply A2,
  },
end

