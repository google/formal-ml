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
import algebra.ordered_ring
import data.nat.basic
import formal_ml.core
import formal_ml.nat

lemma int.coe_lt {a b:ℕ}:a < b ↔ (a:ℤ) < (b:ℤ) :=
begin
  split;intros A1,
  {
    simp,
    apply A1,
  },
  {
    simp at A1,
    apply A1,
  },
end

lemma int.coe_le {a b:ℕ}:a ≤ b ↔ (a:ℤ) ≤ (b:ℤ) :=
begin
  split;intros A1,
  {
    simp,
    apply A1,
  },
  {
    simp at A1,
    apply A1,
  },
end


lemma int.coe_succ {a:ℕ}:((a.succ):int) = (a:int).succ :=
begin
  apply int.nat_succ_eq_int_succ,
end

lemma int.neg_succ_def {x:ℕ}:
  int.neg_succ_of_nat x = -(x.succ) := rfl




lemma int.neg_succ_le_zero {x:ℕ}:(int.neg_succ_of_nat x).succ ≤ 0 :=
begin
  rw int.neg_succ_def,
  rw ← int.neg_pred,  
  rw int.nat_succ_eq_int_succ,  
  simp,
  have A2:(x:int).succ.pred = x,
  {
    rw int.pred_succ,
  },-- := sorry,
  rw A2,
  have A1:(0:int) = ((0:nat):int) := rfl,
  rw A1,
  rw ← int.coe_le,
  simp,
end

lemma int.neg_succ_le_int_of_nat (a b:ℕ): (int.neg_succ_of_nat b) ≤ (int.of_nat a) :=
begin
  apply @int.le.intro_sub _ _ (a + b + 1),
  rw sub_eq_add_neg,
  rw int.neg_neg_of_nat_succ,
  refl,
end 

lemma int.not_int_of_nat_lt_neg_succ (a b:ℕ):(int.of_nat a) < (int.neg_succ_of_nat b) → false :=
begin
  intros A1,
  have A2:=int.neg_succ_le_int_of_nat a b,
  apply not_lt_of_ge A2,
  apply A1,
end 

--This is the hard part. The converse is trivial,
--and once we have this, all other variants can be
--proven.
lemma int.succ_le_of_lt {x y:ℤ}:x < y → x.succ ≤ y :=
begin
  intro A1,
  cases x;cases y,
  {
    have B1:int.of_nat x = x := rfl,
    rw B1,
    rw ← int.nat_succ_eq_int_succ,
    have B2:int.of_nat y = y := rfl,
    rw B2,
    rw ← int.coe_le, 
    apply nat.succ_le_of_lt,
    rw B1 at A1,
    rw B2 at A1,
    rw ← int.coe_lt at A1,
    apply A1,  
  },
  {
    exfalso,
    simp at A1,
    apply int.not_int_of_nat_lt_neg_succ,
    apply A1,
  },
  {
    rw int.neg_succ_def,
    rw ← int.neg_pred,  
    rw int.nat_succ_eq_int_succ,
    rw int.pred_succ,
    simp,
    have D1:0 ≤ (y:ℤ),
    {
      have D1A:((@has_zero.zero ℕ _):ℤ) = 0 := rfl,
      rw ← D1A,
      rw ← int.coe_le,
      simp,
    },
    have D2:(-(x:ℤ))≤ 0,
    {
      simp,
    },
    apply le_trans D2 D1,
  },
  {
    rw int.neg_succ_def,
    rw ← int.neg_pred,  
    rw int.nat_succ_eq_int_succ,
    rw int.pred_succ,
    rw int.neg_succ_def at A1,
    rw int.neg_succ_def at A1,
    rw int.neg_succ_def,
    apply neg_le_neg,
    simp at A1,
    rw ← int.coe_le,
    apply nat.succ_le_of_lt A1,
  },
end

lemma one_le_of_zero_lt {x:ℤ}:0 < x → 1 ≤ x :=
begin
  intro A0,
  have A1:(1:ℤ) = (0:ℤ).succ := rfl,
  rw A1,
  apply int.succ_le_of_lt A0,
end


lemma int.succ_def {a:int}:a.succ = a + 1 := rfl
lemma int.pred_def {a:int}:a.pred = a - 1 := rfl

lemma int.succ_le_iff {x y:ℤ}:x.succ ≤ y ↔ x < y :=
begin
  split;intros A1,
  {
    rw int.succ_def at A1,
    have B1:x + 0 < x + 1,
    {
      simp,
      apply zero_lt_one,
    },
    rw add_zero at B1,
    apply lt_of_lt_of_le B1 A1,
  },
  {
    apply int.succ_le_of_lt A1,
  },
end



lemma int.succ_lt_succ_iff {a b:int}:a.succ < b.succ ↔ a < b :=
begin
  repeat {rw int.succ_def},
  split;intros B3A,
  {
    simp at B3A,
    apply B3A,
  },
  {
    simp,
    apply B3A,
  },
end


lemma int.pred_succ_iff {a b:int}:a.pred = b ↔ a = b.succ :=
begin
  split;intros A1,
  {
    rw ← A1,
    rw int.succ_pred,
  },
  {
    rw A1,
    rw int.pred_succ,
  },
end

lemma int.lt_succ_iff {a b:int}:a < b.succ ↔ a ≤ b := 
begin
  let c := a.pred,
  begin
    have B1:c = a.pred := rfl,
    have B2:a = c.succ := int.pred_succ_iff.mp B1,
    rw B2,
    apply iff.trans (@int.succ_lt_succ_iff c b),
    symmetry,
    apply @int.succ_le_iff c b,
  end
end

lemma int.pred_lt_pred_iff {a b:int}:a.pred < b.pred ↔ a < b :=
begin
  repeat {rw int.pred_def},
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

lemma int.pred_lt_iff {a b:int}:a.pred < b ↔ a ≤ b := 
begin
  let c := a.pred,
  begin
    have B1:c = a.pred:= rfl,
    have B2:a = c.succ := int.pred_succ_iff.mp B1,
    rw ← B1,
    rw B2,
    symmetry,
    apply @int.succ_le_iff c b,
  end
end

lemma int.pred_lt_self {a:int}:a.pred < a :=
begin
  rw int.pred_lt_iff,
end
