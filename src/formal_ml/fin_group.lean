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
import data.fin
import tactic.linarith
import tactic.zify

/-
  Note : Looking at the documentation of zmod suggests this is unnecessary.
 -/

namespace nat


--Used below in simps in many places.
@[simp] lemma mul_mod_mod {a b c : ℕ} : (a * (b % c)) % c = (a * b) % c :=
begin
  rw ← mod_add_div b c,
  simp [right_distrib, left_distrib],
  rw mul_comm a (c * (b / c)),
  rw mul_assoc,
  rw add_mul_mod_self_left,
end

end nat

namespace fin

lemma pos_of_fin {n:ℕ} (a:fin n) : 0 < n :=
begin
  apply lt_of_le_of_lt (nat.zero_le _) a.property,
end

def neg {n:ℕ} (a:fin n):fin n := @subtype.mk ℕ _ ((n - a) % n) 
begin
  apply nat.mod_lt,
  apply fin.pos_of_fin a,
end


instance has_neg (n:ℕ):has_neg (fin n) := ⟨@fin.neg n⟩


lemma neg_def {n:ℕ} (a:fin n.succ):(-a).val = (n.succ - a.val) % n.succ :=
begin
  have A1:(-a) = fin.of_nat (n.succ - a.val) := rfl,
  rw A1, 
  unfold fin.of_nat,
end

@[simp]
lemma val_mod {n:ℕ} {a:fin n}:(↑a:nat) % n = (↑a:nat) :=
begin
  have A1:(↑a:ℕ) = (a.val) := rfl,
  rw A1,
  rw nat.mod_eq_of_lt a.property,
end  

instance add_comm_group (n:ℕ):add_comm_group (fin n.succ) := {
  add_assoc :=
  begin
    intros a b c,
    apply subtype.eq,
    simp [fin.add_def],
    rw add_assoc,
  end,
  zero_add :=
  begin
    intros a,
    apply subtype.eq,
    simp [fin.add_def],
  end,
  add_zero :=
  begin
    intros a,
    apply subtype.eq,
    simp [fin.add_def],
  end,
  add_left_neg :=
  begin
    intro a,
    apply subtype.eq,
    simp [fin.add_def, fin.neg_def],
    have A3: (↑a) < n.succ,
    { apply a.property, },
    have A4: n.succ - (↑a) + (↑a) = n.succ,
    { zify [le_of_lt A3], linarith },
    rw A4,
    simp,
  end,
  add_comm :=
  begin
    intros a b,
    apply subtype.eq,
    simp [fin.add_def],
    rw add_comm,
  end,
  ..fin.has_add,
  ..fin.has_zero,
  ..fin.has_neg (n.succ),
}

instance comm_ring (n:ℕ):comm_ring (fin n.succ.succ) := {
  mul_assoc :=
  begin
    intros a b c,
    apply subtype.eq,
    simp [fin.mul_def],
    rw mul_comm,
    --rw mul_mod_mod,
    rw ← mul_assoc,
    simp,
    rw mul_comm,
  end,
  one_mul := 
  begin
    intros a,
    apply subtype.eq,
    simp [fin.mul_def],
  end,
  mul_one :=
  begin
    intros a,
    apply subtype.eq,
    simp [fin.mul_def],
  end,
  mul_comm :=
  begin
    intros a b,
    apply subtype.eq,
    simp [fin.mul_def],
    rw mul_comm,
  end,
  left_distrib :=
  begin
    intros a b c,
    apply subtype.eq,
    simp [fin.mul_def, fin.add_def],
    rw left_distrib,
  end,
  right_distrib :=
  begin
    intros a b c,
    apply subtype.eq,
    simp [fin.mul_def, fin.add_def],
    rw mul_comm,
    simp,
    rw mul_comm,
    rw right_distrib,
  end,
  ..fin.has_one,
  ..fin.has_mul,
  ..fin.has_add,
  ..fin.has_zero,
  ..fin.has_neg (n.succ.succ),
  ..fin.add_comm_group (n.succ),
}

end fin

