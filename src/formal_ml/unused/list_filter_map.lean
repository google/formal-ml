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
import data.fin
import formal_ml.nat
import formal_ml.core
import data.list.basic
import data.list.intervals

lemma list.cons_eq_append  {α:Type*} {h:α} {t:list α}:
  list.cons h t = [h] ++ t := rfl

def nth_with_default {α:Type*} (l:list α) (n:ℕ) (d:α):α :=
  match (list.nth l n) with
  | (some x) := x
  | (none) := d
  end



lemma nth_with_default_of_le {α:Type*} {a:list α} {n:ℕ} {d:α}:
  list.length a ≤ n → nth_with_default a n d = d :=
begin
  intro A1,
  unfold nth_with_default,
  rw list.nth_len_le A1,
  unfold nth_with_default._match_1,
end 







lemma nth_with_default_of_lt {α:Type*} {a:list α} {n:ℕ} {d:α} (H:n < list.length a):nth_with_default a n d = list.nth_le a n H :=
begin
  unfold nth_with_default,
  rw list.nth_le_nth H,
  unfold nth_with_default._match_1,
end 


lemma list.filter_map_cons_cons {α β:Type*} {f:α → option β} {t:list α} {h:α}:
  list.filter_map f (h::t) = (option.to_list (f h)) ++ (list.filter_map f t) :=
begin
  let z := (f h),
  begin
    have A1:z = f h := rfl,
    cases (f h),
    {
      unfold option.to_list,
      rw list.nil_append,
      rw list.filter_map_cons_none,
      have A2:z = f h := rfl,
      rw ← A2,
      rw A1,
    },
    {
      unfold option.to_list,
      have A2:z = f h := rfl,
      rw A1 at A2,
      have A3 := A2.symm,
      rw list.filter_map_cons_some f h t A3,
      rw list.cons_eq_append,
    }
  end
end


lemma list_filter_map_cons {α β:Type*} {f:α → option β} {h:α} {t:list α} {b:β}:
  (f h=some b) → (list.filter_map f (h::t)) = b::(list.filter_map f t) :=
begin
  apply list.filter_map_cons_some,
end

lemma list_filter_map_cons2 {α β:Type*} {f:α → option β} {h:α} {t:list α} {b:β}:
  (f h=none) → (list.filter_map f (h::t)) = (list.filter_map f t) :=
begin
  apply list.filter_map_cons_none,
end





@[simp] lemma list_filter_map_nil {α β:Type*} {f:α → option β}:
  (list.filter_map f list.nil) = list.nil :=
begin
  apply list.filter_map_nil,
end

lemma list.cons_append_assoc {α:Type*} {h:α} {l1:list α} {l2:list α}:
  (h::l1) ++ l2 = h::(l1 ++ l2) :=
begin
  rw list.cons_eq_append,
  rw @list.cons_eq_append α h (l1 ++ l2),
  rw list.append_assoc,
end

lemma list_filter_map_append {α β:Type*} {f:α → option β} {l1 l2:list α}:
  list.filter_map f (l1 ++ l2) = (list.filter_map f l1) ++ (list.filter_map f l2)
  :=
begin
  induction l1,
  {
    simp,
  },
  {
    rw list.cons_append_assoc,
    rw list.filter_map_cons_cons,
    rw list.filter_map_cons_cons,
    rw list.append_assoc,
    rw ← l1_ih,
  }
end

lemma list_filter_map_append2 {α β:Type*} {f:α → option β} {l1 l2:list α}:
  list.filter_map f (l1 ++ l2) = (list.filter_map f l1) ++ (list.filter_map f l2)
  :=
begin
  induction l1,
  {
    simp,
  },
  {
    rw list.cons_append_assoc,
    rw list.filter_map_cons_cons,
    rw list.filter_map_cons_cons,
    rw list.append_assoc,
    rw ← l1_ih,
  }
end

lemma list_filter_map_cons3 {α β:Type*} {f:α → option β} {h:α} {t:list α}:
  (list.filter_map f (h::t)) = (list.filter_map f [h])++(list.filter_map f t) :=
begin
  rw list.cons_eq_append,
  rw list_filter_map_append,
end


lemma list_filter_map_mem {α β:Type*} {f:α → option β} {l:list α} {b:β}:
  (b∈ (list.filter_map f l) ↔ (∃ a:α, (f a = some b) ∧ a∈ l)) :=
begin
  split;intros A1,
  {
    induction l,
    {
      simp at A1,
      exfalso,
      apply A1,
    },
    {
      rw list.filter_map_cons_cons at A1,
      simp at A1,
      cases A1,
      {
        apply exists.intro l_hd,
        split,
        {
          exact A1,
        },
        {
          simp,
        },
      },
      {
        cases A1 with a A2,
        
        --have A2:=l_ih A1,
        cases A2 with A3 A4,
        apply exists.intro a,
        split,
        {
          apply A4,
        },
        {
          simp,
          right,
          apply A3,
        }
      }
    }
  },
  {
    induction l,
    {
      exfalso,
      cases A1 with a A2,
      cases A2 with A3 A4,
      simp at A4,
      apply A4,
    },
    {
      rw list.filter_map_cons_cons,
      rw list.mem_append,
      cases A1 with a A2,
      cases A2 with A3 A4,
      rw list.mem_cons_eq at A4,
      cases A4,
      {
        left,
        subst a,
        rw A3,
        unfold option.to_list,
        simp,
      },
      {
        right,
        apply l_ih,
        apply exists.intro a,
        apply and.intro A3 A4,
      }
    }
  }
end

def option_fin (n m:ℕ):option (fin n) :=
  dite (m < n) (λ H, some (fin.mk m H)) (λ H, option.none)

def fin.Ico (m n:ℕ):list (fin n) := list.filter_map (option_fin n) (list.Ico m n)

def fin.range (n:ℕ):list (fin n) := list.filter_map (option_fin n) (list.range n)


lemma fin.Ico.zero_bot {n:ℕ}:fin.Ico 0 n = fin.range n :=
begin
  unfold fin.Ico,
  unfold fin.range,
  rw list.Ico.zero_bot,
end

lemma option_some_eq {α:Type*} {a b:α}:(some a = some b) ↔ a = b :=
begin
  split;intro A1,
  {
    simp at A1,
    apply A1,
  },
  {
    rw A1,
  }
end

lemma some_fin_eq {n:ℕ} {a b:fin n}:some a = some b ↔ a.val = b.val :=
begin
  rw option_some_eq,
  split;intro A1,
  {
    rw A1,
  },
  {
    ext,
    apply A1,
  }
end 


lemma  option_fin_some {m n:ℕ} {z:fin m}:option_fin m n = some z → n = z.val :=
begin
  intro A1,
  unfold option_fin at A1,
  have A2:(n < m) ∨ ¬(n < m) := lt_or_not_lt,
  cases A2,
  {
    rw dif_pos A2 at A1,
    apply some_fin_eq.mp A1, 
  },
  {
    rw dif_neg A2 at A1,
    exfalso,
    simp at A1,
    apply A1,
  }
end

lemma fin.Ico.mem {m n:ℕ} (z: fin n):
    (m ≤ z.val) ↔  (z ∈ (fin.Ico m n)) :=
begin
  split;intro A1,
  {
    unfold fin.Ico,
    rw list_filter_map_mem,
    apply exists.intro z.val,
    split,
    {
      unfold option_fin,
      rw dif_pos z.2,
      simp,
    },
    {
      rw list.Ico.mem,
      split,
      apply A1,
      apply z.2,
    }
  },
  {
    unfold fin.Ico at A1,
    rw list_filter_map_mem at A1,
    cases A1 with a A2,
    cases A2 with A3 A4,
    rw list.Ico.mem at A4,
    cases A4 with A5 A6,
    have A7:a=z.val,
    {
      apply option_fin_some A3,
    },
    subst a,
    apply A5,
  }
end

lemma fin.range_def (n:ℕ):
  fin.range n = list.filter_map (option_fin n) (list.range n) := rfl


lemma fin.Ico.eq_cons {n m : ℕ} (h : n < m) : fin.Ico n m = (fin.mk n h) :: fin.Ico (n + 1) m :=
begin
  unfold fin.Ico,
  rw list.Ico.eq_cons,
  rw list_filter_map_cons,
  unfold option_fin,
  rw dif_pos h,
  apply h
end

lemma filter_map_length {α β:Type*} {f:α → option β} {l:list α}:
    (∀ b∈ l, ∃ c, (f b)=some c) → (l.length = (list.filter_map  f l).length) :=
begin
  induction l,
  {
    intro A1,
    simp,
  },
  {
    intro A1,
    have A2:(∃ (c : β), f l_hd = some c),
    {
      apply A1,
      simp,
    },
    cases A2 with c A3,
    rw list.filter_map_cons_some f l_hd l_tl A3,
    simp,
    apply l_ih,
    intros b A4,
    apply A1,
    simp,
    right,
    apply A4,
  }
end

lemma filter_map_nth {α β:Type*} {f:α → option β} {l:list α} (n:ℕ) 
    (H:n < l.length) (H2:∀ b∈ l, ∃ c, (f b)=some c):
    (list.nth (list.filter_map f l) n)
    = f (list.nth_le l n H) :=
begin
  revert H2,
  revert H,
  revert n,
  induction l,
  {
    intros n H H2,
    simp at H,
    exfalso,
    apply nat.not_lt_zero n H,
  },
  {
    intros n,
    intros H H2,
    have A1:∃ c,f l_hd = some c,
    {
      apply H2,
      apply list.mem_cons_self,
    },
    cases A1 with c A2,
    rw list_filter_map_cons A2,
    cases n,
    {
      simp,
      rw A2,
    },
    {
      simp,
      rw l_ih,
      intros b A3,
      apply H2,
      apply list.mem_cons_of_mem,
      apply A3,
    }
  },
end

lemma fin.nth_range_of_lt (m n:ℕ) (H:m < n):
  list.nth (fin.range n) m = (option.some (fin.mk m H)) :=
begin
  unfold fin.range,
  have A1:m < (list.range n).length,
  {
    rw list.length_range,
    apply H,
  },
  have A2:option_fin n (list.nth_le (list.range n) m A1) = 
      (option.some (fin.mk m H)),
  {
    unfold option_fin,
    have A2A1:(list.nth_le (list.range n) m A1 = m),
    apply @list.nth_le_range n m A1,
    have A2A:(list.nth_le (list.range n) m A1 < n),
    {
      rw A2A1,
      apply H,
    },
    rw dif_pos A2A,
    simp,
  },
  rw ← A2,
  apply filter_map_nth,    
  -- ⊢ ∀ (b : ℕ), b ∈ list.range n → (∃ (c : fin n), option_fin n b = some c)
  intros b A3,
  rw list.mem_range at A3,
  apply exists.intro (fin.mk b A3),
  unfold option_fin,
  rw dif_pos A3,
end

lemma list.nth_le_nth_alt {α:Type*} {l:list α} {m:ℕ} {H:m < list.length l} {a:α}:
  list.nth l m = some a →
  list.nth_le l m H = a :=
begin
  intro A1,
  have A2:list.nth l m = some (list.nth_le l m H),
  {
    apply list.nth_le_nth,
  },
  rw A1 at A2,
  simp at A2,
  symmetry,
  apply A2,
end

lemma fin.nth_le_range_of_lt (m n:ℕ) (H:m < list.length (fin.range n)) (H2:m < n):
  list.nth_le (fin.range n) m H = (fin.mk m H2) :=
begin
  have A1:list.nth (fin.range n) m = (option.some (fin.mk m H2)),
  {
    apply fin.nth_range_of_lt,
  },
  apply list.nth_le_nth_alt A1,
end





lemma fin.length_range {n:ℕ}:
  list.length (fin.range n) = n :=
begin
  rw fin.range_def,
  rw ← filter_map_length,
  rw list.length_range,
  intros m A1,
  rw list.mem_range at A1,  
  apply exists.intro (fin.mk m A1),
  unfold option_fin,
  rw dif_pos A1,
end

