import formal_ml.vcd




namespace list
variable {α:Type*}

lemma nth_lt_of_sorted_of_lt [L:linear_order α] {a b:ℕ} {l:list α} (ha:a < l.length)
(hb:b < l.length):list.sorted (<) l → (a < b) → (l.nth_le a ha) < (l.nth_le b hb) :=
begin
  intros A1 A2,
  simp [list.sorted] at A1,
  rw list.pairwise_iff_nth_le at A1,
  apply A1,
  apply A2,
end 




end list


namespace finset
variable {α:Type*}

lemma card_three [L:linear_order α] {T:finset α}:T.card = 3 → 
(∃ (a b c:α), a < b ∧ b < c ∧ T = {a,b,c}) :=
begin
  intros h,
  have A1:(T.sort L.le).length = 3,
  { rw finset.length_sort, apply h },
  rw ← finset.sort_to_finset L.le T,
  have A2:(T.sort L.le).sorted (<) := sort_sorted_lt T,
  cases (T.sort L.le) with a0 S,
  { apply absurd A1, dec_trivial, },
  cases S with a1 S,
  { apply absurd A1, dec_trivial, },
  cases S with a2 S,
  { apply absurd A1, dec_trivial, },
  cases S with a3 S,
  existsi [a0, a1, a2],
  split,
  apply @list.nth_lt_of_sorted_of_lt α L 0 1 [a0, a1, a2],
  dec_trivial,
  dec_trivial,
  apply A2,
  dec_trivial,
  split,
  apply @list.nth_lt_of_sorted_of_lt α L 1 2 [a0, a1, a2],
  dec_trivial,
  dec_trivial,
  apply A2,
  dec_trivial,
  simp,
  apply absurd A1,
  dec_trivial,
end


lemma powerset_two {a b:α} [decidable_eq α] {a≠ b}:({a,b}:finset α).powerset = 
{∅, {a},{b},{a,b}} := begin
  rw finset.powerset_insert,
  rw finset.powerset_singleton,
  simp,
  ext x,
  split; intros A1;
  { simp at A1, simp [A1], cases A1,
    simp [A1], cases A1, simp [A1],
    cases A1, simp [A1], simp [A1],  },
end

lemma forall_subset_card_1 {a:α} {P:finset α → Prop}:
P ∅ → P {a} → (∀ S:finset α, S⊆ {a} → P S) :=
begin
  intros A1 A2,
  intros S,
  intros A3,
  cases (finset.eq_empty_or_nonempty S) with h_empty h_nonempty,
  subst S,
  apply A1,
  simp [finset.nonempty] at h_nonempty,
  cases h_nonempty with x x_in_S,
  have A4:S = {a},
  { apply finset.subset.antisymm, 
    apply A3, rw finset.subset_iff,
    intros y A5, simp at A5, subst y,
    have A6 := A3 x_in_S,
    simp at A6, subst x,
    apply x_in_S,
     },
  subst S,
  apply A2,
end

lemma forall_subset_card_2 {a a':α} [decidable_eq α] {P:finset α → Prop}:
P ∅ → P {a} → P {a'} → P ({a,a'}:finset α) →  (∀ S:finset α, S⊆ {a,a'} → P S) :=
begin
  intros A1 A2 A3 A4,
  intros S A5,
  cases (decidable.em (a∈ S)) with B1 B1;
  cases (decidable.em (a'∈S)) with B2 B2,
  { have A6:S = {a,a'},
    { ext x, split;intros A6_1, apply A5, apply A6_1,
      simp at A6_1, cases A6_1, subst x, apply B1, subst x, apply B2 },
    subst S, apply A4 },
  { have A6:S = {a},
    { ext x, split;intros A6_1, have A6_2 := A5 A6_1, simp at A6_2,
      cases A6_2, { subst x, simp },
      subst x, apply absurd A6_1,
      apply B2, simp at A6_1, subst x, apply B1 },
    subst S, apply A2 },
  { have A6:S = {a'},
    { ext x, split;intros A6_1, have A6_2 := A5 A6_1, simp at A6_2,
      cases A6_2, { subst x, apply absurd A6_1, apply B1 },
      subst x, simp,
      simp at A6_1, subst x, apply B2 },
    subst S, apply A3 },
  { have A6:S = ∅,
    { ext x, split;intros A6_1, have A6_2 := A5 A6_1, simp at A6_2,
      cases A6_2, { subst x, apply absurd A6_1, apply B1 },
      { subst x, apply absurd A6_1, apply B2 },
      simp at A6_1,
      apply false.elim A6_1 },
    subst S, apply A1 },
end

end finset

namespace set
variable {α:Type*}
lemma inter_singleton_eq_singleton_iff {a:α} {c:set α}:c ∩ {a} = {a} ↔ a ∈ c :=
begin
   have A0:a ∈ {a},
   { apply set.mem_singleton, },
  split;intros A1,
  { have A2:c ∩ {a} ⊆ c,
    { apply  set.inter_subset_left },
    apply A2, rw A1, apply A0 },
  { ext x,
    split, intros A1,
    simp at A1, simp,
    apply A1.right,
    intros A2, simp at A2, subst x,
    simp [A1] },
end

lemma two_of_three {a b c:α} {h_a_ne_b:a ≠ b} {h_b_ne_c:b≠ c} {T:set α}:T ∩ {a,b,c} = {a,c} ↔ ((a ∈ T)
∧ (b∉ T) ∧ (c∈ T)):=
begin
  have B0:a∈ ({a,b,c}:set α),
  { simp },
  have B1:a∈ ({a,c}:set α),
  { simp },
  have B2:c ∈ ({a,c}:set α),
  { simp, },
  split; intros A1,
  split,
  { rw set.subset.antisymm_iff at A1,
    have C1 := A1.right B1,
    simp at C1,
    apply C1 },
  split,
  { intros contra,
    rw set.subset.antisymm_iff at A1,
    have C1:b∈ T ∩ {a,b,c},
    { simp, apply contra },
    have C2 := A1.left C1,
    simp at C2,
      cases C2,
      apply h_a_ne_b,
      rw C2,
      apply h_b_ne_c,
      rw C2 },
  { rw set.subset.antisymm_iff at A1,
    have C1 := A1.right B2,
    simp at C1,
    apply C1 },
  ext x;split;intros D1,
  { simp at D1, cases D1 with D1 D2,
    cases D2 with D2 D3,
    subst x, simp,
    cases D3,
    subst x,
    apply absurd D1,
    apply A1.right.left,
    subst x, simp, },
  { simp, simp at D1,
    cases D1; subst x; simp [A1],  },
end

end set


namespace VC_PAC_problem
variable {α:Type*}


/- The class of bounded intervals. -/
def intervals (α) [linear_order α]:set (set α) := 
  {C|∃ (a b:α), C = set.Ioo a b ∨ C = set.Ioc a b ∨ C = set.Ico a b ∨ C = set.Icc a b} 


/- The class of thresholds. -/
def thresholds (α) [linear_order α]:set (set α) :=
  {C|∃ (a:α), C = set.Iio a ∨ C = set.Iic a ∨ C = set.Ioi a ∨ C = set.Ici a} 



lemma non_singleton_two [L:linear_order α]: (∃ a b:α, a ≠ b) → (∃ c d:α, c < d) := begin
  intros h,
  cases h with a h,
  cases h with b h,
  cases (lt_trichotomy a b) with h_a_lt_b h_a_eq_b_or_b_lt_a,
  { existsi [a,b], apply h_a_lt_b },
  cases h_a_eq_b_or_b_lt_a with h_a_eq_b h_b_lt_a,
  { exfalso, apply h, apply h_a_eq_b },
  { existsi [b,a], apply h_b_lt_a, },
end




lemma one_le_VCD {a:α} {C:set (set α)}:(∃ c∈ C, a∈ c) → (∃ c∈ C, a∉ c) → 1 ≤ VCD C :=
begin
  intros h1 h2,
  let T:finset α := {a},
  begin
    have A1:(T.card:enat) = (1:enat),
    { simp,  },
    rw ← A1,
    apply shatters_card_le_VCD,
    rw shatters_iff,
    apply finset.forall_subset_card_1,
    { cases h2 with c h2,
      cases h2 with h2 h3,
      apply exists.intro c,
      apply exists.intro h2,
      simp [h3], },
    { cases h1 with c h1,
      cases h1 with h1 h3,
      apply exists.intro c,
      apply exists.intro h1,
      simp,
      rw set.inter_singleton_eq_singleton_iff,
      apply h3 },
  end
end

/- Though long and drawn out, this should be straightforward to
   automate, which will be useful for when there are 16 or more cases. -/
lemma two_le_VCD {a a':α} [decidable_eq α] {C:set (set α)}:
(∃ c∈ C, a∈ c ∧ a'∈ c) → 
(∃ c∈ C, a∉ c∧ a' ∈ c) → 
(∃ c∈ C, a∈ c∧ a' ∉ c) → 
(∃ c∈ C, a∉ c∧ a' ∉ c) → 
2 ≤ VCD C :=
begin
  intros h1 h2 h3 h4,
  have A1:a ≠ a',
  { cases h2 with c h2, cases h2 with h2 h3,
    intros contra,
    subst a',
    apply h3.left, apply h3.right },
  begin
    have A2:(({a,a'}:finset α).card:enat) = (2:enat),
    { simp [A1], refl },
    rw ← A2,
    apply shatters_card_le_VCD,
    rw shatters_iff,
    apply finset.forall_subset_card_2,
    { cases h4 with c h4,
      cases h4 with h4 h5,
      existsi [c, h4],
      simp,
      ext x,split;intros B1,
      simp at B1,
      cases B1 with B1 B2,
      cases B2; subst x; exfalso, apply h5.left, apply B1,
      apply h5.right, apply B1, simp at B1, apply false.elim B1 },
    { cases h3 with c h3, cases h3 with h3 h5,
      existsi [c, h3],
      simp,
      ext x,split;intros B1,
      simp at B1,
      cases B1 with B1 B2,
      cases B2; subst x, simp,
      exfalso, apply h5.right, apply B1,
      simp at B1, subst x, simp, apply h5.left },
    { cases h2 with c h2, cases h2 with h2 h5,
      existsi [c, h2],
      simp,
      ext x,split;intros B1,
      simp at B1,
      cases B1 with B1 B2,
      cases B2; subst x,exfalso, apply h5.left,
      apply B1, simp,
      simp at B1, subst x, simp, apply h5.right },
    { cases h1 with c h1, cases h1 with h1 h5,
      existsi [c, h1],
      simp,
      ext x,split;intros B1,
      simp at B1,
      cases B1 with B1 B2,
      cases B2; subst x; simp,
      simp at B1, cases B1; subst x; simp [h5], },
  end
end

@[simp]
lemma set_Icc_mem_intervals {a b:α}[L:linear_order α]:set.Icc a b ∈ intervals α :=
begin
  simp [intervals], existsi [a, b], simp,
end

@[simp]
lemma set_Ioc_mem_intervals {a b:α}[L:linear_order α]:set.Ioc a b ∈ intervals α :=
begin
  simp [intervals], existsi [a, b], simp,
end

@[simp]
lemma set_Ico_mem_intervals {a b:α}[L:linear_order α]:set.Ico a b ∈ intervals α :=
begin
  simp [intervals], existsi [a, b], simp,
end

@[simp]
lemma set_Ioo_mem_intervals {a b:α}[L:linear_order α]:set.Ioo a b ∈ intervals α :=
begin
  simp [intervals], existsi [a, b], simp,
end

@[simp]
lemma set_Iio_mem_thresholds {a:α}[L:linear_order α]:set.Iio a ∈ thresholds α :=
begin
  simp [thresholds], existsi a, simp,
end

@[simp]
lemma set_Iic_mem_thresholds {a:α}[L:linear_order α]:set.Iic a ∈ thresholds α :=
begin
  simp [thresholds], existsi [a], simp,
end


@[simp]
lemma set_Ioi_mem_thresholds {a:α}[L:linear_order α]:set.Ioi a ∈ thresholds α :=
begin
  simp [thresholds], existsi a, simp,
end

@[simp]
lemma set_Ici_mem_thresholds {a:α}[L:linear_order α]:set.Ici a ∈ thresholds α :=
begin
  simp [thresholds], existsi [a], simp,
end


lemma intervals_convex {a b c : α} [linear_order α] (T:set α): (T∈ intervals α) →
(a ≤ b) → (b ≤ c) → (a∈ T) → (c ∈ T) → (b∈ T) :=
begin
  intros A1 A2 A3 A4 A5,
  simp [intervals] at A1,
  cases A1 with d A1,
  cases A1 with e A1,
  cases A1,
  { subst T, simp at A4, simp at A5, simp, split,
    apply lt_of_lt_of_le A4.left A2,
    apply lt_of_le_of_lt A3 A5.right },
  cases A1,
  { subst T, simp at A4, simp at A5, simp, split,
    apply lt_of_lt_of_le A4.left A2,
    apply le_trans A3 A5.right },
  cases A1,
  { subst T, simp at A4, simp at A5, simp, split,
    apply le_trans A4.left A2,
    apply lt_of_le_of_lt A3 A5.right },
  { subst T, simp at A4, simp at A5, simp, split,
    apply le_trans A4.left A2,
    apply le_trans A3 A5.right },
end

lemma thresholds_convex {a b c : α} [linear_order α] (T:set α): (T∈ thresholds α) →
(a ≤ b) → (b ≤ c) → (a∈ T) → (c ∈ T) → (b∈ T) :=
begin
  intros A1 A2 A3 A4 A5,
  simp [thresholds] at A1,
  cases A1 with d A1,
  --cases A1 with e A1,
  cases A1,
  { subst T, simp at A4, simp at A5, simp, 
    apply lt_of_le_of_lt A3 A5 },
  cases A1,
  { subst T, simp at A4, simp at A5, simp, 
    apply le_trans A3 A5 },
  cases A1,
  { subst T, simp at A4, simp at A5, simp, 
    apply lt_of_lt_of_le A4 A2 },
  { subst T, simp at A4, simp at A5, simp,
    apply le_trans A4 A2 },
end

lemma enat.coe_two:((2:nat):enat)=2 := 
begin
  have A1:(1:enat) + (1:enat) = (2:enat),
  { refl },
  have A2:(1:nat) + (1:nat) = (2:nat),
  { refl },
  rw ← A2,
  rw ← A1,
  rw enat.coe_add,
  rw enat.coe_one,
end 


lemma convex_VCD_le_2 [L:linear_order α] (C:set (set α)):(∀ (a b c:α) (d∈ C), (a ≤ b) → (b ≤ c) → (a ∈ d) → (c∈ d) → (b ∈ d)) → VCD C ≤ 2 :=
begin
  intros h_convex,
  have A1:(2:enat) = (2:nat),
  { rw enat.coe_two, },
  rw A1,
  apply VCD_le',
  intros S,
  intros h_S,
  have h_shatters := finset.card_three h_S,
  clear h_S,
  cases h_shatters with a h_shatters,
  cases h_shatters with b h_shatters,
  cases h_shatters with c h_shatters,
  cases h_shatters with h_a_lt_b h_shatters,
  cases h_shatters with h_b_lt_c h_shatters,
  subst S,
  have h_a_ne_b:a ≠ b,
  { intros contra, subst b, apply lt_irrefl a h_a_lt_b },
  have h_b_ne_c:b ≠ c,
  { intros contra, subst b, apply lt_irrefl c h_b_lt_c },
  
  intros contra,
  rw shatters_iff at contra,
  
  --cases contra with S' h_subset,
  have contra2 := contra {a,c} _,
  cases contra2 with d contra2,
  cases contra2 with contra2 contra3,
  simp at contra3,
  rw set.two_of_three at contra3,
  apply contra3.right.left,
  apply h_convex a b c d contra2 (le_of_lt h_a_lt_b) (le_of_lt h_b_lt_c) contra3.left contra3.right.right,
  apply h_a_ne_b,
  apply h_b_ne_c,
  simp [finset.insert_subset],
end

lemma intervals_VCD_2 [L:linear_order α] [decidable_eq α]: (∃ a b:α, a ≠ b) → VCD (intervals α) = 2 := begin
  intros h,
  apply le_antisymm,
  { /- In one dimension, a hypothesis space with convex hypotheses
       has a VCD less than or equal to 2. -/
    apply convex_VCD_le_2,
    intros a b c d h_d_mem h_a_le_b h_b_le_c h_a_mem h_b_mem,
    apply intervals_convex _ h_d_mem h_a_le_b h_b_le_c,
    apply h_a_mem,
    apply h_b_mem,
    },
  { have h2 := non_singleton_two h,
    cases h2 with a h2,
    cases h2 with b h2,
    apply @two_le_VCD _ a b,
    { existsi [set.Icc a b], simp [le_of_lt h2] },
    { existsi [set.Ioc a b], simp [le_of_lt h2, h2] },
    { existsi [set.Ico a b], simp [le_of_lt h2, h2] },
    { existsi [set.Ioo a b], simp [le_of_lt h2, h2] } },
end

lemma thresholds_VCD_2 [L:linear_order α] [decidable_eq α]: (∃ a b:α, a ≠ b) → VCD (thresholds α) = 2 := begin
  intros h,
  apply le_antisymm,
  { /- In one dimension, a hypothesis space with convex hypotheses
       has a VCD less than or equal to 2. -/
    apply convex_VCD_le_2,
    intros a b c d h_d_mem h_a_le_b h_b_le_c h_a_mem h_b_mem,
    apply thresholds_convex _ h_d_mem h_a_le_b h_b_le_c,
    apply h_a_mem,
    apply h_b_mem,
    },
  { have h2 := non_singleton_two h,
    cases h2 with a h2,
    cases h2 with b h2,
    apply @two_le_VCD _ a b,
    { existsi [set.Iic b], simp [le_of_lt h2] },
    { existsi [set.Ioi a], simp [le_of_lt h2, h2] },
    { existsi [set.Iic a], simp [le_of_lt h2, h2], },
    { existsi [set.Iio a], simp [le_of_lt h2, h2] } },
end

def set_of_sets.prod {β:Type*} (Cα:set (set α)) (Cβ:set (set β)):set (set (α × β)) := 
{p|∃ (A:set α) (B:set β), (A∈ Cα)  ∧ (B∈ Cβ) ∧ p = A.prod B}  







--noncomputable def get_max_of_three_real (a b c:real):real := get_max_of_three real a b c
--α
end VC_PAC_problem
