import measure_theory.measurable_space
import measure_theory.integration
import measure_theory.borel_space


namespace measure_theory

section product
universes u_1 u_2
variables (α:Type u_1) (β:Type u_2) (s:set α)
open measure_theory measure_theory.simple_func

lemma lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
  {α} [M:measurable_space α] (μ:measure_theory.measure α) 
  (Mf:measurable_space α) (hMf:Mf ≤ M)
  (c:ennreal) (T:set α) (h_meas_T:M.measurable_set' T)
  (h_ind:∀ (S:set α), Mf.measurable_set' S →
  (μ S * μ T = μ (S ∩ T)))   
  (f:α → ennreal) (h_meas_f:@measurable α ennreal Mf _ f):
@lintegral α M μ (λ a, (f * (T.indicator (λ (_x : α), c))) a) =
  @lintegral α M μ f * 
  @lintegral α M μ (T.indicator (λ (_x : α), c)) :=
begin
  revert f,
  apply measurable.ennreal_induction,
  { intros c' s' h_meas_s',
      have h1:(λ a, (s'.indicator (λ (_x : α), c') * T.indicator (λ (_x : α), c)) a) =
         (λ a, (s' ∩ T).indicator (λ (_x :α), c * c') a),
      { ext1 a, cases classical.em (a ∈ s' ∩ T) with h1_1 h1_1,
        { rw set.indicator_of_mem h1_1, simp at h1_1,
          simp, rw if_pos,
          rw if_pos,
          rw mul_comm,
          apply h1_1.right,
          apply h1_1.left },
        { rw set.indicator_of_not_mem h1_1, 
          simp,
          simp at h1_1,
          intros h1_2 h1_3,
          exfalso,
          apply h1_1,
          apply h1_2,
          apply h1_3 } },
      rw h1,
      rw measure_theory.lintegral_indicator,
      rw measure_theory.lintegral_indicator,
      rw measure_theory.lintegral_indicator,
      simp,
      rw ← h_ind,
      ring, apply h_meas_s',
      apply h_meas_T,
      apply hMf,
      apply h_meas_s',
      apply measurable_set.inter,
      apply hMf,
      apply h_meas_s',
      apply h_meas_T  },
  { intros f' g h_univ h_meas_f' h_meas_g h_ind_f' h_ind_g,
    have h_measM_f' := measurable.mono h_meas_f' hMf (le_refl _),
    have h_measM_g := measurable.mono h_meas_g hMf (le_refl _),
    have h_indicator:@measurable α ennreal M ennreal.measurable_space (λ (a : α), T.indicator (λ (_x : α), c) a),
    { apply measurable.indicator,
      apply measurable_const,
      apply h_meas_T,   },
    have h8:(f' + g) * T.indicator (λ (_x : α), c)= 
             (λ a, (f' * (T.indicator (λ _, c))) a + (g * (T.indicator (λ _, c))) a),
    { ext1 a, simp [right_distrib] },
    rw h8,
    have h_add:(f' + g) = (λ a, (f' a + g a)),
   { refl },
   rw h_add,
   rw measure_theory.lintegral_add,
   rw measure_theory.lintegral_add,
   rw right_distrib,
   rw h_ind_f',
   rw h_ind_g,
   apply h_measM_f',
   apply h_measM_g,
   apply measurable.ennreal_mul,
   apply h_measM_f',
   apply h_indicator,
   apply measurable.ennreal_mul,
   apply h_measM_g, 
   apply h_indicator, },
  { intros f h_meas_f h_mono_f h_ind_f,
    have h_measM_f := (λ n, measurable.mono (h_meas_f n) hMf (le_refl _)),
    have h_mul:
     (λ a, ((λ (x : α), ⨆ (n : ℕ), f n x) * T.indicator (λ (_x : α), c)) a) =
      (λ (a : α), ⨆ (n : ℕ), (λ (x:α), f n x * (T.indicator (λ (_x : α), c) x)) a),
    { ext1 a, rw @pi.mul_apply, rw ennreal.supr_mul, },
    rw h_mul,
    rw lintegral_supr,
    rw lintegral_supr,
    rw ennreal.supr_mul,
    have h_mul2:(λ (n:ℕ), (@lintegral α M μ 
       (λ (x : α), f n x * T.indicator (λ (_x : α), c) x)))  =
        (λ n, @lintegral α M μ (f n) * @lintegral α M μ (T.indicator (λ (_x : α), c))), 
    { ext1 n, rw ← h_ind_f n, refl },
    rw h_mul2,
    apply h_measM_f,
    apply h_mono_f,
    { intros n,
      apply measurable.ennreal_mul, apply h_measM_f, apply measurable.indicator,
      apply measurable_const, apply h_meas_T },
    { intros m n h_le a,
      apply ennreal.mul_le_mul, apply h_mono_f, apply h_le, apply le_refl _  },
    },
end

lemma lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space 
{α} [M:measurable_space α] (μ:measure_theory.measure α) 
(Mf:measurable_space α) (Mg:measurable_space α) (hMf:Mf ≤ M)
(hMg:Mg ≤ M)
(h_ind:∀ (S T:set α), Mf.measurable_set' S → Mg.measurable_set' T →
 (μ S * μ T = μ (S ∩ T)))   
(f g:α → ennreal) (h_meas_f:@measurable α ennreal Mf _ f) (h_meas_g:@measurable α ennreal Mg _ g):
   @lintegral α M μ (λ a, (f * g) a) =
   @lintegral α M μ f * 
   @lintegral α M μ g :=
begin
  revert g,
  have h_meas_Mf:∀ ⦃f:α → ennreal⦄, (@measurable α ennreal Mf _ f) → (@measurable α ennreal M _ f),
  { intros f' h_meas_f', apply measurable.mono h_meas_f' hMf, apply le_refl _ }, 
  have h_meas_Mg:∀ ⦃f:α → ennreal⦄, (@measurable α ennreal Mg _ f) → (@measurable α ennreal M _ f),
  { intros f' h_meas_f', apply measurable.mono h_meas_f' hMg, apply le_refl _ }, 
  have H1:= h_meas_Mf h_meas_f,
  apply measurable.ennreal_induction,
  intros c s h_s,
  { apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator,
    apply hMf, 
    apply hMg,
    apply h_s,
    { intros S h_meas_S,
      apply h_ind, apply h_meas_S,
      apply h_s, },
    apply h_meas_f,
 },
  { intros f' g h_univ h_measMg_f' h_measMg_g h_ind_f' h_ind_g',
    have h_measM_f' := h_meas_Mg h_measMg_f',
    have h_measM_g := h_meas_Mg h_measMg_g,
    have h_add:(f' + g) = (λ a, (f' a + g a)),
    { refl },
    rw h_add,
    rw measure_theory.lintegral_add,
    have h8:(λ a, (f * λ a', (f' a' + g a')) a ) = (λ a, (f a * f' a) + (f a * g a)),
    { ext1 a, simp [left_distrib], },
    rw h8,
    rw measure_theory.lintegral_add,
    rw left_distrib,
    have h9:(λ a, (f * f') a) = (λ a, f a * f' a),
    { ext1 a, refl },
    rw ← h9,
    rw h_ind_f',
    have h10:(λ a, (f * g) a) = (λ a, f a * g a),
    { ext1 a, refl },
    rw ← h10,
    rw h_ind_g',
    apply measurable.ennreal_mul,
    apply H1,
    apply h_measM_f',
    apply measurable.ennreal_mul,
    apply H1,
    apply h_measM_g,
    apply h_measM_f',
    apply h_measM_g },
  { intros f' h_meas_f' h_mono_f' h_ind_f',
    have h_measM_f' := (λ n, h_meas_Mg (h_meas_f' n)),
    have h_mul:(λ (a : α), (f * λ (x : α), ⨆ (n : ℕ), f' n x) a) = 
      (λ (a : α), ⨆ (n : ℕ), (λ (x:α), (f x * f' n x)) a),
    { ext1 a, simp, rw ennreal.mul_supr },
    rw h_mul,
    rw lintegral_supr,
    rw lintegral_supr,
    rw ennreal.mul_supr,
    have h_mul2:(λ (n:ℕ), (@lintegral α M μ (λ (x : α), f x * f' n x))) =
        (λ n, @lintegral α M μ f * @lintegral α M μ (f' n)), 
    { ext1 n, rw ← h_ind_f' n, refl },
    rw h_mul2,
    { apply h_measM_f', },
    { apply h_mono_f', },
    { intros n, apply measurable.ennreal_mul,
      apply H1, apply h_measM_f' },
    { intros n m h_le a, apply ennreal.mul_le_mul,
       apply le_refl _, apply h_mono_f' h_le, },
},
end


lemma lintegral_mul_eq_lintegral_mul_lintegral_of_independent_fn {α} [M:measurable_space α] (μ:measure_theory.measure α) 
(f g:α → ennreal) (h_meas_f:measurable f) (h_meas_g:measurable g)
(h_ind:∀ (S T:set ennreal), measurable_set S → measurable_set T →
 (μ (f ⁻¹' S) * μ (g ⁻¹' T) = μ ((f ⁻¹' S) ∩ (g ⁻¹' T)))):
∫⁻ (a : α), (f * g) a ∂μ =
(∫⁻ (a : α), f a ∂μ) *
(∫⁻ (a : α), g a ∂μ) :=
begin
  let Mf := ennreal.measurable_space.comap f,
  let Mg := ennreal.measurable_space.comap g,
  begin
    apply lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space μ Mf Mg,
    { rw measurable_iff_comap_le at h_meas_f,
      apply h_meas_f },
    { rw measurable_iff_comap_le at h_meas_g,
      apply h_meas_g },
    { intros S T h_S h_T,
      have h_S':∃ (A:set ennreal), (measurable_set A) ∧ (f ⁻¹' A = S),
      { apply h_S },
      have h_T':∃ (B:set ennreal), (measurable_set B) ∧ (g ⁻¹' B = T),
      { apply h_T },
      cases h_S' with A h_S',
      cases h_T' with B h_T',
      rw ← h_S'.right,
      rw ← h_T'.right,
      apply h_ind,
      apply h_S'.left,
      apply h_T'.left },
    { rw measurable_iff_comap_le, apply le_refl _ },
    { rw measurable_iff_comap_le, apply le_refl _ },
  end
end
end product
end measure_theory

