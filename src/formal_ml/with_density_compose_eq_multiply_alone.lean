import measure_theory.measurable_space
import measure_theory.integration
import measure_theory.borel_space


namespace measure_theory
namespace with_density
lemma compose_eq_multiply {Ω:Type*} [M:measurable_space Ω] (μ:measure_theory.measure Ω) (f g:Ω → ennreal) (H1:measurable f) (H2:measurable g):
 ∫⁻ a, g a ∂(μ.with_density f)  =  ∫⁻ a, (f * g) a ∂μ :=
begin
  revert g,
  apply measurable.ennreal_induction,
  {
    intros c s h_ms,
    rw lintegral_indicator,
    rw lintegral_const,
    rw measure_theory.measure.restrict_apply,
    have A1:∀ a, (f * s.indicator (λ _,c)) a = s.indicator (λ x, c * f x) a,
    {intro a,rw mul_comm,simp},
    rw lintegral_congr A1,
    rw lintegral_indicator,
    rw measure_theory.with_density_apply,
    rw lintegral_const_mul,
    repeat {simp [h_ms,H1,is_measurable.univ]},
  },
  {
    intros g h B1 B2 B3 B4 B5,
    simp,
    rw lintegral_add,
    have A1:∀ a, (f a) * ((g a) + (h a))  = (f * g ) a  + (f * h) a,
    {intro a,rw left_distrib,simp},
    rw [(measure_theory.lintegral_congr A1), B4, B5, measure_theory.lintegral_add],
    simp, 
    apply measurable.ennreal_mul H1 B2,
    apply measurable.ennreal_mul H1 B3,
    repeat {assumption},
  },
  {
    intros g h_mea_g h_mg h_ind,
    rw lintegral_supr,
    have C1:(λ n:ℕ, ∫⁻ (a : Ω), (g n) a ∂μ.with_density f) =λ n, ∫⁻ (a : Ω), (f * (g n)) a ∂μ,
    {apply funext,apply h_ind},
    rw C1,
    rw ← lintegral_supr,
    simp,
    have C2:∀ a, (⨆ (n : ℕ), f a *  (g n) a) = (f a * ⨆ (n : ℕ), (g n) a),
    { intro a, rw ennreal.mul_supr},
    rw lintegral_congr C2,
    intro n,
    apply measurable.ennreal_mul H1 (h_mea_g _),
    intros n1 n2 A4 ω,
    apply ennreal.mul_le_mul,
    apply le_refl _,
    apply h_mg,
    apply A4,
    intro n,
    apply h_mea_g,
    apply h_mg,
  },
end

#check 2



end with_density
end measure_theory
