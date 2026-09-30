import H0mework.Physics.LowEnergy.DrivenInteraction.Coefficients

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction
open LightModes LightInteraction Filter Topology
noncomputable section

def growthPolynomial (v w : ℂ) : ℂ := sourcePolynomial v w+2*rebuild evenTerms v w
def growthNormal (q : ℝ) : ℝ := currentNormal q+2*q^2*value evenTerms (axialRoot q) (q^2)

theorem growth_polynomial_scaling (r w : ℂ) :
    growthPolynomial (w*r) w=w*(r+w*complexValue responseTerms r w+2*w*complexValue evenTerms r w) := by
  rw [growthPolynomial,source_polynomial_scaling,rebuild_scaling evenTerms even_admissible]
  ring

theorem source_table_bound (terms : List Term) (q : ℝ) (small : |q| ≤ momentumRadius) :
    |q^2*value terms (axialRoot q) (q^2)| ≤ momentumRadius^2*coefficientBound terms := by
  have window := (sourceRoot .axialPhase).root_in_window (q^2)
  have rbound := (sourceRoot .axialPhase).window_bound _ window
  have qbound : |q^2|≤1 := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg q) (small.trans momentumRadius_bound) 2).trans (by norm_num)
  have qsq : q^2 ≤ momentumRadius^2 := by nlinarith [abs_nonneg q,sq_abs q]
  rw [abs_mul,abs_of_nonneg (sq_nonneg q)]
  exact mul_le_mul qsq (value_bound terms _ _ rbound qbound) (abs_nonneg _) (sq_nonneg _)

theorem growth_normal_positive (q : ℝ) (small : |q| ≤ momentumRadius) : 0<growthNormal q := by
  have first := (source_table_bound responseTerms q small).trans_lt response_error_small
  have second := source_table_bound evenTerms q small
  have lower := ((sourceRoot .axialPhase).root_in_window (q^2)).1
  change (125/162 : ℝ)-1/20≤axialRoot q at lower
  have bounded : 2*|q^2*value evenTerms (axialRoot q) (q^2)|<1/20 := by
    nlinarith [even_error_small]
  unfold growthNormal currentNormal
  nlinarith [(abs_lt.mp first).1,neg_le_abs (q^2*value evenTerms (axialRoot q) (q^2))]

theorem growth_normal_limit : Tendsto growthNormal (𝓝 0) (𝓝 (125/162 : ℝ)) := by
  have square : Tendsto (fun q : ℝ => q^2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 2).tendsto (0 : ℝ)
  have table := (value_continuous evenTerms).tendsto ((125/162 : ℝ),0)
  have generated := current_normal_limit.add
    ((square.const_mul 2).mul (table.comp (axial_root_limit.prodMk_nhds square)))
  unfold growthNormal
  simpa only [mul_zero,zero_mul,add_zero,Function.comp_def] using generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction
