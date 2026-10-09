import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.GeneratorResolvent

/-! The actual unitary dilation and its generated strong derivative determine the right-resolvent identity. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem dilation_eigenVelocity_zero (value : BurnolL2) (alpha : ℂ)
    (positive : 0 < alpha.re)
    (differential : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) value)
      (alpha • value) 0) : value = 0 := by
  let : InnerProductSpace ℝ BurnolL2 := InnerProductSpace.rclikeToReal ℂ BurnolL2
  have energy := differential.norm_sq
  have constant : (fun h : ℝ => ‖burnolMultiplicativeDilation (-h / 2) value‖ ^ 2) =
      fun _ : ℝ => ‖value‖ ^ 2 := by
    funext h
    rw [(burnolMultiplicativeDilation (-h / 2)).norm_map]
  rw [constant] at energy
  have zero := energy.unique (hasDerivAt_const (0 : ℝ) (‖value‖ ^ 2))
  change 2 * (inner ℂ (burnolMultiplicativeDilation (-0 / 2) value) (alpha • value)).re = 0 at zero
  rw [neg_zero, zero_div, burnolMultiplicativeDilation_zero,
    inner_smul_right (𝕜 := ℂ) value value alpha,
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) value] at zero
  have realSquare : (‖value‖ : ℂ) ^ 2 = (‖value‖ ^ 2 : ℝ) := by norm_cast
  change 2 * (alpha * ((‖value‖ : ℂ) ^ 2)).re = 0 at zero
  rw [realSquare, Complex.mul_re] at zero
  change 2 * (alpha.re * ‖value‖ ^ 2 - alpha.im * 0) = 0 at zero
  have square : ‖value‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖value‖]
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg value]

/-- The original isometric orbit fixes the solution of its inhomogeneous strong equation. -/
theorem burnolDirectRightResolvent_of_strongEquation (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (source value : BurnolL2)
    (differential : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) value)
      ((z - 1 / 4) • value + source) 0) :
    value = burnolDirectRightResolvent z source := by
  apply sub_eq_zero.mp
  apply dilation_eigenVelocity_zero _ (z - 1 / 4)
  · norm_num
    linarith
  · have generated := differential.sub (burnolDirectRightResolventOrbit_hasDerivAt z rightQuarter source)
    convert! generated using 1
    · funext h
      rw [map_sub]
      rfl
    · module

theorem burnolDirectRightResolvent_smul (z : ℂ) (c : ℂ) (value : BurnolL2) :
    burnolDirectRightResolvent z (c • value) = c • burnolDirectRightResolvent z value := by
  unfold burnolDirectRightResolvent burnolDirectRightResolventIntegrand
  simp only [map_smul, smul_comm (positiveMellinQuarterRightResolventWeight z _) c]
  rw [integral_smul]
  module

theorem burnolDirectRightResolvent_sub (z : ℂ) (rightQuarter : 1 / 4 < z.re) (left right : BurnolL2) :
    burnolDirectRightResolvent z (left - right) =
      burnolDirectRightResolvent z left - burnolDirectRightResolvent z right := by
  unfold burnolDirectRightResolvent
  have integrands (h : ℝ) : burnolDirectRightResolventIntegrand z (left - right) h =
      burnolDirectRightResolventIntegrand z left h - burnolDirectRightResolventIntegrand z right h := by
    simp [burnolDirectRightResolventIntegrand, map_sub, smul_sub]
  simp_rw [integrands]
  rw [integral_sub (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter left)
    (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter right)]
  module

/-- The same unitary action fixes both inverses, so their source-generated difference is a resolvent composition. -/
theorem burnolDirectRightResolvent_identity (z w : ℂ)
    (zRight : 1 / 4 < z.re) (wRight : 1 / 4 < w.re) (value : BurnolL2) :
    burnolDirectRightResolvent z value - burnolDirectRightResolvent w value =
      (z - w) • burnolDirectRightResolvent z (burnolDirectRightResolvent w value) := by
  rw [← burnolDirectRightResolvent_smul]
  apply burnolDirectRightResolvent_of_strongEquation z zRight
  have generated := (burnolDirectRightResolventOrbit_hasDerivAt z zRight value).sub
    (burnolDirectRightResolventOrbit_hasDerivAt w wRight value)
  convert! generated using 1
  · funext h
    rw [map_sub]
    rfl
  · module

theorem burnolDirectRightResolvent_reflects_zero (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : BurnolL2) (zero : burnolDirectRightResolvent z value = 0) : value = 0 := by
  have differential := burnolDirectRightResolventOrbit_hasDerivAt z rightQuarter value
  simp only [zero, map_zero, smul_zero, zero_add] at differential
  exact differential.unique (hasDerivAt_const (0 : ℝ) (0 : BurnolL2))

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
