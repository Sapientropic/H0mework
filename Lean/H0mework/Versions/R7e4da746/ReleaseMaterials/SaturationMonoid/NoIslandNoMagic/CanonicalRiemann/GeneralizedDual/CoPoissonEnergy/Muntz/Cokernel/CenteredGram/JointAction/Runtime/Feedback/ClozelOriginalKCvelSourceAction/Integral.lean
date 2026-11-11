import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators

def actualDilationIntegralLinear (h : ℝ) : BurnolL2 →ₗ[ℂ] BurnolL2 where
  toFun value := ∫ t : ℝ in (0 : ℝ)..h, burnolMultiplicativeDilation t value
  map_add' left right := by
    simp only [map_add]
    exact intervalIntegral.integral_add
      ((burnolMultiplicativeDilation_stronglyContinuous left).intervalIntegrable 0 h)
      ((burnolMultiplicativeDilation_stronglyContinuous right).intervalIntegrable 0 h)
  map_smul' scalar value := by
    simp only [map_smul]
    exact intervalIntegral.integral_smul scalar _

def actualDilationIntegral (h : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (actualDilationIntegralLinear h).mkContinuous |h| (by
    intro value
    change ‖∫ t : ℝ in (0 : ℝ)..h, burnolMultiplicativeDilation t value‖ ≤ |h| * ‖value‖
    have bound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := h) (C := ‖value‖)
      (fun t _ => le_of_eq ((burnolMultiplicativeDilation t).norm_map value))
    simpa only [sub_zero,mul_comm] using bound)

def actualVelocityIntegralStock (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ) : BurnolL2 :=
  actualDilationIntegral h (actualVelocityStock coordinate N) +
  actualDilationIntegral (-h) (actualVelocityStock coordinate N)

theorem actual_velocity_integral_stock_tendsto (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    Tendsto (actualVelocityIntegralStock coordinate h) atTop
      (𝓝 (OriginalKBoundarySourceAction.actualCorrectedVelocityIntegral coordinate h)) := by
  have source := actual_velocity_stock_tendsto coordinate
  exact ((actualDilationIntegral h).continuous.tendsto _).comp source |>.add
    (((actualDilationIntegral (-h)).continuous.tendsto _).comp source)

def actualVelocityIntegralPriceStock (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (h : ℝ) (N : ℕ) : ℂ :=
  inner ℂ (test : BurnolL2) (actualVelocityIntegralStock coordinate h N)

theorem actual_velocity_price_stock_tendsto (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (h : ℝ) :
    Tendsto (actualVelocityIntegralPriceStock coordinate test h) atTop
      (𝓝 (OriginalKBoundarySourceAction.actualCorrectedVelocityPrice coordinate test h)) := by
  rw [← OriginalKBoundarySourceAction.actual_corrected_velocity_integral_price]
  exact ((innerSL ℂ (test : BurnolL2)).continuous.tendsto _).comp
    (actual_velocity_integral_stock_tendsto coordinate h)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
