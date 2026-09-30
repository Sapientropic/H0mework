import H0mework.NavierStokes.CartanAction.Stress

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeSourceColorAction

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineFullDiracAdjointMaterial StageNineCoframeLocalDifferentiability StageNineHolonomicField
open StageNineFullDiracAdjointLocalOperator
open StageNineCurrentCoframeMatterTemporalPrincipal SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7MotherGaugeConnection
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativeMaterialAdjointPrincipal

noncomputable section

def connection (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ) (direction : Fin 4) : P286LieBlockData :=
  compensation velocity direction • gaugePotential coefficients direction

def operator (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ) (direction : Fin 4) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction (p286LieBlockEmbed (connection velocity coefficients direction))

def increment (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ) (direction : Fin 4) :
    DiracExteriorMatterCarrier := operator velocity coefficients direction (NativeCanonicalFluidCoframe.matter velocity)

theorem increment_block (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ) (direction : Fin 4) :
    increment velocity coefficients direction = (compensation velocity direction : ℂ) •
      lowerMatter (∑ color : Fin 3, (coefficients direction color : ℂ) •
        colorAction (hermitianBlock (normalizedVelocity velocity)) color) := by
  simp only [increment, operator, connection, p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_real_smul, LinearMap.smul_apply, source_matter,
    gaugePotential_action, map_sum, map_smul]

theorem vector_eq (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ) :
    gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (increment velocity coefficients) =
      currentCoframeMatterTemporalPrincipal (NativeCanonicalFluidCoframe.coframe velocity)
        (wholeAction (normalizedVelocity velocity) coefficients) := by
  simp only [gaugeVectorAt, increment, operator, connection, source_matter,
    p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul, LinearMap.smul_apply,
    map_smul, Finset.smul_sum, wholeAction, map_sum, temporalPrincipal_spinAction]
  apply Finset.sum_congr rfl
  intro direction _
  simp only [smul_smul]
  rw [mul_comm Complex.I]

theorem operator_commutes (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ)
    (direction : Fin 4) (matter : DiracExteriorMatterCarrier) :
    principal velocity direction (operator velocity coefficients direction matter) =
      operator velocity coefficients direction (principal velocity direction matter) := by
  have commuting := LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal
    (inverseCoframeDiracGamma {coframe := NativeCanonicalFluidCoframe.coframe velocity, derivative := 0} direction)
    (exteriorSpinorMotherLieAction (p286LieBlockEmbed (connection velocity coefficients direction)))) matter
  simpa only [principal, operator, diracExteriorMotherLieAction, LinearMap.smul_apply,
    map_smul, LinearMap.comp_apply] using congrArg (fun value => Complex.I • value) commuting

/-- The full canonical dual response is the adjoint of the actual source color response. -/
theorem dual_eq_adjoint (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ)
    (candidate : DiracExteriorMatterCarrier) :
    (∑ direction, NativeCanonicalFluidCoframe.dual velocity
      (principal velocity direction (operator velocity coefficients direction candidate))) =
        fullCanonicalDiracAdjoint
          (gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (increment velocity coefficients)) candidate := by
  have term (direction : Fin 4) : NativeCanonicalFluidCoframe.dual velocity
      (principal velocity direction (operator velocity coefficients direction candidate)) =
      fullCanonicalDiracAdjoint (principal velocity direction
        (increment velocity coefficients direction)) candidate := by
    rw [NativeSourceMaterialAdjoint.source_dual, principal_adjoint]
    have adjoint := LinearMap.congr_fun (fullCanonicalDiracAdjoint_motherLieConnection
      (p286LieBlockEmbed (connection velocity coefficients direction))
      (NativeCanonicalFluidCoframe.matter velocity)) (principal velocity direction candidate)
    change fullCanonicalDiracAdjoint (increment velocity coefficients direction) (principal velocity direction candidate) =
      -fullCanonicalDiracAdjoint (NativeCanonicalFluidCoframe.matter velocity)
        (operator velocity coefficients direction (principal velocity direction candidate)) at adjoint
    rw [adjoint, neg_neg, ← operator_commutes]
  simp only [term]
  simp only [gaugeVectorAt, principal, LinearMap.smul_apply, Finset.smul_sum]
  simp only [Fin.sum_univ_four, fullCanonicalDiracAdjoint_add, LinearMap.add_apply]

theorem vacuum_zero (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ) (direction : Fin 4) :
    scalarMotherLieAction (p286LieBlockEmbed (connection velocity coefficients direction))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  rw [connection, p286LieBlockEmbed_real_smul, scalarMotherLieAction_real_smul,
    gaugePotential_vacuum_zero, smul_zero]

end
end SaturationMonoid.NavierStokes.NativeSourceColorAction
