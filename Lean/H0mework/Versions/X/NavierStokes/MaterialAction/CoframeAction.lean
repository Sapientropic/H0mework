import H0mework.Versions.X.NavierStokes.MaterialAction.MotherAction

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativePauliCoframeAction

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9CU.Fluid Stage9C.Material.SpinPair StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction StageNineMatterVariation
open StageNineDynamicBreakingVacuum
open StageNineP286GaugeConnectionActionVariation StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity StageNineMatterCovariantDerivativeAffine
open StageNineCurrentCoframeMatterTemporalPrincipal
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorMatterGaugeCovariantJet SU7ExteriorBreakingYukawa
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction

noncomputable section

def normalizedVelocity (velocity : PhysicalSpace) : Vector := fun direction => velocity direction / 4

theorem source_matter (velocity : PhysicalSpace) :
    NativeCanonicalFluidCoframe.matter velocity = lowerMatter (hermitianBlock (normalizedVelocity velocity)) := by
  rw [NativeCanonicalFluidCoframe.matter, InitialLift.matter, lowerMatter_apply]
  apply congrArg sourceColorDiracMatter
  funext spin color
  fin_cases spin <;> fin_cases color <;>
    simp [InitialLift.coefficients, lowerCoefficients, hermitianBlock, normalizedVelocity, pauli,
      Fin.sum_univ_three] <;> ring

def compensation (velocity : PhysicalSpace) (direction : Fin 4) : ℝ :=
  if direction = 0 then 1 else (NativeCanonicalFluidCoframe.density velocity)⁻¹

theorem compensation_diagonal (velocity : PhysicalSpace) (direction : Fin 4) :
    compensation velocity direction * (NativeCanonicalFluidCoframe.diagonal velocity direction)⁻¹ =
      (NativeCanonicalFluidCoframe.scale velocity ^ 2)⁻¹ := by
  fin_cases direction <;> simp [compensation, NativeCanonicalFluidCoframe.diagonal,
    ← NativeCanonicalFluidCoframe.scale_cube velocity]
  all_goals field_simp [(NativeCanonicalFluidCoframe.scale_pos velocity).ne']

theorem gamma_spinAction (direction : Fin 4) :
    diracGamma 0 * spinActionMatrix direction = diracGamma direction := by
  have square : diracGamma 0 * diracGamma 0 = -(1 : DiracMatrix) := diracGammaZero_sq
  fin_cases direction <;> simp [spinActionMatrix, ← mul_assoc, square]

theorem gamma_product (velocity : PhysicalSpace) (direction : Fin 4) :
    inverseCoframeDiracGamma {coframe := NativeCanonicalFluidCoframe.coframe velocity, derivative := 0} 0 *
        spinActionMatrix direction =
      (compensation velocity direction : ℂ) • inverseCoframeDiracGamma
        {coframe := NativeCanonicalFluidCoframe.coframe velocity, derivative := 0} direction := by
  have realVersion :
      inverseCoframeDiracGamma {coframe := NativeCanonicalFluidCoframe.coframe velocity, derivative := 0} 0 *
          spinActionMatrix direction =
        compensation velocity direction • inverseCoframeDiracGamma
          {coframe := NativeCanonicalFluidCoframe.coframe velocity, derivative := 0} direction := by
    rw [NativeCanonicalFluidCoframe.inverseGamma, NativeCanonicalFluidCoframe.inverseGamma,
      Matrix.smul_mul, gamma_spinAction, smul_smul, compensation_diagonal]
    rfl
  exact realVersion.trans (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)

theorem temporalPrincipal_spinAction (velocity : PhysicalSpace) (direction : Fin 4)
    (matter : DiracExteriorMatterCarrier) :
    currentCoframeMatterTemporalPrincipal (NativeCanonicalFluidCoframe.coframe velocity)
        (diracMatrixMatterAction (spinActionMatrix direction) matter) =
      (compensation velocity direction : ℂ) • (Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma
          {coframe := NativeCanonicalFluidCoframe.coframe velocity, derivative := 0} direction) matter) := by
  change Complex.I • diracMatrixMatterAction _ (diracMatrixMatterAction _ matter) = _
  rw [← LinearMap.comp_apply, ← diracMatrixMatterAction_mul, gamma_product,
    diracMatrixMatterAction_smul_matrix]
  simp only [smul_smul]
  rw [mul_comm Complex.I]

def connection (velocity : PhysicalSpace) (target : Block) (direction : Fin 4) : P286LieBlockData :=
  compensation velocity direction • gaugePotential (control (normalizedVelocity velocity) target) direction

theorem connection_vacuum_zero (velocity : PhysicalSpace) (target : Block) (direction : Fin 4) :
    scalarMotherLieAction (p286LieBlockEmbed (connection velocity target direction))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  rw [connection, p286LieBlockEmbed_real_smul, scalarMotherLieAction_real_smul,
    gaugePotential_vacuum_zero, smul_zero]

def gaugeIncrement (velocity : PhysicalSpace) (target : Block) (direction : Fin 4) : DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction (p286LieBlockEmbed (connection velocity target direction))
    (NativeCanonicalFluidCoframe.matter velocity)

def gaugeVectorAt (frame : LorentzianCoframe) (increment : Fin 4 → DiracExteriorMatterCarrier) :=
  Complex.I • ∑ direction, diracMatrixMatterAction
    (inverseCoframeDiracGamma {coframe := frame, derivative := 0} direction) (increment direction)

def normalizedDerivative (velocity : PhysicalSpace) (increment : Fin 4 → DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  ∑ direction, ((compensation velocity direction)⁻¹ : ℂ) •
    diracMatrixMatterAction (spinActionMatrix direction) (increment direction)

theorem derivativeVector_eq_principal (velocity : PhysicalSpace)
    (increment : Fin 4 → DiracExteriorMatterCarrier) :
    gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) increment =
      currentCoframeMatterTemporalPrincipal (NativeCanonicalFluidCoframe.coframe velocity)
        (normalizedDerivative velocity increment) := by
  have nonzero (direction : Fin 4) : compensation velocity direction ≠ 0 := by
    unfold compensation
    split_ifs <;> simp [(NativeCanonicalFluidCoframe.density_pos velocity).ne']
  have complex_nonzero (direction : Fin 4) : (compensation velocity direction : ℂ) ≠ 0 := by
    exact_mod_cast nonzero direction
  simp only [normalizedDerivative, map_sum, map_smul, temporalPrincipal_spinAction,
    smul_smul, inv_mul_cancel_left₀ (complex_nonzero _)]
  simp only [gaugeVectorAt, Finset.smul_sum]

theorem actual_derivative_inverse (velocity : PhysicalSpace)
    (increment : Fin 4 → DiracExteriorMatterCarrier) :
    currentCoframeMatterTemporalPrincipalInverse (NativeCanonicalFluidCoframe.coframe velocity)
        (gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) increment) =
      normalizedDerivative velocity increment := by
  rw [derivativeVector_eq_principal, currentCoframeMatterTemporalPrincipalInverse_left _
    (NativeCanonicalFluidCoframe.temporalPrincipal_noncharacteristic velocity)]

theorem gaugeVectorAt_eq_mother (source : SmoothUnifiedSource)
    (point : ProofFreeRicherAnholonomicSource.BasePoint) (field : StageNineContinuumPointField)
    (increment : Fin 4 → DiracExteriorMatterCarrier) :
    gaugeVectorAt field.coframe increment = matterGaugeConnectionVariationVector source 0 point field increment := by
  simp only [gaugeVectorAt, matterGaugeConnectionVariationVector, matterGaugeKineticSum,
    matterDerivativeFrameRelative_zeroChart]

def gaugeVector (velocity : PhysicalSpace) (target : Block) :=
  gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (gaugeIncrement velocity target)

/-- The coefficients compensate the source frame inside the original temporal Dirac principal. -/
theorem gaugeVector_eq_principal (velocity : PhysicalSpace) (target : Block) :
    gaugeVector velocity target =
      currentCoframeMatterTemporalPrincipal (NativeCanonicalFluidCoframe.coframe velocity)
        (wholeAction (normalizedVelocity velocity) (control (normalizedVelocity velocity) target)) := by
  simp only [gaugeVector, gaugeVectorAt, gaugeIncrement, connection, source_matter,
    p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul, LinearMap.smul_apply,
    map_smul, Finset.smul_sum, wholeAction, map_sum, temporalPrincipal_spinAction]
  apply Finset.sum_congr rfl
  intro direction _
  simp only [smul_smul]
  rw [mul_comm Complex.I]

/-- The actual mother time-response inverse consumes the generated connection, retaining its exact phase residual. -/
theorem actual_inverse_response (velocity : PhysicalSpace) (target : Block) :
    currentCoframeMatterTemporalPrincipalInverse (NativeCanonicalFluidCoframe.coframe velocity)
        (gaugeVector velocity target) =
      lowerMatter target - (phaseResidual (normalizedVelocity velocity) target : ℂ) • lowerMatter 1 := by
  rw [gaugeVector_eq_principal,
    currentCoframeMatterTemporalPrincipalInverse_left _
      (NativeCanonicalFluidCoframe.temporalPrincipal_noncharacteristic velocity),
    controlled_wholeAction]

end
end SaturationMonoid.NavierStokes.NativePauliCoframeAction
