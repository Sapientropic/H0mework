import H0mework.Versions.X.NavierStokes.PhysicalReadout.Material
import H0mework.Versions.X.NavierStokes.PhysicalReadout.Gradient
import H0mework.Physics.Matter.MatterPointwiseEquation

set_option autoImplicit false
open scoped Matrix

namespace SaturationMonoid.NavierStokes.NativeCanonicalFluidCoframe

open PhysicsCore
open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9CU.Fluid StageNineDiracMatterCoordinateCalculus
open StageNineP286GaugeConnectionVariationDensity
open StageNineLorentzConnectionVariation
open StageNineMatterPointwiseEquation StageNineMatterVariation StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open StageNineCurrentCoframeMatterTemporalPrincipal
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open NativePhysicalFourier NativePhysicalSource

noncomputable section

def density (velocity : PhysicalSpace) : ℝ := 2 + ‖velocity‖ ^ 2 / 8

theorem density_pos (velocity : PhysicalSpace) : 0 < density velocity := by
  unfold density
  positivity

def scale (velocity : PhysicalSpace) : ℝ := (density velocity) ^ ((3 : ℝ)⁻¹)

theorem scale_pos (velocity : PhysicalSpace) : 0 < scale velocity :=
  Real.rpow_pos_of_pos (density_pos velocity) _

theorem scale_cube (velocity : PhysicalSpace) : scale velocity ^ 3 = density velocity :=
  Real.rpow_inv_natCast_pow (density_pos velocity).le (by decide : (3 : ℕ) ≠ 0)

def diagonal (velocity : PhysicalSpace) : Fin 4 → ℝ :=
  ![scale velocity ^ 2, (scale velocity)⁻¹, (scale velocity)⁻¹, (scale velocity)⁻¹]

/-- The positive frame is generated from the same canonical time-current density. -/
def coframe (velocity : PhysicalSpace) : LorentzianCoframe := Matrix.diagonal (diagonal velocity)

theorem coframe_det (velocity : PhysicalSpace) : Matrix.det (coframe velocity) = (scale velocity)⁻¹ := by
  rw [coframe, Matrix.det_diagonal]
  rw [Fin.prod_univ_four]
  change scale velocity ^ 2 * (scale velocity)⁻¹ * (scale velocity)⁻¹ * (scale velocity)⁻¹ = _
  field_simp [(scale_pos velocity).ne']

theorem coframe_nondegenerate (velocity : PhysicalSpace) : Matrix.det (coframe velocity) ≠ 0 := by
  rw [coframe_det]
  exact inv_ne_zero (scale_pos velocity).ne'

theorem coframe_volume (velocity : PhysicalSpace) : |Matrix.det (coframe velocity)| = (scale velocity)⁻¹ := by
  rw [coframe_det, abs_of_pos (inv_pos.mpr (scale_pos velocity))]

theorem coframe_inv (velocity : PhysicalSpace) :
    (coframe velocity)⁻¹ = Matrix.diagonal (fun direction => (diagonal velocity direction)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [coframe, Matrix.diagonal_mul_diagonal]
  have nonzero (direction : Fin 4) : diagonal velocity direction ≠ 0 := by
    fin_cases direction <;> simp [diagonal, (scale_pos velocity).ne']
  simp [nonzero]

theorem inverseGamma (velocity : PhysicalSpace) (direction : Fin 4) :
    inverseCoframeDiracGamma {coframe := coframe velocity, derivative := 0} direction =
      ((diagonal velocity direction)⁻¹ : ℝ) • diracGamma direction := by
  simp [inverseCoframeDiracGamma, coframe_inv, Matrix.diagonal_apply]

/-- The generated physical time is noncharacteristic for the existing temporal matter principal. -/
theorem temporalPrincipal_scalar (velocity : PhysicalSpace) :
    coframeTemporalPrincipalScalar (coframe velocity) = ((scale velocity ^ 2)⁻¹) ^ 2 := by
  simp [coframeTemporalPrincipalScalar, coframe_inv, Matrix.diagonal_apply,
    minkowskiInternalSign, diagonal]

theorem temporalPrincipal_noncharacteristic (velocity : PhysicalSpace) :
    coframeTemporalPrincipalScalar (coframe velocity) ≠ 0 := by
  rw [temporalPrincipal_scalar]
  exact pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ (scale_pos velocity).ne'))

def matter (velocity : PhysicalSpace) := InitialLift.matter (fun direction => velocity direction)
def dual (velocity : PhysicalSpace) := InitialLift.dual (fun direction => velocity direction)

def densitizedCurrent (velocity : PhysicalSpace) (direction : Fin 4) : ℝ :=
  |Matrix.det (coframe velocity)| *
    (dual velocity (diracMatrixMatterAction
      (inverseCoframeDiracGamma {coframe := coframe velocity, derivative := 0} direction)
      (matter velocity))).re

theorem densitizedCurrent_eq (velocity : PhysicalSpace) (direction : Fin 4) :
    densitizedCurrent velocity direction = |Matrix.det (coframe velocity)| *
      (diagonal velocity direction)⁻¹ *
        (dual velocity (diracMatrixMatterAction (diracGamma direction) (matter velocity))).re := by
  rw [densitizedCurrent, inverseGamma]
  have scalar : diracMatrixMatterAction (((diagonal velocity direction)⁻¹ : ℝ) • diracGamma direction)
      (matter velocity) = ((diagonal velocity direction)⁻¹ : ℝ) •
        diracMatrixMatterAction (diracGamma direction) (matter velocity) := by
    exact diracMatrixMatterAction_real_smul_matrix_local _ _ _
  rw [scalar]
  change _ * ((dual velocity) ((((diagonal velocity direction)⁻¹ : ℝ) : ℂ) •
    diracMatrixMatterAction (diracGamma direction) (matter velocity))).re = _
  rw [map_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The actual inverse-coframe principal reads the original spatial velocity. -/
theorem densitizedCurrent_spatial (velocity : PhysicalSpace) (direction : Fin 3) :
    densitizedCurrent velocity direction.succ = velocity direction := by
  rw [densitizedCurrent_eq, coframe_volume]
  change _ * (diagonal velocity direction.succ)⁻¹ *
    (InitialLift.dual (fun direction => velocity direction)
      (diracMatrixMatterAction (diracGamma direction.succ)
        (InitialLift.matter (fun direction => velocity direction)))).re = _
  rw [InitialLift.spatialCurrent_eq]
  have spatial : diagonal velocity direction.succ = (scale velocity)⁻¹ := by
    fin_cases direction <;> rfl
  rw [spatial, inv_inv, inv_mul_cancel₀ (scale_pos velocity).ne', one_mul]

/-- The canonical time current generates unit fluid density in the same physical time coordinate. -/
theorem densitizedCurrent_temporal (velocity : PhysicalSpace) : densitizedCurrent velocity 0 = 1 := by
  rw [densitizedCurrent_eq, coframe_volume]
  have current : (dual velocity (diracMatrixMatterAction (diracGamma 0) (matter velocity))).re =
      density velocity := by
    rw [dual, matter, InitialLift.temporalCurrent_eq, density, EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  rw [current, ← scale_cube]
  change (scale velocity)⁻¹ * (scale velocity ^ 2)⁻¹ * scale velocity ^ 3 = 1
  field_simp [(scale_pos velocity).ne']

def phaseVector (frame : LorentzianCoframe) (velocity : PhysicalSpace) (direction : Fin 4) :=
  Complex.I • diracMatrixMatterAction
    (inverseCoframeDiracGamma {coframe := frame, derivative := 0} direction) (Complex.I • matter velocity)

/-- This coordinate is a restriction of the existing differential action, independent of unused point-field slots. -/
theorem phaseVector_eq_mother (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) (velocity : PhysicalSpace) (direction : Fin 4) :
    phaseVector field.coframe velocity direction = matterDifferentialVariationVector source point field
      (matterCoordinateEquiv (Complex.I • matter velocity)) direction := by
  simp only [phaseVector, matterDifferentialVariationVector, matterCoordinateEquiv.symm_apply_apply]

/-- The phase variation uses the original mother-action principal and both canonical material coordinates. -/
def phaseMomentum (velocity : PhysicalSpace) (direction : Fin 4) : ℝ :=
  |Matrix.det (coframe velocity)| * (dual velocity (phaseVector (coframe velocity) velocity direction)).re

theorem phaseMomentum_eq_neg_current (velocity : PhysicalSpace) (direction : Fin 4) :
    phaseMomentum velocity direction = -densitizedCurrent velocity direction := by
  simp only [phaseMomentum, phaseVector, densitizedCurrent, map_smul, smul_smul, Complex.I_mul_I,
    neg_one_smul, Complex.neg_re, mul_neg]

theorem canonical_paired (velocity : PhysicalSpace) :
    StageNineFullDiracAdjointMaterial.FullDiracAdjointPaired
      (matter velocity) (dual velocity) := InitialLift.fullAdjointPaired _

theorem phaseMomentum_temporal (velocity : PhysicalSpace) : phaseMomentum velocity 0 = -1 := by
  rw [phaseMomentum_eq_neg_current, densitizedCurrent_temporal]

theorem phaseMomentum_spatial (velocity : PhysicalSpace) (direction : Fin 3) :
    phaseMomentum velocity direction.succ = -velocity direction := by
  rw [phaseMomentum_eq_neg_current, densitizedCurrent_spatial]

/-- Unit density is generated algebraically along the original physical time, with no regularity premise. -/
theorem densitizedCurrent_temporal_hasDerivAt (path : ℝ → PhysicalSpace) (time : ℝ) :
    HasDerivAt (fun actual => densitizedCurrent (path actual) 0) 0 time := by
  simp only [densitizedCurrent_temporal]
  exact hasDerivAt_const time 1

local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The full original source velocity, in the generated frame's current coordinate. -/
theorem source_densitizedCurrent_fourier (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) (direction : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point : Torus =>
      (densitizedCurrent (realField (wholeBiotSavartVelocityState state) point) direction.succ : ℂ)) wave =
      biotSavartVelocityCoefficient wave (state wave) direction := by
  simp only [densitizedCurrent_spatial]
  exact realField_fourier _ (velocity_reality state reality) direction wave

/-- Every Fourier test of the same complete spatial current has zero divergence. -/
theorem source_densitizedCurrent_divergence (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) (wave : IntegerWavevector) :
    (∑ direction : Coordinate, NativePhysicalGradient.multiplier wave direction *
      UnitAddTorus.mFourierCoeff (fun point : Torus =>
        (densitizedCurrent (realField (wholeBiotSavartVelocityState state) point) direction.succ : ℂ)) wave) = 0 := by
  simp only [source_densitizedCurrent_fourier state reality, NativePhysicalGradient.multiplier,
    mul_assoc, ← Finset.mul_sum]
  change Complex.I * (((2 * Real.pi : ℝ) : ℂ) *
    (complexWavevector wave ⬝ᵥ biotSavartVelocityCoefficient wave (state wave))) = 0
  rw [complexWavevector_dot_biotSavartVelocityCoefficient, mul_zero, mul_zero]

/-- The original whole impulse is read by the same generated frame at its literal next. -/
theorem occurrence_phaseMomentum_write {nu : Viscosity}
    (source : GeneratedWholeRestartCurrent nu) (index : ℕ) (direction : Coordinate) :
    let occurrence := generatedWholeRestartNativeActualOccurrence source index
    let velocity := realField (wholeBiotSavartVelocityState (run source index).contact.physicalState)
    let nextVelocity := realField (wholeBiotSavartVelocityState occurrence.response.1.contact.physicalState)
    let impulse := ∫ actual in 0..occurrence.response.1.contact.time.1,
      NativePhysicalTimeAction.physicalTangent (NativeStressSource.occurrenceReceipt occurrence) actual
    ∀ᵐ point : Torus, phaseMomentum (nextVelocity point) direction.succ -
      phaseMomentum (velocity point) direction.succ = -impulse point direction := by
  let occurrence := generatedWholeRestartNativeActualOccurrence source index
  let velocity := realField (wholeBiotSavartVelocityState (run source index).contact.physicalState)
  let nextVelocity := realField (wholeBiotSavartVelocityState occurrence.response.1.contact.physicalState)
  let impulse := ∫ actual in 0..occurrence.response.1.contact.time.1,
    NativePhysicalTimeAction.physicalTangent (NativeStressSource.occurrenceReceipt occurrence) actual
  have write : impulse = nextVelocity - velocity := NativePhysicalTimeAction.occurrence_physical_write source index
  have representatives := MeasureTheory.Lp.coeFn_sub nextVelocity velocity
  rw [← write] at representatives
  filter_upwards [representatives] with point actual
  have coordinate := congrArg (fun value : PhysicalSpace => value direction) actual
  change impulse point direction = nextVelocity point direction - velocity point direction at coordinate
  simp only [phaseMomentum_spatial]
  change -nextVelocity point direction - -velocity point direction = -impulse point direction
  linarith

end
end SaturationMonoid.NavierStokes.NativeCanonicalFluidCoframe
