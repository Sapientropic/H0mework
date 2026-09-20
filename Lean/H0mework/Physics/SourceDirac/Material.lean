import H0mework.Physics.SourceGauge.Material
import H0mework.Physics.SpinPair.AdjointActual

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Dirac

open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineCoframeLocalDifferentiability
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineFormNativeMatterSpinThreeForm StageNineFormNativeLorentzGeometricFirstVariation
open StageNineMatterCovariantDerivativeAffine StageNineMatterVariation StageNineIIPlusRestriction
open StageNineTopologicalLorentzThreeFormDuality StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous Gauge
open scoped ContDiff

noncomputable section

/-- The chart-zero Lorentz kinetic response reads no gauge coupling. This
eliminates exactly this dependency, without identifying the full source actions. -/
private theorem spin_response_source (source target : SmoothUnifiedSource)
    (field : StageNineHolonomicConfiguration) (point : BasePoint) :
    diracDualFormNativeActionSpinResponseAt source field point =
      diracDualFormNativeActionSpinResponseAt target field point := by
  ext internalPair triple
  change -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
    formNativeLorentzMatterFirstCoefficient source 0 point
      (toContinuumPointField (restrictHolonomicConfigurationToIIPlus field) point)
      (loweredLorentzBivectorOneFormCoordinate (missingTripleOfOneForm triple) internalPair)) =
    -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
    formNativeLorentzMatterFirstCoefficient target 0 point
      (toContinuumPointField (restrictHolonomicConfigurationToIIPlus field) point)
      (loweredLorentzBivectorOneFormCoordinate (missingTripleOfOneForm triple) internalPair))
  unfold formNativeLorentzMatterFirstCoefficient matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
  simp only [matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart]

theorem field_gravityConnection (step : ℕ) :
    (fieldAt step).gravityConnection = fun _ => homogeneousConnection spinScale := by
  funext point
  have generated : (fieldAt step).gravityConnection point =
      diracDualFormNativeActionCartanConnectionAt (sourceAt step) (fieldAt step) point :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
      (sourceAt step) _ point
  have sourceChange : diracDualFormNativeActionCartanConnectionAt (sourceAt step) (fieldAt step) point =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource (fieldAt step) point := by
    unfold diracDualFormNativeActionCartanConnectionAt diracDualFormNativeActionCartanContorsionAt
      diracDualFormNativeActionCartanTorsionAt
    rw [spin_response_source (sourceAt step) positiveSmoothUnifiedSource]
  rw [generated, sourceChange]
  exact homogeneousConnection_generated (fieldAt step) point (clock step) spinScale (clock_pos step)
    (upper step point) (lower step point) (upperDual step point) (lowerDual step point)
    (field_coframe step) (congrFun (field_matter step) point) (congrFun (field_dual step) point)
    (upperDual_lower step point) (lowerDual_upper step point)

def coefficientVelocity (step : ℕ) (point : BasePoint) : DiracSpinorIndex → Fin 2 → ℂ :=
  spinPairCoefficients (upper step point * ((phaseRate step : ℂ) * Complex.I))
    (lower step point * ((-phaseRate step : ℂ) * Complex.I))

private theorem coefficients_hasFDerivAt (step : ℕ) (point : BasePoint) :
    HasFDerivAt (fun point => spinPairCoefficients (upper step point) (lower step point))
      ((EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).smulRight
        (coefficientVelocity step point)) point := by
  have component (row : DiracSpinorIndex) (column : Fin 2) :
      HasFDerivAt (fun candidate => spinPairCoefficients (upper step candidate) (lower step candidate) row column)
        ((EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).smulRight
          (coefficientVelocity step point row column)) point := by
    fin_cases row <;> fin_cases column
    · simpa [spinPairCoefficients, coefficientVelocity] using hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) point
    · exact phase_hasFDerivAt (phaseRate step) point
    · convert (phase_hasFDerivAt (phaseRate step) point).neg using 1 <;>
        first | rfl | ext vector; simp [coefficientVelocity, spinPairCoefficients, upper]
    · simpa [spinPairCoefficients, coefficientVelocity] using hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) point
    · simpa [spinPairCoefficients, coefficientVelocity] using hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) point
    · simpa [coefficientVelocity, spinPairCoefficients, upper, lower] using phase_hasFDerivAt (-phaseRate step) point
    · convert (phase_hasFDerivAt (-phaseRate step) point).neg using 1 <;>
        first | rfl | ext vector; simp [coefficientVelocity, spinPairCoefficients, lower]
    · simpa [spinPairCoefficients, coefficientVelocity] using hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) point
  apply hasFDerivAt_pi''
  intro row
  apply hasFDerivAt_pi''
  intro column
  convert component row column using 1 <;> rfl

private theorem phase_linear_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (step : ℕ) (linear : (DiracSpinorIndex → Fin 2 → ℂ) →L[ℝ] E)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
      (fun candidate => linear (spinPairCoefficients (upper step candidate) (lower step candidate))) point direction =
      if direction = 0 then linear (coefficientVelocity step point) else 0 := by
  have derivative := linear.hasFDerivAt.comp point (coefficients_hasFDerivAt step point)
  change HasFDerivAt (fun candidate =>
    linear (spinPairCoefficients (upper step candidate) (lower step candidate))) _ point at derivative
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  change linear ((coordinateDirection direction) 0 • coefficientVelocity step point) = _
  by_cases same : direction = 0
  · subst direction
    simp [coordinateDirection]
  · simp [coordinateDirection, Ne.symm same, same]

theorem matter_coordinate_derivative (step : ℕ) (point : BasePoint) (direction : LorentzianIndex) :
    matterCoordinateEquiv.symm
      (fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv ((fieldAt step).matter candidate))
        point direction) =
      if direction = 0 then spinPairMatter
        (upper step point * ((phaseRate step : ℂ) * Complex.I))
        (lower step point * ((-phaseRate step : ℂ) * Complex.I)) else 0 := by
  let linear := (sourceColorMatterCoordinateLinear.restrictScalars ℝ).toContinuousLinearMap
  have derivative := phase_linear_derivative step linear point direction
  change fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv ((fieldAt step).matter candidate))
    point direction = _ at derivative
  rw [derivative]
  split_ifs
  · exact matterCoordinateEquiv.symm_apply_apply _
  · exact map_zero _

private def dualEvaluation (matter : DiracExteriorMatterCarrier) :
    (DiracSpinorIndex → Fin 2 → ℂ) →ₗ[ℂ] ℂ where
  toFun coefficients := ∑ spin, ∑ state, coefficients spin state * sourceColorDoubletDual state (matter spin)
  map_add' := by intros; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro coefficient values
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro spin _
    apply Finset.sum_congr rfl
    intro state _
    ring

theorem dual_derivative (step : ℕ) (matter : DiracExteriorMatterCarrier)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate => (fieldAt step).conjugateMatter candidate matter) point direction =
      if direction = 0 then spinPairDual
        (upperDual step point * ((phaseRate step : ℂ) * Complex.I))
        (lowerDual step point * ((-phaseRate step : ℂ) * Complex.I)) matter else 0 := by
  let linear := ((spinScale : ℂ) • dualEvaluation matter).restrictScalars ℝ
  have field (candidate : BasePoint) :
      linear.toContinuousLinearMap (spinPairCoefficients (upper step candidate) (lower step candidate)) =
      (fieldAt step).conjugateMatter candidate matter := by
    change (spinScale : ℂ) * spinPairDual (upper step candidate) (lower step candidate) matter = _
    simp [field_dual, spinPairDual, sourceColorDiracDual, spinPairCoefficients,
      upperDual, lowerDual, Fin.sum_univ_four, Fin.sum_univ_two]
    ring
  have derivative := phase_linear_derivative step linear.toContinuousLinearMap point direction
  simp_rw [field] at derivative
  rw [derivative]
  split_ifs
  · change (spinScale : ℂ) * sourceColorDiracDual (coefficientVelocity step point) matter = _
    simp [coefficientVelocity, spinPairDual, sourceColorDiracDual, spinPairCoefficients,
      upperDual, lowerDual, Fin.sum_univ_four, Fin.sum_univ_two]
    ring
  · rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Dirac
