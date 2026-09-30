import H0mework.NavierStokes.ReferenceErrorCritical.Pairing

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.CriticalError

open Set Filter
open scoped Topology
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget

noncomputable section

/-- The canonical finite restrictions converge in both actual work slots:
H¹ vorticity and H⁻¹ nonlinear tangent. -/
theorem projected_work_tendsto (field : ComplexVorticityHilbertState) (zeroRow : field 0 = 0)
    (transverse : WholeStateTransverse field)
    (gradient : Summable fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq (field wave)) :
    Tendsto (fun radius => NonlinearWork.value
      (complexSharpSupportProjection (puncturedIntegerWaveFrequencyCube radius) field)) atTop
        (𝓝 (NonlinearWork.value field)) := by
  let projected := fun radius => complexSharpSupportProjection (puncturedIntegerWaveFrequencyCube radius) field
  have projectedTransverse (radius : Nat) : WholeStateTransverse (projected radius) :=
    wholeStateTransverse_sharpSupportProjection _ field transverse
  have projectedGradient (radius : Nat) : Summable fun wave => integerWaveNormSq wave *
      complexCoordinateAmplitudeSq (projected radius wave) :=
    summable_wholeStateVorticityGradientDensity_of_supported _ _ (complexSharpSupportProjection_supported _ field)
  let nonlinear := wholeStateVorticityNonlinearNegativeOneState field transverse gradient
  have gradientZero : NonlinearWork.gradientState field gradient 0 = 0 := by
    simp [NonlinearWork.gradientState, wholeStateVorticityViscousNegativeOneState_apply,
      wholeStateVorticityViscousNegativeOneWeightedCoefficient, integerWaveViscousMultiplier, integerWaveNormSq]
  have leftTendsto := complexSharpSupportProjection_puncturedFrequencyCube_tendsto
    (NonlinearWork.gradientState field gradient) gradientZero
  have rightTendsto : Tendsto (fun radius => nonlinear +
      puncturedProjectionNonlinearErrorState radius field transverse gradient) atTop (𝓝 nonlinear) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : Nat => nonlinear) atTop (𝓝 nonlinear)).add
      (puncturedProjectionNonlinearErrorState_tendsto_zero field zeroRow transverse gradient)
  have workTendsto := (coefficientWork_continuous.tendsto
    (NonlinearWork.gradientState field gradient, nonlinear)).comp (leftTendsto.prodMk_nhds rightTendsto)
  rw [← work_eq_weighted field transverse gradient] at workTendsto
  apply workTendsto.congr'
  apply Filter.Eventually.of_forall
  intro radius
  have left : complexSharpSupportProjection (puncturedIntegerWaveFrequencyCube radius)
      (NonlinearWork.gradientState field gradient) = NonlinearWork.gradientState (projected radius) (projectedGradient radius) := by
    apply lp.ext
    funext wave
    by_cases inside : wave ∈ puncturedIntegerWaveFrequencyCube radius
    · simp [projected, complexSharpSupportProjection_apply, inside, NonlinearWork.gradientState,
        wholeStateVorticityViscousNegativeOneState_apply, wholeStateVorticityViscousNegativeOneWeightedCoefficient]
    · simp [projected, complexSharpSupportProjection_apply, inside, NonlinearWork.gradientState,
        wholeStateVorticityViscousNegativeOneState_apply, wholeStateVorticityViscousNegativeOneWeightedCoefficient]
  have right : nonlinear + puncturedProjectionNonlinearErrorState radius field transverse gradient =
      wholeStateVorticityNonlinearNegativeOneState (projected radius) (projectedTransverse radius) (projectedGradient radius) := by
    apply lp.ext
    funext wave
    change wholeStateVorticityNonlinearNegativeOneWeightedCoefficient field wave +
        wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient (projected radius) field wave =
      wholeStateVorticityNonlinearNegativeOneWeightedCoefficient (projected radius) wave
    unfold wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
      wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
    by_cases zero : wave = 0
    · simp [zero]
    · simp only [if_neg zero]
      module
  change CoefficientWork.value _ _ = _
  dsimp only
  rw [left, right, ← work_eq_weighted (projected radius) (projectedTransverse radius) (projectedGradient radius)]

end
end SaturationMonoid.NavierStokes.CriticalError
