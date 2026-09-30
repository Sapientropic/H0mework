import H0mework.NavierStokes.Accumulation.FiniteNormalizedWorkPhaseFace
import H0mework.Versions.X.NavierStokes.Accumulation.ConcretePhaseRichPhysicalSeed

/-!
# Concrete phase-rich normalized-work inward calculation

This file materializes the state-owned finite normalized-work directional
derivative at the source state.  The affine line used below is only the
definition of a directional derivative; it is not a Taylor future table or a
replacement PDE trajectory.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

open scoped BigOperators Matrix Topology

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator
namespace PhaseRichTriple

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkPhaseFace
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw

noncomputable section

/-! ## Exact action carrier and first tangent -/

def sourceActionIntegerModes : Finset IntegerWavevector :=
  sourceGeneratedActionWaveFinset.image Wave.toIntegerWavevector

theorem sourceWaveModes_subset_generatedAction :
    sourceWaveModes ⊆ sourceGeneratedActionWaveFinset := by
  rw [← actionWaveCarrier_toFinset_eq_sourceGenerated]
  exact sourceWaveModes_subset_actionWaveCarrier

theorem sourceIntegerModes_subset_sourceActionIntegerModes :
    sourceIntegerModes ⊆ sourceActionIntegerModes := by
  rw [sourceIntegerModes_eq_sourceWaveModes_image,
    sourceActionIntegerModes]
  exact Finset.image_mono Wave.toIntegerWavevector
    sourceWaveModes_subset_generatedAction

theorem complexSourceState_supported_sourceAction
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ sourceActionIntegerModes) :
    complexSourceState wave = 0 := by
  apply complexSourceState_supported wave
  exact fun sourceMem => waveNotMem
    (sourceIntegerModes_subset_sourceActionIntegerModes sourceMem)

theorem sourceActionProjection_eq_source :
    complexSharpSupportProjection sourceActionIntegerModes
        complexSourceState = complexSourceState := by
  apply lp.ext
  funext wave
  by_cases waveMem : wave ∈ sourceActionIntegerModes
  · simp [complexSharpSupportProjection_apply, waveMem]
  · rw [complexSharpSupportProjection_apply, if_neg waveMem,
      complexSourceState_supported_sourceAction wave waveMem]

/-- At the exact finite-support source the action-incidence carrier already
contains the whole state, so the native coface row vanishes without an
assumption.  This is an anchor fact, not a future closure claim. -/
theorem sourceAction_nativeTurbulenceEnstrophyFlux_eq_zero :
    nativeTurbulenceEnstrophyFlux sourceActionIntegerModes
        complexSourceState = 0 := by
  unfold nativeTurbulenceEnstrophyFlux cofaceInputCorrectionAt
  rw [sourceActionProjection_eq_source]
  simp [complexCoordinateRealInner]

def physicalGeneratedActionState : ComplexVorticityHilbertState :=
  finiteComplexVorticityState sourceActionIntegerModes fun wave =>
    GaussianRatVector.toComplex
      (generatedActionState (Wave.ofIntegerWavevector wave))

theorem generatedActionState_eq_sourceGeneratorAt_of_actionMem
    {wave : Wave}
    (waveMem : wave ∈ sourceGeneratedActionWaveFinset) :
    generatedActionState wave = sourceGeneratorAt wave := by
  apply lookup_map_self_of_mem actionWaveCarrier sourceGeneratorAt
    actionWaveCarrier_nodup
  rw [← List.mem_toFinset,
    actionWaveCarrier_toFinset_eq_sourceGenerated]
  exact waveMem

theorem finiteGenerator_source_actionWave
    {wave : Wave}
    (waveMem : wave ∈ sourceGeneratedActionWaveFinset) :
    finiteStateVorticityGenerator sourceActionIntegerModes viscosity.coeff
        complexSourceState wave.toIntegerWavevector =
      GaussianRatVector.toComplex (generatedActionState wave) := by
  have integerMem : wave.toIntegerWavevector ∈ sourceActionIntegerModes :=
    Finset.mem_image.mpr ⟨wave, waveMem, rfl⟩
  rw [generatedActionState_eq_sourceGeneratorAt_of_actionMem waveMem,
    sourceGeneratorAt_toComplex]
  unfold wholeLatticeVorticityFourierTangentAt
  rw [finiteStateVorticityGenerator_apply, if_pos integerMem]
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    sourceActionIntegerModes complexSourceState
    complexSourceState_supported_sourceAction]

theorem finiteGenerator_source_eq_physicalGeneratedActionState :
    finiteStateVorticityGenerator sourceActionIntegerModes viscosity.coeff
        complexSourceState =
      physicalGeneratedActionState := by
  apply lp.ext
  funext output
  by_cases outputMem : output ∈ sourceActionIntegerModes
  · obtain ⟨wave, waveMem, waveEq⟩ := Finset.mem_image.mp outputMem
    subst output
    rw [physicalGeneratedActionState,
      finiteComplexVorticityState_apply, if_pos outputMem]
    simp only [Wave.ofIntegerWavevector_toIntegerWavevector]
    exact finiteGenerator_source_actionWave waveMem
  · rw [finiteStateVorticityGenerator_apply, if_neg outputMem,
      physicalGeneratedActionState,
      finiteComplexVorticityState_apply, if_neg outputMem]

/-! ## Exact finite-field directional linearization -/

theorem fixedWaveDot_hasDerivAt
    (wave : IntegerWavevector)
    (path : Real → ComplexCoordinateVector)
    (time : Real)
    (tangent : ComplexCoordinateVector)
    (pathDerivative : HasDerivAt path tangent time) :
    HasDerivAt
      (fun moment => complexWavevector wave ⬝ᵥ path moment)
      (complexWavevector wave ⬝ᵥ tangent)
      time := by
  unfold dotProduct
  apply HasDerivAt.fun_sum
  intro coordinate coordinateMem
  have coordinateDerivative :
      HasDerivAt (fun moment => path moment coordinate)
        (tangent coordinate) time :=
    (ContinuousLinearMap.proj coordinate :
      ComplexCoordinateVector →L[Real] Complex).hasFDerivAt
      |>.comp_hasDerivAt time pathDerivative
  exact coordinateDerivative.const_mul (complexWavevector wave coordinate)

theorem nonlinearPair_hasDerivAt_bilinear
    (trajectory : Real → ComplexVorticityHilbertState)
    (time : Real)
    (tangent : ComplexVorticityHilbertState)
    (pair : StretchingPair)
    (trajectoryDerivative : HasDerivAt trajectory tangent time) :
    HasDerivAt
      (fun moment =>
        finiteStateVorticityNonlinearPairContribution
          (trajectory moment) pair)
      (finiteStateVorticityBilinearPairContribution
          tangent (trajectory time) pair +
        finiteStateVorticityBilinearPairContribution
          (trajectory time) tangent pair)
      time := by
  have firstRow := complexVorticityTrajectoryWave_hasDerivAt
    trajectory time tangent pair.1 trajectoryDerivative
  have secondRow := complexVorticityTrajectoryWave_hasDerivAt
    trajectory time tangent pair.2 trajectoryDerivative
  have firstVelocity := finiteStateVelocityTrajectoryWave_hasDerivAt
    trajectory time tangent pair.1 trajectoryDerivative
  have secondVelocity := finiteStateVelocityTrajectoryWave_hasDerivAt
    trajectory time tangent pair.2 trajectoryDerivative
  have stretchingDot := fixedWaveDot_hasDerivAt pair.2
    (fun moment => trajectory moment pair.1) time (tangent pair.1)
    firstRow
  have advectionDot := fixedWaveDot_hasDerivAt pair.2
    (fun moment => finiteStateVelocityCoefficient
      (trajectory moment) pair.1)
    time (biotSavartVelocityCoefficient pair.1 (tangent pair.1))
    firstVelocity
  have stretchingScalar := stretchingDot.const_mul
    (Complex.I * (((2 * Real.pi : Real) : Complex)))
  have advectionScalar := advectionDot.const_mul
    (Complex.I * (((2 * Real.pi : Real) : Complex)))
  have stretching := stretchingScalar.smul secondVelocity
  have advection := advectionScalar.smul secondRow
  have derivative := stretching.sub advection
  convert derivative using 1 <;>
    first
    | rfl
    | (simp only [finiteStateVorticityBilinearPairContribution,
        finiteStateVelocityCoefficient]; abel)

theorem nonlinearCoefficient_hasDerivAt_bilinear
    (modes : Finset IntegerWavevector)
    (trajectory : Real → ComplexVorticityHilbertState)
    (time : Real)
    (tangent : ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (trajectoryDerivative : HasDerivAt trajectory tangent time) :
    HasDerivAt
      (fun moment =>
        finiteStateVorticityNonlinearCoefficientAt modes
          (trajectory moment) output)
      (finiteStateVorticityBilinearCoefficientAt modes
          tangent (trajectory time) output +
        finiteStateVorticityBilinearCoefficientAt modes
          (trajectory time) tangent output)
      time := by
  have pairDerivative : ∀ first ∈ modes, ∀ second ∈ modes,
      HasDerivAt
        (fun moment =>
          if first + second = output then
            finiteStateVorticityNonlinearPairContribution
              (trajectory moment) (first, second)
          else 0)
        (if first + second = output then
          finiteStateVorticityBilinearPairContribution
              tangent (trajectory time) (first, second) +
            finiteStateVorticityBilinearPairContribution
              (trajectory time) tangent (first, second)
        else 0)
        time := by
    intro first firstMem second secondMem
    by_cases incidence : first + second = output
    · simp only [if_pos incidence]
      exact nonlinearPair_hasDerivAt_bilinear
        trajectory time tangent (first, second) trajectoryDerivative
    · simp only [if_neg incidence]
      exact hasDerivAt_const time 0
  have summed := HasDerivAt.fun_sum fun first firstMem =>
    HasDerivAt.fun_sum (pairDerivative first firstMem)
  have derivativeEq :
      (∑ first ∈ modes, ∑ second ∈ modes,
        if first + second = output then
          finiteStateVorticityBilinearPairContribution
              tangent (trajectory time) (first, second) +
            finiteStateVorticityBilinearPairContribution
              (trajectory time) tangent (first, second)
        else 0) =
      finiteStateVorticityBilinearCoefficientAt modes
          tangent (trajectory time) output +
        finiteStateVorticityBilinearCoefficientAt modes
          (trajectory time) tangent output := by
    unfold finiteStateVorticityBilinearCoefficientAt
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro first firstMem
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro second secondMem
    by_cases incidence : first + second = output <;> simp [incidence]
  exact (summed.congr_deriv derivativeEq)

def finiteGeneratorLinearizationAt
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state direction : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState modes fun output =>
    finiteStateVorticityBilinearCoefficientAt modes direction state output +
        finiteStateVorticityBilinearCoefficientAt modes state direction output -
      (viscosity * integerWaveViscousMultiplier output) • direction output

theorem finiteGenerator_hasDerivAt_linearization
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (trajectory : Real → ComplexVorticityHilbertState)
    (time : Real)
    (tangent : ComplexVorticityHilbertState)
    (trajectoryDerivative : HasDerivAt trajectory tangent time) :
    HasDerivAt
      (fun moment =>
        finiteStateVorticityGenerator modes viscosity (trajectory moment))
      (finiteGeneratorLinearizationAt modes viscosity
        (trajectory time) tangent)
      time := by
  unfold finiteStateVorticityGenerator finiteGeneratorLinearizationAt
    finiteComplexVorticityState
  apply HasDerivAt.fun_sum
  intro output outputMem
  apply
    (lp.singleContinuousLinearMap
      Real (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 output)
      |>.hasFDerivAt.comp_hasDerivAt time
  apply (nonlinearCoefficient_hasDerivAt_bilinear
    modes trajectory time tangent output trajectoryDerivative).sub
  have rowDerivative := complexVorticityTrajectoryWave_hasDerivAt
    trajectory time tangent output trajectoryDerivative
  exact rowDerivative.const_smul
    (viscosity * integerWaveViscousMultiplier output)

theorem complexCoordinateRealInner_hasDerivAt
    (left right : Real → ComplexCoordinateVector)
    (leftTangent rightTangent : ComplexCoordinateVector)
    (time : Real)
    (leftDerivative : HasDerivAt left leftTangent time)
    (rightDerivative : HasDerivAt right rightTangent time) :
    HasDerivAt
      (fun moment => complexCoordinateRealInner (left moment) (right moment))
      (complexCoordinateRealInner leftTangent (right time) +
        complexCoordinateRealInner (left time) rightTangent)
      time := by
  unfold complexCoordinateRealInner
  have coordinateDerivative : ∀ coordinate ∈
      (Finset.univ : Finset Coordinate),
      HasDerivAt
        (fun moment =>
          (left moment coordinate).re * (right moment coordinate).re +
            (left moment coordinate).im * (right moment coordinate).im)
        (((leftTangent coordinate).re * (right time coordinate).re +
            (left time coordinate).re * (rightTangent coordinate).re) +
          ((leftTangent coordinate).im * (right time coordinate).im +
            (left time coordinate).im * (rightTangent coordinate).im))
        time := by
    intro coordinate coordinateMem
    have leftCoordinate : HasDerivAt
        (fun moment => left moment coordinate)
        (leftTangent coordinate) time :=
      (ContinuousLinearMap.proj coordinate :
        ComplexCoordinateVector →L[Real] Complex).hasFDerivAt
        |>.comp_hasDerivAt time leftDerivative
    have rightCoordinate : HasDerivAt
        (fun moment => right moment coordinate)
        (rightTangent coordinate) time :=
      (ContinuousLinearMap.proj coordinate :
        ComplexCoordinateVector →L[Real] Complex).hasFDerivAt
        |>.comp_hasDerivAt time rightDerivative
    exact
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt time leftCoordinate).mul
          (Complex.reCLM.hasFDerivAt.comp_hasDerivAt time rightCoordinate)
        |>.add
          ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt time leftCoordinate).mul
            (Complex.imCLM.hasFDerivAt.comp_hasDerivAt time rightCoordinate))
  have summed := HasDerivAt.fun_sum coordinateDerivative
  have derivativeEq :
      (∑ coordinate : Coordinate,
        (((leftTangent coordinate).re * (right time coordinate).re +
            (left time coordinate).re * (rightTangent coordinate).re) +
          ((leftTangent coordinate).im * (right time coordinate).im +
            (left time coordinate).im * (rightTangent coordinate).im))) =
        (∑ coordinate : Coordinate,
          ((leftTangent coordinate).re * (right time coordinate).re +
            (leftTangent coordinate).im * (right time coordinate).im)) +
        (∑ coordinate : Coordinate,
          ((left time coordinate).re * (rightTangent coordinate).re +
            (left time coordinate).im * (rightTangent coordinate).im)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro coordinate coordinateMem
    ring
  exact summed.congr_deriv derivativeEq

def finiteGeneratorRealWorkDerivativeAt
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state direction : ComplexVorticityHilbertState) : Real :=
  ∑ wave ∈ modes,
    (complexCoordinateRealInner (direction wave)
        (finiteStateVorticityGenerator modes viscosity state wave) +
      complexCoordinateRealInner (state wave)
        (finiteGeneratorLinearizationAt modes viscosity state direction wave))

theorem finiteGeneratorRealWork_hasDerivAt
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (trajectory : Real → ComplexVorticityHilbertState)
    (time : Real)
    (tangent : ComplexVorticityHilbertState)
    (trajectoryDerivative : HasDerivAt trajectory tangent time) :
    HasDerivAt
      (fun moment => finiteGeneratorRealWork modes viscosity
        (trajectory moment))
      (finiteGeneratorRealWorkDerivativeAt modes viscosity
        (trajectory time) tangent)
      time := by
  unfold finiteGeneratorRealWork finiteGeneratorRealWorkDerivativeAt
  apply HasDerivAt.fun_sum
  intro wave waveMem
  apply complexCoordinateRealInner_hasDerivAt
  · exact complexVorticityTrajectoryWave_hasDerivAt
      trajectory time tangent wave trajectoryDerivative
  · exact complexVorticityTrajectoryWave_hasDerivAt
      (fun moment =>
        finiteStateVorticityGenerator modes viscosity (trajectory moment))
      time (finiteGeneratorLinearizationAt modes viscosity
        (trajectory time) tangent) wave
      (finiteGenerator_hasDerivAt_linearization
        modes viscosity trajectory time tangent trajectoryDerivative)

/-! ## Rational read-back of the two work-derivative rows -/

theorem physicalGeneratedActionState_actionWave
    {wave : Wave}
    (waveMem : wave ∈ sourceGeneratedActionWaveFinset) :
    physicalGeneratedActionState wave.toIntegerWavevector =
      GaussianRatVector.toComplex (sourceGeneratorAt wave) := by
  have integerMem : wave.toIntegerWavevector ∈ sourceActionIntegerModes :=
    Finset.mem_image.mpr ⟨wave, waveMem, rfl⟩
  rw [physicalGeneratedActionState, finiteComplexVorticityState_apply,
    if_pos integerMem]
  simp only [Wave.ofIntegerWavevector_toIntegerWavevector]
  rw [generatedActionState_eq_sourceGeneratorAt_of_actionMem waveMem]

theorem physicalGeneratedActionMass_eq :
    (∑ wave ∈ sourceActionIntegerModes,
      complexCoordinateRealInner
        (physicalGeneratedActionState wave)
        (physicalGeneratedActionState wave)) =
      (entriesMass generatedActionEntries : Real) := by
  rw [sourceActionIntegerModes,
    Finset.sum_image Wave.toIntegerWavevector_injective.injOn]
  have termEq : ∀ wave ∈ sourceGeneratedActionWaveFinset,
      complexCoordinateRealInner
          (physicalGeneratedActionState wave.toIntegerWavevector)
          (physicalGeneratedActionState wave.toIntegerWavevector) =
        (vectorNormSq (sourceGeneratorAt wave) : Real) := by
    intro wave waveMem
    rw [physicalGeneratedActionState_actionWave waveMem,
      complexCoordinateRealInner_self,
      ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      ← vectorNormSq_toComplex]
  rw [Finset.sum_congr rfl termEq]
  rw [← actionWaveCarrier_toFinset_eq_sourceGenerated]
  rw [← Rat.cast_sum]
  congr 1

@[simp] theorem finiteGeneratorLinearizationAt_apply
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state direction : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    finiteGeneratorLinearizationAt modes viscosity state direction output =
      if output ∈ modes then
        finiteStateVorticityBilinearCoefficientAt modes direction state output +
          finiteStateVorticityBilinearCoefficientAt modes state direction output -
          (viscosity * integerWaveViscousMultiplier output) • direction output
      else 0 := by
  exact finiteComplexVorticityState_apply modes _ output

theorem physicalGeneratedActionState_supported
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ sourceActionIntegerModes) :
    physicalGeneratedActionState wave = 0 := by
  simp [physicalGeneratedActionState, waveNotMem]

theorem finiteBilinearPair_zero_of_leftRow_zero
    (left right : ComplexVorticityHilbertState)
    (pair : StretchingPair)
    (leftZero : left pair.1 = 0) :
    finiteStateVorticityBilinearPairContribution left right pair = 0 := by
  simp [finiteStateVorticityBilinearPairContribution,
    finiteStateVelocityCoefficient, leftZero]

theorem finiteBilinearPair_zero_of_rightRow_zero
    (left right : ComplexVorticityHilbertState)
    (pair : StretchingPair)
    (rightZero : right pair.2 = 0) :
    finiteStateVorticityBilinearPairContribution left right pair = 0 := by
  simp [finiteStateVorticityBilinearPairContribution,
    finiteStateVelocityCoefficient, rightZero]

theorem finiteBilinearCoefficient_restrict_supports
    {leftModes rightModes modes : Finset IntegerWavevector}
    (leftSubset : leftModes ⊆ modes)
    (rightSubset : rightModes ⊆ modes)
    (left right : ComplexVorticityHilbertState)
    (leftSupported : ∀ wave, wave ∉ leftModes → left wave = 0)
    (rightSupported : ∀ wave, wave ∉ rightModes → right wave = 0)
    (output : IntegerWavevector) :
    finiteStateVorticityBilinearCoefficientAt modes left right output =
      ∑ first ∈ leftModes,
        ∑ second ∈ rightModes,
          if first + second = output then
            finiteStateVorticityBilinearPairContribution
              left right (first, second)
          else 0 := by
  unfold finiteStateVorticityBilinearCoefficientAt
  symm
  apply Finset.sum_subset_zero_on_sdiff leftSubset
  · intro first firstInDifference
    have firstNotMem := (Finset.mem_sdiff.mp firstInDifference).2
    apply Finset.sum_eq_zero
    intro second secondMem
    by_cases incidence : first + second = output
    · rw [if_pos incidence]
      exact finiteBilinearPair_zero_of_leftRow_zero
        left right (first, second) (leftSupported first firstNotMem)
    · rw [if_neg incidence]
  · intro first firstMem
    apply Finset.sum_subset_zero_on_sdiff rightSubset
    · intro second secondInDifference
      have secondNotMem := (Finset.mem_sdiff.mp secondInDifference).2
      by_cases incidence : first + second = output
      · rw [if_pos incidence]
        exact finiteBilinearPair_zero_of_rightRow_zero
          left right (first, second) (rightSupported second secondNotMem)
      · rw [if_neg incidence]
    · intro second secondMem
      rfl

theorem finiteBilinearRestricted_eq_first_single_sum
    (leftModes rightModes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    (∑ first ∈ leftModes,
      ∑ second ∈ rightModes,
        if first + second = output then
          finiteStateVorticityBilinearPairContribution
            left right (first, second)
        else 0) =
      ∑ first ∈ leftModes,
        if output - first ∈ rightModes then
          finiteStateVorticityBilinearPairContribution
            left right (first, output - first)
        else 0 := by
  apply Finset.sum_congr rfl
  intro first firstMem
  have condition : ∀ second : IntegerWavevector,
      first + second = output ↔ second = output - first := by
    intro second
    constructor <;> intro equality
    · rw [← equality]
      abel
    · rw [equality]
      abel
  simp_rw [condition]
  by_cases translatedMem : output - first ∈ rightModes
  · simp [translatedMem]
  · simp [translatedMem]

theorem finiteBilinearRestricted_eq_second_single_sum
    (leftModes rightModes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    (∑ first ∈ leftModes,
      ∑ second ∈ rightModes,
        if first + second = output then
          finiteStateVorticityBilinearPairContribution
            left right (first, second)
        else 0) =
      ∑ second ∈ rightModes,
        if output - second ∈ leftModes then
          finiteStateVorticityBilinearPairContribution
            left right (output - second, second)
        else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro second secondMem
  have condition : ∀ first : IntegerWavevector,
      first + second = output ↔ first = output - second := by
    intro first
    constructor <;> intro equality
    · rw [← equality]
      abel
    · rw [equality]
      abel
  simp_rw [condition]
  by_cases translatedMem : output - second ∈ leftModes
  · simp [translatedMem]
  · simp [translatedMem]

theorem GaussianRatVector.toComplex_list_sum
    (values : List GaussianRatVector) :
    GaussianRatVector.toComplex values.sum =
      (values.map GaussianRatVector.toComplex).sum := by
  induction values with
  | nil => simp
  | cons head tail induction => simp [induction]

theorem pairContribution_zero_second
    (first second : Wave)
    (firstRow : GaussianRatVector) :
    pairContribution first second firstRow 0 = 0 := by
  funext coordinate
  fin_cases coordinate <;>
    simp [pairContribution, rationalVorticityPairContribution,
      GaussianRatVector.add, GaussianRatVector.complexScale,
      GaussianRatVector.waveCross, GaussianRatVector.waveDot,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRat.add, GaussianRat.sub,
      GaussianRat.mul, GaussianRat.ratDiv,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.neg]
  all_goals rfl

theorem pairContribution_zero_first
    (first second : Wave)
    (secondRow : GaussianRatVector) :
    pairContribution first second 0 secondRow = 0 := by
  funext coordinate
  fin_cases coordinate <;>
    simp [pairContribution, rationalVorticityPairContribution,
      GaussianRatVector.add, GaussianRatVector.complexScale,
      GaussianRatVector.waveCross, GaussianRatVector.waveDot,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRat.add, GaussianRat.sub,
      GaussianRat.mul, GaussianRat.ratDiv,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.neg]
  all_goals rfl

theorem finiteBilinear_action_source_eq_generatedLeft
    (output : Wave) :
    finiteStateVorticityBilinearCoefficientAt sourceActionIntegerModes
        physicalGeneratedActionState complexSourceState
        output.toIntegerWavevector =
      GaussianRatVector.toComplex (generatedActionOnLeftAt output) := by
  rw [finiteBilinearCoefficient_restrict_supports
    (Finset.Subset.rfl)
    sourceIntegerModes_subset_sourceActionIntegerModes
    physicalGeneratedActionState complexSourceState
    physicalGeneratedActionState_supported complexSourceState_supported
    output.toIntegerWavevector]
  rw [finiteBilinearRestricted_eq_first_single_sum]
  rw [sourceActionIntegerModes,
    Finset.sum_image Wave.toIntegerWavevector_injective.injOn]
  unfold generatedActionOnLeftAt generatedActionEntries
    generatedActionWaveList
  rw [GaussianRatVector.toComplex_list_sum, List.map_map, List.map_map]
  rw [← actionWaveCarrier_toFinset_eq_sourceGenerated]
  rw [List.sum_toFinset _ actionWaveCarrier_nodup]
  apply congrArg List.sum
  apply List.map_congr_left
  intro first firstMemList
  have firstMem : first ∈ sourceGeneratedActionWaveFinset := by
    rw [← actionWaveCarrier_toFinset_eq_sourceGenerated,
      List.mem_toFinset]
    exact firstMemList
  simp only [Function.comp_apply]
  let second := output.sub first
  have differenceEq :
      output.toIntegerWavevector - first.toIntegerWavevector =
        second.toIntegerWavevector :=
    (Wave.toIntegerWavevector_sub output first).symm
  rw [differenceEq]
  by_cases secondMem : second ∈ sourceWaveModes
  · have secondIntegerMem :=
      (sourceWave_mem_iff_integer_mem second).mp secondMem
    rw [if_pos secondIntegerMem]
    change _ = GaussianRatVector.toComplex
      (pairContribution first second (sourceGeneratorAt first) (state second))
    symm
    apply pairContribution_toComplex
    · intro firstZero
      exact (Finset.mem_erase.mp firstMem).1 firstZero
    · exact fun secondZero =>
        sourceWaveModes_zero_not_mem (secondZero ▸ secondMem)
    · exact (physicalGeneratedActionState_actionWave firstMem).symm
    · simpa only [Wave.ofIntegerWavevector_toIntegerWavevector] using
        (complexSourceState_faithful second.toIntegerWavevector).symm
  · have secondIntegerNotMem :
        second.toIntegerWavevector ∉ sourceIntegerModes :=
      fun integerMem => secondMem
        ((sourceWave_mem_iff_integer_mem second).mpr integerMem)
    rw [if_neg secondIntegerNotMem]
    have stateZero : state second = 0 := by
      unfold state
      apply lookup_eq_zero_of_not_mem_keys
      simpa [sourceWaveModes] using secondMem
    change 0 = GaussianRatVector.toComplex
      (pairContribution first second (sourceGeneratorAt first) (state second))
    rw [stateZero, pairContribution_zero_second]
    exact GaussianRatVector.toComplex_zero_instance.symm

theorem finiteBilinear_source_action_eq_generatedRight
    (output : Wave) :
    finiteStateVorticityBilinearCoefficientAt sourceActionIntegerModes
        complexSourceState physicalGeneratedActionState
        output.toIntegerWavevector =
      GaussianRatVector.toComplex (generatedActionOnRightAt output) := by
  rw [finiteBilinearCoefficient_restrict_supports
    sourceIntegerModes_subset_sourceActionIntegerModes
    (Finset.Subset.rfl)
    complexSourceState physicalGeneratedActionState
    complexSourceState_supported physicalGeneratedActionState_supported
    output.toIntegerWavevector]
  rw [finiteBilinearRestricted_eq_second_single_sum]
  rw [sourceActionIntegerModes,
    Finset.sum_image Wave.toIntegerWavevector_injective.injOn]
  unfold generatedActionOnRightAt generatedActionEntries
    generatedActionWaveList
  rw [GaussianRatVector.toComplex_list_sum, List.map_map, List.map_map]
  rw [← actionWaveCarrier_toFinset_eq_sourceGenerated]
  rw [List.sum_toFinset _ actionWaveCarrier_nodup]
  apply congrArg List.sum
  apply List.map_congr_left
  intro second secondMemList
  have secondMem : second ∈ sourceGeneratedActionWaveFinset := by
    rw [← actionWaveCarrier_toFinset_eq_sourceGenerated,
      List.mem_toFinset]
    exact secondMemList
  simp only [Function.comp_apply]
  let first := output.sub second
  have differenceEq :
      output.toIntegerWavevector - second.toIntegerWavevector =
        first.toIntegerWavevector :=
    (Wave.toIntegerWavevector_sub output second).symm
  rw [differenceEq]
  by_cases firstMem : first ∈ sourceWaveModes
  · have firstIntegerMem :=
      (sourceWave_mem_iff_integer_mem first).mp firstMem
    rw [if_pos firstIntegerMem]
    change _ = GaussianRatVector.toComplex
      (pairContribution first second (state first) (sourceGeneratorAt second))
    symm
    apply pairContribution_toComplex
    · exact fun firstZero =>
        sourceWaveModes_zero_not_mem (firstZero ▸ firstMem)
    · intro secondZero
      exact (Finset.mem_erase.mp secondMem).1 secondZero
    · simpa only [Wave.ofIntegerWavevector_toIntegerWavevector] using
        (complexSourceState_faithful first.toIntegerWavevector).symm
    · exact (physicalGeneratedActionState_actionWave secondMem).symm
  · have firstIntegerNotMem :
        first.toIntegerWavevector ∉ sourceIntegerModes :=
      fun integerMem => firstMem
        ((sourceWave_mem_iff_integer_mem first).mpr integerMem)
    rw [if_neg firstIntegerNotMem]
    have stateZero : state first = 0 := by
      unfold state
      apply lookup_eq_zero_of_not_mem_keys
      simpa [sourceWaveModes] using firstMem
    change 0 = GaussianRatVector.toComplex
      (pairContribution first second (state first) (sourceGeneratorAt second))
    rw [stateZero, pairContribution_zero_first]
    exact GaussianRatVector.toComplex_zero_instance.symm

theorem finiteGeneratorLinearization_sourceWave
    {wave : Wave}
    (waveMem : wave ∈ sourceWaveModes) :
    finiteGeneratorLinearizationAt sourceActionIntegerModes viscosity.coeff
        complexSourceState physicalGeneratedActionState
        wave.toIntegerWavevector =
      GaussianRatVector.toComplex (generatedLinearizedAction wave) := by
  have actionMem := sourceWaveModes_subset_generatedAction waveMem
  have integerMem : wave.toIntegerWavevector ∈ sourceActionIntegerModes :=
    Finset.mem_image.mpr ⟨wave, actionMem, rfl⟩
  rw [finiteGeneratorLinearizationAt_apply, if_pos integerMem,
    finiteBilinear_action_source_eq_generatedLeft,
    finiteBilinear_source_action_eq_generatedRight,
    physicalGeneratedActionState_actionWave actionMem]
  rw [generatedLinearizedAction, GaussianRatVector.toComplex_sub,
    GaussianRatVector.toComplex_add,
    GaussianRatVector.toComplex_ratScale,
    generatedActionState_eq_sourceGeneratorAt waveMem]
  have scalarEq :
      viscosity.coeff *
          integerWaveViscousMultiplier wave.toIntegerWavevector =
        ((scaledViscosity * waveNormSq wave : ℚ) : Real) := by
    calc
      viscosity.coeff *
          integerWaveViscousMultiplier wave.toIntegerWavevector =
        (viscosity.coeff * (2 * Real.pi) ^ 2) *
          integerWaveNormSq wave.toIntegerWavevector := by
            unfold integerWaveViscousMultiplier
            ring
      _ = (scaledViscosity : Real) *
          integerWaveNormSq wave.toIntegerWavevector := by
            rw [viscosity_scaled]
      _ = ((scaledViscosity * waveNormSq wave : ℚ) : Real) := by
            rw [Rat.cast_mul, waveNormSq_cast]
  rw [scalarEq]
  rfl

theorem sourceLinearizationPairing_eq_generated :
    (∑ wave ∈ sourceActionIntegerModes,
      complexCoordinateRealInner (complexSourceState wave)
        (finiteGeneratorLinearizationAt sourceActionIntegerModes
          viscosity.coeff complexSourceState
          physicalGeneratedActionState wave)) =
      (entriesRealInner sourceEntries generatedLinearizedAction : Real) := by
  rw [← Finset.sum_subset
    sourceIntegerModes_subset_sourceActionIntegerModes
    (fun wave _waveMem waveNotSource => by
      rw [complexSourceState_supported wave waveNotSource]
      simp [complexCoordinateRealInner])]
  rw [sourceIntegerModes_eq_sourceWaveModes_image,
    Finset.sum_image Wave.toIntegerWavevector_injective.injOn]
  have termEq : ∀ wave ∈ sourceWaveModes,
      complexCoordinateRealInner
          (complexSourceState wave.toIntegerWavevector)
          (finiteGeneratorLinearizationAt sourceActionIntegerModes
            viscosity.coeff complexSourceState
            physicalGeneratedActionState wave.toIntegerWavevector) =
        (vectorRealInner (state wave)
          (generatedLinearizedAction wave) : Real) := by
    intro wave waveMem
    rw [complexSourceState_faithful]
    simp only [Wave.ofIntegerWavevector_toIntegerWavevector]
    rw [finiteGeneratorLinearization_sourceWave waveMem]
    exact (vectorRealInner_toComplex
      (state wave) (generatedLinearizedAction wave)).symm
  rw [Finset.sum_congr rfl termEq]
  rw [← Rat.cast_sum]
  congr 1

theorem sourceFiniteGeneratorWorkDerivative_eq_generated :
    finiteGeneratorRealWorkDerivativeAt sourceActionIntegerModes
        viscosity.coeff complexSourceState physicalGeneratedActionState =
      (generatedSourceWorkDerivative : Real) := by
  unfold finiteGeneratorRealWorkDerivativeAt
  rw [Finset.sum_add_distrib]
  have actionTerm :
      (∑ wave ∈ sourceActionIntegerModes,
        complexCoordinateRealInner (physicalGeneratedActionState wave)
          (finiteStateVorticityGenerator sourceActionIntegerModes
            viscosity.coeff complexSourceState wave)) =
        (entriesMass generatedActionEntries : Real) := by
    rw [finiteGenerator_source_eq_physicalGeneratedActionState]
    exact physicalGeneratedActionMass_eq
  rw [actionTerm, sourceLinearizationPairing_eq_generated,
    generatedSourceWorkDerivative, Rat.cast_add]

theorem sourceFiniteGeneratorWork_eq_generated :
    finiteGeneratorRealWork sourceActionIntegerModes viscosity.coeff
        complexSourceState =
      (generatedSourceWork : Real) := by
  unfold finiteGeneratorRealWork
  rw [← Finset.sum_subset
    sourceIntegerModes_subset_sourceActionIntegerModes
    (fun wave _waveMem waveNotSource => by
      rw [complexSourceState_supported wave waveNotSource]
      simp [complexCoordinateRealInner])]
  rw [sourceIntegerModes_eq_sourceWaveModes_image,
    Finset.sum_image Wave.toIntegerWavevector_injective.injOn]
  have termEq : ∀ wave ∈ sourceWaveModes,
      complexCoordinateRealInner
          (complexSourceState wave.toIntegerWavevector)
          (finiteStateVorticityGenerator sourceActionIntegerModes
            viscosity.coeff complexSourceState wave.toIntegerWavevector) =
        (vectorRealInner (state wave) (sourceGeneratorAt wave) : Real) := by
    intro wave waveMem
    rw [complexSourceState_faithful]
    simp only [Wave.ofIntegerWavevector_toIntegerWavevector]
    rw [finiteGenerator_source_actionWave
      (sourceWaveModes_subset_generatedAction waveMem),
      generatedActionState_eq_sourceGeneratorAt waveMem]
    exact (vectorRealInner_toComplex
      (state wave) (sourceGeneratorAt wave)).symm
  rw [Finset.sum_congr rfl termEq]
  rw [← Rat.cast_sum, sourceWaveGeneratorWork_eq_generatedSourceWork]

theorem sourceFiniteAugmentedMass_eq :
    finiteAugmentedCoefficientMass sourceActionIntegerModes
        complexSourceState =
      (sourceMass + 1 : ℚ) := by
  unfold finiteAugmentedCoefficientMass
  rw [← wholeVorticityEuclideanMass_eq_finite_of_supported
    sourceActionIntegerModes complexSourceState
    complexSourceState_supported_sourceAction]
  rw [complexSourceState_wholeMass_eq, sourceMass_eq]
  norm_num

/-! ## Actual source trajectory and normalized directional inwardness -/

theorem exists_sourceActionActualTrajectory :
    ∃ trajectory : Real → ComplexVorticityHilbertState,
      trajectory 0 = complexSourceState ∧
        HasDerivAt trajectory
          (finiteStateVorticityGenerator sourceActionIntegerModes
            viscosity.coeff (trajectory 0)) 0 := by
  obtain ⟨trajectory, initial, epsilon, epsilonPos, actual⟩ :=
    exists_finiteStateVorticity_localTrajectory
      sourceActionIntegerModes viscosity.coeff complexSourceState
  refine ⟨trajectory, initial, ?_⟩
  exact actual 0 ⟨by linarith, by linarith⟩

noncomputable def sourceActionActualTrajectory :
    Real → ComplexVorticityHilbertState :=
  Classical.choose exists_sourceActionActualTrajectory

theorem sourceActionActualTrajectory_initial :
    sourceActionActualTrajectory 0 = complexSourceState :=
  (Classical.choose_spec exists_sourceActionActualTrajectory).1

theorem sourceActionActualTrajectory_actual :
    HasDerivAt sourceActionActualTrajectory
      (finiteStateVorticityGenerator sourceActionIntegerModes
        viscosity.coeff (sourceActionActualTrajectory 0)) 0 :=
  (Classical.choose_spec exists_sourceActionActualTrajectory).2

theorem sourceActionActualTrajectory_work_hasDerivAt_generated :
    HasDerivAt
      (fun moment => finiteGeneratorRealWork sourceActionIntegerModes
        viscosity.coeff (sourceActionActualTrajectory moment))
      (generatedSourceWorkDerivative : Real) 0 := by
  have workDerivative := finiteGeneratorRealWork_hasDerivAt
    sourceActionIntegerModes viscosity.coeff sourceActionActualTrajectory 0
    (finiteStateVorticityGenerator sourceActionIntegerModes viscosity.coeff
      (sourceActionActualTrajectory 0))
    sourceActionActualTrajectory_actual
  rw [sourceActionActualTrajectory_initial,
    finiteGenerator_source_eq_physicalGeneratedActionState] at workDerivative
  simpa only [sourceFiniteGeneratorWorkDerivative_eq_generated] using
    workDerivative

def sourceNormalizedRawDerivative : Real :=
  let mass : Real := ((sourceMass + 1 : ℚ) : Real)
  let work : Real := generatedSourceWork
  let workDerivative : Real := generatedSourceWorkDerivative
  let massPower := mass ^ (5 / 4 : Real)
  let massPowerDerivative :=
    (2 * work) * (5 / 4 : Real) * mass ^ (5 / 4 - 1 : Real)
  (workDerivative * massPower - work * massPowerDerivative) /
    massPower ^ 2

theorem sourceNormalizedDirectionalDerivative_eq_raw :
    finiteNormalizedWorkDirectionalDerivative sourceActionIntegerModes
        viscosity.coeff complexSourceState =
      sourceNormalizedRawDerivative := by
  have normalizedDerivative :=
    finiteNormalizedGeneratorWork_hasDerivAt_of_actual
      sourceActionIntegerModes viscosity.coeff sourceActionActualTrajectory 0
      sourceActionActualTrajectory_actual
  rw [sourceActionActualTrajectory_initial] at normalizedDerivative
  have massDerivative :=
    finiteStateVorticityCoefficientEnstrophy_hasDerivAt
      sourceActionIntegerModes sourceActionActualTrajectory 0
      (finiteStateVorticityGenerator sourceActionIntegerModes viscosity.coeff
        (sourceActionActualTrajectory 0))
      sourceActionActualTrajectory_actual
  have augmentedMassDerivative : HasDerivAt
      (fun moment => finiteAugmentedCoefficientMass sourceActionIntegerModes
        (sourceActionActualTrajectory moment))
      (2 * (generatedSourceWork : Real)) 0 := by
    rw [sourceActionActualTrajectory_initial] at massDerivative
    change HasDerivAt _
      (2 * finiteGeneratorRealWork sourceActionIntegerModes
        viscosity.coeff complexSourceState) 0 at massDerivative
    rw [sourceFiniteGeneratorWork_eq_generated] at massDerivative
    simpa only [finiteAugmentedCoefficientMass] using
      massDerivative.add_const 1
  have massNe :
      finiteAugmentedCoefficientMass sourceActionIntegerModes
        (sourceActionActualTrajectory 0) ≠ 0 :=
    (finiteAugmentedCoefficientMass_pos sourceActionIntegerModes
      (sourceActionActualTrajectory 0)).ne'
  have massPowerDerivative :=
    augmentedMassDerivative.rpow_const (p := (5 / 4 : Real))
      (Or.inl massNe)
  have massPowerNe :
      finiteAugmentedCoefficientMass sourceActionIntegerModes
          (sourceActionActualTrajectory 0) ^ (5 / 4 : Real) ≠ 0 :=
    (Real.rpow_pos_of_pos
      (finiteAugmentedCoefficientMass_pos sourceActionIntegerModes
        (sourceActionActualTrajectory 0)) _).ne'
  have quotientDerivative :=
    sourceActionActualTrajectory_work_hasDerivAt_generated.div
      massPowerDerivative massPowerNe
  have rawDerivative : HasDerivAt
      (fun moment => finiteNormalizedGeneratorWork sourceActionIntegerModes
        viscosity.coeff (sourceActionActualTrajectory moment))
      sourceNormalizedRawDerivative 0 := by
    have quotientDerivative' : HasDerivAt
        (fun moment => finiteNormalizedGeneratorWork sourceActionIntegerModes
          viscosity.coeff (sourceActionActualTrajectory moment))
        (((generatedSourceWorkDerivative : Real) *
                (((sourceMass + 1 : ℚ) : Real) ^ (5 / 4 : Real)) -
              (generatedSourceWork : Real) *
                ((2 * (generatedSourceWork : Real)) * (5 / 4 : Real) *
                  (((sourceMass + 1 : ℚ) : Real) ^
                    (5 / 4 - 1 : Real)))) /
            ((((sourceMass + 1 : ℚ) : Real) ^ (5 / 4 : Real)) ^ 2))
        0 := by
      refine (quotientDerivative.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards [] with moment
        rfl
      · rw [sourceActionActualTrajectory_initial,
          sourceFiniteAugmentedMass_eq,
          sourceFiniteGeneratorWork_eq_generated]
    simpa only [sourceNormalizedRawDerivative] using quotientDerivative'
  exact normalizedDerivative.unique rawDerivative

theorem sourceNormalizedRawDerivative_eq_fiveQuarterReadout :
    sourceNormalizedRawDerivative =
      ((generatedFiveQuarterWorkInwardNumerator +
          generatedSourceWorkDerivative : ℚ) : Real) /
        (((sourceMass + 1 : ℚ) : Real) ^ 2 *
          (((sourceMass + 1 : ℚ) : Real) ^ (1 / 4 : Real))) := by
  let mass : Real := ((sourceMass + 1 : ℚ) : Real)
  have massPos : 0 < mass := by
    dsimp only [mass]
    rw [sourceMass_eq]
    norm_num
  have quarterPowerNe : mass ^ (1 / 4 : Real) ≠ 0 :=
    (Real.rpow_pos_of_pos massPos _).ne'
  have fiveQuarterPower :
      mass ^ (5 / 4 : Real) = mass * mass ^ (1 / 4 : Real) := by
    calc
      mass ^ (5 / 4 : Real) = mass ^ ((1 : Real) + 1 / 4) := by
        congr 1
        norm_num
      _ = mass ^ (1 : Real) * mass ^ (1 / 4 : Real) := by
        rw [Real.rpow_add massPos]
      _ = _ := by rw [Real.rpow_one]
  have numeratorCast :
      ((generatedFiveQuarterWorkInwardNumerator +
          generatedSourceWorkDerivative : ℚ) : Real) =
        mass * (generatedSourceWorkDerivative : Real) -
          (5 / 2 : Real) * (generatedSourceWork : Real) ^ 2 := by
    dsimp only [mass]
    rw [generatedFiveQuarterWorkInwardNumerator]
    push_cast
    ring
  unfold sourceNormalizedRawDerivative
  dsimp only
  change
    (((generatedSourceWorkDerivative : Real) * mass ^ (5 / 4 : Real) -
        (generatedSourceWork : Real) *
          ((2 * (generatedSourceWork : Real)) * (5 / 4 : Real) *
            mass ^ (5 / 4 - 1 : Real))) /
      (mass ^ (5 / 4 : Real)) ^ 2) =
        ((generatedFiveQuarterWorkInwardNumerator +
          generatedSourceWorkDerivative : ℚ) : Real) /
          (mass ^ 2 * mass ^ (1 / 4 : Real))
  rw [fiveQuarterPower]
  norm_num [numeratorCast]
  field_simp [massPos.ne', quarterPowerNe]
  ring

theorem sourceNormalizedDirectionalDerivative_eq_fiveQuarterReadout :
    finiteNormalizedWorkDirectionalDerivative sourceActionIntegerModes
        viscosity.coeff complexSourceState =
      ((generatedFiveQuarterWorkInwardNumerator +
          generatedSourceWorkDerivative : ℚ) : Real) /
        (((sourceMass + 1 : ℚ) : Real) ^ 2 *
          (((sourceMass + 1 : ℚ) : Real) ^ (1 / 4 : Real))) := by
  rw [sourceNormalizedDirectionalDerivative_eq_raw,
    sourceNormalizedRawDerivative_eq_fiveQuarterReadout]

theorem sourceNormalizedWorkDirectionalDerivative_pos :
    0 < finiteNormalizedWorkDirectionalDerivative sourceActionIntegerModes
      viscosity.coeff complexSourceState := by
  rw [sourceNormalizedDirectionalDerivative_eq_raw,
    sourceNormalizedRawDerivative_eq_fiveQuarterReadout]
  apply div_pos
  · have derivativePos : 0 < generatedSourceWorkDerivative := by
      rw [generatedSourceWorkDerivative_eq]
      norm_num
    exact_mod_cast add_pos generatedFiveQuarterWorkInwardNumerator_pos
      derivativePos
  · have massPos : 0 < (((sourceMass + 1 : ℚ) : Real)) := by
      rw [sourceMass_eq]
      norm_num
    positivity

end


end PhaseRichTriple
end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
