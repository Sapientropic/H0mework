import H0mework.NavierStokes.Accumulation.FiniteNormalizedWorkPhaseFace
import H0mework.NavierStokes.Fourier.WholeNonlinearDifferenceNegativeOne
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Native jet of finite normalized work

The actual projected whole tangent is split before differentiation into the
finite NS generator and the canonical native coface direction.  Applying the
already generated finite normalized-work differential then produces one
exact same-state jet identity.  No sign, horizon, action payment, future
state, or recurrence is stored here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

open scoped Interval

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkNativeJet

open Filter MeasureTheory

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkPhaseFace
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

/-- Finite output restriction of the genuine whole NS tangent. -/
def finiteProjectedWholeTangentState
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState modes fun wave =>
    wholeLatticeVorticityFourierTangentAt viscosity wholeState wave

/-- Finite output restriction of the source-generated native correction. -/
def finiteNativeTurbulenceCorrectionState
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState modes fun wave =>
    nativeTurbulenceCorrectionAt modes wholeState wave

theorem finiteProjectedWholeTangentState_eq_resolved_add_native
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState) :
    finiteProjectedWholeTangentState modes viscosity wholeState =
      finiteStateVorticityGenerator modes viscosity
          (complexSharpSupportProjection modes wholeState) +
        finiteNativeTurbulenceCorrectionState modes wholeState := by
  apply lp.ext
  funext wave
  unfold finiteProjectedWholeTangentState
    finiteNativeTurbulenceCorrectionState
  change
    finiteComplexVorticityState modes
        (fun output =>
          wholeLatticeVorticityFourierTangentAt viscosity wholeState output)
        wave =
      finiteStateVorticityGenerator modes viscosity
          (complexSharpSupportProjection modes wholeState) wave +
        finiteComplexVorticityState modes
          (fun output => nativeTurbulenceCorrectionAt modes wholeState output)
          wave
  rw [finiteComplexVorticityState_apply,
    finiteComplexVorticityState_apply]
  by_cases waveMem : wave ∈ modes
  · rw [if_pos waveMem, if_pos waveMem,
      finiteStateVorticityGenerator_apply, if_pos waveMem]
    have projectedSupported : ∀ input : IntegerWavevector,
        input ∉ modes →
          complexSharpSupportProjection modes wholeState input = 0 :=
      complexSharpSupportProjection_supported modes wholeState
    have finiteEq :=
      wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
        modes (complexSharpSupportProjection modes wholeState)
          projectedSupported wave
    have split := projectedWholeTangent_eq_classical_add_nativeTurbulence
      modes viscosity wholeState wave
    rw [if_pos waveMem] at split
    unfold wholeLatticeVorticityFourierTangentAt at split ⊢
    rw [← finiteEq]
    exact split
  · rw [if_neg waveMem, if_neg waveMem,
      finiteStateVorticityGenerator_apply, if_neg waveMem, zero_add]

/-- Native contribution to the finite normalized-work rate.  It is a value
of the current finite differential on the source-generated coface direction,
not a caller-provided error or sign. -/
def finiteNormalizedWorkNativeCofaceJet
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState) : Real :=
  (fderiv Real (finiteNormalizedGeneratorWork modes viscosity)
      (complexSharpSupportProjection modes wholeState))
    (finiteNativeTurbulenceCorrectionState modes wholeState)

/-- A whole state already supported on the observed carrier has no native
input coface: the whole and resolved nonlinear rows are identical. -/
theorem finiteNativeTurbulenceCorrectionState_eq_zero_of_supported
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → wholeState wave = 0) :
    finiteNativeTurbulenceCorrectionState modes wholeState = 0 := by
  apply lp.ext
  funext wave
  unfold finiteNativeTurbulenceCorrectionState
  rw [finiteComplexVorticityState_apply]
  by_cases waveMem : wave ∈ modes
  · rw [if_pos waveMem]
    unfold nativeTurbulenceCorrectionAt
      projectedWholeNonlinearCoefficientAt
    rw [if_pos waveMem]
    have projectedEq :
        complexSharpSupportProjection modes wholeState = wholeState :=
      complexSharpSupportProjection_eq_self_of_supported
        modes wholeState supported
    rw [projectedEq, sub_self]
    simp
  · rw [if_neg waveMem]
    rfl

theorem finiteNormalizedWorkNativeCofaceJet_eq_zero_of_supported
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → wholeState wave = 0) :
    finiteNormalizedWorkNativeCofaceJet
      modes viscosity wholeState = 0 := by
  unfold finiteNormalizedWorkNativeCofaceJet
  rw [finiteNativeTurbulenceCorrectionState_eq_zero_of_supported
    modes wholeState supported]
  exact map_zero _

/-- Total normalized finite-observation jet of the genuine whole tangent.
The resolved and native terms are projections of the same differential. -/
def finiteNormalizedWorkActualJet
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState) : Real :=
  finiteNormalizedWorkDirectionalDerivative modes viscosity
      (complexSharpSupportProjection modes wholeState) +
    finiteNormalizedWorkNativeCofaceJet modes viscosity wholeState

theorem finiteNormalizedWorkActualJet_eq_fderiv_wholeTangent
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState) :
    finiteNormalizedWorkActualJet modes viscosity wholeState =
      (fderiv Real (finiteNormalizedGeneratorWork modes viscosity)
        (complexSharpSupportProjection modes wholeState))
        (finiteProjectedWholeTangentState
          modes viscosity wholeState) := by
  rw [finiteProjectedWholeTangentState_eq_resolved_add_native,
    map_add]
  rfl

theorem finiteNormalizedWorkActualJet_eq_resolved_of_supported
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → wholeState wave = 0) :
    finiteNormalizedWorkActualJet modes viscosity wholeState =
      finiteNormalizedWorkDirectionalDerivative
        modes viscosity wholeState := by
  unfold finiteNormalizedWorkActualJet
  rw [complexSharpSupportProjection_eq_self_of_supported
      modes wholeState supported,
    finiteNormalizedWorkNativeCofaceJet_eq_zero_of_supported
      modes viscosity wholeState supported,
    add_zero]

/-- Along one actual whole mild receipt, the finite normalized whole-tangent
jet is a continuous current-state readout.  The proof assembles the finitely
many native coface rows on the genuine finite coordinate carrier; it does not
ask for a whole-state tangent norm. -/
theorem finiteNormalizedWorkActualJet_wholePath_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt
      nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    Continuous fun time : Set.Icc (0 : Real) requestedTime =>
      finiteNormalizedWorkActualJet modes nu.coeff
        (receipt.wholePath time) := by
  let transversePath :
      Set.Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
    fun time => ⟨receipt.wholePath time,
      wholePath_transverse receipt time⟩
  have transversePathContinuous : Continuous transversePath :=
    receipt.wholePath.continuous.subtype_mk
      (wholePath_transverse receipt)
  have projectedPathContinuous : Continuous fun time :
      Set.Icc (0 : Real) requestedTime =>
      complexSharpSupportProjection modes (receipt.wholePath time) := by
    have composed := (sharpSupportProjectionCLM modes).continuous.comp
      receipt.wholePath.continuous
    apply composed.congr
    intro time
    exact sharpSupportProjectionCLM_apply modes
      (receipt.wholePath time)
  let projectedTransversePath :
      Set.Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
    fun time =>
      ⟨complexSharpSupportProjection modes (receipt.wholePath time),
        by
          intro wave
          by_cases waveMem : wave ∈ modes
          · simpa [complexSharpSupportProjection_apply, waveMem] using
              wholePath_transverse receipt time wave
          · simp [complexSharpSupportProjection_apply, waveMem]⟩
  have projectedTransversePathContinuous :
      Continuous projectedTransversePath :=
    projectedPathContinuous.subtype_mk fun time =>
      by
        intro wave
        by_cases waveMem : wave ∈ modes
        · simpa [complexSharpSupportProjection_apply, waveMem] using
            wholePath_transverse receipt time wave
        · simp [complexSharpSupportProjection_apply, waveMem]
  let correctionCoordinates :
      Set.Icc (0 : Real) requestedTime →
        FiniteObservedCoefficientState modes :=
    fun time wave =>
      nativeTurbulenceCorrectionAt modes (receipt.wholePath time) wave.1
  have correctionCoordinatesContinuous :
      Continuous correctionCoordinates := by
    apply continuous_pi
    intro wave
    have wholeRowContinuous : Continuous fun time :
        Set.Icc (0 : Real) requestedTime =>
        wholeStateVorticityNonlinearCoefficientAt
          (transversePath time).1 wave.1 :=
      (wholeStateVorticityNonlinearCoefficientAt_continuous wave.1).comp
        transversePathContinuous
    have projectedRowContinuous : Continuous fun time :
        Set.Icc (0 : Real) requestedTime =>
        wholeStateVorticityNonlinearCoefficientAt
          (projectedTransversePath time).1 wave.1 :=
      (wholeStateVorticityNonlinearCoefficientAt_continuous wave.1).comp
        projectedTransversePathContinuous
    change Continuous fun time : Set.Icc (0 : Real) requestedTime =>
      nativeTurbulenceCorrectionAt modes
        (receipt.wholePath time) wave.1
    unfold nativeTurbulenceCorrectionAt
      projectedWholeNonlinearCoefficientAt
    simp only [if_pos wave.2]
    exact wholeRowContinuous.sub projectedRowContinuous
  let correctionPath : Set.Icc (0 : Real) requestedTime →
      ComplexVorticityHilbertState := fun time =>
    finiteObservedEmbedding modes (correctionCoordinates time)
  have correctionPathContinuous : Continuous correctionPath :=
    (finiteObservedEmbedding modes).continuous.comp
      correctionCoordinatesContinuous
  have correctionPathEq : ∀ time,
      correctionPath time =
        finiteNativeTurbulenceCorrectionState modes
          (receipt.wholePath time) := by
    intro time
    apply lp.ext
    funext wave
    by_cases waveMem : wave ∈ modes
    · simp [correctionPath, correctionCoordinates,
        finiteObservedEmbedding_apply,
        finiteNativeTurbulenceCorrectionState,
        finiteComplexVorticityState_apply, waveMem]
    · simp [correctionPath, correctionCoordinates,
        finiteObservedEmbedding_apply,
        finiteNativeTurbulenceCorrectionState,
        finiteComplexVorticityState_apply, waveMem]
  have nativeJetContinuous : Continuous fun time :
      Set.Icc (0 : Real) requestedTime =>
      finiteNormalizedWorkNativeCofaceJet modes nu.coeff
        (receipt.wholePath time) := by
    have pairContinuous : Continuous fun time :
        Set.Icc (0 : Real) requestedTime =>
        (complexSharpSupportProjection modes (receipt.wholePath time),
          correctionPath time) :=
      projectedPathContinuous.prodMk correctionPathContinuous
    have bundledDerivative : Continuous
        (fun pair : ComplexVorticityHilbertState ×
            ComplexVorticityHilbertState =>
          (fderiv Real
            (finiteNormalizedGeneratorWork modes nu.coeff) pair.1) pair.2) :=
      (finiteNormalizedGeneratorWork_contDiff modes nu.coeff)
        |>.continuous_fderiv_apply one_ne_zero
    have composed := bundledDerivative.comp pairContinuous
    apply composed.congr
    intro time
    unfold finiteNormalizedWorkNativeCofaceJet
    change
      (fderiv Real (finiteNormalizedGeneratorWork modes nu.coeff)
          (complexSharpSupportProjection modes (receipt.wholePath time)))
          (correctionPath time) = _
    rw [correctionPathEq time]
  have resolvedJetContinuous : Continuous fun time :
      Set.Icc (0 : Real) requestedTime =>
      finiteNormalizedWorkDirectionalDerivative modes nu.coeff
        (complexSharpSupportProjection modes (receipt.wholePath time)) :=
    (finiteNormalizedWorkDirectionalDerivative_continuous modes nu.coeff).comp
      projectedPathContinuous
  exact resolvedJetContinuous.add nativeJetContinuous

/-! ## Actual whole-receipt scalar action fold -/

private theorem ac_comp_lipschitzOn
    {E F : Type*}
    [PseudoMetricSpace E]
    [PseudoMetricSpace F]
    {path : Real → E}
    {a b : Real}
    {s : Set E}
    {f : E → F}
    {K : NNReal}
    (pathAC : AbsolutelyContinuousOnInterval path a b)
    (pathMem : ∀ time ∈ Set.uIcc a b, path time ∈ s)
    (fLipschitz : LipschitzOnWith K f s) :
    AbsolutelyContinuousOnInterval (fun time => f (path time)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at pathAC ⊢
  intro epsilon epsilonPos
  have denominatorPos : 0 < (K : Real) + 1 := by positivity
  obtain ⟨delta, deltaPos, controls⟩ :=
    pathAC (epsilon / ((K : Real) + 1))
      (div_pos epsilonPos denominatorPos)
  refine ⟨delta, deltaPos, fun intervals intervalsWithin lengthLt => ?_⟩
  have pathControl := controls intervals intervalsWithin lengthLt
  calc
    (∑ index ∈ Finset.range intervals.1,
        dist
          (f (path (intervals.2 index).1))
          (f (path (intervals.2 index).2))) ≤
        ∑ index ∈ Finset.range intervals.1,
          (K : Real) *
            dist
              (path (intervals.2 index).1)
              (path (intervals.2 index).2) := by
      apply Finset.sum_le_sum
      intro index indexMem
      exact fLipschitz.dist_le_mul
        (path (intervals.2 index).1)
        (pathMem _ (intervalsWithin.1 index indexMem).1)
        (path (intervals.2 index).2)
        (pathMem _ (intervalsWithin.1 index indexMem).2)
    _ = (K : Real) *
        ∑ index ∈ Finset.range intervals.1,
          dist
            (path (intervals.2 index).1)
            (path (intervals.2 index).2) := by
      rw [Finset.mul_sum]
    _ ≤ (K : Real) * (epsilon / ((K : Real) + 1)) := by
      exact mul_le_mul_of_nonneg_left pathControl.le K.2
    _ < ((K : Real) + 1) *
        (epsilon / ((K : Real) + 1)) := by
      exact mul_lt_mul_of_pos_right (lt_add_one (K : Real))
        (div_pos epsilonPos denominatorPos)
    _ = epsilon := by field_simp

example (modes : Finset IntegerWavevector) :
    FiniteDimensional ℝ (FiniteObservedCoefficientState modes) := by
  infer_instance

example (modes : Finset IntegerWavevector) :
    ProperSpace (FiniteObservedCoefficientState modes) := by
  infer_instance

private def observedExtension
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (actual : Real) : FiniteObservedCoefficientState modes :=
  fun wave => receipt.rowExtension wave.1
    (fun waveZero => zeroNotMem (waveZero ▸ wave.2)) actual

private theorem observedExtension_ac
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    AbsolutelyContinuousOnInterval
      (observedExtension receipt modes zeroNotMem) 0 requestedTime := by
  have eachAC : ∀ wave : {wave : IntegerWavevector // wave ∈ modes},
      AbsolutelyContinuousOnInterval
        (receipt.rowExtension wave.1
          (fun waveZero => zeroNotMem (waveZero ▸ wave.2)))
        0 requestedTime := by
    intro wave
    exact receipt.rowExtension_absolutelyContinuous wave.1
      (fun waveZero => zeroNotMem (waveZero ▸ wave.2))
  unfold AbsolutelyContinuousOnInterval at eachAC ⊢
  apply squeeze_zero
    (fun _ =>
      Finset.sum_nonneg fun _ _ => dist_nonneg
    )
    (fun intervals => by
      apply Finset.sum_le_sum
      intro index indexMem
      have rhsNonneg : 0 ≤
          ∑ wave : {wave : IntegerWavevector // wave ∈ modes},
            dist
              (observedExtension receipt modes zeroNotMem
                (intervals.2 index).1 wave)
              (observedExtension receipt modes zeroNotMem
                (intervals.2 index).2 wave) :=
        Finset.sum_nonneg fun _ _ => dist_nonneg
      apply (dist_pi_le_iff rhsNonneg).2
      intro wave
      exact Finset.single_le_sum
        (fun _ _ => dist_nonneg)
        (Finset.mem_univ wave))
  have summed : Tendsto
      (fun intervals =>
        ∑ wave : {wave : IntegerWavevector // wave ∈ modes},
          ∑ index ∈ Finset.range intervals.1,
            dist
              (receipt.rowExtension wave.1
                (fun waveZero => zeroNotMem (waveZero ▸ wave.2))
                (intervals.2 index).1)
              (receipt.rowExtension wave.1
                (fun waveZero => zeroNotMem (waveZero ▸ wave.2))
                (intervals.2 index).2))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin 0 requestedTime))
      (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum
        (Finset.univ : Finset
          {wave : IntegerWavevector // wave ∈ modes}) fun wave _ =>
            eachAC wave)
  convert summed using 1
  funext intervals
  exact Finset.sum_comm

private def observedNormalizedWork
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : FiniteObservedCoefficientState modes) : Real :=
  finiteNormalizedGeneratorWork modes viscosity
    (finiteObservedEmbedding modes state)

private theorem observedNormalizedWork_contDiff
    (modes : Finset IntegerWavevector)
    (viscosity : Real) :
    ContDiff Real 1 (observedNormalizedWork modes viscosity) := by
  unfold observedNormalizedWork
  exact (finiteNormalizedGeneratorWork_contDiff modes viscosity).comp
    ((finiteObservedEmbedding modes).restrictScalars Real).contDiff

private theorem observedNormalizedWork_path_ac
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    AbsolutelyContinuousOnInterval
      (fun actual => observedNormalizedWork modes nu.coeff
        (observedExtension receipt modes zeroNotMem actual))
      0 requestedTime := by
  let path := observedExtension receipt modes zeroNotMem
  have pathAC : AbsolutelyContinuousOnInterval path 0 requestedTime :=
    observedExtension_ac receipt modes zeroNotMem
  obtain ⟨bound, pathBound⟩ := pathAC.exists_bound
  let radius := |bound| + 1
  have radiusPos : 0 < radius := by
    dsimp only [radius]
    positivity
  have pathMem : ∀ time ∈ Set.uIcc (0 : Real) requestedTime,
      path time ∈ Metric.closedBall
        (0 : FiniteObservedCoefficientState modes) radius := by
    intro time timeMem
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pathBound time timeMem).trans (by
      dsimp only [radius]
      linarith [le_abs_self bound])
  obtain ⟨constant, lipschitz⟩ :=
    (observedNormalizedWork_contDiff modes nu.coeff).contDiffOn
      |>.exists_lipschitzOnWith one_ne_zero
        (convex_closedBall (0 : FiniteObservedCoefficientState modes) radius)
        (isCompact_closedBall (0 : FiniteObservedCoefficientState modes) radius)
  exact ac_comp_lipschitzOn pathAC pathMem lipschitz

private def observedTangentExtension
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (actual : Real) : FiniteObservedCoefficientState modes :=
  fun wave => commonTimeZeroExtension requestedTime
    (receipt.rowTangent wave.1
      (fun waveZero => zeroNotMem (waveZero ▸ wave.2))) actual

private theorem observedExtension_ae_hasDerivAt
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    ∀ᵐ actual : Real,
      actual ∈ Set.uIcc (0 : Real) requestedTime →
        HasDerivAt
          (observedExtension receipt modes zeroNotMem)
          (observedTangentExtension receipt modes zeroNotMem actual)
          actual := by
  have allRows : ∀ᵐ actual : Real,
      ∀ wave : {wave : IntegerWavevector // wave ∈ modes},
        actual ∈ Set.uIcc (0 : Real) requestedTime →
          HasDerivAt
            (receipt.rowExtension wave.1
              (fun waveZero => zeroNotMem (waveZero ▸ wave.2)))
            (commonTimeZeroExtension requestedTime
              (receipt.rowTangent wave.1
                (fun waveZero => zeroNotMem (waveZero ▸ wave.2))) actual)
            actual := by
    exact MeasureTheory.ae_all_iff.2 fun wave =>
      receipt.rowExtension_ae_hasDerivAt wave.1
        (fun waveZero => zeroNotMem (waveZero ▸ wave.2))
  filter_upwards [allRows] with actual rowDerivative
  intro actualMem
  apply hasDerivAt_pi.mpr
  intro wave
  exact rowDerivative wave actualMem

private def observedNormalizedRate
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (actual : Real) : Real :=
  (fderiv Real (observedNormalizedWork modes nu.coeff)
      (observedExtension receipt modes zeroNotMem actual))
    (observedTangentExtension receipt modes zeroNotMem actual)

private theorem observedNormalizedRate_eq_ambient
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (actual : Real) :
    observedNormalizedRate receipt modes zeroNotMem actual =
      (fderiv Real (finiteNormalizedGeneratorWork modes nu.coeff)
          (finiteObservedEmbedding modes
            (observedExtension receipt modes zeroNotMem actual)))
        (finiteObservedEmbedding modes
          (observedTangentExtension receipt modes zeroNotMem actual)) := by
  unfold observedNormalizedRate observedNormalizedWork
  change
    (fderiv Real
        ((finiteNormalizedGeneratorWork modes nu.coeff) ∘
          ((finiteObservedEmbedding modes).restrictScalars Real))
        (observedExtension receipt modes zeroNotMem actual))
        (observedTangentExtension receipt modes zeroNotMem actual) = _
  rw [fderiv_comp
    (observedExtension receipt modes zeroNotMem actual)
    ((finiteNormalizedGeneratorWork_contDiff modes nu.coeff).differentiable
      (by norm_num) _)
    ((finiteObservedEmbedding modes).restrictScalars Real).differentiableAt]
  rw [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  rfl

private theorem integral_observedNormalizedRate_eq_boundary
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    (∫ actual in (0 : Real)..requestedTime,
        observedNormalizedRate receipt modes zeroNotMem actual) =
      finiteNormalizedGeneratorWork modes nu.coeff
          (complexSharpSupportProjection modes
            (receipt.wholePath
              ⟨requestedTime,
                ⟨receipt.requestedTimePos.le, le_rfl⟩⟩)) -
        finiteNormalizedGeneratorWork modes nu.coeff
          (complexSharpSupportProjection modes initialState) := by
  let path := observedExtension receipt modes zeroNotMem
  let value : Real → Real := fun actual =>
    observedNormalizedWork modes nu.coeff (path actual)
  let rate := observedNormalizedRate receipt modes zeroNotMem
  have valueAC : AbsolutelyContinuousOnInterval value 0 requestedTime := by
    simpa only [value, path] using
      observedNormalizedWork_path_ac receipt modes zeroNotMem
  have derivative : ∀ᵐ actual : Real,
      actual ∈ Set.uIcc (0 : Real) requestedTime →
        HasDerivAt value (rate actual) actual := by
    filter_upwards [observedExtension_ae_hasDerivAt
      receipt modes zeroNotMem] with actual pathDerivative
    intro actualMem
    have readoutDerivative :=
      (observedNormalizedWork_contDiff modes nu.coeff)
        |>.differentiable (by norm_num) (path actual)
        |>.hasFDerivAt
    exact readoutDerivative.comp_hasDerivAt actual
      (pathDerivative actualMem)
  have fold :
      (∫ actual in (0 : Real)..requestedTime, rate actual) =
        value requestedTime - value 0 := by
    calc
      (∫ actual in (0 : Real)..requestedTime, rate actual) =
          ∫ actual in (0 : Real)..requestedTime, deriv value actual := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [derivative] with actual derivativeAt actualMem
        exact (derivativeAt (Set.uIoc_subset_uIcc actualMem)).deriv.symm
      _ = value requestedTime - value 0 :=
        valueAC.integral_deriv_eq_sub
  have terminalObserved :
      path requestedTime =
        finiteObservedCoefficientState modes
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) := by
    funext wave
    exact receipt.rowExtension_on_interval wave.1
      (fun waveZero => zeroNotMem (waveZero ▸ wave.2))
      ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
  have initialObserved :
      path 0 = finiteObservedCoefficientState modes initialState := by
    funext wave
    rw [show path 0 wave = receipt.wholePath
        ⟨0, ⟨le_rfl, receipt.requestedTimePos.le⟩⟩ wave by
      exact receipt.rowExtension_on_interval wave.1
        (fun waveZero => zeroNotMem (waveZero ▸ wave.2))
        ⟨0, ⟨le_rfl, receipt.requestedTimePos.le⟩⟩]
    rw [receipt.wholePath_initial]
    rfl
  rw [fold]
  dsimp only [value]
  rw [terminalObserved, initialObserved]
  unfold observedNormalizedWork
  rw [finiteObservedEmbedding_finiteObservedCoefficientState,
    finiteObservedEmbedding_finiteObservedCoefficientState]

private theorem observedNormalizedRate_eq_actualJet_ae
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      observedNormalizedRate receipt modes zeroNotMem time.1 =
        finiteNormalizedWorkActualJet modes nu.coeff
          (receipt.wholePath time) := by
  have allRows : ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      ∀ wave : {wave : IntegerWavevector // wave ∈ modes},
        (if wave.1 ∈ modes then
            receipt.rowTangent wave.1
              (fun waveZero => zeroNotMem (waveZero ▸ wave.2)) time
          else 0) =
          wholeLatticeVorticityFourierTangentAt nu.coeff
              (complexSharpSupportProjection modes
                (receipt.wholePath time)) wave.1 +
            nativeTurbulenceCorrectionAt modes
              (receipt.wholePath time) wave.1 := by
    exact MeasureTheory.ae_all_iff.2 fun wave =>
      receipt_projectedRowTangent_eq_classical_add_nativeTurbulence_ae
        receipt modes wave.1
          (fun waveZero => zeroNotMem (waveZero ▸ wave.2))
  filter_upwards [allRows] with time rowLaw
  have observedStateEq :
      finiteObservedEmbedding modes
          (observedExtension receipt modes zeroNotMem time.1) =
        complexSharpSupportProjection modes (receipt.wholePath time) := by
    rw [← finiteObservedEmbedding_finiteObservedCoefficientState]
    congr 1
    funext wave
    exact receipt.rowExtension_on_interval wave.1
      (fun waveZero => zeroNotMem (waveZero ▸ wave.2)) time
  have observedTangentEq :
      finiteObservedEmbedding modes
          (observedTangentExtension receipt modes zeroNotMem time.1) =
        finiteProjectedWholeTangentState modes nu.coeff
          (receipt.wholePath time) := by
    apply lp.ext
    funext wave
    by_cases waveMem : wave ∈ modes
    · rw [finiteObservedEmbedding_apply, dif_pos waveMem]
      change
        commonTimeZeroExtension requestedTime
            (receipt.rowTangent wave
              (fun waveZero => zeroNotMem (waveZero ▸ waveMem))) time.1 = _
      rw [commonTimeZeroExtension_of_mem requestedTime
        (receipt.rowTangent wave
          (fun waveZero => zeroNotMem (waveZero ▸ waveMem)))
        time.1 time.property]
      unfold finiteProjectedWholeTangentState
      rw [finiteComplexVorticityState_apply, if_pos waveMem]
      have receiptRow := rowLaw ⟨wave, waveMem⟩
      rw [if_pos waveMem] at receiptRow
      have split := projectedWholeTangent_eq_classical_add_nativeTurbulence
        modes nu.coeff (receipt.wholePath time) wave
      rw [if_pos waveMem] at split
      exact receiptRow.trans split.symm
    · rw [finiteObservedEmbedding_apply, dif_neg waveMem]
      unfold finiteProjectedWholeTangentState
      rw [finiteComplexVorticityState_apply, if_neg waveMem]
  rw [observedNormalizedRate_eq_ambient,
    observedStateEq, observedTangentEq]
  exact (finiteNormalizedWorkActualJet_eq_fderiv_wholeTangent
    modes nu.coeff (receipt.wholePath time)).symm

theorem receipt_finiteNormalizedWorkActualJet_integral_eq_boundary
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    (∫ time,
        finiteNormalizedWorkActualJet modes nu.coeff
          (receipt.wholePath time)
        ∂(commonTimeMeasure requestedTime)) =
      finiteNormalizedGeneratorWork modes nu.coeff
          (complexSharpSupportProjection modes
            (receipt.wholePath
              ⟨requestedTime,
                ⟨receipt.requestedTimePos.le, le_rfl⟩⟩)) -
        finiteNormalizedGeneratorWork modes nu.coeff
          (complexSharpSupportProjection modes initialState) := by
  calc
    (∫ time,
        finiteNormalizedWorkActualJet modes nu.coeff
          (receipt.wholePath time)
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time,
          observedNormalizedRate receipt modes zeroNotMem time.1
          ∂(commonTimeMeasure requestedTime) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [observedNormalizedRate_eq_actualJet_ae
        receipt modes zeroNotMem] with time equality
      exact equality.symm
    _ = ∫ actual in (0 : Real)..requestedTime,
        observedNormalizedRate receipt modes zeroNotMem actual :=
      commonTime_integral_eq_intervalIntegral requestedTime
        receipt.requestedTimePos.le _
    _ = _ := integral_observedNormalizedRate_eq_boundary
      receipt modes zeroNotMem

/-- Exact same-occurrence commuting row.  The finite-only directional rate
and the native coface jet are the two linear projections of the actual whole
tangent under one differential. -/
theorem finiteNormalizedWork_actualJet_eq_resolved_add_native
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState) :
    (fderiv Real (finiteNormalizedGeneratorWork modes viscosity)
        (complexSharpSupportProjection modes wholeState))
        (finiteProjectedWholeTangentState modes viscosity wholeState) =
      finiteNormalizedWorkDirectionalDerivative modes viscosity
          (complexSharpSupportProjection modes wholeState) +
        finiteNormalizedWorkNativeCofaceJet modes viscosity wholeState := by
  rw [finiteProjectedWholeTangentState_eq_resolved_add_native]
  exact map_add _ _ _

/-! ## Exact projected-path chain rule -/

/-- Chain rule for an arbitrary actual path observed through one fixed
finite Fourier projection.  The projected tangent is read from the same path;
it is not replaced by a finite generator. -/
theorem finiteNormalizedGeneratorWork_projectedPath_hasDerivAt
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (trajectory : Real → ComplexVorticityHilbertState)
    (time : Real)
    (tangent : ComplexVorticityHilbertState)
    (trajectoryDerivative : HasDerivAt trajectory tangent time) :
    HasDerivAt
      (fun moment => finiteNormalizedGeneratorWork modes viscosity
        (complexSharpSupportProjection modes (trajectory moment)))
      ((fderiv Real (finiteNormalizedGeneratorWork modes viscosity)
          (complexSharpSupportProjection modes (trajectory time)))
        (complexSharpSupportProjection modes tangent))
      time := by
  have projectedDerivative : HasDerivAt
      (fun moment =>
        complexSharpSupportProjection modes (trajectory moment))
      (complexSharpSupportProjection modes tangent) time := by
    let realProjection : ComplexVorticityHilbertState →L[Real]
        ComplexVorticityHilbertState :=
      (sharpSupportProjectionCLM modes).restrictScalars Real
    have projectionDerivative : HasDerivAt
        (fun _moment : Real => realProjection)
        (0 : ComplexVorticityHilbertState →L[Real]
          ComplexVorticityHilbertState) time := hasDerivAt_const time _
    have combined := HasDerivAt.clm_apply
      (𝕜 := Real)
      (F := ComplexVorticityHilbertState)
      (G := ComplexVorticityHilbertState)
      projectionDerivative trajectoryDerivative
    simpa [realProjection, sharpSupportProjectionCLM_apply] using combined
  have normalizedDerivative :=
    (finiteNormalizedGeneratorWork_contDiff modes viscosity)
      |>.differentiable (by norm_num)
        (complexSharpSupportProjection modes (trajectory time))
      |>.hasFDerivAt
  exact normalizedDerivative.comp_hasDerivAt time projectedDerivative

/-- Two-scale canonical specialization.  `stageRadius` generates the actual
finite Galerkin update; `observationRadius` only reads that update. -/
theorem generatedCurrentCanonicalStage_projectedNormalizedWork_hasDerivAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (observationRadius stageRadius : Nat)
    (time : Real)
    (timeMem : time ∈ Set.Icc (0 : Real)
      (wholeRestartDuration current.contact)) :
    let stage := generatedWholeRestartCanonicalStage
      current.contact stageRadius
    let observationModes := wholeRestartModes observationRadius
    HasDerivAt
      (fun moment => finiteNormalizedGeneratorWork observationModes nu.coeff
        (complexSharpSupportProjection observationModes
          (stage.trajectory moment)))
      ((fderiv Real
          (finiteNormalizedGeneratorWork observationModes nu.coeff)
          (complexSharpSupportProjection observationModes
            (stage.trajectory time)))
        (complexSharpSupportProjection observationModes
          (finiteStateVorticityGenerator (wholeRestartModes stageRadius)
            nu.coeff (stage.trajectory time))))
      time := by
  dsimp only
  apply finiteNormalizedGeneratorWork_projectedPath_hasDerivAt
  exact ((generatedWholeRestartCanonicalStage
    current.contact stageRadius).physical time timeMem).1

/-- Difference between an actual larger Galerkin update observed on
`observationModes` and the autonomous generator of that observation. -/
def finiteGalerkinObservationCofaceDirection
    (observationModes evolutionModes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  complexSharpSupportProjection observationModes
      (finiteStateVorticityGenerator evolutionModes viscosity state) -
    finiteStateVorticityGenerator observationModes viscosity
      (complexSharpSupportProjection observationModes state)

def finiteNormalizedWorkGalerkinCofaceJet
    (observationModes evolutionModes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState) : Real :=
  (fderiv Real (finiteNormalizedGeneratorWork observationModes viscosity)
      (complexSharpSupportProjection observationModes state))
    (finiteGalerkinObservationCofaceDirection
      observationModes evolutionModes viscosity state)

/-- Exact two-scale jet split.  The larger stage generates the tangent; the
smaller observation reads an autonomous finite rate plus the actual coface
rate created by the omitted input rows. -/
theorem finiteNormalizedWork_projectedGalerkinJet_eq_resolved_add_coface
    (observationModes evolutionModes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState) :
    (fderiv Real (finiteNormalizedGeneratorWork observationModes viscosity)
        (complexSharpSupportProjection observationModes state))
        (complexSharpSupportProjection observationModes
          (finiteStateVorticityGenerator evolutionModes viscosity state)) =
      finiteNormalizedWorkDirectionalDerivative observationModes viscosity
          (complexSharpSupportProjection observationModes state) +
        finiteNormalizedWorkGalerkinCofaceJet
          observationModes evolutionModes viscosity state := by
  let differential :=
    fderiv Real (finiteNormalizedGeneratorWork observationModes viscosity)
      (complexSharpSupportProjection observationModes state)
  let resolved := finiteStateVorticityGenerator observationModes viscosity
    (complexSharpSupportProjection observationModes state)
  let actual := complexSharpSupportProjection observationModes
    (finiteStateVorticityGenerator evolutionModes viscosity state)
  have split : actual = resolved + (actual - resolved) := by abel
  rw [show complexSharpSupportProjection observationModes
      (finiteStateVorticityGenerator evolutionModes viscosity state) =
        actual by rfl, split, map_add]
  rfl

/-- Canonical two-scale chain rule with the coface jet already installed in
the derivative. -/
theorem generatedCurrentCanonicalStage_projectedNormalizedWorkJet_hasDerivAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (observationRadius stageRadius : Nat)
    (time : Real)
    (timeMem : time ∈ Set.Icc (0 : Real)
      (wholeRestartDuration current.contact)) :
    let stage := generatedWholeRestartCanonicalStage
      current.contact stageRadius
    let observationModes := wholeRestartModes observationRadius
    HasDerivAt
      (fun moment => finiteNormalizedGeneratorWork observationModes nu.coeff
        (complexSharpSupportProjection observationModes
          (stage.trajectory moment)))
      (finiteNormalizedWorkDirectionalDerivative observationModes nu.coeff
          (complexSharpSupportProjection observationModes
            (stage.trajectory time)) +
        finiteNormalizedWorkGalerkinCofaceJet observationModes
          (wholeRestartModes stageRadius) nu.coeff (stage.trajectory time))
      time := by
  dsimp only
  have chain :=
    generatedCurrentCanonicalStage_projectedNormalizedWork_hasDerivAt
      current observationRadius stageRadius time timeMem
  exact chain.congr_deriv
    (finiteNormalizedWork_projectedGalerkinJet_eq_resolved_add_coface
      (wholeRestartModes observationRadius)
      (wholeRestartModes stageRadius) nu.coeff
      ((generatedWholeRestartCanonicalStage
        current.contact stageRadius).trajectory time))

/-- Derivative row of one fixed observation along a larger canonical
Galerkin stage. -/
def generatedCanonicalStageProjectedNormalizedRate
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (observationRadius stageRadius : Nat)
    (time : Real) : Real :=
  let stage := generatedWholeRestartCanonicalStage
    current.contact stageRadius
  let observationModes := wholeRestartModes observationRadius
  (fderiv Real
      (finiteNormalizedGeneratorWork observationModes nu.coeff)
      (complexSharpSupportProjection observationModes
        (stage.trajectory time)))
    (complexSharpSupportProjection observationModes
      (finiteStateVorticityGenerator (wholeRestartModes stageRadius)
        nu.coeff (stage.trajectory time)))

theorem generatedCanonicalStageProjectedNormalizedRate_continuousOn
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (observationRadius stageRadius : Nat) :
    ContinuousOn
      (generatedCanonicalStageProjectedNormalizedRate
        current observationRadius stageRadius)
      (Set.Icc (0 : Real) (wholeRestartDuration current.contact)) := by
  let stage := generatedWholeRestartCanonicalStage
    current.contact stageRadius
  let observationModes := wholeRestartModes observationRadius
  have stageContinuous : ContinuousOn stage.trajectory
      (Set.Icc (0 : Real) (wholeRestartDuration current.contact)) := by
    intro time timeMem
    exact ((stage.physical time timeMem).1.continuousAt).continuousWithinAt
  have projectedStateContinuous : ContinuousOn
      (fun time => complexSharpSupportProjection observationModes
        (stage.trajectory time))
      (Set.Icc (0 : Real) (wholeRestartDuration current.contact)) := by
    have composed := (sharpSupportProjectionCLM observationModes).continuous
      |>.comp_continuousOn stageContinuous
    apply composed.congr
    intro time timeMem
    exact (sharpSupportProjectionCLM_apply observationModes
      (stage.trajectory time)).symm
  have stageGeneratorContinuous : ContinuousOn
      (fun time => finiteStateVorticityGenerator
        (wholeRestartModes stageRadius) nu.coeff (stage.trajectory time))
      (Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :=
    (finiteStateVorticityGenerator_contDiff
      (wholeRestartModes stageRadius) nu.coeff).continuous.comp_continuousOn
        stageContinuous
  have projectedTangentContinuous : ContinuousOn
      (fun time => complexSharpSupportProjection observationModes
        (finiteStateVorticityGenerator (wholeRestartModes stageRadius)
          nu.coeff (stage.trajectory time)))
      (Set.Icc (0 : Real) (wholeRestartDuration current.contact)) := by
    have composed := (sharpSupportProjectionCLM observationModes).continuous
      |>.comp_continuousOn stageGeneratorContinuous
    apply composed.congr
    intro time timeMem
    exact (sharpSupportProjectionCLM_apply observationModes
      (finiteStateVorticityGenerator (wholeRestartModes stageRadius)
        nu.coeff (stage.trajectory time))).symm
  have stateTangentContinuous : ContinuousOn
      (fun time =>
        (complexSharpSupportProjection observationModes
            (stage.trajectory time),
          complexSharpSupportProjection observationModes
            (finiteStateVorticityGenerator (wholeRestartModes stageRadius)
              nu.coeff (stage.trajectory time))))
      (Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :=
    projectedStateContinuous.prodMk projectedTangentContinuous
  have bundledDerivative : Continuous
      (fun pair : ComplexVorticityHilbertState ×
          ComplexVorticityHilbertState =>
        (fderiv Real
          (finiteNormalizedGeneratorWork observationModes nu.coeff) pair.1)
          pair.2) :=
    (finiteNormalizedGeneratorWork_contDiff observationModes nu.coeff)
      |>.continuous_fderiv_apply one_ne_zero
  have composed := bundledDerivative.comp_continuousOn
    stateTangentContinuous
  apply composed.congr
  intro time timeMem
  rfl

/-- Exact finite-stage action fold for one fixed observation.  This is the
AC chain rule before any Galerkin limit or sign estimate. -/
theorem integral_generatedCanonicalStageProjectedNormalizedRate_eq_boundary
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (observationRadius stageRadius : Nat) :
    let stage := generatedWholeRestartCanonicalStage
      current.contact stageRadius
    let observationModes := wholeRestartModes observationRadius
    (∫ time in (0 : Real)..wholeRestartDuration current.contact,
        generatedCanonicalStageProjectedNormalizedRate
          current observationRadius stageRadius time) =
      finiteNormalizedGeneratorWork observationModes nu.coeff
          (complexSharpSupportProjection observationModes
            (stage.trajectory (wholeRestartDuration current.contact))) -
        finiteNormalizedGeneratorWork observationModes nu.coeff
          (complexSharpSupportProjection observationModes
            (stage.trajectory 0)) := by
  dsimp only
  let stage := generatedWholeRestartCanonicalStage
    current.contact stageRadius
  let observationModes := wholeRestartModes observationRadius
  let value : Real → Real := fun time =>
    finiteNormalizedGeneratorWork observationModes nu.coeff
      (complexSharpSupportProjection observationModes
        (stage.trajectory time))
  let rate := generatedCanonicalStageProjectedNormalizedRate
    current observationRadius stageRadius
  have rateIntegrable : IntervalIntegrable rate volume
      0 (wholeRestartDuration current.contact) :=
    ContinuousOn.intervalIntegrable_of_Icc
      (wholeRestartDuration_pos current.contact).le
      (generatedCanonicalStageProjectedNormalizedRate_continuousOn
        current observationRadius stageRadius)
  have derivative : ∀ time ∈ Set.uIcc (0 : Real)
      (wholeRestartDuration current.contact),
      HasDerivAt value (rate time) time := by
    intro time timeMem
    rw [Set.uIcc_of_le (wholeRestartDuration_pos current.contact).le]
      at timeMem
    simpa only [value, rate,
      generatedCanonicalStageProjectedNormalizedRate,
      stage, observationModes] using
      generatedCurrentCanonicalStage_projectedNormalizedWork_hasDerivAt
        current observationRadius stageRadius time timeMem
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
    rateIntegrable

/-- Current-generated dual energy of the finite normalized-work
differential.  The multiplier sum converts the native `H⁻¹` row to the
finite output `L²` carrier without discarding its provenance. -/
def finiteNormalizedWorkNativeJetDualEnergy
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState) : Real :=
  3 * (∑ wave ∈ modes, integerWaveViscousMultiplier wave) *
    ‖fderiv Real (finiteNormalizedGeneratorWork modes viscosity)
      (complexSharpSupportProjection modes wholeState)‖ ^ 2

theorem finiteNormalizedWorkNativeJetDualEnergy_nonneg
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState) :
    0 ≤ finiteNormalizedWorkNativeJetDualEnergy
      modes viscosity wholeState := by
  unfold finiteNormalizedWorkNativeJetDualEnergy
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun wave _ => by
        unfold integerWaveViscousMultiplier
        exact mul_nonneg (sq_nonneg _)
          (integerWaveNormSq_nonneg wave)))
    (sq_nonneg _)

private theorem finiteNativeCorrection_norm_sq_le_multiplier_mul_difference
    (modes : Finset IntegerWavevector)
    (modesZeroFree : (0 : IntegerWavevector) ∉ modes)
    (wholeState : ComplexVorticityHilbertState)
    (wholeTransverse : WholeStateTransverse wholeState)
    (wholeGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (wholeState wave)) :
    ‖finiteNativeTurbulenceCorrectionState modes wholeState‖ ^ 2 ≤
      3 * (∑ wave ∈ modes, integerWaveViscousMultiplier wave) *
        wholeStateVorticityNonlinearDifferenceNegativeOneMass
          (complexSharpSupportProjection modes wholeState) wholeState := by
  let projected := complexSharpSupportProjection modes wholeState
  let correction := finiteNativeTurbulenceCorrectionState modes wholeState
  have correctionSupported : ∀ wave : IntegerWavevector,
      wave ∉ modes → correction wave = 0 := by
    intro wave waveNotMem
    simp [correction, finiteNativeTurbulenceCorrectionState,
      finiteComplexVorticityState_apply, waveNotMem]
  have normLe :=
    complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
      modes correction correctionSupported
  have projectedTransverse : WholeStateTransverse projected := by
    intro wave
    by_cases waveMem : wave ∈ modes
    · simpa [projected, complexSharpSupportProjection_apply, waveMem] using
        wholeTransverse wave
    · simp [projected, complexSharpSupportProjection_apply, waveMem]
  have projectedGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (projected wave) :=
    summable_wholeStateVorticityGradientDensity_of_supported
      modes projected
      (complexSharpSupportProjection_supported modes wholeState)
  have differenceGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((projected - wholeState) wave) :=
    summable_wholeStateVorticityGradientDensity_sub
      projected wholeState projectedGradientSummable wholeGradientSummable
  have differenceSummable :=
    summable_wholeStateVorticityNonlinearDifferenceNegativeOneDensity
      projected wholeState projectedTransverse wholeTransverse
      projectedGradientSummable wholeGradientSummable
      differenceGradientSummable
  have densityLeMass (wave : IntegerWavevector) :
      wholeStateVorticityNonlinearDifferenceNegativeOneDensity
          projected wholeState wave ≤
        wholeStateVorticityNonlinearDifferenceNegativeOneMass
          projected wholeState := by
    have finiteLe := differenceSummable.sum_le_tsum {wave}
      (fun index _ =>
        wholeStateVorticityNonlinearDifferenceNegativeOneDensity_nonneg
          projected wholeState index)
    simpa [wholeStateVorticityNonlinearDifferenceNegativeOneMass] using
      finiteLe
  have finiteMassLe :
      finiteStateVorticityCoefficientEnstrophy modes correction ≤
        3 * (∑ wave ∈ modes, integerWaveViscousMultiplier wave) *
          wholeStateVorticityNonlinearDifferenceNegativeOneMass
            projected wholeState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    calc
      (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (correction wave)) ≤
          ∑ wave ∈ modes,
            3 * integerWaveViscousMultiplier wave *
              wholeStateVorticityNonlinearDifferenceNegativeOneDensity
                projected wholeState wave := by
        apply Finset.sum_le_sum
        intro wave waveMem
        have waveNe : wave ≠ 0 := fun waveZero =>
          modesZeroFree (waveZero ▸ waveMem)
        have correctionEq : correction wave =
            wholeStateVorticityNonlinearCoefficientAt wholeState wave -
              wholeStateVorticityNonlinearCoefficientAt projected wave := by
          simp [correction, finiteNativeTurbulenceCorrectionState,
            finiteComplexVorticityState_apply, waveMem,
            nativeTurbulenceCorrectionAt,
            projectedWholeNonlinearCoefficientAt, projected]
        rw [correctionEq]
        have amplitudeLe :=
          complexCoordinateAmplitudeSq_le_three_mul_norm_sq
            (wholeStateVorticityNonlinearCoefficientAt wholeState wave -
              wholeStateVorticityNonlinearCoefficientAt projected wave)
        unfold wholeStateVorticityNonlinearDifferenceNegativeOneDensity
        rw [if_neg waveNe]
        have multiplierPos : 0 < integerWaveViscousMultiplier wave := by
          unfold integerWaveViscousMultiplier
          exact mul_pos (sq_pos_of_pos (by positivity))
            (integerWaveNormSq_pos waveNe)
        calc
          complexCoordinateAmplitudeSq
              (wholeStateVorticityNonlinearCoefficientAt wholeState wave -
                wholeStateVorticityNonlinearCoefficientAt projected wave) ≤
              3 * ‖wholeStateVorticityNonlinearCoefficientAt projected wave -
                wholeStateVorticityNonlinearCoefficientAt wholeState wave‖ ^ 2 := by
            simpa only [norm_sub_rev] using amplitudeLe
          _ = 3 * integerWaveViscousMultiplier wave *
              (‖wholeStateVorticityNonlinearCoefficientAt projected wave -
                  wholeStateVorticityNonlinearCoefficientAt wholeState wave‖ ^ 2 /
                integerWaveViscousMultiplier wave) := by
            field_simp [multiplierPos.ne']
      _ ≤ ∑ wave ∈ modes,
          3 * integerWaveViscousMultiplier wave *
            wholeStateVorticityNonlinearDifferenceNegativeOneMass
              projected wholeState := by
        apply Finset.sum_le_sum
        intro wave waveMem
        exact mul_le_mul_of_nonneg_left (densityLeMass wave)
          (mul_nonneg (by norm_num) (by
            unfold integerWaveViscousMultiplier
            exact mul_nonneg (sq_nonneg _)
              (integerWaveNormSq_nonneg wave)))
      _ = 3 * (∑ wave ∈ modes, integerWaveViscousMultiplier wave) *
          wholeStateVorticityNonlinearDifferenceNegativeOneMass
            projected wholeState := by
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.mul_sum]
  exact normLe.trans finiteMassLe

/-- Quantitative native-jet escrow.  The coface contribution is controlled
by the exact nonlinear `H⁻¹` difference between the whole state and its
finite projection, multiplied by a current-generated finite dual energy. -/
theorem finiteNormalizedWorkNativeCofaceJet_sq_le_negativeOne
    (modes : Finset IntegerWavevector)
    (modesZeroFree : (0 : IntegerWavevector) ∉ modes)
    (viscosity : Real)
    (wholeState : ComplexVorticityHilbertState)
    (wholeTransverse : WholeStateTransverse wholeState)
    (wholeGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (wholeState wave)) :
    finiteNormalizedWorkNativeCofaceJet
          modes viscosity wholeState ^ 2 ≤
      finiteNormalizedWorkNativeJetDualEnergy modes viscosity wholeState *
        wholeStateVorticityNonlinearDifferenceNegativeOneMass
          (complexSharpSupportProjection modes wholeState) wholeState := by
  let differential :=
    fderiv Real (finiteNormalizedGeneratorWork modes viscosity)
      (complexSharpSupportProjection modes wholeState)
  let correction := finiteNativeTurbulenceCorrectionState modes wholeState
  have applyLe :
      |differential correction| ≤ ‖differential‖ * ‖correction‖ := by
    simpa only [Real.norm_eq_abs] using differential.le_opNorm correction
  have applySq :
      (differential correction) ^ 2 ≤
        ‖differential‖ ^ 2 * ‖correction‖ ^ 2 := by
    have := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      |>.2 applyLe
    simpa only [sq_abs, mul_pow] using this
  have correctionLe :=
    finiteNativeCorrection_norm_sq_le_multiplier_mul_difference
      modes modesZeroFree wholeState wholeTransverse wholeGradientSummable
  unfold finiteNormalizedWorkNativeCofaceJet
    finiteNormalizedWorkNativeJetDualEnergy
  dsimp only [differential, correction] at applySq correctionLe ⊢
  calc
    _ ≤ ‖fderiv Real (finiteNormalizedGeneratorWork modes viscosity)
          (complexSharpSupportProjection modes wholeState)‖ ^ 2 *
        ‖finiteNativeTurbulenceCorrectionState modes wholeState‖ ^ 2 :=
      applySq
    _ ≤ ‖fderiv Real (finiteNormalizedGeneratorWork modes viscosity)
          (complexSharpSupportProjection modes wholeState)‖ ^ 2 *
        (3 * (∑ wave ∈ modes, integerWaveViscousMultiplier wave) *
          wholeStateVorticityNonlinearDifferenceNegativeOneMass
            (complexSharpSupportProjection modes wholeState) wholeState) :=
      mul_le_mul_of_nonneg_left correctionLe (sq_nonneg _)
    _ = (3 * (∑ wave ∈ modes, integerWaveViscousMultiplier wave) *
          ‖fderiv Real (finiteNormalizedGeneratorWork modes viscosity)
            (complexSharpSupportProjection modes wholeState)‖ ^ 2) *
        wholeStateVorticityNonlinearDifferenceNegativeOneMass
          (complexSharpSupportProjection modes wholeState) wholeState := by
      ring

end

end ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkNativeJet
end NavierStokes
end SaturationMonoid
