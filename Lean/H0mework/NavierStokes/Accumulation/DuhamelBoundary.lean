import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import H0mework.NavierStokes.Restart.NativeAccumulationVorticityCourt
import H0mework.NavierStokes.Restart.NonlinearRegenerationCascade
import H0mework.NavierStokes.EndpointTransport.CofinalNonlinearNegativeOneEuclideanBalance
import H0mework.NavierStokes.EndpointTransport.NativeHighFrequencyProjectedParabolicTrace
import H0mework.NavierStokes.PairRestart.SourcePairOccurrence
import H0mework.NavierStokes.PairRestart.PairDuhamelOccurrence
import H0mework.NavierStokes.PairRestart.PairOccurrenceRateSettlement
import H0mework.NavierStokes.Restart.SymmetricVelocityMultiplierGapTransport
import H0mework.NavierStokes.KineticRestart.ActualKineticViscousExhaustion
import H0mework.NavierStokes.Crossing.FrequencySupportExhaustion
import H0mework.NavierStokes.Crossing.HighFrequencyAggregateCharge
import H0mework.NavierStokes.Crossing.HighFrequencyAggregateResponsibility
import H0mework.NavierStokes.Restart.BoundedPreAccumulationVelocityStrongTrace
import H0mework.NavierStokes.VelocityGalerkin.InitialConvergence
import H0mework.NavierStokes.KineticRestart.KineticEndpointResidualCarrier
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinPositiveTimeSuffix
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinWeakAction
import H0mework.NavierStokes.Fourier.CoarseFilterSpatialCommutation
import H0mework.NavierStokes.Energy.ClosedEnstrophyPhysicalBridge
import H0mework.Foundation.Authority.EntryDisposition

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration

open scoped BigOperators ContDiff ENNReal FourierTransform Pointwise SchwartzMap Topology

open Set Filter MeasureTheory
open ResponsibilityLifecycle
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.TotalReality
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ZeroLawRootAdmission
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalPeriodicCoarseFilterSpatialCommutation
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientPhysicalFourierCoordinateObserver
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientFiniteModalPicardBounds
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinWeakAction
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeHighFrequencyTailDivergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearDuhamelRegeneration
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeVorticityDivergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointTailLocalization
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointResidualCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationVelocityStrongTrace
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationVorticityCourt
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityPairDiagonalAction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSymmetricVelocityMultiplierGapTransport
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualKineticFluxWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualKineticViscousExhaustion
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateCharge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateResponsibility
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityNativeHighFrequencyProjectedParabolicTrace
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityFixedWindowLanding
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinPositiveTimeSuffix

noncomputable section

variable {nu : Viscosity}

private theorem complexCoordinateAmplitudeSq_real_smul
    (scalar : Real)
    (vector : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (scalar • vector) =
      scalar ^ 2 * complexCoordinateAmplitudeSq vector := by
  simp_rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  change
    complexCoordinateVectorNormSq ((scalar : Complex) • vector) = _
  rw [complexCoordinateVectorNormSq_smul, Complex.normSq_ofReal]
  ring

private theorem cofinally_exists_adjacent_strictIncrease
    (value : Nat → Real)
    (diverges : Tendsto value atTop atTop)
    (lower : Nat) :
    ∃ index : Nat,
      lower ≤ index ∧ value index < value (index + 1) := by
  by_contra noIncrease
  have shiftedStepLe : ∀ offset : Nat,
      value (lower + (offset + 1)) ≤ value (lower + offset) := by
    intro offset
    apply le_of_not_gt
    intro increase
    apply noIncrease
    exact ⟨lower + offset, by omega, by simpa [Nat.add_assoc] using increase⟩
  have shiftedAntitone :
      Antitone fun offset : Nat => value (lower + offset) := by
    apply antitone_nat_of_succ_le
    intro offset
    simpa [Nat.add_assoc] using shiftedStepLe offset
  have eventuallyLarge :=
    (tendsto_atTop.1 diverges) (value lower + 1)
  rw [Filter.eventually_atTop] at eventuallyLarge
  obtain ⟨threshold, eventuallyLarge⟩ := eventuallyLarge
  have largeAtShift :
      value lower + 1 ≤ value (lower + threshold) :=
    eventuallyLarge (lower + threshold) (by omega)
  have boundedAtShift :
      value (lower + threshold) ≤ value lower := by
    simpa using shiftedAntitone (Nat.zero_le threshold)
  linarith

private theorem nativeTemporalCofinalRootDifference_actualAndStructural
    (initial : GeneratedWholeRestartCurrent nu) :
    let root := nativeTemporalAuthoritativeRoot initial
    let cofinalVisit : LawfulWorldStateAt root :=
      .cofinal (nativeTemporalCofinalVisit initial)
    let nextVisit : LawfulWorldStateAt root :=
      (nativeTemporalCofinalNextCurrent initial).visit
    let difference : RootTotalReality.RootDifference root :=
      (cofinalVisit, nextVisit)
    ActualDifferenceAt (RootTotalReality.semantics root) difference ∧
      (RootTotalReality.semantics root).StructuralIdentityAt difference := by
  dsimp only
  let root := nativeTemporalAuthoritativeRoot initial
  let cofinalVisit : LawfulWorldStateAt root :=
    .cofinal (nativeTemporalCofinalVisit initial)
  let nextVisit : LawfulWorldStateAt root :=
    (nativeTemporalCofinalNextCurrent initial).visit
  let difference : RootTotalReality.RootDifference root :=
    (cofinalVisit, nextVisit)
  have different : cofinalVisit ≠ nextVisit := by
    intro same
    have currentSame :=
      congrArg SourceNativeTemporalVisitAt.current same
    change
      (.cofinal : NativeTemporalCurrent initial) = .galerkin 0
      at currentSame
    cases currentSame
  have actual :
      ActualDifferenceAt (RootTotalReality.semantics root) difference :=
    RootTotalReality.actualDifference root different
  refine ⟨actual, ?_⟩
  rcases (RootTotalReality.isTotal root).locate difference actual with
    redundant | identity
  · exact False.elim
      (different
        (LawfulWorldStateAt.eq_of_registeredOccurrence_eq redundant))
  · exact identity

/-- A nonzero pair vector outside the doubled low cube exposes a nonzero input
row outside the original cube at the same physical time and on the same
receipt. -/
theorem sameReceipt_pairVector_outsideDoubledRadius_generates_highInput
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat)
    (output : NonzeroIntegerWavevector)
    (first : IntegerWavevector)
    (time : Set.Icc (0 : Real) requestedTime)
    (outputOutside : output.1 ∉ wholeRestartModes (2 * radius))
    (pairNonzero :
      actualWholeContinuousPairVector
        receipt output.1 first time ≠ 0) :
    (first ∉ wholeRestartModes radius ∧
        receipt.wholePath time first ≠ 0) ∨
      (output.1 - first ∉ wholeRestartModes radius ∧
        receipt.wholePath time (output.1 - first) ≠ 0) := by
  have crosses :
      first ∉ wholeRestartModes radius ∨
        output.1 - first ∉ wholeRestartModes radius := by
    by_contra bothInside
    push Not at bothInside
    obtain ⟨firstMem, secondMem⟩ := bothInside
    have outputInPairSupport :
        output.1 ∈ finiteVorticityPairOutputSupport
          (wholeRestartModes radius) := by
      rw [finiteVorticityPairOutputSupport, Finset.mem_image]
      exact
        ⟨(first, output.1 - first),
          Finset.mem_product.mpr ⟨firstMem, secondMem⟩, by simp⟩
    have outputInDoubledCube :
        output.1 ∈ integerWaveFrequencyCube (2 * radius) := by
      apply
        finiteVorticityPairOutputSupport_puncturedCube_subset_doubledCube
          radius
      simpa only [wholeRestartModes] using outputInPairSupport
    apply outputOutside
    unfold wholeRestartModes puncturedIntegerWaveFrequencyCube
    exact Finset.mem_erase.mpr ⟨output.2, outputInDoubledCube⟩
  have firstNonzero : receipt.wholePath time first ≠ 0 := by
    intro firstZero
    apply pairNonzero
    unfold actualWholeContinuousPairVector
    exact finiteStateVorticityNonlinearPairContribution_zero_first
      (receipt.wholePath time) (first, output.1 - first) firstZero
  have secondNonzero :
      receipt.wholePath time (output.1 - first) ≠ 0 := by
    intro secondZero
    apply pairNonzero
    unfold actualWholeContinuousPairVector
    exact finiteStateVorticityNonlinearPairContribution_zero_second
      (receipt.wholePath time) (first, output.1 - first) secondZero
  exact crosses.elim
    (fun outside => Or.inl ⟨outside, firstNonzero⟩)
    (fun outside => Or.inr ⟨outside, secondNonzero⟩)

/-- A nonlinear pair output outside the doubled low cube cannot be generated
autonomously there.  The same actual pair occurrence exposes a nonzero input
row outside the original cube on its own whole receipt. -/
theorem sameReceipt_pairWork_outsideDoubledRadius_generates_highInput
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat)
    (output : NonzeroIntegerWavevector)
    (first : IntegerWavevector)
    (outputOutside : output.1 ∉ wholeRestartModes (2 * radius))
    (workNonzero :
      actualWholePairOccurrenceWork receipt output.1 first ≠ 0) :
    ∃ time : Set.Icc (0 : Real) requestedTime,
      actualWholeContinuousPairVector receipt output.1 first time ≠ 0 ∧
        ((first ∉ wholeRestartModes radius ∧
            receipt.wholePath time first ≠ 0) ∨
          (output.1 - first ∉ wholeRestartModes radius ∧
            receipt.wholePath time (output.1 - first) ≠ 0)) := by
  obtain ⟨time, pairNonzero⟩ :=
    actualWholePairOccurrenceWork_ne_zero_generates_pairVector
      receipt output.1 first workNonzero
  exact
    ⟨time, pairNonzero,
      sameReceipt_pairVector_outsideDoubledRadius_generates_highInput
        receipt radius output first time outputOutside pairNonzero⟩

/-- Outside the doubled low cube, an endpoint row is either the exact
homogeneous heat transport of the source row or is generated by a strictly
earlier pair whose same-receipt incidence exposes a high input. -/
theorem
    sameReceipt_rowOutsideDoubledRadius_eq_heatInitial_or_causalHighInput
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat)
    (output : NonzeroIntegerWavevector)
    (endpoint : Set.Icc (0 : Real) requestedTime)
    (outputOutside : output.1 ∉ wholeRestartModes (2 * radius)) :
    receipt.wholePath endpoint output.1 =
        finiteStateVorticityHeatMultiplier
          nu.coeff endpoint.1 output.1 • initialState output.1 ∨
      ∃ first : IntegerWavevector,
        ∃ earlier : Set.Icc (0 : Real) requestedTime,
          earlier < endpoint ∧
            actualWholeContinuousPairVector
                receipt output.1 first earlier ≠ 0 ∧
              ((first ∉ wholeRestartModes radius ∧
                  receipt.wholePath earlier first ≠ 0) ∨
                (output.1 - first ∉ wholeRestartModes radius ∧
                  receipt.wholePath earlier (output.1 - first) ≠ 0)) := by
  obtain heatEq | ⟨first, earlier, earlierLt, pairNonzero⟩ :=
    sameReceipt_row_eq_heatInitial_or_strictEarlier_pairVector
      receipt output.1 output.2 endpoint
  · exact Or.inl heatEq
  · exact Or.inr
      ⟨first, earlier, earlierLt, pairNonzero,
        sameReceipt_pairVector_outsideDoubledRadius_generates_highInput
          receipt radius output first earlier outputOutside pairNonzero⟩

/-- Every concrete Fourier row debit is paid by the complete kinetic ledger on
the identical native edge. -/
theorem actualEdgeRowKineticViscousWork_le_nextPayment
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (input : NonzeroIntegerWavevector) :
    actualWholeRowKineticViscousWork
          (run initial index).nextContact.prefixReceipt input ≤
      wholeRestartNextKineticDissipationPayment initial index := by
  let debitRadius := integerWaveCoordinateRadius input.1
  have inputMemCube :
      input.1 ∈ integerWaveFrequencyCube debitRadius :=
    integerWave_mem_frequencyCube_of_radius_le
      input.1 debitRadius le_rfl
  have inputMem : input.1 ∈ wholeRestartModes debitRadius :=
    Finset.mem_erase.mpr ⟨input.2, inputMemCube⟩
  calc
    actualWholeRowKineticViscousWork
        (run initial index).nextContact.prefixReceipt input =
        ∑ wave ∈ {input.1},
          actualWholeRowViscousPayment
              (run initial index).nextContact.prefixReceipt wave /
            integerWaveViscousMultiplier wave := by
          simp [actualWholeRowKineticViscousWork]
    _ ≤ actualWholeKineticViscousPayment
          (run initial index).nextContact.prefixReceipt debitRadius := by
      unfold actualWholeKineticViscousPayment
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa using inputMem
      · intro wave _waveMem _waveNotMem
        exact div_nonneg
          (actualWholeRowViscousPayment_nonneg
            (run initial index).nextContact.prefixReceipt wave)
          (by
            unfold integerWaveViscousMultiplier
            exact mul_nonneg (sq_nonneg _)
              (integerWaveNormSq_nonneg wave))
    _ ≤ 2 * nu.coeff *
          wholePrefixVorticityMass
            ⟨(run initial index).nextContact.time.1,
              ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩
            (run initial index).nextContact.prefixReceipt.stateLimit :=
      actualWholeKineticViscousPayment_le_full
        (run initial index).nextContact.prefixReceipt debitRadius
    _ = wholeRestartNextKineticDissipationPayment initial index := by
      unfold wholeRestartNextKineticDissipationPayment
      rw [prefixReceipt_terminal_wholePrefixVorticityMass_eq]

/-- The high input exposed by one nonzero pair vector creates a strictly
positive viscous debit on that same edge, paid by its existing kinetic
ledger. -/
theorem
    wholeRestartPairVector_outsideDoubledRadius_generates_highInputKineticDebit
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (output : NonzeroIntegerWavevector)
    (first : IntegerWavevector)
    (time : Set.Icc (0 : Real)
      (run initial index).nextContact.time.1)
    (outputOutside : output.1 ∉ wholeRestartModes (2 * radius))
    (pairNonzero :
      actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output.1 first time ≠ 0) :
    ∃ input : NonzeroIntegerWavevector,
      input.1 ∉ wholeRestartModes radius ∧
        (run initial index).nextContact.prefixReceipt.wholePath
            time input.1 ≠ 0 ∧
          0 < actualWholeRowKineticViscousWork
            (run initial index).nextContact.prefixReceipt input ∧
          actualWholeRowKineticViscousWork
              (run initial index).nextContact.prefixReceipt input ≤
            wholeRestartNextKineticDissipationPayment initial index := by
  have highInput :=
    sameReceipt_pairVector_outsideDoubledRadius_generates_highInput
      (run initial index).nextContact.prefixReceipt radius
      output first time outputOutside pairNonzero
  rcases highInput with
    ⟨outside, inputNonzero⟩ | ⟨outside, inputNonzero⟩
  · let input : NonzeroIntegerWavevector :=
      ⟨first, fun firstZero => by
        subst first
        exact inputNonzero
          ((run initial index).nextContact.prefixReceipt.wholePath_zero_row
            time)⟩
    exact
      ⟨input, outside, inputNonzero,
        actualWholeRowKineticViscousWork_pos_of_wholePath_ne_zero
          (run initial index).nextContact.prefixReceipt input time inputNonzero,
        actualEdgeRowKineticViscousWork_le_nextPayment initial index input⟩
  · let second := output.1 - first
    let input : NonzeroIntegerWavevector :=
      ⟨second, by
        intro secondZero
        apply inputNonzero
        change
          (run initial index).nextContact.prefixReceipt.wholePath
            time second = 0
        rw [secondZero]
        exact
          (run initial index).nextContact.prefixReceipt.wholePath_zero_row
            time⟩
    exact
      ⟨input, outside, inputNonzero,
        actualWholeRowKineticViscousWork_pos_of_wholePath_ne_zero
          (run initial index).nextContact.prefixReceipt input time inputNonzero,
        actualEdgeRowKineticViscousWork_le_nextPayment initial index input⟩

/-- Exact no-free carrier-downgrade law on one native restart edge.  A row
outside the doubled low cube is either the homogeneous heat write of the same
source row, or an actual strictly earlier pair incidence exposes a high input
whose kinetic debit is positive and paid by this very edge's whole ledger. -/
theorem
    wholeRestartTerminalHighRow_eq_heatSource_or_highInputKineticDebit
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (output : NonzeroIntegerWavevector)
    (outputOutside : output.1 ∉ wholeRestartModes (2 * radius)) :
    (run initial index).nextContact.physicalState output.1 =
        finiteStateVorticityHeatMultiplier
            nu.coeff (run initial index).nextContact.time.1 output.1 •
          (run initial index).contact.physicalState output.1 ∨
      ∃ first : IntegerWavevector,
        ∃ earlier : Set.Icc (0 : Real)
            (run initial index).nextContact.time.1,
          earlier <
              (⟨(run initial index).nextContact.time.1,
                ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ :
                Set.Icc (0 : Real)
                  (run initial index).nextContact.time.1) ∧
            actualWholeContinuousPairVector
                (run initial index).nextContact.prefixReceipt
                output.1 first earlier ≠ 0 ∧
              ∃ input : NonzeroIntegerWavevector,
                input.1 ∉ wholeRestartModes radius ∧
                  (run initial index).nextContact.prefixReceipt.wholePath
                      earlier input.1 ≠ 0 ∧
                    0 < actualWholeRowKineticViscousWork
                      (run initial index).nextContact.prefixReceipt input ∧
                    actualWholeRowKineticViscousWork
                        (run initial index).nextContact.prefixReceipt input ≤
                      wholeRestartNextKineticDissipationPayment
                        initial index := by
  let endpoint : Set.Icc (0 : Real)
      (run initial index).nextContact.time.1 :=
    ⟨(run initial index).nextContact.time.1,
      ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩
  obtain heatEq |
      ⟨first, earlier, earlierLt, pairNonzero, _highInput⟩ :=
    sameReceipt_rowOutsideDoubledRadius_eq_heatInitial_or_causalHighInput
      (run initial index).nextContact.prefixReceipt radius
      output endpoint outputOutside
  · left
    rw [← (run initial index).nextContact.prefixReceipt_terminal]
    exact heatEq
  · obtain ⟨input, outside, inputNonzero, debitPos, debitLe⟩ :=
      wholeRestartPairVector_outsideDoubledRadius_generates_highInputKineticDebit
        initial index radius output first earlier outputOutside pairNonzero
    exact Or.inr
      ⟨first, earlier, earlierLt, pairNonzero,
        input, outside, inputNonzero, debitPos, debitLe⟩

/-- Any high-frequency departure from the exact homogeneous source write is
therefore not autonomous: it generates a concrete earlier pair incidence and
a positive high-input debit already charged to the same native edge. -/
theorem
    wholeRestartTerminalHighRow_ne_heatSource_generates_highInputKineticDebit
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (output : NonzeroIntegerWavevector)
    (outputOutside : output.1 ∉ wholeRestartModes (2 * radius))
    (notHeatWrite :
      (run initial index).nextContact.physicalState output.1 ≠
        finiteStateVorticityHeatMultiplier
            nu.coeff (run initial index).nextContact.time.1 output.1 •
          (run initial index).contact.physicalState output.1) :
    ∃ first : IntegerWavevector,
      ∃ earlier : Set.Icc (0 : Real)
          (run initial index).nextContact.time.1,
        earlier <
            (⟨(run initial index).nextContact.time.1,
              ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ :
              Set.Icc (0 : Real)
                (run initial index).nextContact.time.1) ∧
          actualWholeContinuousPairVector
              (run initial index).nextContact.prefixReceipt
              output.1 first earlier ≠ 0 ∧
            ∃ input : NonzeroIntegerWavevector,
              input.1 ∉ wholeRestartModes radius ∧
                (run initial index).nextContact.prefixReceipt.wholePath
                    earlier input.1 ≠ 0 ∧
                  0 < actualWholeRowKineticViscousWork
                    (run initial index).nextContact.prefixReceipt input ∧
                  actualWholeRowKineticViscousWork
                      (run initial index).nextContact.prefixReceipt input ≤
                    wholeRestartNextKineticDissipationPayment
                      initial index := by
  rcases
      wholeRestartTerminalHighRow_eq_heatSource_or_highInputKineticDebit
        initial index radius output outputOutside with heatEq | paid
  · exact (notHeatWrite heatEq).elim
  · exact paid

/-- Every nonzero terminal row outside the doubled cube exposes an actual
high input on the same receipt and hence a positive kinetic debit paid by the
same edge.  The homogeneous branch is included: its nonzero source row is
already present at physical time zero of that receipt. -/
theorem wholeRestartTerminalHighRow_generates_highInputKineticDebit
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (output : NonzeroIntegerWavevector)
    (outputOutside : output.1 ∉ wholeRestartModes (2 * radius))
    (terminalRowNonzero :
      (run initial index).nextContact.physicalState output.1 ≠ 0) :
    ∃ input : NonzeroIntegerWavevector,
      input.1 ∉ wholeRestartModes radius ∧
        ∃ time : Set.Icc (0 : Real)
            (run initial index).nextContact.time.1,
          (run initial index).nextContact.prefixReceipt.wholePath
              time input.1 ≠ 0 ∧
            0 < actualWholeRowKineticViscousWork
              (run initial index).nextContact.prefixReceipt input ∧
            actualWholeRowKineticViscousWork
                (run initial index).nextContact.prefixReceipt input ≤
              wholeRestartNextKineticDissipationPayment initial index := by
  rcases
      wholeRestartTerminalHighRow_eq_heatSource_or_highInputKineticDebit
        initial index radius output outputOutside with heatEq | paid
  · have sourceNonzero :
        (run initial index).contact.physicalState output.1 ≠ 0 := by
      intro sourceZero
      apply terminalRowNonzero
      rw [heatEq, sourceZero]
      simp
    have outputOutsideRadius :
        output.1 ∉ wholeRestartModes radius := by
      intro outputInside
      apply outputOutside
      unfold wholeRestartModes puncturedIntegerWaveFrequencyCube at outputInside ⊢
      rw [Finset.mem_erase] at outputInside ⊢
      exact
        ⟨outputInside.1,
          integerWaveFrequencyCube_mono (by omega) outputInside.2⟩
    let zeroTime : Set.Icc (0 : Real)
        (run initial index).nextContact.time.1 :=
      ⟨0, ⟨le_rfl, (run initial index).nextContact.time_pos.le⟩⟩
    have initialRowNonzero :
        (run initial index).nextContact.prefixReceipt.wholePath
            zeroTime output.1 ≠ 0 := by
      dsimp only [zeroTime]
      rw [(run initial index).nextContact.prefixReceipt.wholePath_initial]
      exact sourceNonzero
    exact
      ⟨output, outputOutsideRadius, zeroTime, initialRowNonzero,
        actualWholeRowKineticViscousWork_pos_of_wholePath_ne_zero
          (run initial index).nextContact.prefixReceipt
          output zeroTime initialRowNonzero,
        actualEdgeRowKineticViscousWork_le_nextPayment
          initial index output⟩
  · obtain ⟨_first, earlier, _earlierLt, _pairNonzero,
        input, inputOutside, inputNonzero, debitPos, debitLe⟩ := paid
    exact
      ⟨input, inputOutside, earlier, inputNonzero, debitPos, debitLe⟩

/-- Vanishing high-input debit on one native edge forces every row outside
the doubled cube of its terminal whole state to vanish. -/
theorem wholeRestartNextHighFrequencyRow_eq_zero_of_noHighInputKineticDebit
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (noHighInputDebit :
      ∀ input : NonzeroIntegerWavevector,
        input.1 ∉ wholeRestartModes radius →
          actualWholeRowKineticViscousWork
            (run initial index).nextContact.prefixReceipt input = 0)
    (wave : IntegerWavevector)
    (waveOutside : wave ∉ wholeRestartModes (2 * radius)) :
    (run initial index).nextContact.physicalState wave = 0 := by
  by_cases waveZero : wave = 0
  · subst wave
    exact (run initial index).nextContact.physicalState_zero
  · let output : NonzeroIntegerWavevector := ⟨wave, waveZero⟩
    by_contra terminalRowNonzero
    obtain ⟨input, inputOutside, _time, _inputNonzero,
        debitPos, _debitLe⟩ :=
      wholeRestartTerminalHighRow_generates_highInputKineticDebit
        initial index radius output waveOutside terminalRowNonzero
    have debitZero := noHighInputDebit input inputOutside
    linarith

/-- Whole-carrier no-free consumer: if an edge has no high-input debit beyond
`radius`, then the complete terminal tail beyond the doubled cube is zero. -/
theorem wholeRestartNextHighFrequencyTailMass_eq_zero_of_noHighInputKineticDebit
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (noHighInputDebit :
      ∀ input : NonzeroIntegerWavevector,
        input.1 ∉ wholeRestartModes radius →
          actualWholeRowKineticViscousWork
            (run initial index).nextContact.prefixReceipt input = 0) :
    restartPhysicalHighFrequencyTailMass
        initial (index + 1) (2 * radius) = 0 := by
  rw [restartPhysicalHighFrequencyTailMass_eq_tsum_compl]
  have densityZero :
      (fun wave : IntegerWavevector =>
        if wave ∈ wholeRestartModes (2 * radius) then 0
        else complexCoordinateAmplitudeSq
          ((run initial (index + 1)).contact.physicalState wave)) = 0 := by
    funext wave
    by_cases waveMem : wave ∈ wholeRestartModes (2 * radius)
    · simp only [waveMem, if_true, Pi.zero_apply]
    · simp only [waveMem, if_false, Pi.zero_apply]
      have rowZero :=
        wholeRestartNextHighFrequencyRow_eq_zero_of_noHighInputKineticDebit
          initial index radius noHighInputDebit wave waveMem
      change
        complexCoordinateAmplitudeSq
            ((run initial index).nextContact.physicalState wave) = 0
      rw [rowZero]
      simp [complexCoordinateAmplitudeSq]
  rw [densityZero]
  exact tsum_zero

/-- If every terminal row outside the doubled cube is the exact homogeneous
write of its source row, the complete terminal tail cannot exceed the source
tail on that same cube. -/
theorem wholeRestartNextHighFrequencyTailMass_le_of_highRows_eq_heatSource
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (highRowsHeat :
      ∀ output : NonzeroIntegerWavevector,
        output.1 ∉ wholeRestartModes (2 * radius) →
          (run initial index).nextContact.physicalState output.1 =
            finiteStateVorticityHeatMultiplier
                nu.coeff (run initial index).nextContact.time.1 output.1 •
              (run initial index).contact.physicalState output.1) :
    restartPhysicalHighFrequencyTailMass
        initial (index + 1) (2 * radius) ≤
      restartPhysicalHighFrequencyTailMass
        initial index (2 * radius) := by
  rw [restartPhysicalHighFrequencyTailMass_eq_tsum_compl,
    restartPhysicalHighFrequencyTailMass_eq_tsum_compl]
  have tailSummable (state : ComplexVorticityHilbertState) :
      Summable fun wave : IntegerWavevector =>
        if wave ∈ wholeRestartModes (2 * radius) then 0
        else complexCoordinateAmplitudeSq (state wave) := by
    have amplitudeSummable :
        Summable fun wave : IntegerWavevector =>
          complexCoordinateAmplitudeSq (state wave) := by
      simpa only [vorticityRowAmplitude_sq,
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
        summable_vorticityRowAmplitude_sq state
    apply amplitudeSummable.of_nonneg_of_le
    · intro wave
      split
      · exact le_rfl
      · exact complexCoordinateAmplitudeSq_nonneg _
    · intro wave
      split
      · exact complexCoordinateAmplitudeSq_nonneg _
      · exact le_rfl
  have pointwise : ∀ wave : IntegerWavevector,
      (if wave ∈ wholeRestartModes (2 * radius) then 0
        else complexCoordinateAmplitudeSq
          ((run initial (index + 1)).contact.physicalState wave)) ≤
      (if wave ∈ wholeRestartModes (2 * radius) then 0
        else complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState wave)) := by
    intro wave
    by_cases waveMem : wave ∈ wholeRestartModes (2 * radius)
    · simp only [waveMem, if_true]
      exact le_rfl
    · simp only [waveMem, if_false]
      by_cases waveZero : wave = 0
      · subst wave
        rw [(run initial (index + 1)).contact.physicalState_zero,
          (run initial index).contact.physicalState_zero]
      · let output : NonzeroIntegerWavevector := ⟨wave, waveZero⟩
        have heatEq := highRowsHeat output waveMem
        dsimp only [output] at heatEq
        change
          complexCoordinateAmplitudeSq
              ((run initial index).nextContact.physicalState wave) ≤
            complexCoordinateAmplitudeSq
              ((run initial index).contact.physicalState wave)
        rw [heatEq, complexCoordinateAmplitudeSq_real_smul]
        have multiplierNonneg :=
          finiteStateVorticityHeatMultiplier_nonneg
            nu.coeff (run initial index).nextContact.time.1 wave
        have multiplierLe :=
          finiteStateVorticityHeatMultiplier_le_one
            nu.coeff_pos.le
            (run initial index).nextContact.time_pos.le wave
        have multiplierSqLe :
            finiteStateVorticityHeatMultiplier
                  nu.coeff (run initial index).nextContact.time.1 wave ^ 2 ≤
              1 := by
          nlinarith
        exact
          (mul_le_mul_of_nonneg_right multiplierSqLe
            (complexCoordinateAmplitudeSq_nonneg
              ((run initial index).contact.physicalState wave))).trans_eq
            (one_mul _)
  exact Summable.tsum_le_tsum pointwise
    (tailSummable (run initial (index + 1)).contact.physicalState)
    (tailSummable (run initial index).contact.physicalState)

/-- A strict increase of the complete high-frequency tail forces a terminal
row that is not the homogeneous source write.  Its departure is therefore an
actual nonlinear occurrence, not an observer-only carrier downgrade. -/
theorem wholeRestartHighFrequencyTail_increase_generates_nonHeatHighRow
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (tailIncrease :
      restartPhysicalHighFrequencyTailMass initial index (2 * radius) <
        restartPhysicalHighFrequencyTailMass
          initial (index + 1) (2 * radius)) :
    ∃ output : NonzeroIntegerWavevector,
      output.1 ∉ wholeRestartModes (2 * radius) ∧
        (run initial index).nextContact.physicalState output.1 ≠
          finiteStateVorticityHeatMultiplier
              nu.coeff (run initial index).nextContact.time.1 output.1 •
            (run initial index).contact.physicalState output.1 := by
  by_contra noNonHeatRow
  have highRowsHeat :
      ∀ output : NonzeroIntegerWavevector,
        output.1 ∉ wholeRestartModes (2 * radius) →
          (run initial index).nextContact.physicalState output.1 =
            finiteStateVorticityHeatMultiplier
                nu.coeff (run initial index).nextContact.time.1 output.1 •
              (run initial index).contact.physicalState output.1 := by
    intro output outputOutside
    by_contra notHeat
    exact noNonHeatRow ⟨output, outputOutside, notHeat⟩
  exact
    (not_lt_of_ge
      (wholeRestartNextHighFrequencyTailMass_le_of_highRows_eq_heatSource
        initial index radius highRowsHeat)) tailIncrease

/-- Outside pair-incidence work left after the identical receipt's literal
viscous debit. -/
def wholeRestartOutsidePairViscousFlux
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat) : Real :=
  ∑' output : NonzeroIntegerWavevector,
    if output.1 ∈ wholeRestartModes radius then 0
    else
      (∑' first : IntegerWavevector,
          actualWholePairOccurrenceWork
            (run initial index).nextContact.prefixReceipt output.1 first) -
        actualWholeRowViscousPayment
          (run initial index).nextContact.prefixReceipt output.1

/-- A strict high-frequency tail increase on one native edge is exactly the
positive outside pair-incidence flux left after the same receipt's literal
viscous debit. -/
theorem wholeRestartHighFrequencyTailIncrease_exactOutsidePairFlux
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (tailIncrease :
      restartPhysicalHighFrequencyTailMass initial index radius <
        restartPhysicalHighFrequencyTailMass initial (index + 1) radius) :
    0 < wholeRestartOutsidePairViscousFlux initial index radius ∧
      restartPhysicalHighFrequencyTailMass initial (index + 1) radius -
          restartPhysicalHighFrequencyTailMass initial index radius =
        wholeRestartOutsidePairViscousFlux initial index radius := by
  let receipt := (run initial index).nextContact.prefixReceipt
  have boundary :=
    receiptHighFrequencyProjectedParabolicTrace_eq_boundaryComplement
      receipt radius
  have incidence :=
    receiptHighFrequencyProjectedParabolicTrace_eq_complementPair_sub_viscous
      receipt radius
  rw [(run initial index).nextContact_prefix_terminal] at boundary
  have fluxEq :
      restartPhysicalHighFrequencyTailMass initial (index + 1) radius -
          restartPhysicalHighFrequencyTailMass initial index radius =
        wholeRestartOutsidePairViscousFlux initial index radius := by
    change
      receiptHighFrequencyProjectedParabolicTrace receipt radius =
          nu.coeff *
            (restartPhysicalHighFrequencyTailMass
                initial (index + 1) radius -
              restartPhysicalHighFrequencyTailMass initial index radius)
        at boundary
    have scaledEq :
        nu.coeff *
              (restartPhysicalHighFrequencyTailMass
                  initial (index + 1) radius -
                restartPhysicalHighFrequencyTailMass initial index radius) =
          nu.coeff *
            wholeRestartOutsidePairViscousFlux initial index radius := by
      calc
        _ = receiptHighFrequencyProjectedParabolicTrace receipt radius :=
          boundary.symm
        _ = _ := by
          simpa only [receipt, wholeRestartOutsidePairViscousFlux] using
            incidence
    exact mul_left_cancel₀ (ne_of_gt nu.coeff_pos) scaledEq
  constructor
  · rw [← fluxEq]
    exact sub_pos.mpr tailIncrease
  · exact fluxEq

/-- The outside pair-viscous flux of one native edge is paid by the complete
whole-carrier dual action of the identical receipt. -/
theorem wholeRestartOutsidePairViscousFlux_le_nextDualPayment
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat) :
    wholeRestartOutsidePairViscousFlux initial index radius ≤
      (6 / nu.coeff) *
        (‖receiptViscousNegativeOneState
              (run initial index).nextContact.prefixReceipt‖ *
          ‖receiptNonlinearNegativeOneState
              (run initial index).nextContact.prefixReceipt‖) := by
  let receipt := (run initial index).nextContact.prefixReceipt
  let terminal : ComplexVorticityHilbertState :=
    receipt.wholePath
      ⟨(run initial index).nextContact.time.1,
        ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩
  have outsideRowsSummable :
      Summable fun output : NonzeroIntegerWavevector =>
        if output.1 ∈ wholeRestartModes radius then 0
        else
          (∑' first : IntegerWavevector,
              actualWholePairOccurrenceWork receipt output.1 first) -
            actualWholeRowViscousPayment receipt output.1 := by
    have terminalSummable :=
      summable_puncturedWholeVorticityEuclideanMass terminal
    have initialSummable :=
      summable_puncturedWholeVorticityEuclideanMass
        (run initial index).contact.physicalState
    let outside : Set NonzeroIntegerWavevector :=
      { output | output.1 ∉ wholeRestartModes radius }
    refine ((terminalSummable.sub initialSummable).indicator outside).congr ?_
    intro output
    by_cases outputMem : output.1 ∈ wholeRestartModes radius
    · simp only [Set.indicator, outside, Set.mem_setOf_eq,
        outputMem, not_true_eq_false, if_false, if_pos]
    · rw [if_neg outputMem]
      simp only [Set.indicator, outside, Set.mem_setOf_eq,
        outputMem, not_false_eq_true, if_true]
      rw [tsum_actualWholePairOccurrenceWork_eq_rowPreQuotientWork
          receipt output.1 output.2,
        actualWholeRowPreQuotientWork_eq_bilinearWork,
        ← actualWholeRowNonlinearWork_eq_bilinearWork]
      unfold actualWholeRowNonlinearWork
      rw [actualWholeRowNetWork_eq_terminal_sub_initial]
      simp only [terminal]
      ring
  have positiveRowsSummable :
      Summable fun output : NonzeroIntegerWavevector =>
        max (actualWholeRowBilinearWork receipt output.1) 0 :=
    (summable_max_actualWholeRowBilinearWork receipt).subtype
      { wave : IntegerWavevector | wave ≠ 0 }
  have outsideLePositive :
      wholeRestartOutsidePairViscousFlux initial index radius ≤
        ∑' output : NonzeroIntegerWavevector,
          max (actualWholeRowBilinearWork receipt output.1) 0 := by
    unfold wholeRestartOutsidePairViscousFlux
    exact outsideRowsSummable.tsum_le_tsum
      (fun output => by
        by_cases outputMem : output.1 ∈ wholeRestartModes radius
        · rw [if_pos outputMem]
          exact le_max_right _ _
        · rw [if_neg outputMem,
            tsum_actualWholePairOccurrenceWork_eq_rowPreQuotientWork
              receipt output.1 output.2,
            actualWholeRowPreQuotientWork_eq_bilinearWork]
          exact
            (sub_le_self _
              (actualWholeRowViscousPayment_nonneg receipt output.1)).trans
              (le_max_left _ _))
      positiveRowsSummable
  calc
    wholeRestartOutsidePairViscousFlux initial index radius ≤
        ∑' output : NonzeroIntegerWavevector,
          max (actualWholeRowBilinearWork receipt output.1) 0 :=
      outsideLePositive
    _ ≤
        ∑' output : IntegerWavevector,
          max (actualWholeRowBilinearWork receipt output) 0 := by
      exact
        Summable.tsum_subtype_le
          (fun output : IntegerWavevector =>
            max (actualWholeRowBilinearWork receipt output) 0)
          { output : IntegerWavevector | output ≠ 0 }
          (fun output => le_max_right _ _)
          (summable_max_actualWholeRowBilinearWork receipt)
    _ ≤ _ :=
      tsum_max_actualWholeRowBilinearWork_le_dualBudget receipt

/-- Finite blocks of outside pair-viscous flux are paid by the adjacent
source-generated dual actions with the exact restart index shift. -/
theorem wholeRestartIcoOutsidePairViscousFlux_le_shiftedDualPayment
    (initial : GeneratedWholeRestartCurrent nu)
    (radius start finish : Nat) :
    (∑ index ∈ Finset.Ico start finish,
        wholeRestartOutsidePairViscousFlux initial index radius) ≤
      ∑ index ∈ Finset.Ico start finish,
        wholeRestartSegmentDualPayment initial (index + 1) := by
  apply Finset.sum_le_sum
  intro index _indexMem
  change wholeRestartOutsidePairViscousFlux initial index radius ≤
    (6 / nu.coeff) *
      (‖receiptViscousNegativeOneState
            (run initial index).nextContact.prefixReceipt‖ *
        ‖receiptNonlinearNegativeOneState
            (run initial index).nextContact.prefixReceipt‖)
  exact
    wholeRestartOutsidePairViscousFlux_le_nextDualPayment
      initial index radius

/-- One actual nonlinear transfer outside the doubled low cube produces a
strictly positive high-input kinetic debit, and the existing source-owned
kinetic ledger pays that debit on the identical native edge. -/
theorem
    wholeRestartPairWork_outsideDoubledRadius_generates_highInputKineticDebit
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (output : NonzeroIntegerWavevector)
    (first : IntegerWavevector)
    (outputOutside : output.1 ∉ wholeRestartModes (2 * radius))
    (workNonzero :
      actualWholePairOccurrenceWork
        (run initial index).nextContact.prefixReceipt output.1 first ≠ 0) :
    ∃ time : Set.Icc (0 : Real)
        (run initial index).nextContact.time.1,
      ∃ input : NonzeroIntegerWavevector,
        actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output.1 first time ≠ 0 ∧
          input.1 ∉ wholeRestartModes radius ∧
          (run initial index).nextContact.prefixReceipt.wholePath
              time input.1 ≠ 0 ∧
          0 < actualWholeRowKineticViscousWork
            (run initial index).nextContact.prefixReceipt input ∧
          actualWholeRowKineticViscousWork
              (run initial index).nextContact.prefixReceipt input ≤
            wholeRestartNextKineticDissipationPayment initial index := by
  obtain ⟨time, pairNonzero, _highInput⟩ :=
    sameReceipt_pairWork_outsideDoubledRadius_generates_highInput
      (run initial index).nextContact.prefixReceipt radius
      output first outputOutside workNonzero
  obtain ⟨input, outside, inputNonzero, debitPos, debitLe⟩ :=
    wholeRestartPairVector_outsideDoubledRadius_generates_highInputKineticDebit
      initial index radius output first time outputOutside pairNonzero
  exact
    ⟨time, input, pairNonzero, outside, inputNonzero, debitPos, debitLe⟩

/-- The original cofinal occurrence generates arbitrarily late strict tail
increases.  Each increase forces an actual non-heat row, hence a strictly
earlier pair incidence with a high input and positive kinetic debit paid on
that identical native edge.  The root occurrence and whole write are fixed
before the bounded analytic fibre is consumed. -/
theorem
    sourceGeneratedNativeAccumulationCofinalTailIncrease_generates_pairKineticDebit
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (radius lower : Nat) :
    let root := nativeTemporalAuthoritativeRoot initial
    let cofinalVisit : LawfulWorldStateAt root :=
      .cofinal (nativeTemporalCofinalVisit initial)
    let nextVisit : LawfulWorldStateAt root :=
      (nativeTemporalCofinalNextCurrent initial).visit
    let difference : RootTotalReality.RootDifference root :=
      (cofinalVisit, nextVisit)
    ActualDifferenceAt (RootTotalReality.semantics root) difference ∧
      (RootTotalReality.semantics root).StructuralIdentityAt difference ∧
      (root.toLedgerRoot.generatedAtTemporalVisit cofinalVisit).wholeLedgerWriteBack =
        nativeTemporalCofinalWrite initial ∧
      (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence =
        nativeTemporalEmitted initial .cofinal ∧
      ∃ index : Nat,
        lower ≤ index ∧
          restartPhysicalHighFrequencyTailMass
              initial index (2 * radius) <
            restartPhysicalHighFrequencyTailMass
              initial (index + 1) (2 * radius) ∧
          ∃ output : NonzeroIntegerWavevector,
            output.1 ∉ wholeRestartModes (2 * radius) ∧
              (run initial index).nextContact.physicalState output.1 ≠
                finiteStateVorticityHeatMultiplier
                    nu.coeff
                    (run initial index).nextContact.time.1 output.1 •
                  (run initial index).contact.physicalState output.1 ∧
              ∃ first : IntegerWavevector,
                ∃ earlier : Set.Icc (0 : Real)
                    (run initial index).nextContact.time.1,
                  ∃ input : NonzeroIntegerWavevector,
                    earlier <
                        (⟨(run initial index).nextContact.time.1,
                          ⟨(run initial index).nextContact.time_pos.le,
                            le_rfl⟩⟩ :
                          Set.Icc (0 : Real)
                            (run initial index).nextContact.time.1) ∧
                    actualWholeContinuousPairVector
                        (run initial index).nextContact.prefixReceipt
                        output.1 first earlier ≠ 0 ∧
                    input.1 ∉ wholeRestartModes radius ∧
                    (run initial index).nextContact.prefixReceipt.wholePath
                        earlier input.1 ≠ 0 ∧
                    0 < actualWholeRowKineticViscousWork
                      (run initial index).nextContact.prefixReceipt input ∧
                    actualWholeRowKineticViscousWork
                        (run initial index).nextContact.prefixReceipt input ≤
                      wholeRestartNextKineticDissipationPayment
                        initial index := by
  dsimp only
  have rootGrounding :=
    nativeTemporalCofinalRootDifference_actualAndStructural initial
  dsimp only at rootGrounding
  rcases rootGrounding with ⟨actual, structural⟩
  refine
    ⟨actual, structural,
      nativeTemporalCofinalAuthority_generates_write initial, rfl, ?_⟩
  have tailDiverges :=
    nativeTemporalCofinalWrite_target_highFrequencyTailDiverges
      initial elapsedBounded (2 * radius)
  obtain ⟨index, lowerLe, tailIncrease⟩ :=
    cofinally_exists_adjacent_strictIncrease
      (fun index =>
        restartPhysicalHighFrequencyTailMass
          initial index (2 * radius))
      tailDiverges lower
  obtain ⟨output, outputOutside, notHeatWrite⟩ :=
    wholeRestartHighFrequencyTail_increase_generates_nonHeatHighRow
      initial index radius tailIncrease
  obtain ⟨first, earlier, earlierLt, pairNonzero,
      input, inputOutside, inputNonzero, debitPos, debitLe⟩ :=
    wholeRestartTerminalHighRow_ne_heatSource_generates_highInputKineticDebit
      initial index radius output outputOutside notHeatWrite
  exact
    ⟨index, lowerLe, tailIncrease, output, outputOutside, notHeatWrite,
      first, earlier, input, earlierLt, pairNonzero,
      inputOutside, inputNonzero, debitPos, debitLe⟩

/-- Every source-selected cofinal block carries more than one unit of exact
outside pair-incidence flux after the same receipts' viscous debits.  The
block flux is the literal high-frequency tail gain on the original run. -/
theorem
    sourceGeneratedNativeAccumulationCofinalSelectedBlock_exactOutsidePairFlux
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let root := nativeTemporalAuthoritativeRoot initial
    let cofinalVisit : LawfulWorldStateAt root :=
      .cofinal (nativeTemporalCofinalVisit initial)
    let nextVisit : LawfulWorldStateAt root :=
      (nativeTemporalCofinalNextCurrent initial).visit
    let difference : RootTotalReality.RootDifference root :=
      (cofinalVisit, nextVisit)
    ActualDifferenceAt (RootTotalReality.semantics root) difference ∧
      (RootTotalReality.semantics root).StructuralIdentityAt difference ∧
      (root.toLedgerRoot.generatedAtTemporalVisit cofinalVisit).wholeLedgerWriteBack =
        nativeTemporalCofinalWrite initial ∧
      (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence =
        nativeTemporalEmitted initial .cofinal ∧
      ∃ contactIndex : Nat → Nat,
        contactIndex 0 = 0 ∧
          StrictMono contactIndex ∧
          ∀ step : Nat,
            let baseRadius := contactIndex step + 1
            let radius := 2 * baseRadius
            let interval :=
              Finset.Ico (contactIndex step) (contactIndex (step + 1))
            nu.coeff <
                ∑ index ∈ interval,
                  receiptHighFrequencyProjectedParabolicTrace
                    (run initial index).nextContact.prefixReceipt radius ∧
              1 < ∑ index ∈ interval,
                wholeRestartOutsidePairViscousFlux initial index radius ∧
              1 < ∑ index ∈ interval,
                wholeRestartSegmentDualPayment initial (index + 1) ∧
              restartPhysicalHighFrequencyTailMass
                    initial (contactIndex (step + 1)) radius -
                  restartPhysicalHighFrequencyTailMass
                    initial (contactIndex step) radius =
                ∑ index ∈ interval,
                  wholeRestartOutsidePairViscousFlux initial index radius := by
  dsimp only
  have rootGrounding :=
    nativeTemporalCofinalRootDifference_actualAndStructural initial
  dsimp only at rootGrounding
  rcases rootGrounding with ⟨actual, structural⟩
  refine
    ⟨actual, structural,
      nativeTemporalCofinalAuthority_generates_write initial, rfl, ?_⟩
  have generated :=
    elapsedBounded_generatesCofinalHighFrequencyProjectedParabolicTrace
      initial elapsedBounded
  dsimp only at generated
  rcases generated with
    ⟨contactIndex, contactIndexZero, contactIndexStrictMono, blockEffect⟩
  refine
    ⟨contactIndex, contactIndexZero, contactIndexStrictMono, ?_⟩
  intro step
  let baseRadius := contactIndex step + 1
  let radius := 2 * baseRadius
  let interval :=
    Finset.Ico (contactIndex step) (contactIndex (step + 1))
  have block := blockEffect step
  have tracePositive :
      nu.coeff <
        ∑ index ∈ interval,
          receiptHighFrequencyProjectedParabolicTrace
            (run initial index).nextContact.prefixReceipt radius := by
    simpa only [interval, radius, baseRadius] using block.1
  refine ⟨tracePositive, ?_⟩
  have edgeFluxEq (index : Nat) :
      receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt radius =
        nu.coeff *
          wholeRestartOutsidePairViscousFlux initial index radius := by
    unfold wholeRestartOutsidePairViscousFlux
    exact
      (receiptHighFrequencyProjectedParabolicTrace_eq_complementPair_sub_viscous
        (run initial index).nextContact.prefixReceipt radius)
  have traceSumFluxEq :
      (∑ index ∈ interval,
          receiptHighFrequencyProjectedParabolicTrace
            (run initial index).nextContact.prefixReceipt radius) =
        nu.coeff * ∑ index ∈ interval,
          wholeRestartOutsidePairViscousFlux initial index radius := by
    calc
      _ = ∑ index ∈ interval,
            nu.coeff *
              wholeRestartOutsidePairViscousFlux initial index radius := by
        apply Finset.sum_congr rfl
        intro index _indexMem
        exact edgeFluxEq index
      _ = _ := by rw [← Finset.mul_sum]
  have blockFluxGt :
      1 < ∑ index ∈ interval,
        wholeRestartOutsidePairViscousFlux initial index radius := by
    rw [traceSumFluxEq] at tracePositive
    nlinarith [nu.coeff_pos]
  have blockDualGt :
      1 < ∑ index ∈ interval,
        wholeRestartSegmentDualPayment initial (index + 1) :=
    blockFluxGt.trans_le
      (wholeRestartIcoOutsidePairViscousFlux_le_shiftedDualPayment
        initial radius (contactIndex step) (contactIndex (step + 1)))
  have blockTailEq :
      restartPhysicalHighFrequencyTailMass
            initial (contactIndex (step + 1)) radius -
          restartPhysicalHighFrequencyTailMass
            initial (contactIndex step) radius =
        ∑ index ∈ interval,
          wholeRestartOutsidePairViscousFlux initial index radius := by
    have telescope :=
      wholeRestartIcoHighFrequencyProjectedParabolicTrace_telescope
        initial radius (contactIndex step) (contactIndex (step + 1))
        (contactIndexStrictMono (Nat.lt_succ_self step)).le
    change
      (∑ index ∈ interval,
          receiptHighFrequencyProjectedParabolicTrace
            (run initial index).nextContact.prefixReceipt radius) =
        nu.coeff *
          (restartPhysicalHighFrequencyTailMass
              initial (contactIndex (step + 1)) radius -
            restartPhysicalHighFrequencyTailMass
              initial (contactIndex step) radius)
      at telescope
    nlinarith [nu.coeff_pos, traceSumFluxEq]
  exact ⟨blockFluxGt, blockDualGt, blockTailEq⟩

/-- The whole nonlinear Duhamel prefix written by the first `index` actual native restart events.
The start index is fixed by the original source; no crossing or future scheduler is selected. -/
def nativeAccumulationNonlinearDuhamelPrefix
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) : ComplexVorticityHilbertState :=
  wholeRestartBlockNonlinearRegenerationAggregate initial 0 index

/-- Exact whole-carrier write-back for the original finite source prefix. -/
theorem run_contact_eq_transportedInitial_add_nativeAccumulationNonlinearDuhamelPrefix
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) :
    (run initial index).contact.physicalState =
      wholeRestartBlockTransportedInitialState initial 0 index +
        nativeAccumulationNonlinearDuhamelPrefix initial index := by
  have write :=
    run_contact_eq_blockTransportedInitial_add_nonlinearAggregate initial 0 index
  rw [show 0 + index = index by omega] at write
  exact write

/-- Two finite temporal-root occurrences carry the exact whole-vorticity
contact difference written by their common nonlinear Duhamel prefix. -/
theorem finiteRootNonlinearDuhamelDifference_commutes_with_temporalOccurrences
    (initial : GeneratedWholeRestartCurrent nu)
    (left right : Nat) :
    let root := nativeTemporalRoot initial
    let history := nativeTemporalProductiveHistory initial
    let leftVisit : SourceNativeTemporalVisitAt root :=
      .finite (history.visitAt left)
    let rightVisit : SourceNativeTemporalVisitAt root :=
      .finite (history.visitAt right)
    let leftEvolution := root.generatedAtTemporalVisit leftVisit
    let rightEvolution := root.generatedAtTemporalVisit rightVisit
    leftEvolution.occurrence =
        nativeTemporalEmitted initial (history.visitAt left).current ∧
      rightEvolution.occurrence =
        nativeTemporalEmitted initial (history.visitAt right).current ∧
      leftVisit.current =
        (.finite left : NativeTemporalCurrent initial) ∧
      rightVisit.current =
        (.finite right : NativeTemporalCurrent initial) ∧
      (run initial left).contact.physicalState -
          (run initial right).contact.physicalState =
        (wholeRestartBlockTransportedInitialState initial 0 left -
            wholeRestartBlockTransportedInitialState initial 0 right) +
          (nativeAccumulationNonlinearDuhamelPrefix initial left -
            nativeAccumulationNonlinearDuhamelPrefix initial right) := by
  dsimp only
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact (nativeTemporalProductiveHistory initial).visitAt_current left
  · exact (nativeTemporalProductiveHistory initial).visitAt_current right
  · rw [
      run_contact_eq_transportedInitial_add_nativeAccumulationNonlinearDuhamelPrefix,
      run_contact_eq_transportedInitial_add_nativeAccumulationNonlinearDuhamelPrefix]
    abel

/-- The prefix is advanced by the same actual native event: old nonlinear responsibility is heat
transported and the event's exact unforced Duhamel receipt is written once. -/
theorem nativeAccumulationNonlinearDuhamelPrefix_succ
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) :
    nativeAccumulationNonlinearDuhamelPrefix initial (index + 1) =
      wholeVorticityHeatEvolution nu
          ⟨(run initial (0 + index)).nextContact.time.1,
            (run initial (0 + index)).nextContact.time_pos.le⟩
          (nativeAccumulationNonlinearDuhamelPrefix initial index) +
        wholeRestartNonlinearRegenerationState initial (0 + index) := by
  rfl

/-- Coordinate form of the same update: every nonzero row is written by the actual unforced
Duhamel receipt on that native edge. -/
theorem nativeAccumulationNonlinearDuhamelPrefix_succ_apply_eq_actualDuhamel
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    nativeAccumulationNonlinearDuhamelPrefix initial (index + 1) output =
      finiteStateVorticityHeatMultiplier nu.coeff
          (run initial (0 + index)).nextContact.time.1 output •
        nativeAccumulationNonlinearDuhamelPrefix initial index output +
      receiptWeightedNonlinearDuhamelAt
        (run initial (0 + index)).nextContact.prefixReceipt
        output outputNonzero
        ⟨(run initial (0 + index)).nextContact.time.1,
          ⟨(run initial (0 + index)).nextContact.time_pos.le, le_rfl⟩⟩ := by
  have update := congrArg
    (fun state : ComplexVorticityHilbertState => state output)
    (nativeAccumulationNonlinearDuhamelPrefix_succ initial index)
  change
    nativeAccumulationNonlinearDuhamelPrefix initial (index + 1) output =
      wholeVorticityHeatEvolution nu
          ⟨(run initial (0 + index)).nextContact.time.1,
            (run initial (0 + index)).nextContact.time_pos.le⟩
          (nativeAccumulationNonlinearDuhamelPrefix initial index) output +
        wholeRestartNonlinearRegenerationState
          initial (0 + index) output at update
  change
    nativeAccumulationNonlinearDuhamelPrefix initial (index + 1) output =
      finiteStateVorticityHeatMultiplier nu.coeff
          (run initial (0 + index)).nextContact.time.1 output •
        nativeAccumulationNonlinearDuhamelPrefix initial index output +
      wholeRestartNonlinearRegenerationState initial (0 + index) output
    at update
  rw [wholeRestartNonlinearRegenerationState_apply_eq_actualDuhamel] at update
  exact update

/-- The source-owned same-`T` vorticity failure is carried by the complete nonlinear Duhamel
prefix.  The theorem consumes no finite crossing, selected index, endpoint, branch, or bound. -/
theorem nativeAccumulationNonlinearDuhamelPrefix_punctured_norm_tendsto_atTop
    (initial : GeneratedWholeRestartCurrent nu)
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (failure : SourceGeneratedNativeAccumulationVorticityFailureAt
      initial elapsedBounded) :
    Tendsto
      (fun index =>
        ‖puncturedEuclideanize
          (nativeAccumulationNonlinearDuhamelPrefix initial index)‖)
      atTop atTop := by
  rw [tendsto_atTop]
  intro requested
  let initialNorm :=
    ‖puncturedEuclideanize (run initial 0).contact.physicalState‖
  let threshold := max requested 0 + initialNorm + 1
  have thresholdNonneg : 0 ≤ threshold := by
    dsimp only [threshold]
    positivity
  have endpointMassEventually :
      ∀ᶠ index : Nat in atTop,
        threshold ^ 2 ≤ restartPhysicalVorticityMass initial index :=
    (tendsto_atTop.1 failure.vorticityDiverges) (threshold ^ 2)
  filter_upwards [endpointMassEventually] with index endpointMassLarge
  let finish :=
    puncturedEuclideanize (run initial index).contact.physicalState
  let transported :=
    puncturedEuclideanize
      (wholeRestartBlockTransportedInitialState initial 0 index)
  let nonlinear :=
    puncturedEuclideanize
      (nativeAccumulationNonlinearDuhamelPrefix initial index)
  have endpointDecomposition : finish = transported + nonlinear := by
    dsimp only [finish, transported, nonlinear]
    rw [run_contact_eq_transportedInitial_add_nativeAccumulationNonlinearDuhamelPrefix]
    apply lp.ext
    funext wave
    rfl
  have transportedLe : ‖transported‖ ≤ initialNorm := by
    exact blockTransportedInitial_punctured_norm_le initial 0 index
  have finishLe : ‖finish‖ ≤ initialNorm + ‖nonlinear‖ := by
    calc
      ‖finish‖ = ‖transported + nonlinear‖ := by rw [endpointDecomposition]
      _ ≤ ‖transported‖ + ‖nonlinear‖ := norm_add_le _ _
      _ ≤ initialNorm + ‖nonlinear‖ := by
        simpa only [add_comm] using
          add_le_add_right transportedLe ‖nonlinear‖
  have endpointSquareLarge : threshold ^ 2 ≤ ‖finish‖ ^ 2 := by
    rw [restartPhysicalVorticityMass_eq_puncturedEuclideanize_norm_sq]
      at endpointMassLarge
    exact endpointMassLarge
  have thresholdLeFinish : threshold ≤ ‖finish‖ := by
    nlinarith [norm_nonneg finish]
  have requestedLeMax : requested ≤ max requested 0 := le_max_left _ _
  dsimp only [threshold] at thresholdLeFinish
  nlinarith

/-- Source-facing form: the original finite source and bounded elapsed-time law generate the
same-`T` nonlinear whole-PDE concentration directly. -/
theorem sourceGeneratedNativeAccumulationNonlinearDuhamelPrefix_punctured_norm_tendsto_atTop
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (fun index =>
        ‖puncturedEuclideanize
          (nativeAccumulationNonlinearDuhamelPrefix initial index)‖)
      atTop atTop := by
  exact
    nativeAccumulationNonlinearDuhamelPrefix_punctured_norm_tendsto_atTop
      initial
      (sourceGeneratedNativeAccumulationVorticityFailure
        initial elapsedBounded)

/-- Every requested late scale is witnessed by an actual pair of finite
temporal-root occurrences whose exact nonlinear Duhamel difference carries
that scale.  The bounded fibre selects `finish`; both occurrences and their
whole writes remain generated by the original finite root. -/
theorem sourceGeneratedNativeAccumulationNonlinearDuhamelPrefix_lateRootDifference
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (requested : Real)
    (start : Nat) :
    ∃ finish : Nat,
      start ≤ finish ∧
        requested ≤
          ‖puncturedEuclideanize
            (nativeAccumulationNonlinearDuhamelPrefix initial finish -
              nativeAccumulationNonlinearDuhamelPrefix initial start)‖ ∧
        (let root := nativeTemporalRoot initial
         let history := nativeTemporalProductiveHistory initial
         let leftVisit : SourceNativeTemporalVisitAt root :=
           .finite (history.visitAt finish)
         let rightVisit : SourceNativeTemporalVisitAt root :=
           .finite (history.visitAt start)
         let leftEvolution := root.generatedAtTemporalVisit leftVisit
         let rightEvolution := root.generatedAtTemporalVisit rightVisit
         leftEvolution.occurrence =
             nativeTemporalEmitted initial (history.visitAt finish).current ∧
           rightEvolution.occurrence =
             nativeTemporalEmitted initial (history.visitAt start).current ∧
           leftVisit.current =
             (.finite finish : NativeTemporalCurrent initial) ∧
           rightVisit.current =
             (.finite start : NativeTemporalCurrent initial) ∧
           (run initial finish).contact.physicalState -
               (run initial start).contact.physicalState =
             (wholeRestartBlockTransportedInitialState initial 0 finish -
                 wholeRestartBlockTransportedInitialState initial 0 start) +
               (nativeAccumulationNonlinearDuhamelPrefix initial finish -
                 nativeAccumulationNonlinearDuhamelPrefix initial start)) := by
  have prefixTendsto :=
    sourceGeneratedNativeAccumulationNonlinearDuhamelPrefix_punctured_norm_tendsto_atTop
      initial elapsedBounded
  have largeEventually :=
    (tendsto_atTop.1 prefixTendsto)
      (max requested 0 +
        ‖puncturedEuclideanize
          (nativeAccumulationNonlinearDuhamelPrefix initial start)‖)
  have bothEventually :=
    largeEventually.and (eventually_ge_atTop start)
  rcases bothEventually.exists with ⟨finish, large, finishGe⟩
  refine ⟨finish, finishGe, ?_, ?_⟩
  · rw [puncturedEuclideanize_sub]
    calc
      requested ≤ max requested 0 := le_max_left _ _
      _ ≤
          ‖puncturedEuclideanize
            (nativeAccumulationNonlinearDuhamelPrefix initial finish)‖ -
          ‖puncturedEuclideanize
            (nativeAccumulationNonlinearDuhamelPrefix initial start)‖ := by
        linarith
      _ ≤
          ‖puncturedEuclideanize
              (nativeAccumulationNonlinearDuhamelPrefix initial finish) -
            puncturedEuclideanize
              (nativeAccumulationNonlinearDuhamelPrefix initial start)‖ :=
        norm_sub_norm_le _ _
  · exact
      finiteRootNonlinearDuhamelDifference_commutes_with_temporalOccurrences
        initial finish start

/-! ## Exact fixed-row landing of the same whole-PDE prefix -/

/-- The boundary value of the heat-transported original contact on one fixed Fourier row. -/
def nativeAccumulationTransportedInitialBoundaryRow
    (initial : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  finiteStateVorticityHeatMultiplier nu.coeff
      (wholeRestartVelocityAccumulationTime initial - elapsedTime initial 1)
      wave •
    (run initial 0).contact.physicalState wave

/-- The exact row carried by the nonlinear Duhamel prefix at `T`. -/
def nativeAccumulationNonlinearDuhamelBoundaryRow
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  accumulationBoundaryFormalVorticityRow initial elapsedBounded wave -
    nativeAccumulationTransportedInitialBoundaryRow
      initial wave

/-- The transported original contact has an actual row limit at the same accumulation time. -/
theorem nativeAccumulationTransportedInitialState_row_tendsto
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : IntegerWavevector) :
    Tendsto
      (fun index =>
        wholeRestartBlockTransportedInitialState initial 0 index wave)
      atTop
      (nhds (nativeAccumulationTransportedInitialBoundaryRow
        initial wave)) := by
  have elapsedTendsto :
      Tendsto (elapsedTime initial) atTop
        (nhds (wholeRestartVelocityAccumulationTime initial)) := by
    simpa only [wholeRestartVelocityAccumulationTime,
      wholeRestartAccumulationTime] using
      tendsto_atTop_ciSup
        (elapsedTime_strictMono initial).monotone elapsedBounded
  have durationTendsto :
      Tendsto
        (fun index =>
          elapsedTime initial (index + 1) - elapsedTime initial 1)
        atTop
        (nhds
          (wholeRestartVelocityAccumulationTime initial -
            elapsedTime initial 1)) :=
    (elapsedTendsto.comp (tendsto_add_atTop_nat 1)).sub tendsto_const_nhds
  have exponentTendsto :=
    durationTendsto.const_mul
      (-(nu.coeff * integerWaveViscousMultiplier wave))
  have multiplierTendsto :=
    Real.continuous_exp.continuousAt.tendsto.comp exponentTendsto
  have transportedTendsto :=
    multiplierTendsto.smul_const
      ((run initial 0).contact.physicalState wave)
  convert transportedTendsto using 1
  · funext index
    rw [wholeRestartBlockTransportedInitialState_apply_eq_totalHeat]
    simp only [Nat.zero_add]
    unfold finiteStateVorticityHeatMultiplier
    congr 2
  · unfold nativeAccumulationTransportedInitialBoundaryRow
    unfold finiteStateVorticityHeatMultiplier
    congr 2

/-- Every fixed Fourier row of the complete actual nonlinear Duhamel prefix has an exact limit at
the same `T`; the whole-norm divergence therefore lives beyond every fixed row inventory. -/
theorem nativeAccumulationNonlinearDuhamelPrefix_row_tendsto
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : IntegerWavevector) :
    Tendsto
      (fun index =>
        nativeAccumulationNonlinearDuhamelPrefix initial index wave)
      atTop
      (nhds (nativeAccumulationNonlinearDuhamelBoundaryRow
        initial elapsedBounded wave)) := by
  let failure :=
    sourceGeneratedNativeAccumulationVorticityFailure initial elapsedBounded
  have finishTendsto := failure.rowLanding wave
  have transportedTendsto :=
    nativeAccumulationTransportedInitialState_row_tendsto
      initial elapsedBounded wave
  have differenceTendsto := finishTendsto.sub transportedTendsto
  convert differenceTendsto using 1
  · funext index
    have write := congrArg
      (fun state : ComplexVorticityHilbertState => state wave)
      (run_contact_eq_transportedInitial_add_nativeAccumulationNonlinearDuhamelPrefix
        initial index)
    change
      (run initial index).contact.physicalState wave =
        wholeRestartBlockTransportedInitialState initial 0 index wave +
          nativeAccumulationNonlinearDuhamelPrefix initial index wave at write
    rw [write]
    abel
  · rfl

/-- Canonical finite-window landing of the nonlinear Duhamel prefix. -/
def nativeAccumulationNonlinearDuhamelFiniteWindowLimit
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (modes : Finset IntegerWavevector) : ComplexVorticityHilbertState :=
  finiteModeExtension modes fun wave =>
    nativeAccumulationNonlinearDuhamelBoundaryRow
      initial elapsedBounded wave.1

/-- Every fixed Fourier window of the same divergent nonlinear Duhamel prefix lands strongly and
canonically.  Together with the whole-norm theorem this is the exact same-`T` projection-loss
obstruction consumed by the next whole-NS boundary law. -/
theorem nativeAccumulationNonlinearDuhamelPrefix_fixedWindow_tendsto
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (modes : Finset IntegerWavevector) :
    Tendsto
      (fun index =>
        complexSharpSupportProjection modes
          (nativeAccumulationNonlinearDuhamelPrefix initial index))
      atTop
      (nhds (nativeAccumulationNonlinearDuhamelFiniteWindowLimit
        initial elapsedBounded modes)) := by
  have restrictedTendsto :
      Tendsto
        (fun index =>
          finiteModeRestriction modes
            (nativeAccumulationNonlinearDuhamelPrefix initial index))
        atTop
        (nhds (fun wave =>
          nativeAccumulationNonlinearDuhamelBoundaryRow
            initial elapsedBounded wave.1)) := by
    apply tendsto_pi_nhds.mpr
    intro wave
    simpa only [finiteModeRestriction_apply] using
      nativeAccumulationNonlinearDuhamelPrefix_row_tendsto
        initial elapsedBounded wave.1
  have extendedTendsto :=
    (finiteModeExtension modes).continuous.tendsto
        (fun wave =>
          nativeAccumulationNonlinearDuhamelBoundaryRow
            initial elapsedBounded wave.1)
      |>.comp restrictedTendsto
  convert extendedTendsto using 1
  · funext index
    simpa only [Function.comp_apply] using
      (finiteModeExtension_restriction modes
        (nativeAccumulationNonlinearDuhamelPrefix initial index)).symm
  · rfl

/-! ## The complete responsibility survives every fixed observation quotient -/

/-- Complement of one fixed Fourier observation, taken before the quotient forgets the generated
whole-PDE responsibility. -/
def nativeAccumulationNonlinearDuhamelOutsideWindow
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (index : Nat) : ComplexVorticityHilbertState :=
  nativeAccumulationNonlinearDuhamelPrefix initial index -
    complexSharpSupportProjection modes
      (nativeAccumulationNonlinearDuhamelPrefix initial index)

/-- The same-`T` nonlinear responsibility escapes every fixed Fourier window as a complete family.
No late index or outside coordinate appears in the theorem mouth. -/
theorem nativeAccumulationNonlinearDuhamelOutsideWindow_norm_tendsto_atTop
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (modes : Finset IntegerWavevector) :
    Tendsto
      (fun index =>
        ‖nativeAccumulationNonlinearDuhamelOutsideWindow
          initial modes index‖)
      atTop atTop := by
  let windowLimit :=
    nativeAccumulationNonlinearDuhamelFiniteWindowLimit
      initial elapsedBounded modes
  have prefixTendsto :=
    sourceGeneratedNativeAccumulationNonlinearDuhamelPrefix_punctured_norm_tendsto_atTop
      initial elapsedBounded
  have projectionNormTendsto :
      Tendsto
        (fun index =>
          ‖complexSharpSupportProjection modes
            (nativeAccumulationNonlinearDuhamelPrefix initial index)‖)
        atTop
        (nhds ‖windowLimit‖) := by
    simpa only [windowLimit] using
      (nativeAccumulationNonlinearDuhamelPrefix_fixedWindow_tendsto
        initial elapsedBounded modes).norm
  rw [tendsto_atTop]
  intro requested
  have prefixEventually :
      ∀ᶠ index : Nat in atTop,
        2 * (requested + (‖windowLimit‖ + 1)) ≤
          ‖puncturedEuclideanize
            (nativeAccumulationNonlinearDuhamelPrefix initial index)‖ :=
    (tendsto_atTop.1 prefixTendsto)
      (2 * (requested + (‖windowLimit‖ + 1)))
  have projectionEventually :
      ∀ᶠ index : Nat in atTop,
        ‖complexSharpSupportProjection modes
            (nativeAccumulationNonlinearDuhamelPrefix initial index)‖ <
          ‖windowLimit‖ + 1 :=
    (tendsto_order.1 projectionNormTendsto).2
      (‖windowLimit‖ + 1) (by linarith)
  filter_upwards [prefixEventually, projectionEventually] with
      index prefixLarge projectionSmall
  let wholePrefix := nativeAccumulationNonlinearDuhamelPrefix initial index
  let projection := complexSharpSupportProjection modes wholePrefix
  have euclideanLeTwoWhole :
      ‖puncturedEuclideanize wholePrefix‖ ≤ 2 * ‖wholePrefix‖ := by
    have squareLe := puncturedEuclideanize_norm_sq_le wholePrefix
    nlinarith [norm_nonneg (puncturedEuclideanize wholePrefix),
      norm_nonneg wholePrefix,
      sq_nonneg
        (‖puncturedEuclideanize wholePrefix‖ - 2 * ‖wholePrefix‖)]
  have prefixLe :
      ‖wholePrefix‖ ≤ ‖wholePrefix - projection‖ + ‖projection‖ := by
    calc
      ‖wholePrefix‖ = ‖(wholePrefix - projection) + projection‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖wholePrefix - projection‖ + ‖projection‖ := norm_add_le _ _
  change requested ≤
    ‖nativeAccumulationNonlinearDuhamelOutsideWindow initial modes index‖
  unfold nativeAccumulationNonlinearDuhamelOutsideWindow
  dsimp only [wholePrefix, projection] at prefixLe projectionSmall
  linarith

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
end NavierStokes
end SaturationMonoid
