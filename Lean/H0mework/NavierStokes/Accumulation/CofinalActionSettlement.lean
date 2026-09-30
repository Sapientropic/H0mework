import H0mework.NavierStokes.Accumulation.DuhamelBoundary

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

/-! ## Independent whole-NS action consumer -/

/-- The three aggregate payment coordinates on one source-selected block:
pair incidence, tangent/viscous cross, and viscous debit. -/
def nativeAccumulationCofinalBlockPayments
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (step : Nat) : Real × (Real × Real) :=
  let radius := 2 * (contactIndex step + 1)
  let interval := Finset.Ico (contactIndex step) (contactIndex (step + 1))
  (nu.coeff *
      (∑ index ∈ interval,
        actualWholeFinitePairOccurrenceWork
          (run initial index).nextContact.prefixReceipt
          (wholeRestartModes radius)),
    (∑ index ∈ interval,
      2 * RCLike.re (inner ℂ
        (puncturedEuclideanSpaceTimeState
          (run initial index).nextContact.prefixReceipt.wholeTangent)
        (puncturedEuclideanSpaceTimeState
          (receiptViscousNegativeOneState
            (run initial index).nextContact.prefixReceipt))),
    nu.coeff *
      (∑ index ∈ interval,
        actualWholeFiniteViscousPayment
          (run initial index).nextContact.prefixReceipt
          (wholeRestartModes radius))))

/-- Inside the bounded analytic fibre, the source-generated high-frequency
failure selects a strictly increasing subsequence of the original restart
run.  On every selected `Ico`, that same run's whole-PDE receipts write a
strictly positive projected parabolic trace.  The selector has no occurrence,
branch, next-current, or root authority; those remain fixed by the separately
anchored original cofinal admission. -/
theorem
    sourceGeneratedNativeAccumulationCofinalHighFrequencyProjectedParabolicTrace
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let failure :=
      sourceGeneratedNativeAccumulationVorticityFailure
        initial elapsedBounded
    failure.rootCofinalOccurrence =
        (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence ∧
      ∃ contactIndex : Nat → Nat,
        contactIndex 0 = 0 ∧
          StrictMono contactIndex ∧
          ∀ step : Nat,
            let radius := 2 * (contactIndex step + 1)
            let interval :=
              Finset.Ico (contactIndex step) (contactIndex (step + 1))
            let trace :=
              ∑ index ∈ interval,
                receiptHighFrequencyProjectedParabolicTrace
                  (run initial index).nextContact.prefixReceipt radius
            let pairWork :=
              ∑ index ∈ interval,
                actualWholeFinitePairOccurrenceWork
                  (run initial index).nextContact.prefixReceipt
                  (wholeRestartModes radius)
            let tangentViscousCross :=
              ∑ index ∈ interval,
                2 * RCLike.re (inner ℂ
                  (puncturedEuclideanSpaceTimeState
                    (run initial index).nextContact.prefixReceipt.wholeTangent)
                  (puncturedEuclideanSpaceTimeState
                    (receiptViscousNegativeOneState
                      (run initial index).nextContact.prefixReceipt)))
            let viscousDebit :=
              ∑ index ∈ interval,
                actualWholeFiniteViscousPayment
                  (run initial index).nextContact.prefixReceipt
                  (wholeRestartModes radius)
            nu.coeff < trace ∧
              trace + nu.coeff * pairWork =
                tangentViscousCross + nu.coeff * viscousDebit ∧
              ∃ index ∈ interval,
                receiptHighFrequencyProjectedParabolicTrace
                    (run initial index).nextContact.prefixReceipt radius ≠ 0 ∧
                  ((∃ output ∈ wholeRestartModes radius,
                      ∃ first : IntegerWavevector,
                        ∃ time : Set.Icc (0 : Real)
                            (run initial index).nextContact.time.1,
                          actualWholeContinuousPairVector
                              (run initial index).nextContact.prefixReceipt
                              output first time ≠ 0 ∧
                            (wholeRestartNextPairOccurrence
                                  initial index output first ≠ 0 ∨
                              wholeRestartPairOccurrenceTrace
                                  initial index output first time ≠ 0)) ∨
                    wholeVorticityEuclideanMass
                          (run initial index).nextContact.physicalState ≠
                        wholeVorticityEuclideanMass
                          (run initial index).contact.physicalState ∨
                    ∃ wave ∈ wholeRestartModes radius,
                      0 < actualWholeRowViscousPayment
                        (run initial index).nextContact.prefixReceipt wave) := by
  dsimp only
  let failure :=
    sourceGeneratedNativeAccumulationVorticityFailure
      initial elapsedBounded
  let payload := nativeTemporalCofinalEntryStrongFaceFailure initial
    (nativeTemporalCofinalEntry initial)
  rcases payload.wholePDEEffect elapsedBounded with
    ⟨contactIndex, contactIndexZero, contactIndexStrictMono, blockEffect⟩
  refine
    ⟨failure.rootCofinalOccurrence_eq, contactIndex,
      contactIndexZero, contactIndexStrictMono, ?_⟩
  intro step
  have block := blockEffect step
  dsimp only at block ⊢
  rcases block with
    ⟨tracePositive, blockBalance, index, indexMem,
      receiptTraceNonzero, channel⟩
  refine
    ⟨tracePositive, blockBalance, index, indexMem,
      receiptTraceNonzero, ?_⟩
  rcases channel with pair | cross | viscous
  · rcases pair with ⟨output, outputMem, first, workNonzero⟩
    obtain ⟨time, pairVectorNonzero⟩ :=
      actualWholePairOccurrenceWork_ne_zero_generates_pairVector
        (run initial index).nextContact.prefixReceipt
        output first workNonzero
    refine
      Or.inl ⟨output, outputMem, first, time,
        pairVectorNonzero, ?_⟩
    exact
      actualWholeContinuousPairVector_ne_zero_next_or_trace
        initial index output first time pairVectorNonzero
  · refine Or.inr (Or.inl ?_)
    intro massEq
    apply cross
    have boundaryEq :=
      receipt_puncturedEuclidean_cross_eq_boundary
        (run initial index).nextContact.prefixReceipt
    rw [(run initial index).nextContact_prefix_terminal] at boundaryEq
    rw [boundaryEq, massEq, sub_self, mul_zero]
  · unfold actualWholeFiniteViscousPayment at viscous
    obtain ⟨wave, waveMem, rowNonzero⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero viscous
    refine Or.inr (Or.inr ⟨wave, waveMem, ?_⟩)
    exact
      lt_of_le_of_ne
        (actualWholeRowViscousPayment_nonneg
          (run initial index).nextContact.prefixReceipt wave)
        (Ne.symm rowNonzero)

/-- The tangent/viscous coordinate of every selected block is the exact
whole-vorticity boundary change of the same original NS receipts. -/
theorem nativeAccumulationCofinalBlockCrossPayment_eq
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex)
    (step : Nat) :
    (nativeAccumulationCofinalBlockPayments
        initial contactIndex step).2.1 =
      nu.coeff *
        (restartPhysicalVorticityMass
            initial (contactIndex (step + 1)) -
          restartPhysicalVorticityMass initial (contactIndex step)) := by
  unfold nativeAccumulationCofinalBlockPayments
  dsimp only
  exact
    wholeRestartIcoPuncturedEuclideanCross_telescope
      initial (contactIndex step) (contactIndex (step + 1))
      (contactIndexStrictMono (Nat.lt_succ_self step)).le

/-- Summing the source-selected moving-cutoff traces exposes the exact
annular responsibility at every intermediate contact. -/
theorem
    nativeAccumulationCofinalMovingCutoffTrace_eq_terminalTail_add_annularDebit
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex)
    (length : Nat) :
    (∑ step ∈ Finset.range (length + 1),
      ∑ index ∈ Finset.Ico (contactIndex step) (contactIndex (step + 1)),
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt
          (2 * (contactIndex step + 1))) =
      nu.coeff *
        (restartPhysicalHighFrequencyTailMass
              initial (contactIndex (length + 1))
              (2 * (contactIndex length + 1)) -
            restartPhysicalHighFrequencyTailMass
              initial (contactIndex 0) (2 * (contactIndex 0 + 1)) +
          ∑ step ∈ Finset.range length,
            (restartPhysicalHighFrequencyTailMass
                  initial (contactIndex (step + 1))
                  (2 * (contactIndex step + 1)) -
              restartPhysicalHighFrequencyTailMass
                  initial (contactIndex (step + 1))
                  (2 * (contactIndex (step + 1) + 1)))) := by
  have blockEq (step : Nat) :
      (∑ index ∈ Finset.Ico
          (contactIndex step) (contactIndex (step + 1)),
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt
          (2 * (contactIndex step + 1))) =
        nu.coeff *
          (restartPhysicalHighFrequencyTailMass
                initial (contactIndex (step + 1))
                (2 * (contactIndex step + 1)) -
            restartPhysicalHighFrequencyTailMass
                initial (contactIndex step)
                (2 * (contactIndex step + 1))) := by
    exact
      wholeRestartIcoHighFrequencyProjectedParabolicTrace_telescope
        initial (2 * (contactIndex step + 1))
        (contactIndex step) (contactIndex (step + 1))
        (contactIndexStrictMono (Nat.lt_succ_self step)).le
  simp_rw [blockEq]
  rw [← Finset.mul_sum]
  congr 1
  induction length with
  | zero =>
      simp
  | succ length inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis,
        Finset.sum_range_succ]
      ring

/-- Changing the canonical cutoff on one actual contact transfers exactly
the newly exposed finite coefficient mass out of the high-frequency tail. -/
theorem restartPhysicalHighFrequencyTailMass_sub_eq_projectedAnnularMass
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    {smaller larger : Nat}
    (radiusLe : smaller ≤ larger) :
    restartPhysicalHighFrequencyTailMass initial index smaller -
        restartPhysicalHighFrequencyTailMass initial index larger =
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes larger \ wholeRestartModes smaller)
          (run initial index).contact.physicalState := by
  have modesSubset :
      wholeRestartModes smaller ⊆ wholeRestartModes larger := by
    intro wave waveMem
    rw [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
      Finset.mem_erase] at waveMem ⊢
    refine ⟨waveMem.1, ?_⟩
    rw [integerWaveFrequencyCube, Fintype.mem_piFinset]
      at waveMem ⊢
    intro coordinate
    have coordinateMem := waveMem.2 coordinate
    rw [Finset.mem_Icc] at coordinateMem ⊢
    have radiusCastLe : (smaller : Int) ≤ larger := by
      exact_mod_cast radiusLe
    constructor <;> omega
  have smallerSplit :=
    restartPhysicalVorticityMass_eq_low_add_tail
      initial index smaller
  have largerSplit :=
    restartPhysicalVorticityMass_eq_low_add_tail
      initial index larger
  rw [← finiteStateVorticityCoefficientEnstrophy_eq_projectionMass]
    at smallerSplit largerSplit
  unfold finiteStateVorticityCoefficientEnstrophy
    at smallerSplit largerSplit ⊢
  have coefficientSplit :=
    Finset.sum_sdiff
      (f := fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState wave))
      modesSubset
  linarith

/-- The same annular responsibility stays on the source selector's next
whole-PDE block until its pair-incidence work, terminal shell mass, and
viscous payment have all been written. -/
theorem
    nativeAccumulationCofinalMovingCutoffAnnularDebit_add_nextBlockPairOccurrenceWork
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex)
    (step : Nat) :
    let start := contactIndex (step + 1)
    let finish := contactIndex (step + 2)
    let smaller := 2 * (contactIndex step + 1)
    let larger := 2 * (contactIndex (step + 1) + 1)
    let shell := wholeRestartModes larger \ wholeRestartModes smaller
    restartPhysicalHighFrequencyTailMass initial start smaller -
          restartPhysicalHighFrequencyTailMass initial start larger +
        (∑ index ∈ Finset.Ico start finish,
          actualWholeFinitePairOccurrenceWork
            (run initial index).nextContact.prefixReceipt shell) =
      finiteStateVorticityCoefficientEnstrophy shell
          (run initial finish).contact.physicalState +
        ∑ index ∈ Finset.Ico start finish,
          actualWholeFiniteViscousPayment
            (run initial index).nextContact.prefixReceipt shell := by
  dsimp only
  have radiusLe :
      2 * (contactIndex step + 1) ≤
        2 * (contactIndex (step + 1) + 1) :=
    Nat.mul_le_mul_left 2
      (Nat.add_le_add_right
        (contactIndexStrictMono (Nat.lt_succ_self step)).le 1)
  have startLeFinish :
      contactIndex (step + 1) ≤ contactIndex (step + 2) := by
    simpa only [Nat.add_assoc] using
      (contactIndexStrictMono
        (Nat.lt_succ_self (step + 1))).le
  have debitEq :=
    restartPhysicalHighFrequencyTailMass_sub_eq_projectedAnnularMass
      initial (contactIndex (step + 1)) radiusLe
  let shell :=
    wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
      wholeRestartModes (2 * (contactIndex step + 1))
  have zeroNotMem : (0 : IntegerWavevector) ∉ shell := by
    intro zeroMem
    have zeroMemLarger := (Finset.mem_sdiff.mp zeroMem).1
    have zeroNotMemLarger :
        (0 : IntegerWavevector) ∉
          wholeRestartModes (2 * (contactIndex (step + 1) + 1)) := by
      exact zero_not_mem_puncturedIntegerWaveFrequencyCube
        (2 * (contactIndex (step + 1) + 1))
    exact zeroNotMemLarger zeroMemLarger
  let shellMass : Nat → Real := fun index =>
    finiteStateVorticityCoefficientEnstrophy shell
      (run initial index).contact.physicalState
  have edgeEq (index : Nat) :
      actualWholeFinitePairOccurrenceWork
          (run initial index).nextContact.prefixReceipt shell =
        shellMass (index + 1) - shellMass index +
          actualWholeFiniteViscousPayment
            (run initial index).nextContact.prefixReceipt shell := by
    have pairEq :=
      actualWholeFinitePairOccurrenceWork_eq_terminal_sub_initial_add_viscousPayment
        (run initial index).nextContact.prefixReceipt shell zeroNotMem
    rw [(run initial index).nextContact_prefix_terminal] at pairEq
    have nextContactEq :
        (run initial index).next.contact.physicalState =
          (run initial index).nextContact.physicalState := by
      rfl
    dsimp only [shellMass] at ⊢
    rw [run_succ, nextContactEq]
    exact pairEq
  have shellMassTelescope :
      (∑ index ∈
          Finset.Ico (contactIndex (step + 1)) (contactIndex (step + 2)),
        (shellMass (index + 1) - shellMass index)) =
        shellMass (contactIndex (step + 2)) -
          shellMass (contactIndex (step + 1)) := by
    rw [Finset.sum_Ico_eq_sub _ startLeFinish,
      Finset.sum_range_sub, Finset.sum_range_sub]
    ring
  change
    restartPhysicalHighFrequencyTailMass
          initial (contactIndex (step + 1))
          (2 * (contactIndex step + 1)) -
        restartPhysicalHighFrequencyTailMass
          initial (contactIndex (step + 1))
          (2 * (contactIndex (step + 1) + 1)) +
        (∑ index ∈
          Finset.Ico (contactIndex (step + 1)) (contactIndex (step + 2)),
          actualWholeFinitePairOccurrenceWork
            (run initial index).nextContact.prefixReceipt shell) =
      shellMass (contactIndex (step + 2)) +
        ∑ index ∈
          Finset.Ico (contactIndex (step + 1)) (contactIndex (step + 2)),
          actualWholeFiniteViscousPayment
            (run initial index).nextContact.prefixReceipt shell
  rw [debitEq]
  simp_rw [edgeEq]
  rw [Finset.sum_add_distrib, shellMassTelescope]
  dsimp only [shellMass, shell]
  ring

/-- A positive moving annular responsibility cannot disappear under the
Galerkin observation.  On the identical original NS run it either exposes a
high-input pair debit, is paid directly by a viscous row, or persists to the
terminal contact and generates a positive kinetic charge on the next edge. -/
theorem
    nativeAccumulationCofinalMovingAnnularMass_generates_nativeKineticSettlement
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex)
    (step : Nat)
    (annularMassPos :
      0 < finiteStateVorticityCoefficientEnstrophy
        (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
          wholeRestartModes (2 * (contactIndex step + 1)))
        (run initial (contactIndex (step + 1))).contact.physicalState) :
    (∃ index ∈ Finset.Ico
        (contactIndex (step + 1)) (contactIndex (step + 2)),
      ∃ output : NonzeroIntegerWavevector,
        ∃ first : IntegerWavevector,
          output.1 ∈
              wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
                wholeRestartModes (2 * (contactIndex step + 1)) ∧
            actualWholePairOccurrenceWork
                (run initial index).nextContact.prefixReceipt
                output.1 first ≠ 0 ∧
            ∃ time : Set.Icc (0 : Real)
                (run initial index).nextContact.time.1,
              ∃ input : NonzeroIntegerWavevector,
                actualWholeContinuousPairVector
                    (run initial index).nextContact.prefixReceipt
                    output.1 first time ≠ 0 ∧
                  input.1 ∉ wholeRestartModes (contactIndex step + 1) ∧
                  (run initial index).nextContact.prefixReceipt.wholePath
                      time input.1 ≠ 0 ∧
                  0 < actualWholeRowKineticViscousWork
                    (run initial index).nextContact.prefixReceipt input ∧
                  actualWholeRowKineticViscousWork
                      (run initial index).nextContact.prefixReceipt input ≤
                    wholeRestartNextKineticDissipationPayment initial index) ∨
      (∃ index ∈ Finset.Ico
          (contactIndex (step + 1)) (contactIndex (step + 2)),
        ∃ wave : NonzeroIntegerWavevector,
          wave.1 ∈
              wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
                wholeRestartModes (2 * (contactIndex step + 1)) ∧
            0 < actualWholeRowKineticViscousWork
              (run initial index).nextContact.prefixReceipt wave ∧
            actualWholeRowKineticViscousWork
                (run initial index).nextContact.prefixReceipt wave ≤
              wholeRestartNextKineticDissipationPayment initial index) ∨
      ∃ actual : Set.Ioo (0 : Real)
          (run initial (contactIndex (step + 2))).nextContact.time.1,
        0 < nu.coeff * actual.1 *
            finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
                wholeRestartModes (2 * (contactIndex step + 1)))
              (run initial (contactIndex (step + 2))).contact.physicalState ∧
          nu.coeff * actual.1 *
              finiteStateVorticityCoefficientEnstrophy
                (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
                  wholeRestartModes (2 * (contactIndex step + 1)))
                (run initial (contactIndex (step + 2))).contact.physicalState ≤
            wholeRestartNextKineticDissipationPayment
              initial (contactIndex (step + 2)) := by
  let start := contactIndex (step + 1)
  let finish := contactIndex (step + 2)
  let smaller := 2 * (contactIndex step + 1)
  let larger := 2 * (contactIndex (step + 1) + 1)
  let shell := wholeRestartModes larger \ wholeRestartModes smaller
  let annularMass := finiteStateVorticityCoefficientEnstrophy shell
    (run initial start).contact.physicalState
  let terminalMass := finiteStateVorticityCoefficientEnstrophy shell
    (run initial finish).contact.physicalState
  let pairTotal := ∑ index ∈ Finset.Ico start finish,
    actualWholeFinitePairOccurrenceWork
      (run initial index).nextContact.prefixReceipt shell
  let viscousTotal := ∑ index ∈ Finset.Ico start finish,
    actualWholeFiniteViscousPayment
      (run initial index).nextContact.prefixReceipt shell
  have radiusLe : smaller ≤ larger := by
    dsimp only [smaller, larger]
    exact Nat.mul_le_mul_left 2
      (Nat.add_le_add_right
        (contactIndexStrictMono (Nat.lt_succ_self step)).le 1)
  have debitEq :=
    restartPhysicalHighFrequencyTailMass_sub_eq_projectedAnnularMass
      initial start radiusLe
  have balance :=
    nativeAccumulationCofinalMovingCutoffAnnularDebit_add_nextBlockPairOccurrenceWork
      initial contactIndex contactIndexStrictMono step
  dsimp only at balance
  change
    restartPhysicalHighFrequencyTailMass initial start smaller -
          restartPhysicalHighFrequencyTailMass initial start larger +
        pairTotal = terminalMass + viscousTotal at balance
  change
    restartPhysicalHighFrequencyTailMass initial start smaller -
        restartPhysicalHighFrequencyTailMass initial start larger =
      annularMass at debitEq
  rw [debitEq] at balance
  have annularMassPos' : 0 < annularMass := by
    simpa only [annularMass, shell, start, smaller, larger] using
      annularMassPos
  have terminalMassNonneg : 0 ≤ terminalMass := by
    unfold terminalMass finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have viscousTotalNonneg : 0 ≤ viscousTotal := by
    unfold viscousTotal
    exact Finset.sum_nonneg fun index indexMem =>
      actualWholeFiniteViscousPayment_nonneg
        (run initial index).nextContact.prefixReceipt shell
  by_cases pairTotalZero : pairTotal = 0
  · by_cases terminalMassZero : terminalMass = 0
    · have viscousTotalPos : 0 < viscousTotal := by
        linarith
      obtain ⟨index, indexMem, edgeViscousNonzero⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt viscousTotalPos)
      unfold actualWholeFiniteViscousPayment at edgeViscousNonzero
      obtain ⟨wave, waveMem, rowPaymentNonzero⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero edgeViscousNonzero
      have waveNonzero : wave ≠ 0 := by
        intro waveZero
        subst wave
        exact
          (zero_not_mem_wholeRestartModes larger)
            (Finset.mem_sdiff.mp waveMem).1
      let nonzeroWave : NonzeroIntegerWavevector := ⟨wave, waveNonzero⟩
      have rowPaymentPos :
          0 < actualWholeRowViscousPayment
            (run initial index).nextContact.prefixReceipt wave :=
        lt_of_le_of_ne
          (actualWholeRowViscousPayment_nonneg
            (run initial index).nextContact.prefixReceipt wave)
          (Ne.symm rowPaymentNonzero)
      have rowKineticPos :
          0 < actualWholeRowKineticViscousWork
            (run initial index).nextContact.prefixReceipt nonzeroWave := by
        unfold actualWholeRowKineticViscousWork
        exact div_pos rowPaymentPos
          (integerWaveViscousMultiplier_pos nonzeroWave)
      exact Or.inr (Or.inl
        ⟨index, indexMem, nonzeroWave, waveMem, rowKineticPos,
          actualEdgeRowKineticViscousWork_le_nextPayment
            initial index nonzeroWave⟩)
    · have terminalMassPos : 0 < terminalMass :=
        lt_of_le_of_ne terminalMassNonneg (Ne.symm terminalMassZero)
      obtain ⟨actual, chargePos, chargeLe, _massPersists⟩ :=
        wholeRestartActualWholeFiniteAmplitudeSq_generates_aggregateKineticPersistenceCharge
          initial finish shell terminalMassPos
      exact Or.inr (Or.inr ⟨actual, chargePos, chargeLe⟩)
  · obtain ⟨index, indexMem, edgePairNonzero⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero pairTotalZero
    unfold actualWholeFinitePairOccurrenceWork at edgePairNonzero
    obtain ⟨output, outputMem, outputPairNonzero⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero edgePairNonzero
    have existsFirst :
        ∃ first : IntegerWavevector,
          actualWholePairOccurrenceWork
            (run initial index).nextContact.prefixReceipt output first ≠ 0 := by
      by_contra noFirst
      push Not at noFirst
      apply outputPairNonzero
      simp only [noFirst, tsum_zero]
    obtain ⟨first, workNonzero⟩ := existsFirst
    have outputNonzero : output ≠ 0 := by
      intro outputZero
      subst output
      exact
        (zero_not_mem_wholeRestartModes larger)
          (Finset.mem_sdiff.mp outputMem).1
    let nonzeroOutput : NonzeroIntegerWavevector :=
      ⟨output, outputNonzero⟩
    have outputOutside :
        nonzeroOutput.1 ∉ wholeRestartModes (2 * (contactIndex step + 1)) := by
      simpa only [nonzeroOutput, smaller] using
        (Finset.mem_sdiff.mp outputMem).2
    obtain ⟨time, input, pairVectorNonzero, inputOutside,
        inputRowNonzero, rowKineticPos, rowKineticLe⟩ :=
      wholeRestartPairWork_outsideDoubledRadius_generates_highInputKineticDebit
        initial index (contactIndex step + 1) nonzeroOutput first
        outputOutside workNonzero
    exact Or.inl
      ⟨index, indexMem, nonzeroOutput, first, outputMem, workNonzero,
        time, input, pairVectorNonzero, inputOutside, inputRowNonzero,
        rowKineticPos, rowKineticLe⟩

/-- The same moving annular balance retains its quantitative responsibility.
At least one third of the initial annular mass is carried by the signed pair
work, by terminal shell mass whose persistence is charged on the next edge,
or by the literal block viscous debit.  The viscous branch is normalized only
by the exact Fourier multiplier of the source-selected outer cube and is paid
by the existing kinetic ledger on the identical block. -/
theorem
    nativeAccumulationCofinalMovingAnnularMass_quantitativeSettlement
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex)
    (step : Nat) :
    let start := contactIndex (step + 1)
    let finish := contactIndex (step + 2)
    let smaller := 2 * (contactIndex step + 1)
    let larger := 2 * (contactIndex (step + 1) + 1)
    let shell := wholeRestartModes larger \ wholeRestartModes smaller
    let annularMass := finiteStateVorticityCoefficientEnstrophy shell
      (run initial start).contact.physicalState
    let terminalMass := finiteStateVorticityCoefficientEnstrophy shell
      (run initial finish).contact.physicalState
    let pairTotal := ∑ index ∈ Finset.Ico start finish,
      actualWholeFinitePairOccurrenceWork
        (run initial index).nextContact.prefixReceipt shell
    let viscousTotal := ∑ index ∈ Finset.Ico start finish,
      actualWholeFiniteViscousPayment
        (run initial index).nextContact.prefixReceipt shell
    annularMass / 3 ≤ |pairTotal| ∨
      (annularMass / 3 ≤ terminalMass ∧
        ∃ actual : Set.Ioo (0 : Real)
            (run initial finish).nextContact.time.1,
          0 < nu.coeff * actual.1 * terminalMass ∧
            nu.coeff * actual.1 * (annularMass / 3) ≤
              nu.coeff * actual.1 * terminalMass ∧
            nu.coeff * actual.1 * terminalMass ≤
              wholeRestartNextKineticDissipationPayment initial finish) ∨
      (annularMass / 3 ≤ viscousTotal ∧
        viscousTotal /
              ((2 * Real.pi) ^ 2 * (3 * (larger : Real) ^ 2)) ≤
          ∑ index ∈ Finset.Ico start finish,
            wholeRestartNextKineticDissipationPayment initial index) := by
  dsimp only
  let start := contactIndex (step + 1)
  let finish := contactIndex (step + 2)
  let smaller := 2 * (contactIndex step + 1)
  let larger := 2 * (contactIndex (step + 1) + 1)
  let shell := wholeRestartModes larger \ wholeRestartModes smaller
  let annularMass := finiteStateVorticityCoefficientEnstrophy shell
    (run initial start).contact.physicalState
  let terminalMass := finiteStateVorticityCoefficientEnstrophy shell
    (run initial finish).contact.physicalState
  let pairTotal := ∑ index ∈ Finset.Ico start finish,
    actualWholeFinitePairOccurrenceWork
      (run initial index).nextContact.prefixReceipt shell
  let viscousTotal := ∑ index ∈ Finset.Ico start finish,
    actualWholeFiniteViscousPayment
      (run initial index).nextContact.prefixReceipt shell
  have balance :=
    nativeAccumulationCofinalMovingCutoffAnnularDebit_add_nextBlockPairOccurrenceWork
      initial contactIndex contactIndexStrictMono step
  dsimp only at balance
  have radiusLe : smaller ≤ larger := by
    dsimp only [smaller, larger]
    exact Nat.mul_le_mul_left 2
      (Nat.add_le_add_right
        (contactIndexStrictMono (Nat.lt_succ_self step)).le 1)
  have debitEq :=
    restartPhysicalHighFrequencyTailMass_sub_eq_projectedAnnularMass
      initial start radiusLe
  change
    restartPhysicalHighFrequencyTailMass initial start smaller -
        restartPhysicalHighFrequencyTailMass initial start larger =
      annularMass at debitEq
  rw [debitEq] at balance
  change annularMass + pairTotal = terminalMass + viscousTotal at balance
  have annularMassNonneg : 0 ≤ annularMass := by
    unfold annularMass finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have terminalMassNonneg : 0 ≤ terminalMass := by
    unfold terminalMass finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have viscousTotalNonneg : 0 ≤ viscousTotal := by
    unfold viscousTotal
    exact Finset.sum_nonneg fun index indexMem =>
      actualWholeFiniteViscousPayment_nonneg
        (run initial index).nextContact.prefixReceipt shell
  have responsibilityLe :
      annularMass ≤ |pairTotal| + terminalMass + viscousTotal := by
    have pairNegLe : -pairTotal ≤ |pairTotal| := neg_le_abs pairTotal
    linarith
  by_cases pairPays : annularMass / 3 ≤ |pairTotal|
  · exact Or.inl pairPays
  · have pairSmall : |pairTotal| < annularMass / 3 :=
      lt_of_not_ge pairPays
    by_cases terminalPays : annularMass / 3 ≤ terminalMass
    · right
      left
      have terminalMassPos : 0 < terminalMass := by
        have : 0 < annularMass / 3 := by
          have annularMassPos : 0 < annularMass := by
            by_contra annularMassNotPos
            have annularMassZero : annularMass = 0 := by
              exact le_antisymm (le_of_not_gt annularMassNotPos)
                annularMassNonneg
            rw [annularMassZero] at pairSmall
            nlinarith [abs_nonneg pairTotal]
          positivity
        exact this.trans_le terminalPays
      obtain ⟨actual, chargePos, chargeLe, _massPersists⟩ :=
        wholeRestartActualWholeFiniteAmplitudeSq_generates_aggregateKineticPersistenceCharge
          initial finish shell terminalMassPos
      refine ⟨terminalPays, actual, chargePos, ?_, chargeLe⟩
      have coefficientTimeNonneg : 0 ≤ nu.coeff * actual.1 :=
        mul_nonneg nu.coeff_pos.le actual.2.1.le
      exact mul_le_mul_of_nonneg_left terminalPays coefficientTimeNonneg
    · right
      right
      have terminalSmall : terminalMass < annularMass / 3 :=
        lt_of_not_ge terminalPays
      have viscousPays : annularMass / 3 ≤ viscousTotal := by
        nlinarith
      refine ⟨viscousPays, ?_⟩
      have largerPos : 0 < larger := by
        dsimp only [larger]
        omega
      have shellSub : shell ⊆ wholeRestartModes larger := by
        exact Finset.sdiff_subset
      calc
        viscousTotal /
              ((2 * Real.pi) ^ 2 * (3 * (larger : Real) ^ 2)) =
            ∑ index ∈ Finset.Ico start finish,
              actualWholeFiniteViscousPayment
                  (run initial index).nextContact.prefixReceipt shell /
                ((2 * Real.pi) ^ 2 * (3 * (larger : Real) ^ 2)) := by
          unfold viscousTotal
          rw [Finset.sum_div]
        _ ≤ ∑ index ∈ Finset.Ico start finish,
              wholeRestartNextKineticDissipationPayment initial index := by
          apply Finset.sum_le_sum
          intro index indexMem
          exact selected_shellViscousPayment_div_radiusSq_le_nextPayment
            initial index larger largerPos shell shellSub

/-- Consecutive source-selected blocks cannot spend the same kinetic edge
twice.  Their complete block payments therefore remain summable under the
original whole-restart kinetic ledger. -/
theorem summable_nativeAccumulationCofinalMovingBlockKineticPayment
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex) :
    Summable fun step =>
      ∑ index ∈ Finset.Ico
          (contactIndex (step + 1)) (contactIndex (step + 2)),
        wholeRestartNextKineticDissipationPayment initial index := by
  let payment : Nat → Real :=
    wholeRestartNextKineticDissipationPayment initial
  let block : Nat → Real := fun step =>
    ∑ index ∈ Finset.Ico
        (contactIndex (step + 1)) (contactIndex (step + 2)),
      payment index
  have paymentSummable : Summable payment := by
    exact summable_wholeRestartNextKineticDissipationPayment initial
  have paymentNonneg : ∀ index, 0 ≤ payment index := by
    intro index
    exact wholeRestartNextKineticDissipationPayment_nonneg initial index
  have initialLe (length : Nat) :
      contactIndex 1 ≤ contactIndex (length + 1) := by
    exact contactIndexStrictMono.monotone (Nat.add_le_add_right (Nat.zero_le length) 1)
  have stepLe (length : Nat) :
      contactIndex (length + 1) ≤ contactIndex (length + 2) := by
    exact (contactIndexStrictMono (Nat.lt_succ_self (length + 1))).le
  have partialEq : ∀ length : Nat,
      (∑ step ∈ Finset.range length, block step) =
        ∑ index ∈ Finset.Ico
          (contactIndex 1) (contactIndex (length + 1)),
          payment index := by
    intro length
    induction length with
    | zero => simp [block]
    | succ length inductionHypothesis =>
        rw [Finset.sum_range_succ, inductionHypothesis]
        exact Finset.sum_Ico_consecutive payment
          (initialLe length) (stepLe length)
  change Summable block
  apply summable_of_sum_range_le
  · intro step
    unfold block
    exact Finset.sum_nonneg fun index indexMem => paymentNonneg index
  · intro length
    rw [partialEq length]
    exact paymentSummable.sum_le_tsum
      (Finset.Ico (contactIndex 1) (contactIndex (length + 1)))
      (fun index indexNotMem => paymentNonneg index)

/-- The cube-normalized viscous part of every moving annular block is an
unconditional summable payment.  This is the quantitative no-double-spend
consumer for the viscous branch above. -/
theorem summable_nativeAccumulationCofinalMovingNormalizedViscousBlock
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex) :
    Summable fun step =>
      let start := contactIndex (step + 1)
      let finish := contactIndex (step + 2)
      let smaller := 2 * (contactIndex step + 1)
      let larger := 2 * (contactIndex (step + 1) + 1)
      let shell := wholeRestartModes larger \ wholeRestartModes smaller
      (∑ index ∈ Finset.Ico start finish,
          actualWholeFiniteViscousPayment
            (run initial index).nextContact.prefixReceipt shell) /
        ((2 * Real.pi) ^ 2 * (3 * (larger : Real) ^ 2)) := by
  let normalized : Nat → Real := fun step =>
    let start := contactIndex (step + 1)
    let finish := contactIndex (step + 2)
    let smaller := 2 * (contactIndex step + 1)
    let larger := 2 * (contactIndex (step + 1) + 1)
    let shell := wholeRestartModes larger \ wholeRestartModes smaller
    (∑ index ∈ Finset.Ico start finish,
        actualWholeFiniteViscousPayment
          (run initial index).nextContact.prefixReceipt shell) /
      ((2 * Real.pi) ^ 2 * (3 * (larger : Real) ^ 2))
  change Summable normalized
  apply
    (summable_nativeAccumulationCofinalMovingBlockKineticPayment
      initial contactIndex contactIndexStrictMono).of_nonneg_of_le
  · intro step
    unfold normalized
    dsimp only
    exact div_nonneg
      (Finset.sum_nonneg fun index indexMem =>
        actualWholeFiniteViscousPayment_nonneg
          (run initial index).nextContact.prefixReceipt _)
      (by positivity)
  · intro step
    unfold normalized
    dsimp only
    let larger := 2 * (contactIndex (step + 1) + 1)
    let shell := wholeRestartModes larger \
      wholeRestartModes (2 * (contactIndex step + 1))
    have largerPos : 0 < larger := by
      dsimp only [larger]
      omega
    have shellSub : shell ⊆ wholeRestartModes larger :=
      Finset.sdiff_subset
    change
      (∑ index ∈ Finset.Ico
          (contactIndex (step + 1)) (contactIndex (step + 2)),
        actualWholeFiniteViscousPayment
          (run initial index).nextContact.prefixReceipt shell) /
          ((2 * Real.pi) ^ 2 * (3 * (larger : Real) ^ 2)) ≤
        ∑ index ∈ Finset.Ico
          (contactIndex (step + 1)) (contactIndex (step + 2)),
          wholeRestartNextKineticDissipationPayment initial index
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro index indexMem
    exact selected_shellViscousPayment_div_radiusSq_le_nextPayment
      initial index larger largerPos shell shellSub

private theorem actualWholeFiniteKineticNetWork_eq_contact_sub
    (initial : GeneratedWholeRestartCurrent nu)
    (outputs : Finset NonzeroIntegerWavevector)
    (index : Nat) :
    actualWholeFiniteKineticNetWork
        (run initial index).nextContact.prefixReceipt outputs =
      ‖actualWholeFiniteVelocityObservation outputs
          (run initial (index + 1)).contact.physicalState‖ ^ 2 -
        ‖actualWholeFiniteVelocityObservation outputs
          (run initial index).contact.physicalState‖ ^ 2 := by
  rw [actualWholeFiniteKineticNetWork_eq_velocityObservation_norm_sq_sub,
    (run initial index).nextContact_prefix_terminal, run_succ]
  rfl

/-- Any moving finite shell selected from the original whole-restart run has
one exact kinetic incidence ledger on its literal `Ico`.  Its nonlinear work
is precisely the two endpoint shell inventories plus the same receipts'
viscous work; no macro continuation or independently selected occurrence is
used. -/
theorem actualMovingShellFiniteKineticWork_eq_endpointMassSub_add_viscous
    (initial : GeneratedWholeRestartCurrent nu)
    (outputs : Nat → Finset NonzeroIntegerWavevector)
    (start finish : Nat → Nat)
    (start_le_finish : ∀ step, start step ≤ finish step)
    (step : Nat) :
    (∑ index ∈ Finset.Ico (start step) (finish step),
        actualWholeFiniteBilinearKineticWork
          (run initial index).nextContact.prefixReceipt (outputs step)) =
      (‖actualWholeFiniteVelocityObservation (outputs step)
          (run initial (finish step)).contact.physicalState‖ ^ 2 -
        ‖actualWholeFiniteVelocityObservation (outputs step)
          (run initial (start step)).contact.physicalState‖ ^ 2) +
        ∑ index ∈ Finset.Ico (start step) (finish step),
          actualWholeFiniteKineticViscousWork
            (run initial index).nextContact.prefixReceipt (outputs step) := by
  have blockBalance :
      (∑ index ∈ Finset.Ico (start step) (finish step),
          actualWholeFiniteKineticNetWork
            (run initial index).nextContact.prefixReceipt (outputs step)) +
        (∑ index ∈ Finset.Ico (start step) (finish step),
          actualWholeFiniteKineticViscousWork
            (run initial index).nextContact.prefixReceipt (outputs step)) =
          ∑ index ∈ Finset.Ico (start step) (finish step),
            actualWholeFiniteBilinearKineticWork
              (run initial index).nextContact.prefixReceipt
                (outputs step) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _
    exact actualWholeFiniteKineticNetWork_add_viscousWork
      (run initial index).nextContact.prefixReceipt (outputs step)
  have netTelescope :
      (∑ index ∈ Finset.Ico (start step) (finish step),
          actualWholeFiniteKineticNetWork
            (run initial index).nextContact.prefixReceipt (outputs step)) =
        ‖actualWholeFiniteVelocityObservation (outputs step)
            (run initial (finish step)).contact.physicalState‖ ^ 2 -
          ‖actualWholeFiniteVelocityObservation (outputs step)
            (run initial (start step)).contact.physicalState‖ ^ 2 := by
    simp_rw [actualWholeFiniteKineticNetWork_eq_contact_sub]
    rw [Finset.sum_Ico_eq_sub _ (start_le_finish step)]
    have finishTelescope := Finset.sum_range_sub
      (fun index : Nat =>
        ‖actualWholeFiniteVelocityObservation (outputs step)
          (run initial index).contact.physicalState‖ ^ 2)
      (finish step)
    have startTelescope := Finset.sum_range_sub
      (fun index : Nat =>
        ‖actualWholeFiniteVelocityObservation (outputs step)
          (run initial index).contact.physicalState‖ ^ 2)
      (start step)
    rw [finishTelescope, startTelescope]
    ring
  calc
    _ = (∑ index ∈ Finset.Ico (start step) (finish step),
          actualWholeFiniteKineticNetWork
            (run initial index).nextContact.prefixReceipt (outputs step)) +
        (∑ index ∈ Finset.Ico (start step) (finish step),
          actualWholeFiniteKineticViscousWork
            (run initial index).nextContact.prefixReceipt (outputs step)) :=
      blockBalance.symm
    _ = _ := by rw [netTelescope]

private theorem nativeAccumulation_integerWaveNormSq_le_cubeWeight
    (radius : Nat)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ wholeRestartModes radius) :
    integerWaveNormSq wave ≤ 3 * (radius : Real) ^ 2 := by
  have cubeMem : wave ∈ integerWaveFrequencyCube radius :=
    (Finset.mem_erase.mp waveMem).2
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at cubeMem
  have h0 := cubeMem (0 : Fin 3)
  have h1 := cubeMem (1 : Fin 3)
  have h2 := cubeMem (2 : Fin 3)
  rw [Finset.mem_Icc] at h0 h1 h2
  have h0r :
      -((radius : Nat) : Real) ≤ (wave (0 : Fin 3) : Real) ∧
        (wave (0 : Fin 3) : Real) ≤ radius := by
    exact_mod_cast h0
  have h1r :
      -((radius : Nat) : Real) ≤ (wave (1 : Fin 3) : Real) ∧
        (wave (1 : Fin 3) : Real) ≤ radius := by
    exact_mod_cast h1
  have h2r :
      -((radius : Nat) : Real) ≤ (wave (2 : Fin 3) : Real) ∧
        (wave (2 : Fin 3) : Real) ≤ radius := by
    exact_mod_cast h2
  have h0sq : (wave (0 : Fin 3) : Real) ^ 2 ≤ (radius : Real) ^ 2 := by
    nlinarith
  have h1sq : (wave (1 : Fin 3) : Real) ^ 2 ≤ (radius : Real) ^ 2 := by
    nlinarith
  have h2sq : (wave (2 : Fin 3) : Real) ^ 2 ≤ (radius : Real) ^ 2 := by
    nlinarith
  rw [integerWaveNormSq]
  norm_num [Fin.sum_univ_succ]
  linarith

/-- A finite coefficient inventory inside one canonical cube is paid by the
same modes' inverse-Laplacian kinetic inventory.  Keeping the literal modes
is essential: disjoint source-selected shells may then share one whole
kinetic ledger without being charged twice. -/
theorem finiteEnstrophy_div_cubeWeight_le_weightedInventory
    (radius : Nat)
    (radiusPos : 0 < radius)
    (modes : Finset IntegerWavevector)
    (modesSub : modes ⊆ wholeRestartModes radius)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy modes state /
        ((2 * Real.pi) ^ 2 * (3 * (radius : Real) ^ 2)) ≤
      ∑ wave ∈ modes,
        complexCoordinateAmplitudeSq (state wave) /
          integerWaveViscousMultiplier wave := by
  let cubeWeight : Real :=
    (2 * Real.pi) ^ 2 * (3 * (radius : Real) ^ 2)
  have cubeWeightPos : 0 < cubeWeight := by
    dsimp only [cubeWeight]
    positivity
  calc
    finiteStateVorticityCoefficientEnstrophy modes state / cubeWeight =
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (state wave) / cubeWeight := by
      unfold finiteStateVorticityCoefficientEnstrophy
      rw [Finset.sum_div]
    _ ≤ ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (state wave) /
            integerWaveViscousMultiplier wave := by
      apply Finset.sum_le_sum
      intro wave waveMem
      have wholeMem := modesSub waveMem
      have waveNe : wave ≠ 0 := fun waveZero => by
        subst wave
        exact (zero_not_mem_wholeRestartModes radius) wholeMem
      have multiplierPos : 0 < integerWaveViscousMultiplier wave :=
        integerWaveViscousMultiplier_pos ⟨wave, waveNe⟩
      have multiplierLe :
          integerWaveViscousMultiplier wave ≤ cubeWeight := by
        dsimp only [cubeWeight]
        unfold integerWaveViscousMultiplier
        exact mul_le_mul_of_nonneg_left
          (nativeAccumulation_integerWaveNormSq_le_cubeWeight
            radius wave wholeMem)
          (sq_nonneg _)
      exact (div_le_div_iff₀ cubeWeightPos multiplierPos).2
        (mul_le_mul_of_nonneg_left multiplierLe
          (complexCoordinateAmplitudeSq_nonneg _))

/-- On one exact whole-PDE receipt, the normalized signed pair magnitude is
carried by the identical modes at its two endpoints and its literal viscous
debit.  No whole-carrier enlargement occurs in this connector. -/
theorem
    actualWholeFinitePairOccurrenceWork_abs_div_cubeWeight_le_weightedEndpoints
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat)
    (radiusPos : 0 < radius)
    (modes : Finset IntegerWavevector)
    (modesSub : modes ⊆ wholeRestartModes radius) :
    |actualWholeFinitePairOccurrenceWork receipt modes| /
        ((2 * Real.pi) ^ 2 * (3 * (radius : Real) ^ 2)) ≤
      (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
            ((receipt.wholePath
              ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) wave) /
          integerWaveViscousMultiplier wave) +
        (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (initialState wave) /
            integerWaveViscousMultiplier wave) +
        actualWholeFiniteViscousPayment receipt modes /
          ((2 * Real.pi) ^ 2 * (3 * (radius : Real) ^ 2)) := by
  let terminalState := receipt.wholePath
    ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
  let cubeWeight : Real :=
    (2 * Real.pi) ^ 2 * (3 * (radius : Real) ^ 2)
  have cubeWeightPos : 0 < cubeWeight := by
    dsimp only [cubeWeight]
    positivity
  have zeroNotMem : (0 : IntegerWavevector) ∉ modes := by
    intro zeroMem
    exact (zero_not_mem_wholeRestartModes radius) (modesSub zeroMem)
  have balance :=
    actualWholeFinitePairOccurrenceWork_eq_terminal_sub_initial_add_viscousPayment
      receipt modes zeroNotMem
  change
    actualWholeFinitePairOccurrenceWork receipt modes =
      finiteStateVorticityCoefficientEnstrophy modes terminalState -
        finiteStateVorticityCoefficientEnstrophy modes initialState +
        actualWholeFiniteViscousPayment receipt modes at balance
  have terminalNonneg :
      0 ≤ finiteStateVorticityCoefficientEnstrophy modes terminalState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have initialNonneg :
      0 ≤ finiteStateVorticityCoefficientEnstrophy modes
        initialState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have viscousNonneg :
      0 ≤ actualWholeFiniteViscousPayment receipt modes :=
    actualWholeFiniteViscousPayment_nonneg receipt modes
  have magnitudeBound :
      |actualWholeFinitePairOccurrenceWork receipt modes| ≤
        finiteStateVorticityCoefficientEnstrophy modes terminalState +
          finiteStateVorticityCoefficientEnstrophy modes
            initialState +
          actualWholeFiniteViscousPayment receipt modes := by
    rw [balance, abs_le]
    constructor <;> linarith
  have normalizedMagnitude :=
    (div_le_div_iff_of_pos_right cubeWeightPos).2 magnitudeBound
  have terminalKinetic :=
    finiteEnstrophy_div_cubeWeight_le_weightedInventory
      radius radiusPos modes modesSub terminalState
  have initialKinetic :=
    finiteEnstrophy_div_cubeWeight_le_weightedInventory
      radius radiusPos modes modesSub
        initialState
  change
    |actualWholeFinitePairOccurrenceWork receipt modes| / cubeWeight ≤ _
  calc
    |actualWholeFinitePairOccurrenceWork receipt modes| / cubeWeight ≤
        (finiteStateVorticityCoefficientEnstrophy modes terminalState +
            finiteStateVorticityCoefficientEnstrophy modes
              initialState +
            actualWholeFiniteViscousPayment receipt modes) / cubeWeight :=
      normalizedMagnitude
    _ = finiteStateVorticityCoefficientEnstrophy modes terminalState /
          cubeWeight +
        finiteStateVorticityCoefficientEnstrophy modes
            initialState / cubeWeight +
        actualWholeFiniteViscousPayment receipt modes / cubeWeight := by ring
    _ ≤ _ := by linarith

/-- Specializing the same connector to an actual restart edge preserves both
selected endpoint inventories; only the literal viscous coordinate is
discharged into the source-owned successor kinetic ledger. -/
theorem
    nextReceiptFinitePairOccurrenceWork_abs_div_cubeWeight_le_weightedEndpoints
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    (radiusPos : 0 < radius)
    (modes : Finset IntegerWavevector)
    (modesSub : modes ⊆ wholeRestartModes radius) :
    |actualWholeFinitePairOccurrenceWork
          (run initial index).nextContact.prefixReceipt modes| /
        ((2 * Real.pi) ^ 2 * (3 * (radius : Real) ^ 2)) ≤
      (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
            ((run initial index).nextContact.physicalState wave) /
          integerWaveViscousMultiplier wave) +
        (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
              ((run initial index).contact.physicalState wave) /
            integerWaveViscousMultiplier wave) +
        wholeRestartNextKineticDissipationPayment initial index := by
  have connector :=
    actualWholeFinitePairOccurrenceWork_abs_div_cubeWeight_le_weightedEndpoints
      (run initial index).nextContact.prefixReceipt
      radius radiusPos modes modesSub
  rw [(run initial index).nextContact_prefix_terminal] at connector
  have viscousLe :=
    selected_shellViscousPayment_div_radiusSq_le_nextPayment
      initial index radius radiusPos modes modesSub
  exact connector.trans (by linarith)

/-- The source-selected moving block retains the sharper receipt connector
after its actual edge telescope.  Its normalized signed pair work is carried
by the same annulus at the two literal contact endpoints plus the block's
normalized viscous debit. -/
theorem
    nativeAccumulationCofinalMovingPairTotal_abs_div_cubeWeight_le_weightedEndpoints
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex)
    (step : Nat) :
    let start := contactIndex (step + 1)
    let finish := contactIndex (step + 2)
    let smaller := 2 * (contactIndex step + 1)
    let larger := 2 * (contactIndex (step + 1) + 1)
    let shell := wholeRestartModes larger \ wholeRestartModes smaller
    let pairTotal := ∑ index ∈ Finset.Ico start finish,
      actualWholeFinitePairOccurrenceWork
        (run initial index).nextContact.prefixReceipt shell
    let viscousTotal := ∑ index ∈ Finset.Ico start finish,
      actualWholeFiniteViscousPayment
        (run initial index).nextContact.prefixReceipt shell
    |pairTotal| /
          ((2 * Real.pi) ^ 2 * (3 * (larger : Real) ^ 2)) ≤
      (∑ wave ∈ shell,
        complexCoordinateAmplitudeSq
            ((run initial finish).contact.physicalState wave) /
          integerWaveViscousMultiplier wave) +
        (∑ wave ∈ shell,
          complexCoordinateAmplitudeSq
              ((run initial start).contact.physicalState wave) /
            integerWaveViscousMultiplier wave) +
        viscousTotal /
          ((2 * Real.pi) ^ 2 * (3 * (larger : Real) ^ 2)) := by
  dsimp only
  let start := contactIndex (step + 1)
  let finish := contactIndex (step + 2)
  let smaller := 2 * (contactIndex step + 1)
  let larger := 2 * (contactIndex (step + 1) + 1)
  let shell := wholeRestartModes larger \ wholeRestartModes smaller
  let annularMass := finiteStateVorticityCoefficientEnstrophy shell
    (run initial start).contact.physicalState
  let terminalMass := finiteStateVorticityCoefficientEnstrophy shell
    (run initial finish).contact.physicalState
  let pairTotal := ∑ index ∈ Finset.Ico start finish,
    actualWholeFinitePairOccurrenceWork
      (run initial index).nextContact.prefixReceipt shell
  let viscousTotal := ∑ index ∈ Finset.Ico start finish,
    actualWholeFiniteViscousPayment
      (run initial index).nextContact.prefixReceipt shell
  let cubeWeight : Real :=
    (2 * Real.pi) ^ 2 * (3 * (larger : Real) ^ 2)
  have largerPos : 0 < larger := by
    dsimp only [larger]
    omega
  have cubeWeightPos : 0 < cubeWeight := by
    dsimp only [cubeWeight]
    positivity
  have shellSub : shell ⊆ wholeRestartModes larger :=
    Finset.sdiff_subset
  have radiusLe : smaller ≤ larger := by
    dsimp only [smaller, larger]
    exact Nat.mul_le_mul_left 2
      (Nat.add_le_add_right
        (contactIndexStrictMono (Nat.lt_succ_self step)).le 1)
  have debitEq :=
    restartPhysicalHighFrequencyTailMass_sub_eq_projectedAnnularMass
      initial start radiusLe
  change
    restartPhysicalHighFrequencyTailMass initial start smaller -
        restartPhysicalHighFrequencyTailMass initial start larger =
      annularMass at debitEq
  have balance :=
    nativeAccumulationCofinalMovingCutoffAnnularDebit_add_nextBlockPairOccurrenceWork
      initial contactIndex contactIndexStrictMono step
  dsimp only at balance
  rw [debitEq] at balance
  change annularMass + pairTotal = terminalMass + viscousTotal at balance
  have annularNonneg : 0 ≤ annularMass := by
    unfold annularMass finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have terminalNonneg : 0 ≤ terminalMass := by
    unfold terminalMass finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have viscousNonneg : 0 ≤ viscousTotal := by
    unfold viscousTotal
    exact Finset.sum_nonneg fun index indexMem =>
      actualWholeFiniteViscousPayment_nonneg
        (run initial index).nextContact.prefixReceipt shell
  have magnitudeBound :
      |pairTotal| ≤ terminalMass + annularMass + viscousTotal := by
    rw [abs_le]
    constructor <;> linarith
  have normalizedMagnitude :=
    (div_le_div_iff_of_pos_right cubeWeightPos).2 magnitudeBound
  have terminalKinetic :=
    finiteEnstrophy_div_cubeWeight_le_weightedInventory
      larger largerPos shell shellSub
        (run initial finish).contact.physicalState
  have annularKinetic :=
    finiteEnstrophy_div_cubeWeight_le_weightedInventory
      larger largerPos shell shellSub
        (run initial start).contact.physicalState
  change
    |pairTotal| / cubeWeight ≤
      (∑ wave ∈ shell,
        complexCoordinateAmplitudeSq
            ((run initial finish).contact.physicalState wave) /
          integerWaveViscousMultiplier wave) +
        (∑ wave ∈ shell,
          complexCoordinateAmplitudeSq
              ((run initial start).contact.physicalState wave) /
            integerWaveViscousMultiplier wave) +
        viscousTotal / cubeWeight
  calc
    |pairTotal| / cubeWeight ≤
        (terminalMass + annularMass + viscousTotal) / cubeWeight :=
      normalizedMagnitude
    _ = terminalMass / cubeWeight + annularMass / cubeWeight +
        viscousTotal / cubeWeight := by ring
    _ ≤ _ := by linarith

/-- On the next source-selected block, the previous cutoff's projected
parabolic trace is exactly the terminal annular mass plus the change of the
moving terminal tail.  This keeps both terminal coordinates on the same
actual receipts rather than treating either as a boundary disposition. -/
theorem nativeAccumulationCofinalAdjacentTerminalTrace_eq
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex)
    (step : Nat) :
    let radius : Nat → Nat := fun offset =>
      2 * (contactIndex offset + 1)
    let terminalTail : Nat → Real := fun offset =>
      restartPhysicalHighFrequencyTailMass
        initial (contactIndex (offset + 1)) (radius offset)
    let terminalMass :=
      finiteStateVorticityCoefficientEnstrophy
        (wholeRestartModes (radius (step + 1)) \
          wholeRestartModes (radius step))
        (run initial (contactIndex (step + 2))).contact.physicalState
    let shiftedTrace :=
      ∑ index ∈ Finset.Ico
          (contactIndex (step + 1)) (contactIndex (step + 2)),
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt (radius step)
    shiftedTrace =
      nu.coeff *
        (terminalMass + terminalTail (step + 1) - terminalTail step) := by
  dsimp only
  have radiusLe :
      2 * (contactIndex step + 1) ≤
        2 * (contactIndex (step + 1) + 1) :=
    Nat.mul_le_mul_left 2
      (Nat.add_le_add_right
        (contactIndexStrictMono (Nat.lt_succ_self step)).le 1)
  have shellEq :=
    restartPhysicalHighFrequencyTailMass_sub_eq_projectedAnnularMass
      initial (contactIndex (step + 2)) radiusLe
  have traceEq :=
    wholeRestartIcoHighFrequencyProjectedParabolicTrace_telescope
      initial (2 * (contactIndex step + 1))
      (contactIndex (step + 1)) (contactIndex (step + 2))
      (contactIndexStrictMono (Nat.lt_succ_self (step + 1))).le
  rw [traceEq]
  apply congrArg (fun value : Real => nu.coeff * value)
  norm_num [Nat.add_assoc] at ⊢
  linarith

/-- An unbounded moving terminal tail or a nonsummable terminal annular mass
cannot disappear between adjacent native blocks.  Their exact telescope
forces the previous cutoff's actual projected traces to be non-absolutely
summable. -/
theorem
    nativeAccumulationCofinalTerminalExhaustion_forces_adjacentTrace_not_summable
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex) :
    let radius : Nat → Nat := fun step =>
      2 * (contactIndex step + 1)
    let terminalTail : Nat → Real := fun step =>
      restartPhysicalHighFrequencyTailMass
        initial (contactIndex (step + 1)) (radius step)
    let terminalMass : Nat → Real := fun step =>
      finiteStateVorticityCoefficientEnstrophy
        (wholeRestartModes (radius (step + 1)) \
          wholeRestartModes (radius step))
        (run initial (contactIndex (step + 2))).contact.physicalState
    let shiftedTrace : Nat → Real := fun step =>
      ∑ index ∈ Finset.Ico
          (contactIndex (step + 1)) (contactIndex (step + 2)),
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt (radius step)
    (¬ BddAbove (Set.range terminalTail) ∨ ¬ Summable terminalMass) →
      ¬ Summable (fun step => |shiftedTrace step|) := by
  let radius : Nat → Nat := fun step =>
    2 * (contactIndex step + 1)
  let terminalTail : Nat → Real := fun step =>
    restartPhysicalHighFrequencyTailMass
      initial (contactIndex (step + 1)) (radius step)
  let terminalMass : Nat → Real := fun step =>
    finiteStateVorticityCoefficientEnstrophy
      (wholeRestartModes (radius (step + 1)) \
        wholeRestartModes (radius step))
      (run initial (contactIndex (step + 2))).contact.physicalState
  let shiftedTrace : Nat → Real := fun step =>
    ∑ index ∈ Finset.Ico
        (contactIndex (step + 1)) (contactIndex (step + 2)),
      receiptHighFrequencyProjectedParabolicTrace
        (run initial index).nextContact.prefixReceipt (radius step)
  change
    (¬ BddAbove (Set.range terminalTail) ∨ ¬ Summable terminalMass) →
      ¬ Summable (fun step => |shiftedTrace step|)
  intro exhaustion shiftedTraceAbsSummable
  have terminalTailNonneg : ∀ step, 0 ≤ terminalTail step := by
    intro step
    unfold terminalTail restartPhysicalHighFrequencyTailMass
      wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _
  have terminalMassNonneg : ∀ step, 0 ≤ terminalMass step := by
    intro step
    unfold terminalMass finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have adjacentBalance (step : Nat) :
      shiftedTrace step = nu.coeff *
        (terminalMass step + terminalTail (step + 1) - terminalTail step) := by
    exact nativeAccumulationCofinalAdjacentTerminalTrace_eq
      initial contactIndex contactIndexStrictMono step
  have partialEq (length : Nat) :
      (∑ step ∈ Finset.range length, shiftedTrace step) =
        nu.coeff *
          ((∑ step ∈ Finset.range length, terminalMass step) +
            terminalTail length - terminalTail 0) := by
    have adjacentBalance' (step : Nat) :
        shiftedTrace step = nu.coeff *
          (terminalMass step +
            (terminalTail (step + 1) - terminalTail step)) := by
      rw [adjacentBalance]
      ring
    simp_rw [adjacentBalance']
    rw [← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_range_sub]
    ring
  have partialTraceLe (length : Nat) :
      (∑ step ∈ Finset.range length, shiftedTrace step) ≤
        ∑' step, |shiftedTrace step| := by
    calc
      (∑ step ∈ Finset.range length, shiftedTrace step) ≤
          |(∑ step ∈ Finset.range length, shiftedTrace step)| :=
        le_abs_self _
      _ ≤ ∑ step ∈ Finset.range length, |shiftedTrace step| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑' step, |shiftedTrace step| :=
        shiftedTraceAbsSummable.sum_le_tsum (Finset.range length)
          (fun step stepNotMem => abs_nonneg _)
  rcases exhaustion with terminalTailUnbounded | terminalMassNotSummable
  · apply terminalTailUnbounded
    refine ⟨terminalTail 0 +
        (∑' step, |shiftedTrace step|) / nu.coeff, ?_⟩
    rintro value ⟨length, rfl⟩
    have massPartialNonneg :
        0 ≤ ∑ step ∈ Finset.range length, terminalMass step :=
      Finset.sum_nonneg fun step stepMem => terminalMassNonneg step
    have scaledTailLe :
        nu.coeff * (terminalTail length - terminalTail 0) ≤
          ∑' step, |shiftedTrace step| := by
      have := partialTraceLe length
      rw [partialEq] at this
      nlinarith [nu.coeff_pos.le]
    have tailDiffLe :
        terminalTail length - terminalTail 0 ≤
          (∑' step, |shiftedTrace step|) / nu.coeff := by
      apply (le_div_iff₀ nu.coeff_pos).2
      simpa only [mul_comm] using scaledTailLe
    linarith
  · apply terminalMassNotSummable
    apply summable_of_sum_range_le terminalMassNonneg
    intro length
    have scaledMassLe :
        nu.coeff *
            (∑ step ∈ Finset.range length, terminalMass step) ≤
          (∑' step, |shiftedTrace step|) +
            nu.coeff * terminalTail 0 := by
      have := partialTraceLe length
      rw [partialEq] at this
      nlinarith [nu.coeff_pos.le, terminalTailNonneg length]
    apply (le_div_iff₀ nu.coeff_pos).2
    simpa only [mul_comm] using scaledMassLe

private theorem tendsto_terminal_add_partialSum_forces_exhaustion
    (terminal annular : Nat → Real)
    (annularNonneg : ∀ step, 0 ≤ annular step)
    (totalTendsto :
      Tendsto
        (fun length =>
          terminal length + ∑ step ∈ Finset.range length, annular step)
        atTop atTop) :
    ¬ BddAbove (Set.range terminal) ∨ ¬ Summable annular := by
  by_contra neither
  push Not at neither
  rcases neither with ⟨terminalBounded, annularSummable⟩
  obtain ⟨terminalBound, terminalBoundSpec⟩ := terminalBounded
  have annularPartialLe (length : Nat) :
      (∑ step ∈ Finset.range length, annular step) ≤
        ∑' step, annular step := by
    exact annularSummable.sum_le_tsum (Finset.range length)
      (fun step stepNotMem => annularNonneg step)
  let totalBound := terminalBound + ∑' step, annular step
  obtain ⟨length, lengthLarge⟩ :=
    ((tendsto_atTop.1 totalTendsto) (totalBound + 1)).exists
  have bounded :
      terminal length + ∑ step ∈ Finset.range length, annular step ≤
        totalBound :=
    add_le_add (terminalBoundSpec ⟨length, rfl⟩)
      (annularPartialLe length)
  linarith

/-- The moving annular responsibility reaches the complete reflected
velocity-triad transport on the identical next block.  The reflected keep and
the forced Laplacian multiplier-gap trace stay paired until a downstream
physical consumer settles them. -/
theorem
    nativeAccumulationCofinalMovingCutoffAnnularDebit_add_nextBlockReflectedTransport
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex)
    (step : Nat) :
    let start := contactIndex (step + 1)
    let finish := contactIndex (step + 2)
    let smaller := 2 * (contactIndex step + 1)
    let larger := 2 * (contactIndex (step + 1) + 1)
    let shell := wholeRestartModes larger \ wholeRestartModes smaller
    2 *
          (restartPhysicalHighFrequencyTailMass initial start smaller -
            restartPhysicalHighFrequencyTailMass initial start larger) +
        (∑ index ∈ Finset.Ico start finish,
          ∑ output ∈ shell,
            ∑' first : IntegerWavevector,
              (actualWholeSymmetricVelocityReflectedKeepWork
                  (run initial index).nextContact.prefixReceipt output first +
                actualWholeSymmetricVelocityMultiplierGapTraceWork
                  (run initial index).nextContact.prefixReceipt output first)) =
      2 * finiteStateVorticityCoefficientEnstrophy shell
          (run initial finish).contact.physicalState +
        2 * ∑ index ∈ Finset.Ico start finish,
          actualWholeFiniteViscousPayment
            (run initial index).nextContact.prefixReceipt shell := by
  dsimp only
  let shell :=
    wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
      wholeRestartModes (2 * (contactIndex step + 1))
  have zeroNotMem : (0 : IntegerWavevector) ∉ shell := by
    intro zeroMem
    exact
      (zero_not_mem_wholeRestartModes
        (2 * (contactIndex (step + 1) + 1)))
        (Finset.mem_sdiff.mp zeroMem).1
  have transportEq (index : Nat) :
      (∑ output ∈ shell,
          ∑' first : IntegerWavevector,
            (actualWholeSymmetricVelocityReflectedKeepWork
                (run initial index).nextContact.prefixReceipt output first +
              actualWholeSymmetricVelocityMultiplierGapTraceWork
                (run initial index).nextContact.prefixReceipt output first)) =
        2 * actualWholeFinitePairOccurrenceWork
          (run initial index).nextContact.prefixReceipt shell := by
    exact
      (actualWholeFinitePairOccurrenceWork_two_mul_eq_reflectedTransport_of_zero_not_mem
        (run initial index).nextContact.prefixReceipt shell zeroNotMem).symm
  have balance :=
    nativeAccumulationCofinalMovingCutoffAnnularDebit_add_nextBlockPairOccurrenceWork
      initial contactIndex contactIndexStrictMono step
  dsimp only at balance ⊢
  change
    2 *
          (restartPhysicalHighFrequencyTailMass
              initial (contactIndex (step + 1))
                (2 * (contactIndex step + 1)) -
            restartPhysicalHighFrequencyTailMass
              initial (contactIndex (step + 1))
                (2 * (contactIndex (step + 1) + 1))) +
        (∑ index ∈ Finset.Ico
            (contactIndex (step + 1)) (contactIndex (step + 2)),
          ∑ output ∈ shell,
            ∑' first : IntegerWavevector,
              (actualWholeSymmetricVelocityReflectedKeepWork
                  (run initial index).nextContact.prefixReceipt output first +
                actualWholeSymmetricVelocityMultiplierGapTraceWork
                  (run initial index).nextContact.prefixReceipt output first)) =
      2 * finiteStateVorticityCoefficientEnstrophy shell
          (run initial (contactIndex (step + 2))).contact.physicalState +
        2 * ∑ index ∈ Finset.Ico
            (contactIndex (step + 1)) (contactIndex (step + 2)),
          actualWholeFiniteViscousPayment
            (run initial index).nextContact.prefixReceipt shell
  simp_rw [transportEq]
  rw [← Finset.mul_sum]
  linarith

/-- The selector generated by the bounded accumulation fibre carries an
unbounded total of terminal high-frequency mass and exact intermediate
annular debits. -/
theorem
    sourceGeneratedNativeAccumulationCofinalMovingCutoffTotalResponsibility_tendsto_atTop
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∃ contactIndex : Nat → Nat,
      contactIndex 0 = 0 ∧
        StrictMono contactIndex ∧
        Tendsto
          (fun length =>
            restartPhysicalHighFrequencyTailMass
                initial (contactIndex (length + 1))
                (2 * (contactIndex length + 1)) +
              ∑ step ∈ Finset.range length,
                (restartPhysicalHighFrequencyTailMass
                      initial (contactIndex (step + 1))
                      (2 * (contactIndex step + 1)) -
                  restartPhysicalHighFrequencyTailMass
                      initial (contactIndex (step + 1))
                      (2 * (contactIndex (step + 1) + 1))))
          atTop atTop := by
  have generated :=
    sourceGeneratedNativeAccumulationCofinalHighFrequencyProjectedParabolicTrace
      initial elapsedBounded
  dsimp only at generated
  rcases generated with
    ⟨_occurrenceEq, contactIndex, contactIndexZero,
      contactIndexStrictMono, blockEffect⟩
  refine
    ⟨contactIndex, contactIndexZero, contactIndexStrictMono, ?_⟩
  let trace : Nat → Real := fun step =>
    ∑ index ∈ Finset.Ico
        (contactIndex step) (contactIndex (step + 1)),
      receiptHighFrequencyProjectedParabolicTrace
        (run initial index).nextContact.prefixReceipt
        (2 * (contactIndex step + 1))
  let total : Nat → Real := fun length =>
    restartPhysicalHighFrequencyTailMass
        initial (contactIndex (length + 1))
        (2 * (contactIndex length + 1)) +
      ∑ step ∈ Finset.range length,
        (restartPhysicalHighFrequencyTailMass
              initial (contactIndex (step + 1))
              (2 * (contactIndex step + 1)) -
          restartPhysicalHighFrequencyTailMass
              initial (contactIndex (step + 1))
              (2 * (contactIndex (step + 1) + 1)))
  have traceLower (length : Nat) :
      nu.coeff * ((length + 1 : Nat) : Real) ≤
        ∑ step ∈ Finset.range (length + 1), trace step := by
    calc
      nu.coeff * ((length + 1 : Nat) : Real) =
          ∑ _step ∈ Finset.range (length + 1), nu.coeff := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ ∑ step ∈ Finset.range (length + 1), trace step := by
        apply Finset.sum_le_sum
        intro step _stepMem
        have block := blockEffect step
        exact block.1.le
  have initialTailNonneg :
      0 ≤ restartPhysicalHighFrequencyTailMass
        initial (contactIndex 0) (2 * (contactIndex 0 + 1)) := by
    unfold restartPhysicalHighFrequencyTailMass
      wholeVorticityEuclideanMass
    exact tsum_nonneg fun _wave => sq_nonneg _
  have totalLower (length : Nat) : (length : Real) ≤ total length := by
    have traceEq :=
      nativeAccumulationCofinalMovingCutoffTrace_eq_terminalTail_add_annularDebit
        initial contactIndex contactIndexStrictMono length
    change
      (∑ step ∈ Finset.range (length + 1), trace step) =
        nu.coeff *
          (restartPhysicalHighFrequencyTailMass
                initial (contactIndex (length + 1))
                (2 * (contactIndex length + 1)) -
              restartPhysicalHighFrequencyTailMass
                initial (contactIndex 0) (2 * (contactIndex 0 + 1)) +
            ∑ step ∈ Finset.range length,
              (restartPhysicalHighFrequencyTailMass
                    initial (contactIndex (step + 1))
                    (2 * (contactIndex step + 1)) -
                restartPhysicalHighFrequencyTailMass
                    initial (contactIndex (step + 1))
                    (2 * (contactIndex (step + 1) + 1)))) at traceEq
    have scaled := traceLower length
    rw [traceEq] at scaled
    have unscaled := le_of_mul_le_mul_left scaled nu.coeff_pos
    dsimp only [total]
    norm_num at unscaled ⊢
    linarith
  change Tendsto total atTop atTop
  exact Filter.tendsto_atTop_mono totalLower tendsto_natCast_atTop_atTop

/-- The unbounded cofinal responsibility is now exhausted inside one exact
moving-cutoff PDE balance.  Either its terminal tail remains unbounded, or
one of the pair, terminal-shell, or raw viscous coordinates is non-summable.
The cube-normalized viscous coordinate is nevertheless already summable on
the same disjoint native blocks, so no duplicate kinetic payment is hidden
in the last alternative. -/
theorem
    sourceGeneratedNativeAccumulationCofinalMovingResponsibility_quantitativeExhaustion
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∃ contactIndex : Nat → Nat,
      contactIndex 0 = 0 ∧
        StrictMono contactIndex ∧
        let terminalTail : Nat → Real := fun length =>
          restartPhysicalHighFrequencyTailMass
            initial (contactIndex (length + 1))
            (2 * (contactIndex length + 1))
        let terminalMass : Nat → Real := fun step =>
          finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
              wholeRestartModes (2 * (contactIndex step + 1)))
            (run initial (contactIndex (step + 2))).contact.physicalState
        let pairTotal : Nat → Real := fun step =>
          ∑ index ∈ Finset.Ico
              (contactIndex (step + 1)) (contactIndex (step + 2)),
            actualWholeFinitePairOccurrenceWork
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
                wholeRestartModes (2 * (contactIndex step + 1)))
        let viscousTotal : Nat → Real := fun step =>
          ∑ index ∈ Finset.Ico
              (contactIndex (step + 1)) (contactIndex (step + 2)),
            actualWholeFiniteViscousPayment
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
                wholeRestartModes (2 * (contactIndex step + 1)))
        let normalizedViscous : Nat → Real := fun step =>
          viscousTotal step /
            ((2 * Real.pi) ^ 2 *
              (3 * ((2 * (contactIndex (step + 1) + 1) : Nat) : Real) ^ 2))
        Summable normalizedViscous ∧
          (¬ BddAbove (Set.range terminalTail) ∨
            ¬ Summable (fun step => |pairTotal step|) ∨
            ¬ Summable terminalMass ∨
            ¬ Summable viscousTotal) := by
  obtain ⟨contactIndex, contactIndexZero, contactIndexStrictMono,
      totalTendsto⟩ :=
    sourceGeneratedNativeAccumulationCofinalMovingCutoffTotalResponsibility_tendsto_atTop
      initial elapsedBounded
  refine ⟨contactIndex, contactIndexZero, contactIndexStrictMono, ?_⟩
  let terminalTail : Nat → Real := fun length =>
    restartPhysicalHighFrequencyTailMass
      initial (contactIndex (length + 1))
      (2 * (contactIndex length + 1))
  let annularMass : Nat → Real := fun step =>
    finiteStateVorticityCoefficientEnstrophy
      (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
        wholeRestartModes (2 * (contactIndex step + 1)))
      (run initial (contactIndex (step + 1))).contact.physicalState
  let terminalMass : Nat → Real := fun step =>
    finiteStateVorticityCoefficientEnstrophy
      (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
        wholeRestartModes (2 * (contactIndex step + 1)))
      (run initial (contactIndex (step + 2))).contact.physicalState
  let pairTotal : Nat → Real := fun step =>
    ∑ index ∈ Finset.Ico
        (contactIndex (step + 1)) (contactIndex (step + 2)),
      actualWholeFinitePairOccurrenceWork
        (run initial index).nextContact.prefixReceipt
        (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
          wholeRestartModes (2 * (contactIndex step + 1)))
  let viscousTotal : Nat → Real := fun step =>
    ∑ index ∈ Finset.Ico
        (contactIndex (step + 1)) (contactIndex (step + 2)),
      actualWholeFiniteViscousPayment
        (run initial index).nextContact.prefixReceipt
        (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
          wholeRestartModes (2 * (contactIndex step + 1)))
  let normalizedViscous : Nat → Real := fun step =>
    viscousTotal step /
      ((2 * Real.pi) ^ 2 *
        (3 * ((2 * (contactIndex (step + 1) + 1) : Nat) : Real) ^ 2))
  have normalizedSummable : Summable normalizedViscous := by
    simpa only [normalizedViscous, viscousTotal] using
      summable_nativeAccumulationCofinalMovingNormalizedViscousBlock
        initial contactIndex contactIndexStrictMono
  refine ⟨normalizedSummable, ?_⟩
  have annularNonneg : ∀ step, 0 ≤ annularMass step := by
    intro step
    unfold annularMass finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have exhaustion :
      ¬ BddAbove (Set.range terminalTail) ∨
        ¬ Summable annularMass := by
    apply tendsto_terminal_add_partialSum_forces_exhaustion
      terminalTail annularMass annularNonneg
    apply (Filter.Tendsto.congr ?_) totalTendsto
    intro length
    congr 1
    apply Finset.sum_congr rfl
    intro step stepMem
    have radiusLe :
        2 * (contactIndex step + 1) ≤
          2 * (contactIndex (step + 1) + 1) :=
      Nat.mul_le_mul_left 2
        (Nat.add_le_add_right
          (contactIndexStrictMono (Nat.lt_succ_self step)).le 1)
    exact
      restartPhysicalHighFrequencyTailMass_sub_eq_projectedAnnularMass
        initial (contactIndex (step + 1)) radiusLe
  rcases exhaustion with terminalUnbounded | annularNotSummable
  · exact Or.inl terminalUnbounded
  · right
    by_contra allComponentsSummable
    push Not at allComponentsSummable
    rcases allComponentsSummable with
      ⟨pairSummable, terminalSummable, viscousSummable⟩
    have componentSummable : Summable fun step =>
        |pairTotal step| + terminalMass step + viscousTotal step :=
      (pairSummable.add terminalSummable).add viscousSummable
    have terminalNonneg : ∀ step, 0 ≤ terminalMass step := by
      intro step
      unfold terminalMass finiteStateVorticityCoefficientEnstrophy
      exact Finset.sum_nonneg fun wave waveMem =>
        complexCoordinateAmplitudeSq_nonneg _
    have viscousNonneg : ∀ step, 0 ≤ viscousTotal step := by
      intro step
      unfold viscousTotal
      exact Finset.sum_nonneg fun index indexMem =>
        actualWholeFiniteViscousPayment_nonneg
          (run initial index).nextContact.prefixReceipt _
    have annularThirdLe (step : Nat) :
        annularMass step / 3 ≤
          |pairTotal step| + terminalMass step + viscousTotal step := by
      have settlement :=
        nativeAccumulationCofinalMovingAnnularMass_quantitativeSettlement
          initial contactIndex contactIndexStrictMono step
      dsimp only at settlement
      change
        annularMass step / 3 ≤ |pairTotal step| ∨
          (annularMass step / 3 ≤ terminalMass step ∧ _) ∨
          (annularMass step / 3 ≤ viscousTotal step ∧ _) at settlement
      rcases settlement with pairPays | terminalOrViscous
      · linarith [terminalNonneg step, viscousNonneg step]
      · rcases terminalOrViscous with terminalPays | viscousPays
        · linarith [abs_nonneg (pairTotal step), viscousNonneg step]
        · linarith [abs_nonneg (pairTotal step), terminalNonneg step]
    have annularThirdSummable : Summable fun step => annularMass step / 3 :=
      componentSummable.of_nonneg_of_le
        (fun step => div_nonneg (annularNonneg step) (by norm_num))
        annularThirdLe
    have annularSummable : Summable annularMass := by
      exact (annularThirdSummable.mul_left 3).congr fun step => by ring
    exact annularNotSummable annularSummable

/-- The terminal-tail and terminal-shell alternatives above are the same
adjacent source-owned trace after its exact telescope.  Thus the cofinal
responsibility has only three live PDE coordinates: shifted projected trace,
signed pair magnitude, or raw viscous debit.  The normalized viscous debit
remains paid by the disjoint kinetic ledger. -/
theorem
    sourceGeneratedNativeAccumulationCofinalMovingResponsibility_threeCoordinateExhaustion
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∃ contactIndex : Nat → Nat,
      contactIndex 0 = 0 ∧
        StrictMono contactIndex ∧
        let radius : Nat → Nat := fun step =>
          2 * (contactIndex step + 1)
        let shiftedTrace : Nat → Real := fun step =>
          ∑ index ∈ Finset.Ico
              (contactIndex (step + 1)) (contactIndex (step + 2)),
            receiptHighFrequencyProjectedParabolicTrace
              (run initial index).nextContact.prefixReceipt (radius step)
        let pairTotal : Nat → Real := fun step =>
          ∑ index ∈ Finset.Ico
              (contactIndex (step + 1)) (contactIndex (step + 2)),
            actualWholeFinitePairOccurrenceWork
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes (radius (step + 1)) \
                wholeRestartModes (radius step))
        let viscousTotal : Nat → Real := fun step =>
          ∑ index ∈ Finset.Ico
              (contactIndex (step + 1)) (contactIndex (step + 2)),
            actualWholeFiniteViscousPayment
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes (radius (step + 1)) \
                wholeRestartModes (radius step))
        let normalizedViscous : Nat → Real := fun step =>
          viscousTotal step /
            ((2 * Real.pi) ^ 2 *
              (3 * ((radius (step + 1) : Nat) : Real) ^ 2))
        Summable normalizedViscous ∧
          (¬ Summable (fun step => |shiftedTrace step|) ∨
            ¬ Summable (fun step => |pairTotal step|) ∨
            ¬ Summable viscousTotal) := by
  obtain ⟨contactIndex, contactIndexZero, contactIndexStrictMono,
      generated⟩ :=
    sourceGeneratedNativeAccumulationCofinalMovingResponsibility_quantitativeExhaustion
      initial elapsedBounded
  refine
    ⟨contactIndex, contactIndexZero, contactIndexStrictMono, ?_⟩
  dsimp only at generated ⊢
  rcases generated with ⟨normalizedSummable, exhaustion⟩
  refine ⟨normalizedSummable, ?_⟩
  rcases exhaustion with terminalTailUnbounded | pairOrTerminalOrViscous
  · left
    have adjacent :=
      nativeAccumulationCofinalTerminalExhaustion_forces_adjacentTrace_not_summable
        initial contactIndex contactIndexStrictMono
    dsimp only at adjacent
    exact adjacent (Or.inl terminalTailUnbounded)
  · rcases pairOrTerminalOrViscous with
      pairNotSummable | terminalOrViscous
    · exact Or.inr (Or.inl pairNotSummable)
    · rcases terminalOrViscous with
        terminalNotSummable | viscousNotSummable
      · left
        have adjacent :=
          nativeAccumulationCofinalTerminalExhaustion_forces_adjacentTrace_not_summable
            initial contactIndex contactIndexStrictMono
        dsimp only at adjacent
        exact adjacent (Or.inr terminalNotSummable)
      · exact Or.inr (Or.inr viscousNotSummable)


/-- On the selector generated by the original cofinal failure, the cross
coordinate is necessarily non-summable.  This fixes the former payment
trichotomy to one exact whole-vorticity telescope; it does not create a new
disposition or revised law. -/
theorem sourceGeneratedNativeAccumulationCofinalCrossPayment_not_summable
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let failure :=
      sourceGeneratedNativeAccumulationVorticityFailure
        initial elapsedBounded
    failure.rootCofinalOccurrence =
        (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence ∧
      ∃ contactIndex : Nat → Nat,
        contactIndex 0 = 0 ∧
          StrictMono contactIndex ∧
          ¬ Summable (fun step =>
            |(nativeAccumulationCofinalBlockPayments
              initial contactIndex step).2.1|) := by
  have generated :=
    sourceGeneratedNativeAccumulationCofinalHighFrequencyProjectedParabolicTrace
      initial elapsedBounded
  dsimp only at generated ⊢
  rcases generated with
    ⟨occurrenceEq, contactIndex, contactIndexZero,
      contactIndexStrictMono, _blockEffect⟩
  refine
    ⟨occurrenceEq,
      contactIndex, contactIndexZero,
      contactIndexStrictMono, ?_⟩
  let cross : Nat → Real := fun step =>
    (nativeAccumulationCofinalBlockPayments
      initial contactIndex step).2.1
  have partialSum_eq (length : Nat) :
      (∑ step ∈ Finset.range length, cross step) =
        nu.coeff *
          (restartPhysicalVorticityMass initial (contactIndex length) -
            restartPhysicalVorticityMass initial (contactIndex 0)) := by
    have crossEq (step : Nat) :
        cross step =
          nu.coeff *
            (restartPhysicalVorticityMass
                initial (contactIndex (step + 1)) -
              restartPhysicalVorticityMass
                initial (contactIndex step)) := by
      exact nativeAccumulationCofinalBlockCrossPayment_eq
        initial contactIndex contactIndexStrictMono step
    simp_rw [crossEq]
    rw [← Finset.mul_sum]
    have telescoped :
        (∑ step ∈ Finset.range length,
          (restartPhysicalVorticityMass
              initial (contactIndex (step + 1)) -
            restartPhysicalVorticityMass
              initial (contactIndex step))) =
          restartPhysicalVorticityMass initial (contactIndex length) -
            restartPhysicalVorticityMass initial (contactIndex 0) := by
      simpa only using Finset.sum_range_sub
        (fun step =>
          restartPhysicalVorticityMass initial (contactIndex step)) length
    rw [telescoped]
  have massTendsto :
      Tendsto
        (fun length =>
          restartPhysicalVorticityMass initial (contactIndex length))
        atTop atTop :=
    (tendsto_restartPhysicalVorticityMass_atTop_of_elapsedTime_bddAbove
      initial elapsedBounded).comp contactIndexStrictMono.tendsto_atTop
  have partialSumTendsto :
      Tendsto
        (fun length => ∑ step ∈ Finset.range length, cross step)
        atTop atTop := by
    rw [tendsto_atTop]
    intro requested
    have massEventually :=
      (tendsto_atTop.1 massTendsto)
        (requested / nu.coeff +
          restartPhysicalVorticityMass initial (contactIndex 0))
    filter_upwards [massEventually] with length massLarge
    rw [partialSum_eq]
    have divided :
        requested / nu.coeff ≤
          restartPhysicalVorticityMass initial (contactIndex length) -
            restartPhysicalVorticityMass initial (contactIndex 0) := by
      linarith
    have scaled :=
      mul_le_mul_of_nonneg_left divided nu.coeff_pos.le
    calc
      requested = nu.coeff * (requested / nu.coeff) := by
        field_simp [ne_of_gt nu.coeff_pos]
      _ ≤ nu.coeff *
          (restartPhysicalVorticityMass initial (contactIndex length) -
            restartPhysicalVorticityMass initial (contactIndex 0)) := scaled
  intro absoluteSummable
  have normSummable : Summable (fun step => ‖cross step‖) := by
    simpa only [Real.norm_eq_abs] using absoluteSummable
  have signedSummable : Summable cross := Summable.of_norm normSummable
  exact
    not_tendsto_nhds_of_tendsto_atTop partialSumTendsto _
      signedSummable.hasSum.tendsto_sum_nat

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
end NavierStokes
end SaturationMonoid
