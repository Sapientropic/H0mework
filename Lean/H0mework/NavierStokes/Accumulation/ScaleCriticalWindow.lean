import H0mework.NavierStokes.Accumulation.CofinalActionSettlement

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

private theorem commonTimeMeasure_eq_comap_volume_for_prehistory
    (requestedTime : Real) :
    commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val : Icc (0 : Real) requestedTime → Real) volume := by
  ext measurable measurableSet
  unfold commonTimeMeasure
  rw [comap_subtype_coe_apply measurableSet_Icc]
  rw [comap_subtype_coe_apply measurableSet_Icc]
  have imageMeasurable : MeasurableSet
      ((fun time : Icc (0 : Real) requestedTime => time.1) '' measurable) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image'
      measurableSet
  rw [Measure.restrict_apply imageMeasurable]
  rw [inter_eq_left.2 (by
    rintro _ ⟨time, _, rfl⟩
    exact time.2)]

/-- A continuous physical row on a positive common-time interval inherits an
almost-everywhere source ceiling at every actual time. -/
theorem continuous_le_of_ae_le_commonTime
    {requestedTime ceiling : Real}
    (requestedTimePos : 0 < requestedTime)
    (value : Icc (0 : Real) requestedTime → Real)
    (valueContinuous : Continuous value)
    (valueAE : ∀ᵐ time ∂commonTimeMeasure requestedTime,
      value time ≤ ceiling) :
    ∀ time, value time ≤ ceiling := by
  let extended : Real → Real := fun time =>
    value (projIcc 0 requestedTime requestedTimePos.le time)
  let clipped : Real → Real := fun time => min (extended time) ceiling
  have extendedContinuous : Continuous extended := by
    dsimp only [extended]
    exact valueContinuous.comp continuous_projIcc
  have clippedContinuous : Continuous clipped := by
    dsimp only [clipped]
    fun_prop
  rw [commonTimeMeasure_eq_comap_volume_for_prehistory] at valueAE
  have extendedAE :
      ∀ᵐ time ∂volume.restrict (Icc (0 : Real) requestedTime),
        extended time ≤ ceiling := by
    rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [valueAE] with time valueLe
    simpa only [extended,
      projIcc_of_mem requestedTimePos.le time.2] using valueLe
  have extendedEqClippedAE :
      extended =ᵐ[volume.restrict (Icc (0 : Real) requestedTime)] clipped :=
    extendedAE.mono fun time valueLe => by
      dsimp only [clipped]
      rw [min_eq_left valueLe]
  have denseInterior :
      Icc (0 : Real) requestedTime ⊆
        closure (interior (Icc (0 : Real) requestedTime)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt requestedTimePos)]
  have extendedEqClipped : EqOn extended clipped (Icc 0 requestedTime) :=
    MeasureTheory.Measure.eqOn_of_ae_eq extendedEqClippedAE
      extendedContinuous.continuousOn clippedContinuous.continuousOn
      denseInterior
  intro time
  have pointEq := extendedEqClipped time.2
  dsimp only [extended, clipped] at pointEq
  rw [projIcc_of_mem requestedTimePos.le time.2] at pointEq
  rw [pointEq]
  exact min_le_right _ _

private theorem receipt_mass_le_of_ae_lt
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime ceiling : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (massAE :
      ∀ᵐ time ∂commonTimeMeasure requestedTime,
        wholeVorticityEuclideanMass (receipt.wholePath time) < ceiling) :
    ∀ time,
      wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling := by
  apply continuous_le_of_ae_le_commonTime receipt.requestedTimePos
    (fun time =>
      wholeVorticityEuclideanMass (receipt.wholePath time))
    (wholeReceiptVorticityMass_continuous receipt)
  exact massAE.mono fun _ massLt => massLt.le

private theorem firstHit_generates_range_receipt_mass_ae_lt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (level : Real)
    (existsMassAbove :
      ∃ index : Nat,
        level ≤ restartPhysicalVorticityMass initial index) :
    ∀ index, index ∈ Finset.range (Nat.find existsMassAbove) →
      ∀ᵐ localTime
          ∂(commonTimeMeasure
            (run initial index).nextContact.time.1),
        wholeVorticityEuclideanMass
            ((run initial index).nextContact.prefixReceipt.wholePath
              localTime) <
          level + 2 := by
  intro index indexMem
  have contactMassLt :
      restartPhysicalVorticityMass initial index < level :=
    lt_of_not_ge
      (Nat.find_min existsMassAbove (Finset.mem_range.mp indexMem))
  have contactMassNonneg :
      0 ≤ restartPhysicalVorticityMass initial index := by
    unfold restartPhysicalVorticityMass wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _
  have rawNonneg :
      0 ≤ wholeRestartRawCoefficientCeiling
        (run initial index).contact := by
    change
      0 ≤ wholeVorticityEuclideanMass
        (run initial index).contact.physicalState + 1
    exact add_nonneg contactMassNonneg zero_le_one
  have ceilingLtRaw := Nat.ceil_lt_add_one rawNonneg
  have ceilingLt :
      wholeRestartCoefficientCeiling (run initial index).contact <
        level + 2 := by
    unfold wholeRestartCoefficientCeiling
    change
      (Nat.ceil
        (wholeVorticityEuclideanMass
          (run initial index).contact.physicalState + 1) : Real) <
        level + 2
    change
      (Nat.ceil
        (wholeVorticityEuclideanMass
          (run initial index).contact.physicalState + 1) : Real) <
        wholeVorticityEuclideanMass
            (run initial index).contact.physicalState + 1 + 1
      at ceilingLtRaw
    unfold restartPhysicalVorticityMass at contactMassLt
    linarith
  have eventuallyFull :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
      (generatedWholeRestartCanonicalReplay
        (run initial index).contact)
  have onPrefixImage :
      ∀ᵐ localTime
          ∂((commonTimeMeasure
              (wholeRestartDuration (run initial index).contact)).restrict
            (Set.range
              (commonTimeInclusion
                (run initial index).nextContact.time.2.2))),
        wholeVorticityEuclideanMass
            ((generatedWholeRestartWholeContinuousMildSerrinReceipt
              (generatedWholeRestartCanonicalReplay
                (run initial index).contact)).wholePath localTime) ≤
          wholeRestartCoefficientCeiling
            (run initial index).contact :=
    MeasureTheory.ae_restrict_le eventuallyFull
  have pulledToPrefix :=
    (commonTimeInclusion_measurePreserving
        (run initial index).nextContact.time.2.2
      |>.quasiMeasurePreserving.tendsto_ae) onPrefixImage
  filter_upwards [pulledToPrefix] with localTime massLe
  have sourceMassLe :
      wholeVorticityEuclideanMass
          ((run initial index).nextContact.prefixReceipt.wholePath
            localTime) ≤
        wholeRestartCoefficientCeiling
          (run initial index).contact := by
    simpa [prefixReceipt, restrictWholeContinuousMildSerrinReceipt,
      GeneratedWholeRestartCurrent.nextReceipt] using massLe
  exact sourceMassLe.trans_lt ceilingLt

private theorem firstHitPrehistory_prefix_mass_le
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (finish : Nat)
    (finishPos : 0 < finish)
    (ceiling : Real)
    (receiptMass :
      ∀ index, index ∈ Finset.range finish →
        ∀ localTime :
            Icc (0 : Real) (run initial index).nextContact.time.1,
          wholeVorticityEuclideanMass
              ((run initial index).nextContact.prefixReceipt.wholePath
                localTime) ≤ ceiling) :
    ∀ absoluteTime,
      absoluteTime ∈
          Icc
            (elapsedTime initial 1)
            (elapsedTime initial (finish + 1)) →
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory
              initial (finish + 1) absoluteTime) ≤ ceiling := by
  intro absoluteTime timeMem
  by_cases atLower : absoluteTime = elapsedTime initial 1
  · subst absoluteTime
    have pathEq :=
      wholeRestartPrefixPhysicalTrajectory_eq_receipt initial
        (length := finish + 1)
        (index := 0)
        (by omega)
        (time := elapsedTime initial 1)
        ⟨elapsedTime_strictMono initial (Nat.zero_lt_succ 0), le_rfl⟩
    rw [pathEq]
    simp only [elapsedTime_succ, elapsedTime_zero, zero_add, sub_zero]
    rw [wholeRestartReceiptPhysicalTrajectory_contact]
    have boundAtZero := receiptMass 0 (Finset.mem_range.mpr finishPos)
      ⟨0, ⟨le_rfl,
        (run initial 0).nextContact.time_pos.le⟩⟩
    simpa only [
      (run initial 0).nextContact.prefixReceipt.wholePath_initial] using
      boundAtZero
  · have lowerLt : elapsedTime initial 1 < absoluteTime :=
      lt_of_le_of_ne timeMem.1 (Ne.symm atLower)
    have elapsedOnePos : 0 < elapsedTime initial 1 := by
      simpa only [elapsedTime_zero] using
        elapsedTime_strictMono initial (Nat.zero_lt_succ 0)
    have timePos : 0 < absoluteTime := elapsedOnePos.trans lowerLt
    obtain ⟨index, indexSpec, _indexUnique⟩ :=
      wholeRestartPhysicalWindow_existsUnique initial
        (length := finish + 1)
        (time := absoluteTime)
        ⟨timePos, timeMem.2⟩
    rcases indexSpec with ⟨indexLt, windowMem⟩
    have oneLeIndex : 1 ≤ index := by
      by_contra indexLtOne
      have indexZero : index = 0 := by omega
      subst index
      exact (not_lt_of_ge windowMem.2) lowerLt
    obtain ⟨prior, rfl⟩ := Nat.exists_eq_add_of_le oneLeIndex
    simp only [Nat.one_add] at indexLt windowMem _indexUnique ⊢
    have priorLt : prior < finish := by omega
    rw [wholeRestartPrefixPhysicalTrajectory_eq_receipt
      initial (by omega) windowMem]
    unfold wholeRestartReceiptPhysicalTrajectory
    rw [run_succ]
    exact receiptMass prior (Finset.mem_range.mpr priorLt) _

private theorem firstHitPrehistory_ae_mass_lt_generates_prefix_mass_le
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (finish : Nat)
    (finishPos : 0 < finish)
    (ceiling : Real)
    (receiptMassAE :
      ∀ index, index ∈ Finset.range finish →
        ∀ᵐ localTime
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1),
          wholeVorticityEuclideanMass
              ((run initial index).nextContact.prefixReceipt.wholePath
                localTime) < ceiling) :
    ∀ absoluteTime,
      absoluteTime ∈
          Icc
            (elapsedTime initial 1)
            (elapsedTime initial (finish + 1)) →
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory
              initial (finish + 1) absoluteTime) ≤ ceiling := by
  apply firstHitPrehistory_prefix_mass_le initial finish finishPos ceiling
  intro index indexMem
  exact receipt_mass_le_of_ae_lt
    (run initial index).nextContact.prefixReceipt
    (receiptMassAE index indexMem)

/-- Every positive source level selects an original actual `Ico` whose
whole-vorticity gain pays a fixed inverse-level nonlinear quantum. -/
theorem sourceGeneratedNativeAccumulationInverseLevelActualIcoNonlinearAction
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (level : Real)
    (levelPos : 0 < level)
    (initialLeHalf :
      restartPhysicalVorticityMass initial 0 ≤ level / 2) :
    ∃ start finish : Nat,
      start < finish ∧
      elapsedTime initial (start + 1) <
        elapsedTime initial (finish + 1) ∧
      restartPhysicalVorticityMass initial start ≤ level / 2 ∧
      level ≤ restartPhysicalVorticityMass initial finish ∧
      nu.coeff / 2 ≤
        level⁻¹ *
          wholeRestartIcoNonlinearNegativeOneEuclideanPayment
            initial start finish ∧
      (∀ index, index ∈ Finset.Ico start finish →
        ∀ᵐ localTime
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1),
          wholeVorticityEuclideanMass
              ((run initial index).nextContact.prefixReceipt.wholePath
                localTime) <
            level + 2) ∧
      (∀ time ∈
          Icc (elapsedTime initial 1)
            (elapsedTime initial (finish + 1)),
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
              time) ≤
          level + 2) ∧
      nu.coeff * (level / 2) ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          ((level + 2) ^ 3 *
            (elapsedTime initial (finish + 1) -
              elapsedTime initial (start + 1))) ∧
      (2 ≤ level →
        nu.coeff ^ 3 * (2 * Real.pi) ^ 2 ≤
          (72 * 1557504 * biotSavartSerrinConstant ^ 2) *
            (level ^ 2 *
              (elapsedTime initial (finish + 1) -
                elapsedTime initial (start + 1)))) ∧
      ∀ index, index ∈ Finset.Ico start finish →
        ∀ localTime :
            Icc (0 : Real) (run initial (index + 1)).contact.time.1,
          let absoluteTime :=
            wholeRestartReceiptPreAccumulationTime
              initial elapsedBounded (index + 1) localTime
          elapsedTime initial (start + 1) ≤ absoluteTime.1 ∧
          absoluteTime.1 ≤ elapsedTime initial (finish + 1) ∧
          wholeRestartBoundedPreAccumulationPhysicalTrajectory
              initial elapsedBounded absoluteTime =
            (run initial (index + 1)).contact.prefixReceipt.wholePath
              localTime := by
  have massUnbounded :=
    elapsedTime_bddAbove_forces_physicalVorticityMass_unbounded
      initial elapsedBounded
  have existsMassAbove (requested : Real) :
      ∃ index : Nat,
        requested ≤ restartPhysicalVorticityMass initial index := by
    by_contra noIndex
    push Not at noIndex
    apply massUnbounded
    refine ⟨requested, ?_⟩
    rintro mass ⟨index, rfl⟩
    exact (noIndex index).le
  let halfExists :
      ∃ index : Nat,
        level / 2 ≤ restartPhysicalVorticityMass initial index :=
    existsMassAbove (level / 2)
  let halfIndex : Nat := Nat.find halfExists
  let finishExists :
      ∃ index : Nat,
        level ≤ restartPhysicalVorticityMass initial index :=
    existsMassAbove level
  let finish : Nat := Nat.find finishExists
  let start : Nat := halfIndex.pred
  have finishSpec :
      level ≤ restartPhysicalVorticityMass initial finish :=
    Nat.find_spec finishExists
  have halfLeLevel : level / 2 ≤ level := by linarith
  have halfIndexLeFinish : halfIndex ≤ finish :=
    Nat.find_min' halfExists (halfLeLevel.trans finishSpec)
  have startLeFinish : start ≤ finish :=
    (Nat.pred_le halfIndex).trans halfIndexLeFinish
  have startMassLeHalf :
      restartPhysicalVorticityMass initial start ≤ level / 2 := by
    by_cases halfZero : halfIndex = 0
    · simp only [start, halfZero, Nat.pred_zero]
      exact initialLeHalf
    · have startLtHalfIndex : start < halfIndex := by
        simpa only [start] using Nat.pred_lt halfZero
      exact le_of_not_gt (fun startAbove =>
        (Nat.not_lt_of_ge
          (Nat.find_min' halfExists startAbove.le))
          startLtHalfIndex)
  have startLtFinish : start < finish := by
    apply lt_of_le_of_ne startLeFinish
    intro startEqFinish
    rw [startEqFinish] at startMassLeHalf
    linarith
  have elapsedActionStartLtFinish :
      elapsedTime initial (start + 1) <
        elapsedTime initial (finish + 1) :=
    (elapsedTime_strictMono initial) (by omega)
  have balance :=
    wholeRestartIcoNonlinearNegativeOneEuclideanPayment_balance
      initial start finish startLeFinish
  have tangentNonneg :
      0 ≤ wholeRestartIcoTangentNegativeOneEuclideanPayment
        initial start finish := by
    unfold wholeRestartIcoTangentNegativeOneEuclideanPayment
    exact Finset.sum_nonneg fun _index _indexMem => sq_nonneg _
  have viscousNonneg :
      0 ≤ wholeRestartIcoViscousNegativeOneEuclideanPayment
        initial start finish := by
    unfold wholeRestartIcoViscousNegativeOneEuclideanPayment
    exact Finset.sum_nonneg fun _index _indexMem => sq_nonneg _
  have payment :
      nu.coeff * (level / 2) ≤
        wholeRestartIcoNonlinearNegativeOneEuclideanPayment
          initial start finish := by
    change
      wholeRestartIcoNonlinearNegativeOneEuclideanPayment
            initial start finish +
          nu.coeff * restartPhysicalVorticityMass initial start =
        wholeRestartIcoTangentNegativeOneEuclideanPayment
              initial start finish +
            wholeRestartIcoViscousNegativeOneEuclideanPayment
              initial start finish +
          nu.coeff * restartPhysicalVorticityMass initial finish at balance
    nlinarith [nu.coeff_pos]
  have inverseLevelPayment :
      nu.coeff / 2 ≤
        level⁻¹ *
          wholeRestartIcoNonlinearNegativeOneEuclideanPayment
            initial start finish := by
    calc
      nu.coeff / 2 =
          level⁻¹ * (nu.coeff * (level / 2)) := by
        field_simp
      _ ≤
          level⁻¹ *
            wholeRestartIcoNonlinearNegativeOneEuclideanPayment
              initial start finish :=
        mul_le_mul_of_nonneg_left payment (inv_nonneg.mpr levelPos.le)
  have actionRangeMassLt :=
    firstHit_generates_range_receipt_mass_ae_lt
      initial level finishExists
  have actionInteriorMassLt :
      ∀ index, index ∈ Finset.Ico start finish →
        ∀ᵐ localTime
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1),
          wholeVorticityEuclideanMass
              ((run initial index).nextContact.prefixReceipt.wholePath
                localTime) <
            level + 2 := by
    intro index indexMem
    exact actionRangeMassLt index
      (Finset.mem_range.mpr (Finset.mem_Ico.mp indexMem).2)
  have finishPos : 0 < finish :=
    lt_of_le_of_lt (Nat.zero_le start) startLtFinish
  have prehistoryCeiling :
      ∀ time ∈
          Icc (elapsedTime initial 1)
            (elapsedTime initial (finish + 1)),
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
              time) ≤
          level + 2 :=
    firstHitPrehistory_ae_mass_lt_generates_prefix_mass_le
      initial finish finishPos (level + 2) actionRangeMassLt
  let cubicConstant : Real :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
  have edgeCubic
      (index : Nat)
      (indexMem : index ∈ Finset.Ico start finish) :
      nu.coeff *
          (restartPhysicalVorticityMass initial (index + 1) -
            restartPhysicalVorticityMass initial index) ≤
        cubicConstant *
          ((level + 2) ^ 3 *
            (run initial index).nextContact.time.1) := by
    let receipt := (run initial index).nextContact.prefixReceipt
    let mass := fun localTime =>
      wholeVorticityEuclideanMass (receipt.wholePath localTime)
    have massCubeContinuous :
        Continuous (fun localTime => mass localTime ^ 3) :=
      (wholeReceiptVorticityMass_continuous receipt).pow 3
    have massCubeIntegrable :
        Integrable (fun localTime => mass localTime ^ 3)
          (commonTimeMeasure (run initial index).nextContact.time.1) := by
      simpa only [receipt, MeasureTheory.integrableOn_univ] using
        (ContinuousOn.integrableOn_compact isCompact_univ
          massCubeContinuous.continuousOn)
    have constantIntegrable :
        Integrable
          (fun _localTime :
              Icc (0 : Real) (run initial index).nextContact.time.1 =>
            (level + 2) ^ 3)
          (commonTimeMeasure (run initial index).nextContact.time.1) :=
      integrable_const _
    have massCubeLe :
        ∀ᵐ localTime
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1),
          mass localTime ^ 3 ≤ (level + 2) ^ 3 := by
      filter_upwards [actionInteriorMassLt index indexMem] with
        localTime massLess
      apply pow_le_pow_left₀
      · unfold mass wholeVorticityEuclideanMass
        exact tsum_nonneg fun wave => sq_nonneg _
      · exact massLess.le
    have integralLe :
        (∫ localTime, mass localTime ^ 3
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1)) ≤
          ∫ _localTime, (level + 2) ^ 3
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1) :=
      integral_mono_ae massCubeIntegrable constantIntegrable massCubeLe
    have constantIntegral :
        (∫ _localTime :
              Icc (0 : Real) (run initial index).nextContact.time.1,
            (level + 2) ^ 3
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1)) =
          (level + 2) ^ 3 *
            (run initial index).nextContact.time.1 := by
      change
        (∫ localTime :
              Icc (0 : Real) (run initial index).nextContact.time.1,
            (fun _ : Real => (level + 2) ^ 3) localTime.1
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1)) = _
      rw [commonTime_integral_eq_intervalIntegral
        (run initial index).nextContact.time.1
        (run initial index).nextContact.time_pos.le
        (fun _ : Real => (level + 2) ^ 3)]
      simp
      ring
    have cubicConstantNonneg : 0 ≤ cubicConstant := by
      dsimp only [cubicConstant]
      positivity
    have receiptCubic :=
      receiptVorticityMass_increment_le_cubicPayment receipt
    have receiptCubicCeiling :
        nu.coeff *
            (wholeVorticityEuclideanMass
                (receipt.wholePath
                  ⟨(run initial index).nextContact.time.1,
                    (run initial index).nextContact.time_pos.le,
                    le_rfl⟩) -
              wholeVorticityEuclideanMass
                (run initial index).contact.physicalState) ≤
          cubicConstant *
            ((level + 2) ^ 3 *
              (run initial index).nextContact.time.1) := by
      calc
        nu.coeff *
            (wholeVorticityEuclideanMass
                (receipt.wholePath
                  ⟨(run initial index).nextContact.time.1,
                    (run initial index).nextContact.time_pos.le,
                    le_rfl⟩) -
              wholeVorticityEuclideanMass
                (run initial index).contact.physicalState) ≤
            cubicConstant *
              ∫ localTime, mass localTime ^ 3
                ∂(commonTimeMeasure
                  (run initial index).nextContact.time.1) := by
          simpa only [receipt, mass, cubicConstant] using receiptCubic
        _ ≤ cubicConstant *
              (∫ _localTime, (level + 2) ^ 3
                ∂(commonTimeMeasure
                  (run initial index).nextContact.time.1)) :=
          mul_le_mul_of_nonneg_left integralLe cubicConstantNonneg
        _ = cubicConstant *
              ((level + 2) ^ 3 *
                (run initial index).nextContact.time.1) := by
          rw [constantIntegral]
    rw [(run initial index).nextContact_prefix_terminal]
      at receiptCubicCeiling
    change
      nu.coeff *
          (restartPhysicalVorticityMass initial (index + 1) -
            restartPhysicalVorticityMass initial index) ≤
        cubicConstant *
          ((level + 2) ^ 3 *
            (run initial index).nextContact.time.1)
    simpa only [receipt, restartPhysicalVorticityMass, run_succ,
      GeneratedWholeRestartCurrent.next] using receiptCubicCeiling
  have summedCubic := Finset.sum_le_sum edgeCubic
  have massIncrementTelescope :
      (∑ index ∈ Finset.Ico start finish,
        nu.coeff *
          (restartPhysicalVorticityMass initial (index + 1) -
            restartPhysicalVorticityMass initial index)) =
        nu.coeff *
          (restartPhysicalVorticityMass initial finish -
            restartPhysicalVorticityMass initial start) := by
    rw [← Finset.mul_sum]
    rw [Finset.sum_Ico_eq_sub _ startLeFinish,
      Finset.sum_range_sub, Finset.sum_range_sub]
    ring
  have timeTelescope :
      (∑ index ∈ Finset.Ico start finish,
        (run initial index).nextContact.time.1) =
        elapsedTime initial (finish + 1) -
          elapsedTime initial (start + 1) := by
    have edgeTime (index : Nat) :
        (run initial index).nextContact.time.1 =
          elapsedTime initial (index + 2) -
            elapsedTime initial (index + 1) := by
      rw [elapsedTime_succ]
      have nextTimeEq :
          (run initial (index + 1)).contact.time.1 =
            (run initial index).nextContact.time.1 := by
        rfl
      rw [nextTimeEq]
      ring
    have shiftedTelescope (length : Nat) :
        (∑ index ∈ Finset.range length,
          (elapsedTime initial (index + 2) -
            elapsedTime initial (index + 1))) =
          elapsedTime initial (length + 1) -
            elapsedTime initial 1 := by
      simpa [Nat.add_assoc] using
        Finset.sum_range_sub
          (fun index => elapsedTime initial (index + 1)) length
    simp_rw [edgeTime]
    rw [Finset.sum_Ico_eq_sub _ startLeFinish,
      shiftedTelescope finish, shiftedTelescope start]
    ring
  have cubicSumFactor :
      (∑ index ∈ Finset.Ico start finish,
        cubicConstant *
          ((level + 2) ^ 3 *
            (run initial index).nextContact.time.1)) =
        cubicConstant *
          ((level + 2) ^ 3 *
            (elapsedTime initial (finish + 1) -
              elapsedTime initial (start + 1))) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, timeTelescope]
  rw [massIncrementTelescope, cubicSumFactor] at summedCubic
  have massGain :
      level / 2 ≤
        restartPhysicalVorticityMass initial finish -
          restartPhysicalVorticityMass initial start := by
    linarith
  have cubicSpanPayment :
      nu.coeff * (level / 2) ≤
        cubicConstant *
          ((level + 2) ^ 3 *
            (elapsedTime initial (finish + 1) -
              elapsedTime initial (start + 1))) :=
    (mul_le_mul_of_nonneg_left massGain nu.coeff_pos.le).trans
      summedCubic
  have normalizedSpanPayment :
      2 ≤ level →
        nu.coeff ^ 3 * (2 * Real.pi) ^ 2 ≤
          (72 * 1557504 * biotSavartSerrinConstant ^ 2) *
            (level ^ 2 *
              (elapsedTime initial (finish + 1) -
                elapsedTime initial (start + 1))) := by
    intro levelTwo
    let scaleConstant : Real :=
      9 * 1557504 * biotSavartSerrinConstant ^ 2
    let denominator : Real :=
      2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
    have denominatorPos : 0 < denominator := by
      dsimp only [denominator]
      exact mul_pos (by norm_num)
        (mul_pos (sq_pos_of_pos nu.coeff_pos)
          (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)))
    have scaled :=
      mul_le_mul_of_nonneg_left cubicSpanPayment denominatorPos.le
    have scaledClean :
        nu.coeff ^ 3 * (2 * Real.pi) ^ 2 * level ≤
          scaleConstant *
            ((level + 2) ^ 3 *
              (elapsedTime initial (finish + 1) -
                elapsedTime initial (start + 1))) := by
      calc
        nu.coeff ^ 3 * (2 * Real.pi) ^ 2 * level =
            denominator * (nu.coeff * (level / 2)) := by
          dsimp only [denominator]
          ring
        _ ≤ denominator *
            ((scaleConstant / denominator) *
              ((level + 2) ^ 3 *
                (elapsedTime initial (finish + 1) -
                  elapsedTime initial (start + 1)))) := by
          simpa only [scaleConstant, denominator, cubicConstant] using
            scaled
        _ = scaleConstant *
              ((level + 2) ^ 3 *
                (elapsedTime initial (finish + 1) -
                  elapsedTime initial (start + 1))) := by
          field_simp [ne_of_gt denominatorPos]
    have levelPlusLe : level + 2 ≤ 2 * level := by
      linarith
    have cubeLe : (level + 2) ^ 3 ≤ (2 * level) ^ 3 :=
      pow_le_pow_left₀ (by linarith) levelPlusLe 3
    have spanNonneg :
        0 ≤ elapsedTime initial (finish + 1) -
          elapsedTime initial (start + 1) := by
      linarith
    have scaleConstantNonneg : 0 ≤ scaleConstant := by
      dsimp only [scaleConstant]
      positivity
    have productLe :
        scaleConstant *
            ((level + 2) ^ 3 *
              (elapsedTime initial (finish + 1) -
                elapsedTime initial (start + 1))) ≤
          scaleConstant *
            ((2 * level) ^ 3 *
              (elapsedTime initial (finish + 1) -
                elapsedTime initial (start + 1))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right cubeLe spanNonneg)
        scaleConstantNonneg
    have uncancelled := scaledClean.trans productLe
    apply le_of_mul_le_mul_right _ levelPos
    calc
      (nu.coeff ^ 3 * (2 * Real.pi) ^ 2) * level =
          nu.coeff ^ 3 * (2 * Real.pi) ^ 2 * level := by
        ring
      _ ≤ scaleConstant *
            ((2 * level) ^ 3 *
              (elapsedTime initial (finish + 1) -
                elapsedTime initial (start + 1))) := uncancelled
      _ = ((72 * 1557504 * biotSavartSerrinConstant ^ 2) *
          (level ^ 2 *
            (elapsedTime initial (finish + 1) -
              elapsedTime initial (start + 1)))) * level := by
        dsimp only [scaleConstant]
        ring
  refine ⟨start, finish, startLtFinish, elapsedActionStartLtFinish,
    startMassLeHalf, finishSpec, inverseLevelPayment,
    actionInteriorMassLt, prehistoryCeiling, ?_, normalizedSpanPayment, ?_⟩
  · simpa only [cubicConstant] using cubicSpanPayment
  intro index indexMem localTime
  have indexBounds := Finset.mem_Ico.mp indexMem
  have actionStartLeIndex : start + 1 ≤ index + 1 := by omega
  have indexActionSuccLeFinish : index + 2 ≤ finish + 1 := by omega
  have absoluteLower :
      elapsedTime initial (start + 1) ≤
        elapsedTime initial (index + 1) + localTime.1 := by
    exact
      ((elapsedTime_strictMono initial).monotone
        actionStartLeIndex).trans
      (le_add_of_nonneg_right localTime.2.1)
  have absoluteUpper :
      elapsedTime initial (index + 1) + localTime.1 ≤
        elapsedTime initial (finish + 1) := by
    calc
      elapsedTime initial (index + 1) + localTime.1 ≤
          elapsedTime initial (index + 2) := by
        change
          elapsedTime initial (index + 1) + localTime.1 ≤
            elapsedTime initial (index + 1) +
              (run initial (index + 1)).contact.time.1
        simpa only [add_comm] using
          add_le_add_left localTime.2.2
            (elapsedTime initial (index + 1))
      _ ≤ elapsedTime initial (finish + 1) :=
        (elapsedTime_strictMono initial).monotone
          indexActionSuccLeFinish
  exact
    ⟨absoluteLower, absoluteUpper,
      wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_receipt_chart
        initial elapsedBounded (index + 1) localTime⟩

/-- The first actual contact reaching a source level retains a fixed nonlinear
payment after projecting every input to one source-selected finite cube.  The
same original whole receipts supply the mass ceiling, viscous absorption, and
chronological balance. -/
theorem sourceGeneratedNativeAccumulationFirstLevelActualPrefixFiniteInputOutputAction
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (level : Real)
    (levelPos : 0 < level)
    (initialLeHalf :
      restartPhysicalVorticityMass initial 0 ≤ level / 2) :
    ∃ finish radius : Nat,
      0 < finish ∧
      0 < radius ∧
      level ≤ restartPhysicalVorticityMass initial finish ∧
      restartPhysicalVorticityMass initial finish < level + 2 ∧
      (radius : Real) ≤
        (4368 * biotSavartSerrinConstant * (level + 2)) /
            (nu.coeff ^ 2 * (2 * Real.pi) ^ 2) + 2 ∧
      (∀ index, index ∈ Finset.range finish →
        ∀ᵐ localTime
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1),
          wholeVorticityEuclideanMass
              ((run initial index).nextContact.prefixReceipt.wholePath
                localTime) <
            level + 2) ∧
      nu.coeff * (level / 2) ≤
        2 * ∑ index ∈ Finset.range finish,
          ∫ localTime,
            ∑ output ∈
                finiteVorticityPairOutputSupport
                  (integerWaveFrequencyCube radius),
              (integerWaveViscousMultiplier output)⁻¹ *
                complexCoordinateAmplitudeSq
                  (wholeStateVorticityNonlinearCoefficientAt
                    (complexSharpSupportProjection
                      (integerWaveFrequencyCube radius)
                      ((run initial index).nextContact.prefixReceipt.wholePath
                        localTime))
                    output)
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1) := by
  have massUnbounded :=
    elapsedTime_bddAbove_forces_physicalVorticityMass_unbounded
      initial elapsedBounded
  have existsMassAbove :
      ∃ index : Nat,
        level ≤ restartPhysicalVorticityMass initial index := by
    by_contra noIndex
    push Not at noIndex
    apply massUnbounded
    refine ⟨level, ?_⟩
    rintro mass ⟨index, rfl⟩
    exact (noIndex index).le
  let finish : Nat := Nat.find existsMassAbove
  have finishSpec :
      level ≤ restartPhysicalVorticityMass initial finish :=
    Nat.find_spec existsMassAbove
  have finishPos : 0 < finish := by
    by_contra finishNotPos
    have finishZero : finish = 0 := Nat.eq_zero_of_not_pos finishNotPos
    rw [finishZero] at finishSpec
    linarith
  have priorMassLt :
      ∀ index, index ∈ Finset.range finish →
        restartPhysicalVorticityMass initial index < level := by
    intro index indexMem
    exact lt_of_not_ge
      (Nat.find_min existsMassAbove (Finset.mem_range.mp indexMem))
  have finishMassLt :
      restartPhysicalVorticityMass initial finish < level + 2 := by
    obtain ⟨prior, finishEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero finishPos.ne'
    have priorLtFinish : prior < finish := by omega
    have priorLt :
        restartPhysicalVorticityMass initial prior < level :=
      lt_of_not_ge (Nat.find_min existsMassAbove priorLtFinish)
    have massLe :=
      restartPhysicalVorticityMass_succ_le_ceiling initial prior
    rw [finishEq]
    unfold restartCoefficientCeiling wholeRestartCoefficientCeiling at massLe
    have priorNonneg :
        0 ≤ restartPhysicalVorticityMass initial prior := by
      unfold restartPhysicalVorticityMass wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _
    have ceilLt :=
      Nat.ceil_lt_add_one (add_nonneg priorNonneg zero_le_one)
    change
      restartPhysicalVorticityMass initial (prior + 1) ≤
        (Nat.ceil
          (restartPhysicalVorticityMass initial prior + 1) : Real)
      at massLe
    have ceilingLt :
        (Nat.ceil
          (restartPhysicalVorticityMass initial prior + 1) : Real) <
        restartPhysicalVorticityMass initial prior + 2 := by
      simpa only [add_assoc, one_add_one_eq_two] using ceilLt
    linarith
  have interiorMassLt :
      ∀ index, index ∈ Finset.range finish →
        ∀ᵐ localTime
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1),
          wholeVorticityEuclideanMass
              ((run initial index).nextContact.prefixReceipt.wholePath
                localTime) <
            level + 2 := by
    intro index indexMem
    have contactMassLt := priorMassLt index indexMem
    have contactMassNonneg :
        0 ≤ restartPhysicalVorticityMass initial index := by
      unfold restartPhysicalVorticityMass wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _
    have rawNonneg :
        0 ≤ wholeRestartRawCoefficientCeiling
          (run initial index).contact := by
      change
        0 ≤ wholeVorticityEuclideanMass
          (run initial index).contact.physicalState + 1
      exact add_nonneg contactMassNonneg zero_le_one
    have ceilingLtRaw := Nat.ceil_lt_add_one rawNonneg
    have ceilingLt :
        wholeRestartCoefficientCeiling (run initial index).contact <
          level + 2 := by
      unfold wholeRestartCoefficientCeiling
      change
        (Nat.ceil
          (wholeVorticityEuclideanMass
            (run initial index).contact.physicalState + 1) : Real) <
          level + 2
      change
        (Nat.ceil
          (wholeVorticityEuclideanMass
            (run initial index).contact.physicalState + 1) : Real) <
          wholeVorticityEuclideanMass
              (run initial index).contact.physicalState + 1 + 1
        at ceilingLtRaw
      unfold restartPhysicalVorticityMass at contactMassLt
      linarith
    have eventuallyFull :=
      generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
        (generatedWholeRestartCanonicalReplay
          (run initial index).contact)
    have onPrefixImage :
        ∀ᵐ localTime
            ∂((commonTimeMeasure
                (wholeRestartDuration (run initial index).contact)).restrict
              (Set.range
                (commonTimeInclusion
                  (run initial index).nextContact.time.2.2))),
          wholeVorticityEuclideanMass
              ((generatedWholeRestartWholeContinuousMildSerrinReceipt
                (generatedWholeRestartCanonicalReplay
                  (run initial index).contact)).wholePath localTime) ≤
            wholeRestartCoefficientCeiling
              (run initial index).contact :=
      MeasureTheory.ae_restrict_le eventuallyFull
    have pulledToPrefix :=
      (commonTimeInclusion_measurePreserving
          (run initial index).nextContact.time.2.2
        |>.quasiMeasurePreserving.tendsto_ae) onPrefixImage
    filter_upwards [pulledToPrefix] with localTime massLe
    have sourceMassLe :
        wholeVorticityEuclideanMass
            ((run initial index).nextContact.prefixReceipt.wholePath
              localTime) ≤
          wholeRestartCoefficientCeiling
            (run initial index).contact := by
      simpa [prefixReceipt, restrictWholeContinuousMildSerrinReceipt,
        GeneratedWholeRestartCurrent.nextReceipt] using massLe
    exact sourceMassLe.trans_lt ceilingLt
  let viscousConstant := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let numerator :=
    4368 * biotSavartSerrinConstant * (level + 2)
  let ratio := numerator / viscousConstant
  let radius := Nat.ceil ratio + 1
  have viscousConstantPos : 0 < viscousConstant := by
    unfold viscousConstant
    exact mul_pos
      (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
  have numeratorNonneg : 0 ≤ numerator := by
    unfold numerator
    exact mul_nonneg
      (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
      (by linarith)
  have ratioNonneg : 0 ≤ ratio :=
    div_nonneg numeratorNonneg viscousConstantPos.le
  have radiusPos : 0 < radius := by
    unfold radius
    omega
  have ratioLeRadius : ratio ≤ (radius : Real) := by
    calc
      ratio ≤ (Nat.ceil ratio : Real) := Nat.le_ceil ratio
      _ ≤ (radius : Real) := by
        have ceilLe : Nat.ceil ratio ≤ radius := by
          unfold radius
          omega
        exact_mod_cast ceilLe
  have radiusUpper : (radius : Real) ≤ ratio + 2 := by
    have ceilLt : (Nat.ceil ratio : Real) < ratio + 1 :=
      Nat.ceil_lt_add_one ratioNonneg
    unfold radius
    push_cast
    linarith
  have numeratorEq : numerator = ratio * viscousConstant := by
    unfold ratio
    field_simp [viscousConstantPos.ne']
  have radiusAbsorbs :
      4368 * biotSavartSerrinConstant * (level + 2) ≤
        (radius : Real) * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2) := by
    change numerator ≤ (radius : Real) * viscousConstant
    rw [numeratorEq]
    exact mul_le_mul_of_nonneg_right ratioLeRadius viscousConstantPos.le
  let finiteInputOutputPayment : Nat → Real := fun index =>
    ∫ localTime,
      ∑ output ∈
          finiteVorticityPairOutputSupport
            (integerWaveFrequencyCube radius),
        (integerWaveViscousMultiplier output)⁻¹ *
          complexCoordinateAmplitudeSq
            (wholeStateVorticityNonlinearCoefficientAt
              (complexSharpSupportProjection
                (integerWaveFrequencyCube radius)
                ((run initial index).nextContact.prefixReceipt.wholePath
                  localTime))
              output)
      ∂(commonTimeMeasure (run initial index).nextContact.time.1)
  have edgeEstimate
      (index : Nat)
      (indexMem : index ∈ Finset.range finish) :
      puncturedEuclideanSpaceTimeSquare
          (receiptNonlinearNegativeOneState
            (run initial index).nextContact.prefixReceipt) ≤
        puncturedEuclideanSpaceTimeSquare
            (receiptViscousNegativeOneState
              (run initial index).nextContact.prefixReceipt) +
          2 * finiteInputOutputPayment index := by
    have massBound :
        ∀ᵐ localTime
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1),
          wholeVorticityEuclideanMass
              ((run initial index).nextContact.prefixReceipt.wholePath
                localTime) ≤
            level + 2 :=
      (interiorMassLt index indexMem).mono fun _ massLt => massLt.le
    simpa only [finiteInputOutputPayment] using
      receiptNonlinearNegativeOneEuclideanSquare_le_viscous_add_two_finiteInputOutput
        (run initial index).nextContact.prefixReceipt radius radiusPos
        massBound radiusAbsorbs
  have aggregateEstimate :
      wholeRestartIcoNonlinearNegativeOneEuclideanPayment
            initial 0 finish ≤
        wholeRestartIcoViscousNegativeOneEuclideanPayment
              initial 0 finish +
          2 * ∑ index ∈ Finset.range finish,
            finiteInputOutputPayment index := by
    unfold wholeRestartIcoNonlinearNegativeOneEuclideanPayment
      wholeRestartIcoViscousNegativeOneEuclideanPayment
    rw [Nat.Ico_zero_eq_range]
    calc
      (∑ index ∈ Finset.range finish,
          puncturedEuclideanSpaceTimeSquare
            (receiptNonlinearNegativeOneState
              (run initial index).nextContact.prefixReceipt)) ≤
          ∑ index ∈ Finset.range finish,
            (puncturedEuclideanSpaceTimeSquare
                (receiptViscousNegativeOneState
                  (run initial index).nextContact.prefixReceipt) +
              2 * finiteInputOutputPayment index) :=
        Finset.sum_le_sum edgeEstimate
      _ =
          (∑ index ∈ Finset.range finish,
            puncturedEuclideanSpaceTimeSquare
              (receiptViscousNegativeOneState
                (run initial index).nextContact.prefixReceipt)) +
            2 * ∑ index ∈ Finset.range finish,
              finiteInputOutputPayment index := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have balance :=
    wholeRestartIcoNonlinearNegativeOneEuclideanPayment_balance
      initial 0 finish (Nat.zero_le finish)
  have tangentNonneg :
      0 ≤ wholeRestartIcoTangentNegativeOneEuclideanPayment
        initial 0 finish := by
    unfold wholeRestartIcoTangentNegativeOneEuclideanPayment
    exact Finset.sum_nonneg fun _index _indexMem => sq_nonneg _
  have incrementPayment :
      nu.coeff *
          (restartPhysicalVorticityMass initial finish -
            restartPhysicalVorticityMass initial 0) ≤
        2 * ∑ index ∈ Finset.range finish,
          finiteInputOutputPayment index := by
    change
      wholeRestartIcoNonlinearNegativeOneEuclideanPayment
            initial 0 finish +
          nu.coeff * restartPhysicalVorticityMass initial 0 =
        wholeRestartIcoTangentNegativeOneEuclideanPayment
              initial 0 finish +
            wholeRestartIcoViscousNegativeOneEuclideanPayment
              initial 0 finish +
          nu.coeff * restartPhysicalVorticityMass initial finish
      at balance
    nlinarith
  have massGain :
      level / 2 ≤
        restartPhysicalVorticityMass initial finish -
          restartPhysicalVorticityMass initial 0 := by
    linarith
  have finitePayment :
      nu.coeff * (level / 2) ≤
        2 * ∑ index ∈ Finset.range finish,
          finiteInputOutputPayment index :=
    (mul_le_mul_of_nonneg_left massGain nu.coeff_pos.le).trans
      incrementPayment
  refine ⟨finish, radius, finishPos, radiusPos, finishSpec,
    finishMassLt, ?_, interiorMassLt, ?_⟩
  · simpa only [ratio, numerator, viscousConstant] using radiusUpper
  · simpa only [finiteInputOutputPayment] using finitePayment

theorem continuous_wholeVorticityEuclideanMass :
    Continuous wholeVorticityEuclideanMass := by
  have functionalEq :
      wholeVorticityEuclideanMass =
        fun state : ComplexVorticityHilbertState =>
          ∑ coordinate : Coordinate,
            ‖wholeStateCoordinateSliceCLM coordinate state‖ ^ 2 := by
    funext state
    exact wholeVorticityEuclideanMass_eq_coordinateSlices state
  rw [functionalEq]
  fun_prop

private theorem continuous_first_last_level_window
    {a b level : Real}
    (aLeB : a ≤ b)
    (levelPos : 0 < level)
    (mass : Real → Real)
    (massContinuous : ContinuousOn mass (Icc a b))
    (massStart : mass a ≤ level / 2)
    (massFinish : level ≤ mass b) :
    ∃ start finish : Real,
      start ∈ Icc a b ∧
      finish ∈ Icc a b ∧
      start < finish ∧
      mass start = level / 2 ∧
      mass finish = level ∧
      ∀ time ∈ Icc start finish,
        level / 2 ≤ mass time ∧ mass time ≤ level := by
  let highSet : Set Real := Icc a b ∩ mass ⁻¹' Ici level
  have highCompact : IsCompact highSet := by
    dsimp only [highSet]
    exact massContinuous.upperSemicontinuousOn.isCompact_inter_preimage_Ici
      isCompact_Icc level
  have bHigh : b ∈ highSet := ⟨⟨aLeB, le_rfl⟩, massFinish⟩
  obtain ⟨finish, finishHigh, finishFirst⟩ :=
    highCompact.exists_isMinOn (f := id) ⟨b, bHigh⟩
      continuous_id.continuousOn
  have finishMem : finish ∈ Icc a b := finishHigh.1
  have finishMassGe : level ≤ mass finish := finishHigh.2
  have finishMassEq : mass finish = level := by
    apply le_antisymm
    · by_contra massGt
      have levelLtFinish : level < mass finish := lt_of_not_ge massGt
      have halfLeFinish : level / 2 ≤ mass finish :=
        (by linarith [levelPos] : level / 2 ≤ level).trans finishMassGe
      obtain ⟨earlier, earlierMem, earlierMassEq⟩ :=
        intermediate_value_Icc
          (a := a) (b := finish) finishMem.1
          (massContinuous.mono (Icc_subset_Icc_right finishMem.2))
          ⟨by linarith [levelPos], finishMassGe⟩
      have earlierHigh : earlier ∈ highSet := by
        exact ⟨⟨earlierMem.1, earlierMem.2.trans finishMem.2⟩,
          earlierMassEq.ge⟩
      have finishLeEarlier : finish ≤ earlier := finishFirst earlierHigh
      have earlierEqFinish : earlier = finish :=
        le_antisymm earlierMem.2 finishLeEarlier
      subst earlier
      exact (ne_of_gt levelLtFinish) earlierMassEq
    · exact finishMassGe
  let lowSet : Set Real := Icc a finish ∩ mass ⁻¹' Iic (level / 2)
  have lowCompact : IsCompact lowSet := by
    dsimp only [lowSet]
    exact
      (massContinuous.lowerSemicontinuousOn.mono
        (Icc_subset_Icc_right finishMem.2)).isCompact_inter_preimage_Iic
          isCompact_Icc (level / 2)
  have aLow : a ∈ lowSet := ⟨⟨le_rfl, finishMem.1⟩, massStart⟩
  obtain ⟨start, startLow, startLast⟩ :=
    lowCompact.exists_isMaxOn (f := id) ⟨a, aLow⟩
      continuous_id.continuousOn
  have startMemSmall : start ∈ Icc a finish := startLow.1
  have startMem : start ∈ Icc a b :=
    ⟨startMemSmall.1, startMemSmall.2.trans finishMem.2⟩
  have startMassLe : mass start ≤ level / 2 := startLow.2
  have startMassEq : mass start = level / 2 := by
    apply le_antisymm startMassLe
    by_contra massLt
    have startLtHalf : mass start < level / 2 := lt_of_not_ge massLt
    have halfLeFinish : level / 2 ≤ mass finish := by
      rw [finishMassEq]
      linarith [levelPos]
    obtain ⟨later, laterMem, laterMassEq⟩ :=
      intermediate_value_Icc
        startMemSmall.2
        (massContinuous.mono
          (Icc_subset_Icc startMemSmall.1 finishMem.2))
        ⟨startMassLe, halfLeFinish⟩
    have laterLow : later ∈ lowSet := by
      exact ⟨⟨startMemSmall.1.trans laterMem.1, laterMem.2⟩,
        laterMassEq.le⟩
    have laterLeStart : later ≤ start := startLast laterLow
    have laterEqStart : later = start :=
      le_antisymm laterLeStart laterMem.1
    subst later
    exact (ne_of_lt startLtHalf) laterMassEq
  have startLtFinish : start < finish := by
    have massLt : mass start < mass finish := by
      rw [startMassEq, finishMassEq]
      linarith [levelPos]
    exact lt_of_le_of_ne startMemSmall.2 (fun eq => by subst finish; exact (ne_of_lt massLt) rfl)
  refine ⟨start, finish, startMem, finishMem, startLtFinish,
    startMassEq, finishMassEq, ?_⟩
  intro time timeMem
  constructor
  · by_contra below
    have timeLow : time ∈ lowSet := by
      refine ⟨⟨startMemSmall.1.trans timeMem.1, timeMem.2⟩, ?_⟩
      exact (lt_of_not_ge below).le
    have timeLeStart : time ≤ start := startLast timeLow
    have timeEqStart : time = start := le_antisymm timeLeStart timeMem.1
    subst time
    exact below startMassEq.ge
  · by_contra above
    have timeHigh : time ∈ highSet := by
      refine ⟨⟨startMem.1.trans timeMem.1,
        timeMem.2.trans finishMem.2⟩, ?_⟩
      exact (lt_of_not_ge above).le
    have finishLeTime : finish ≤ time := finishFirst timeHigh
    have timeEqFinish : time = finish := le_antisymm timeMem.2 finishLeTime
    subst time
    exact above finishMassEq.le

private theorem actualPrefix_lastHit_vorticityMass_window
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (level : Real)
    (levelPos : 0 < level)
    (start finish : Nat)
    (startLtFinish : start < finish)
    (startMass : restartPhysicalVorticityMass initial start ≤ level / 2)
    (finishMass : level ≤ restartPhysicalVorticityMass initial finish) :
    ∃ beginTime endTime : Real,
      beginTime ∈
        Icc (elapsedTime initial (start + 1))
          (elapsedTime initial (finish + 1)) ∧
      endTime ∈
        Icc (elapsedTime initial (start + 1))
          (elapsedTime initial (finish + 1)) ∧
      beginTime < endTime ∧
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
            beginTime) = level / 2 ∧
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
            endTime) = level ∧
      ∀ time ∈ Icc beginTime endTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ≤ level := by
  let a := elapsedTime initial (start + 1)
  let b := elapsedTime initial (finish + 1)
  let mass : Real → Real := fun time =>
    wholeVorticityEuclideanMass
      (wholeRestartPrefixPhysicalTrajectory initial (finish + 1) time)
  have aNonneg : 0 ≤ a := by
    exact ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
      initial (start + 1)
  have aLeB : a ≤ b :=
    (elapsedTime_strictMono initial).monotone (by omega)
  have massContinuous : ContinuousOn mass (Icc a b) := by
    apply continuous_wholeVorticityEuclideanMass.comp_continuousOn
    exact
      (wholeRestartPrefixPhysicalTrajectory_continuousOn
        initial (finish + 1)).mono
          (Icc_subset_Icc aNonneg le_rfl)
  have massA : mass a = restartPhysicalVorticityMass initial start := by
    dsimp only [mass, a]
    rw [wholeRestartPrefixPhysicalTrajectory_eq_of_le initial
        (show start + 1 ≤ finish + 1 by omega) le_rfl,
      wholeRestartPrefixPhysicalTrajectory_endpoint]
    simp only [restartPhysicalVorticityMass, run_succ,
      GeneratedWholeRestartCurrent.next]
  have massB : mass b = restartPhysicalVorticityMass initial finish := by
    dsimp only [mass, b]
    rw [wholeRestartPrefixPhysicalTrajectory_endpoint]
    simp only [restartPhysicalVorticityMass, run_succ,
      GeneratedWholeRestartCurrent.next]
  obtain ⟨beginTime, endTime, beginMem, endMem, beginLtEnd,
      beginMass, endMass, interior⟩ :=
    continuous_first_last_level_window aLeB levelPos mass massContinuous
      (massA.trans_le startMass) (finishMass.trans_eq massB.symm)
  exact ⟨beginTime, endTime, beginMem, endMem, beginLtEnd,
    beginMass, endMass, interior⟩

private theorem receiptVorticityMass_increment_between_le_cubicPayment
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime start finish : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ requestedTime) :
    nu.coeff *
        (wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨finish, ⟨startNonneg.trans (startLtFinish.le), finishLe⟩⟩) -
          wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨start, ⟨startNonneg,
                startLtFinish.le.trans finishLe⟩⟩)) ≤
      ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
        ∫ time : Icc (0 : Real) (finish - start),
          wholeVorticityEuclideanMass
              (receipt.wholePath
                (commonTimeShift startNonneg
                  (startLtFinish.le.trans finishLe)
                  (commonTimeInclusion
                    (sub_le_sub_right finishLe start) time))) ^ 3
          ∂(commonTimeMeasure (finish - start)) := by
  have startLtRequested : start < requestedTime :=
    startLtFinish.trans_le finishLe
  let suffix :=
    positiveTimeSuffixWholeContinuousMildSerrinReceipt
      receipt start startNonneg startLtRequested
  have intervalPos : 0 < finish - start := sub_pos.mpr startLtFinish
  have intervalLe : finish - start ≤ requestedTime - start :=
    sub_le_sub_right finishLe start
  let intervalReceipt :=
    restrictWholeContinuousMildSerrinReceipt
      intervalPos intervalLe suffix
  have cubic :=
    receiptVorticityMass_increment_le_cubicPayment intervalReceipt
  have terminalEq :
      intervalReceipt.wholePath
          ⟨finish - start, ⟨intervalPos.le, le_rfl⟩⟩ =
        receipt.wholePath
          ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩ := by
    apply congrArg receipt.wholePath
    apply Subtype.ext
    simp [commonTimeInclusion_apply, commonTimeShift_apply]
  have pathEq
      (time : Icc (0 : Real) (finish - start)) :
      intervalReceipt.wholePath time =
        receipt.wholePath
          (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion intervalLe time)) := by
    rfl
  have integralEq :
      (∫ time : Icc (0 : Real) (finish - start),
          wholeVorticityEuclideanMass
              (intervalReceipt.wholePath time) ^ 3
          ∂(commonTimeMeasure (finish - start))) =
        ∫ time : Icc (0 : Real) (finish - start),
          wholeVorticityEuclideanMass
              (receipt.wholePath
                (commonTimeShift startNonneg
                  (startLtFinish.le.trans finishLe)
                  (commonTimeInclusion intervalLe time))) ^ 3
          ∂(commonTimeMeasure (finish - start)) := by
    apply integral_congr_ae
    filter_upwards [] with time
    rw [pathEq]
  rw [terminalEq, integralEq] at cubic
  simpa only [intervalReceipt, suffix,
    restrictWholeContinuousMildSerrinReceipt,
    positiveTimeSuffixWholeContinuousMildSerrinReceipt,
    wholeContinuousMildSerrinSuffixStartTime, add_zero] using cubic

private theorem receiptVorticityMass_increment_between_le_cubicCeiling
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime start finish ceiling : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ requestedTime)
    (massLe :
      ∀ time : Icc (0 : Real) requestedTime,
        start ≤ time.1 → time.1 ≤ finish →
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling) :
    nu.coeff *
        (wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩) -
          wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨start, ⟨startNonneg,
                startLtFinish.le.trans finishLe⟩⟩)) ≤
      ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
        (ceiling ^ 3 * (finish - start)) := by
  have intervalLe : finish - start ≤ requestedTime - start :=
    sub_le_sub_right finishLe start
  have cubic :=
    receiptVorticityMass_increment_between_le_cubicPayment
      receipt startNonneg startLtFinish finishLe
  have massCubeLe :
      ∀ time : Icc (0 : Real) (finish - start),
        wholeVorticityEuclideanMass
            (receipt.wholePath
              (commonTimeShift startNonneg
                (startLtFinish.le.trans finishLe)
                (commonTimeInclusion intervalLe time))) ^ 3 ≤
          ceiling ^ 3 := by
    intro time
    have shiftedLower :
        start ≤
          (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion intervalLe time)).1 := by
      simp only [commonTimeShift_apply, commonTimeInclusion_apply]
      linarith [time.2.1]
    have shiftedUpper :
        (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion intervalLe time)).1 ≤ finish := by
      simp only [commonTimeShift_apply, commonTimeInclusion_apply]
      linarith [time.2.2]
    exact pow_le_pow_left₀
      (by
        unfold wholeVorticityEuclideanMass
        exact tsum_nonneg fun wave => sq_nonneg _)
      (massLe _ shiftedLower shiftedUpper) 3
  have integrandIntegrable :
      Integrable
        (fun time : Icc (0 : Real) (finish - start) =>
          wholeVorticityEuclideanMass
              (receipt.wholePath
                (commonTimeShift startNonneg
                  (startLtFinish.le.trans finishLe)
                  (commonTimeInclusion intervalLe time))) ^ 3)
        (commonTimeMeasure (finish - start)) := by
    have pathContinuous :
        Continuous fun time : Icc (0 : Real) (finish - start) =>
          wholeVorticityEuclideanMass
            (receipt.wholePath
              (commonTimeShift startNonneg
                (startLtFinish.le.trans finishLe)
                (commonTimeInclusion intervalLe time))) := by
      exact (wholeReceiptVorticityMass_continuous receipt).comp
        ((commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)).continuous.comp
          (commonTimeInclusion intervalLe).continuous)
    change Integrable
      ((fun time : Icc (0 : Real) (finish - start) =>
          wholeVorticityEuclideanMass
            (receipt.wholePath
              (commonTimeShift startNonneg
                (startLtFinish.le.trans finishLe)
                (commonTimeInclusion intervalLe time)))) ^ 3)
      (commonTimeMeasure (finish - start))
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (pathContinuous.pow 3).continuousOn)
  have integralLe :
      (∫ time : Icc (0 : Real) (finish - start),
          wholeVorticityEuclideanMass
              (receipt.wholePath
                (commonTimeShift startNonneg
                  (startLtFinish.le.trans finishLe)
                  (commonTimeInclusion intervalLe time))) ^ 3
          ∂(commonTimeMeasure (finish - start))) ≤
        ceiling ^ 3 * (finish - start) := by
    calc
      (∫ time : Icc (0 : Real) (finish - start),
          wholeVorticityEuclideanMass
              (receipt.wholePath
                (commonTimeShift startNonneg
                  (startLtFinish.le.trans finishLe)
                  (commonTimeInclusion intervalLe time))) ^ 3
          ∂(commonTimeMeasure (finish - start))) ≤
          ∫ _time : Icc (0 : Real) (finish - start), ceiling ^ 3
            ∂(commonTimeMeasure (finish - start)) := by
        apply integral_mono
        · exact integrandIntegrable
        · exact integrable_const _
        · exact massCubeLe
      _ = ceiling ^ 3 * (finish - start) := by
        change
          (∫ time : Icc (0 : Real) (finish - start),
              (fun _ : Real => ceiling ^ 3) time.1
              ∂(commonTimeMeasure (finish - start))) = _
        rw [commonTime_integral_eq_intervalIntegral
          (finish - start) (sub_nonneg.mpr startLtFinish.le)
          (fun _ : Real => ceiling ^ 3)]
        simp
        ring
  have constantNonneg :
      0 ≤
        (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) := by
    positivity
  exact cubic.trans
    (mul_le_mul_of_nonneg_left integralLe constantNonneg)

private theorem wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (localTime :
      Icc (0 : Real) (run initial index).contact.time.1) :
    wholeRestartPrefixPhysicalTrajectory initial (index + 1)
        (elapsedTime initial index + localTime.1) =
      (run initial index).contact.prefixReceipt.wholePath localTime := by
  by_cases localZero : localTime.1 = 0
  · have absoluteLe :
        elapsedTime initial index + localTime.1 ≤
          elapsedTime initial index := by
      rw [localZero, add_zero]
    rw [wholeRestartPrefixPhysicalTrajectory,
      ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice.endpointSplice_of_le
        _ _ _ _ absoluteLe,
      localZero, add_zero,
      wholeRestartPrefixPhysicalTrajectory_endpoint]
    change
      (run initial index).initialState =
        (run initial index).contact.prefixReceipt.wholePath localTime
    calc
      (run initial index).initialState =
          (run initial index).contact.prefixReceipt.wholePath
            ⟨0, ⟨le_rfl,
              (run initial index).contact.time_pos.le⟩⟩ :=
        (run initial index).contact.prefixReceipt.wholePath_initial.symm
      _ = (run initial index).contact.prefixReceipt.wholePath localTime := by
        apply congrArg _
        apply Subtype.ext
        exact localZero.symm
  · have localPos : 0 < localTime.1 :=
      lt_of_le_of_ne localTime.2.1 (Ne.symm localZero)
    rw [wholeRestartPrefixPhysicalTrajectory,
      ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice.endpointSplice_of_lt
        _ _ _ _ (by linarith)]
    unfold wholeRestartReceiptPhysicalTrajectory
    have localArg :
        elapsedTime initial index + localTime.1 -
            elapsedTime initial index = localTime.1 := by
      ring
    rw [localArg]
    rw [projIcc_of_mem
      (run initial index).contact.time_pos.le localTime.2]

private def wholeStateVorticityNonlinearNegativeOneEuclideanDensity
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : Real :=
  (integerWaveViscousMultiplier output)⁻¹ *
    complexCoordinateAmplitudeSq
      (wholeStateVorticityNonlinearCoefficientAt state output)

private def wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
    (radius : Nat)
    (state : ComplexVorticityHilbertState) : Real :=
  ∑ output ∈ integerWaveFrequencyCube (2 * radius),
    wholeStateVorticityNonlinearNegativeOneEuclideanDensity state output

private theorem actualPairAggregateNegativeOneDensity_eq_stateEuclidean
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (output : IntegerWavevector) :
    actualWholeContinuousPairAggregateNegativeOneDensity
        receipt time output =
      wholeStateVorticityNonlinearNegativeOneEuclideanDensity
        (receipt.wholePath time) output := by
  unfold actualWholeContinuousPairAggregateNegativeOneDensity
    wholeStateVorticityNonlinearNegativeOneEuclideanDensity
  rw [tsum_actualWholeContinuousPairVector_eq_nonlinearOutput]

private theorem receiptVorticityMass_increment_between_le_lowOutputPayment
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime start finish ceiling : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ requestedTime)
    (radius : Nat)
    (radiusPos : 0 < radius)
    (massLe :
      ∀ time : Icc (0 : Real) requestedTime,
        start ≤ time.1 → time.1 ≤ finish →
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling)
    (radiusAbsorbs :
      4368 * biotSavartSerrinConstant * ceiling ≤
        (radius : Real) * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) :
    nu.coeff *
        (wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩) -
          wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨start, ⟨startNonneg,
                startLtFinish.le.trans finishLe⟩⟩)) ≤
      ∫ time in start..finish,
        wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
          radius (wholeRestartReceiptPhysicalTrajectory receipt time) := by
  have startLtRequested : start < requestedTime :=
    startLtFinish.trans_le finishLe
  let suffix :=
    positiveTimeSuffixWholeContinuousMildSerrinReceipt
      receipt start startNonneg startLtRequested
  have intervalPos : 0 < finish - start := sub_pos.mpr startLtFinish
  have intervalLe : finish - start ≤ requestedTime - start :=
    sub_le_sub_right finishLe start
  let intervalReceipt :=
    restrictWholeContinuousMildSerrinReceipt
      intervalPos intervalLe suffix
  have intervalMassLe :
      ∀ time : Icc (0 : Real) (finish - start),
        wholeVorticityEuclideanMass
            (intervalReceipt.wholePath time) ≤ ceiling := by
    intro time
    have shiftedLower :
        start ≤
          (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion intervalLe time)).1 := by
      simp only [commonTimeShift_apply, commonTimeInclusion_apply]
      linarith [time.2.1]
    have shiftedUpper :
        (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion intervalLe time)).1 ≤ finish := by
      simp only [commonTimeShift_apply, commonTimeInclusion_apply]
      linarith [time.2.2]
    exact massLe _ shiftedLower shiftedUpper
  have localPayment :=
    receiptVorticityMass_increment_le_lowOutputPayment
      intervalReceipt ceiling radius radiusPos intervalMassLe radiusAbsorbs
  have terminalEq :
      intervalReceipt.wholePath
          ⟨finish - start, ⟨intervalPos.le, le_rfl⟩⟩ =
        receipt.wholePath
          ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩ := by
    apply congrArg receipt.wholePath
    apply Subtype.ext
    simp [commonTimeInclusion_apply, commonTimeShift_apply]
  have localPairEq
      (time : Icc (0 : Real) (finish - start)) :
      (∑ output ∈ integerWaveFrequencyCube (2 * radius),
          actualWholeContinuousPairAggregateNegativeOneDensity
            intervalReceipt time output) =
        wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
          radius (intervalReceipt.wholePath time) := by
    unfold wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
    apply Finset.sum_congr rfl
    intro output _outputMem
    exact actualPairAggregateNegativeOneDensity_eq_stateEuclidean
      intervalReceipt time output
  have localIntegralEq :
      (∫ time,
          ∑ output ∈ integerWaveFrequencyCube (2 * radius),
            actualWholeContinuousPairAggregateNegativeOneDensity
              intervalReceipt time output
          ∂(commonTimeMeasure (finish - start))) =
        ∫ time in start..finish,
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
            radius (wholeRestartReceiptPhysicalTrajectory receipt time) := by
    rw [show
      (∫ time,
          ∑ output ∈ integerWaveFrequencyCube (2 * radius),
            actualWholeContinuousPairAggregateNegativeOneDensity
              intervalReceipt time output
          ∂(commonTimeMeasure (finish - start))) =
        ∫ time,
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
            radius (intervalReceipt.wholePath time)
          ∂(commonTimeMeasure (finish - start)) by
        apply integral_congr_ae
        filter_upwards [] with time
        exact localPairEq time]
    rw [show
      (∫ time,
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
            radius (intervalReceipt.wholePath time)
          ∂(commonTimeMeasure (finish - start))) =
        ∫ time in (0 : Real)..(finish - start),
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
            radius (wholeRestartReceiptPhysicalTrajectory intervalReceipt time) by
        rw [← commonTime_integral_eq_intervalIntegral
          (finish - start) intervalPos.le]
        apply integral_congr_ae
        filter_upwards [] with time
        unfold wholeRestartReceiptPhysicalTrajectory
        rw [projIcc_of_mem intervalPos.le time.2]
      ]
    calc
      (∫ time in (0 : Real)..(finish - start),
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
            radius (wholeRestartReceiptPhysicalTrajectory intervalReceipt time)) =
          ∫ time in (0 : Real)..(finish - start),
            wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
              radius
                (wholeRestartReceiptPhysicalTrajectory receipt (start + time)) := by
        apply intervalIntegral.integral_congr
        intro time timeMem
        have timeIcc : time ∈ Icc (0 : Real) (finish - start) := by
          simpa [uIcc_of_le intervalPos.le] using timeMem
        unfold wholeRestartReceiptPhysicalTrajectory
        change
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
              radius
                (intervalReceipt.wholePath
                  (projIcc 0 (finish - start)
                    intervalReceipt.requestedTimePos.le time)) =
            wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
              radius
                (receipt.wholePath
                  (projIcc 0 requestedTime receipt.requestedTimePos.le
                    (start + time)))
        rw [projIcc_of_mem intervalReceipt.requestedTimePos.le timeIcc,
          projIcc_of_mem receipt.requestedTimePos.le
            (show start + time ∈ Icc (0 : Real) requestedTime by
              exact ⟨add_nonneg startNonneg timeIcc.1, by linarith [timeIcc.2]⟩)]
        change
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
              radius (intervalReceipt.wholePath ⟨time, timeIcc⟩) =
            wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
              radius (receipt.wholePath ⟨start + time, _⟩)
        rfl
      _ = ∫ time in start..finish,
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
            radius (wholeRestartReceiptPhysicalTrajectory receipt time) := by
        have shifted :=
          intervalIntegral.integral_comp_add_left
            (f := fun time : Real =>
              wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                radius (wholeRestartReceiptPhysicalTrajectory receipt time))
            (a := 0) (b := finish - start) start
        convert shifted using 1
        ring_nf
  rw [terminalEq, localIntegralEq] at localPayment
  simpa only [intervalReceipt, suffix,
    restrictWholeContinuousMildSerrinReceipt,
    positiveTimeSuffixWholeContinuousMildSerrinReceipt,
    wholeContinuousMildSerrinSuffixStartTime, add_zero] using localPayment

private theorem wholeRestartReceiptPhysicalTrajectory_transverse
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Real) :
    WholeStateTransverse
      (wholeRestartReceiptPhysicalTrajectory receipt time) := by
  unfold wholeRestartReceiptPhysicalTrajectory
  exact wholePath_transverse receipt _

theorem wholeRestartPrefixPhysicalTrajectory_transverse
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ (length : Nat) (time : Real),
      WholeStateTransverse
        (wholeRestartPrefixPhysicalTrajectory initial length time)
  | 0, time => by
      rw [wholeRestartPrefixPhysicalTrajectory_zero]
      have initialTransverse :=
        wholePath_transverse initial.receipt
          ⟨0, ⟨le_rfl, initial.receipt.requestedTimePos.le⟩⟩
      simpa only [initial.receipt.wholePath_initial] using initialTransverse
  | length + 1, time => by
      by_cases timeLe : time ≤ elapsedTime initial length
      · rw [wholeRestartPrefixPhysicalTrajectory,
          endpointSplice_of_le _ _ _ _ timeLe]
        exact wholeRestartPrefixPhysicalTrajectory_transverse initial length time
      · have timeGt : elapsedTime initial length < time := lt_of_not_ge timeLe
        rw [wholeRestartPrefixPhysicalTrajectory,
          endpointSplice_of_lt _ _ _ _ timeGt]
        exact wholeRestartReceiptPhysicalTrajectory_transverse
          (run initial length).contact.prefixReceipt _

private theorem receipt_physicalWeakRow_between_eq_boundary
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime start finish : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (test : Real → Complex)
    (testSmooth : ContDiff Real ∞ test) :
    (∫ time in start..finish,
        deriv test time •
          wholeRestartReceiptPhysicalTrajectory receipt time wave) +
      (∫ time in start..finish,
        test time •
          wholeStateVorticityNonlinearCoefficientAt
            (wholeRestartReceiptPhysicalTrajectory receipt time) wave) -
      (∫ time in start..finish,
        test time •
          ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
            wholeRestartReceiptPhysicalTrajectory receipt time wave) =
      test finish •
          wholeRestartReceiptPhysicalTrajectory receipt finish wave -
        test start •
          wholeRestartReceiptPhysicalTrajectory receipt start wave := by
  have startLtRequested : start < requestedTime :=
    startLtFinish.trans_le finishLe
  let suffix := positiveTimeSuffixWholeContinuousMildSerrinReceipt
    receipt start startNonneg startLtRequested
  have durationPos : 0 < finish - start := sub_pos.mpr startLtFinish
  have durationLe : finish - start ≤ requestedTime - start :=
    sub_le_sub_right finishLe start
  let window := restrictWholeContinuousMildSerrinReceipt
    durationPos durationLe suffix
  let shiftedTest : Real → Complex := fun localTime => test (start + localTime)
  have shiftedTestSmooth : ContDiff Real ∞ shiftedTest := by
    dsimp only [shiftedTest]
    exact testSmooth.comp (contDiff_const.add contDiff_id)
  have localBoundary :=
    WholeContinuousMildSerrinReceipt.fixedWavePhysicalPathWeakAction_eq_boundary
      window wave waveNe shiftedTest shiftedTestSmooth
  have windowChart
      (localTime : Real) (localTimeMem : localTime ∈ Icc (0 : Real) (finish - start)) :
      wholeRestartReceiptPhysicalTrajectory window localTime =
        wholeRestartReceiptPhysicalTrajectory receipt (start + localTime) := by
    unfold wholeRestartReceiptPhysicalTrajectory
    have absoluteMem : start + localTime ∈ Icc (0 : Real) requestedTime := by
      constructor
      · exact add_nonneg startNonneg localTimeMem.1
      · linarith [localTimeMem.2]
    rw [projIcc_of_mem window.requestedTimePos.le localTimeMem,
      projIcc_of_mem receipt.requestedTimePos.le absoluteMem]
    change
      window.wholePath ⟨localTime, localTimeMem⟩ =
        receipt.wholePath ⟨start + localTime, absoluteMem⟩
    rfl
  have shiftedDerivative (localTime : Real) :
      deriv shiftedTest localTime = deriv test (start + localTime) := by
    exact deriv_comp_const_add test start localTime
  have stateIntegralEq :
      (∫ localTime in (0 : Real)..(finish - start),
          deriv shiftedTest localTime •
            window.wholePath
              (projIcc 0 (finish - start) durationPos.le localTime) wave) =
        ∫ time in start..finish,
          deriv test time •
            wholeRestartReceiptPhysicalTrajectory receipt time wave := by
    calc
      _ = ∫ localTime in (0 : Real)..(finish - start),
          deriv test (start + localTime) •
            wholeRestartReceiptPhysicalTrajectory receipt (start + localTime) wave := by
        apply intervalIntegral.integral_congr
        intro localTime localTimeMem
        have localTimeIcc : localTime ∈ Icc (0 : Real) (finish - start) := by
          simpa [uIcc_of_le durationPos.le] using localTimeMem
        change
          deriv shiftedTest localTime •
              wholeRestartReceiptPhysicalTrajectory window localTime wave =
            deriv test (start + localTime) •
              wholeRestartReceiptPhysicalTrajectory receipt (start + localTime) wave
        rw [shiftedDerivative]
        exact congrArg
          (fun state : ComplexVorticityHilbertState =>
            deriv test (start + localTime) • state wave)
          (windowChart localTime localTimeIcc)
      _ = _ := by
        have shifted := intervalIntegral.integral_comp_add_left
          (f := fun time : Real =>
            deriv test time •
              wholeRestartReceiptPhysicalTrajectory receipt time wave)
          (a := 0) (b := finish - start) start
        convert shifted using 1 <;> ring_nf
  have nonlinearIntegralEq :
      (∫ localTime in (0 : Real)..(finish - start),
          shiftedTest localTime •
            wholeStateVorticityNonlinearCoefficientAt
              (window.wholePath
                (projIcc 0 (finish - start) durationPos.le localTime)) wave) =
        ∫ time in start..finish,
          test time •
            wholeStateVorticityNonlinearCoefficientAt
              (wholeRestartReceiptPhysicalTrajectory receipt time) wave := by
    calc
      _ = ∫ localTime in (0 : Real)..(finish - start),
          test (start + localTime) •
            wholeStateVorticityNonlinearCoefficientAt
              (wholeRestartReceiptPhysicalTrajectory receipt (start + localTime)) wave := by
        apply intervalIntegral.integral_congr
        intro localTime localTimeMem
        have localTimeIcc : localTime ∈ Icc (0 : Real) (finish - start) := by
          simpa [uIcc_of_le durationPos.le] using localTimeMem
        change
          shiftedTest localTime •
              wholeStateVorticityNonlinearCoefficientAt
                (wholeRestartReceiptPhysicalTrajectory window localTime) wave =
            test (start + localTime) •
              wholeStateVorticityNonlinearCoefficientAt
                (wholeRestartReceiptPhysicalTrajectory receipt (start + localTime)) wave
        dsimp only [shiftedTest]
        exact congrArg
          (fun state : ComplexVorticityHilbertState =>
            test (start + localTime) •
              wholeStateVorticityNonlinearCoefficientAt state wave)
          (windowChart localTime localTimeIcc)
      _ = _ := by
        have shifted := intervalIntegral.integral_comp_add_left
          (f := fun time : Real =>
            test time •
              wholeStateVorticityNonlinearCoefficientAt
                (wholeRestartReceiptPhysicalTrajectory receipt time) wave)
          (a := 0) (b := finish - start) start
        convert shifted using 1 <;> ring_nf
  have viscousIntegralEq :
      (∫ localTime in (0 : Real)..(finish - start),
          shiftedTest localTime •
            ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
              window.wholePath
                (projIcc 0 (finish - start) durationPos.le localTime) wave) =
        ∫ time in start..finish,
          test time •
            ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
              wholeRestartReceiptPhysicalTrajectory receipt time wave := by
    calc
      _ = ∫ localTime in (0 : Real)..(finish - start),
          test (start + localTime) •
            ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
              wholeRestartReceiptPhysicalTrajectory receipt (start + localTime) wave := by
        apply intervalIntegral.integral_congr
        intro localTime localTimeMem
        have localTimeIcc : localTime ∈ Icc (0 : Real) (finish - start) := by
          simpa [uIcc_of_le durationPos.le] using localTimeMem
        change
          shiftedTest localTime •
              ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                wholeRestartReceiptPhysicalTrajectory window localTime wave =
            test (start + localTime) •
              ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                wholeRestartReceiptPhysicalTrajectory receipt (start + localTime) wave
        dsimp only [shiftedTest]
        exact congrArg
          (fun state : ComplexVorticityHilbertState =>
            test (start + localTime) •
              ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                state wave)
          (windowChart localTime localTimeIcc)
      _ = _ := by
        have shifted := intervalIntegral.integral_comp_add_left
          (f := fun time : Real =>
            test time •
              ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                wholeRestartReceiptPhysicalTrajectory receipt time wave)
          (a := 0) (b := finish - start) start
        convert shifted using 1 <;> ring_nf
  have initialEq :
      window.wholePath ⟨0, le_rfl, durationPos.le⟩ =
        wholeRestartReceiptPhysicalTrajectory receipt start := by
    calc
      window.wholePath ⟨0, le_rfl, durationPos.le⟩ =
          suffix.wholePath
            (commonTimeInclusion durationLe ⟨0, le_rfl, durationPos.le⟩) := rfl
      _ = receipt.wholePath
          (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion durationLe ⟨0, le_rfl, durationPos.le⟩)) := rfl
      _ = wholeRestartReceiptPhysicalTrajectory receipt start := by
        unfold wholeRestartReceiptPhysicalTrajectory
        apply congrArg receipt.wholePath
        apply Subtype.ext
        simp [commonTimeShift_apply, commonTimeInclusion_apply,
          projIcc_of_mem receipt.requestedTimePos.le
            ⟨startNonneg, startLtFinish.le.trans finishLe⟩]
  have terminalEq :
      window.wholePath ⟨finish - start, durationPos.le, le_rfl⟩ =
        wholeRestartReceiptPhysicalTrajectory receipt finish := by
    calc
      window.wholePath ⟨finish - start, durationPos.le, le_rfl⟩ =
          suffix.wholePath
            (commonTimeInclusion durationLe
              ⟨finish - start, durationPos.le, le_rfl⟩) := rfl
      _ = receipt.wholePath
          (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion durationLe
              ⟨finish - start, durationPos.le, le_rfl⟩)) := rfl
      _ = wholeRestartReceiptPhysicalTrajectory receipt finish := by
        unfold wholeRestartReceiptPhysicalTrajectory
        apply congrArg receipt.wholePath
        apply Subtype.ext
        simp [commonTimeShift_apply, commonTimeInclusion_apply,
          projIcc_of_mem receipt.requestedTimePos.le
            ⟨startNonneg.trans startLtFinish.le, finishLe⟩]
  rw [stateIntegralEq, nonlinearIntegralEq, viscousIntegralEq,
    initialEq, terminalEq] at localBoundary
  dsimp only [shiftedTest] at localBoundary
  convert localBoundary using 1 <;> ring

theorem wholeRestartPrefix_physicalWeakRows_intervalIntegrable
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    {start finish : Real}
    (startNonneg : 0 ≤ start)
    (startLeFinish : start ≤ finish)
    (finishLe : finish ≤ elapsedTime initial length)
    (wave : IntegerWavevector)
    (test : Real → Complex)
    (testSmooth : ContDiff Real ∞ test) :
    IntervalIntegrable
        (fun time =>
          deriv test time •
            wholeRestartPrefixPhysicalTrajectory initial length time wave)
        volume start finish ∧
      IntervalIntegrable
        (fun time =>
          test time •
            wholeStateVorticityNonlinearCoefficientAt
              (wholeRestartPrefixPhysicalTrajectory initial length time) wave)
        volume start finish ∧
      IntervalIntegrable
        (fun time =>
          test time •
            ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
              wholeRestartPrefixPhysicalTrajectory initial length time wave)
        volume start finish := by
  let path : Real → ComplexVorticityHilbertState :=
    wholeRestartPrefixPhysicalTrajectory initial length
  have intervalSubset :
      Icc start finish ⊆ Icc (0 : Real) (elapsedTime initial length) :=
    Icc_subset_Icc startNonneg finishLe
  have pathContinuous :
      ContinuousOn path (Icc start finish) :=
    (wholeRestartPrefixPhysicalTrajectory_continuousOn initial length).mono
      intervalSubset
  have rowContinuous :
      ContinuousOn (fun time => path time wave) (Icc start finish) :=
    (lp.evalCLM Complex
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp_continuousOn pathContinuous
  have nonlinearContinuous :
      ContinuousOn
        (fun time =>
          wholeStateVorticityNonlinearCoefficientAt (path time) wave)
        (Icc start finish) :=
    wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
      path wave start finish pathContinuous
      (fun time _timeMem =>
        wholeRestartPrefixPhysicalTrajectory_transverse initial length time)
  have testContinuous : ContinuousOn test (Icc start finish) :=
    testSmooth.continuous.continuousOn
  have testDerivativeContinuous :
      ContinuousOn (deriv test) (Icc start finish) :=
    (testSmooth.continuous_deriv (by simp)).continuousOn
  have stateContinuous :
      ContinuousOn
        (fun time => deriv test time • path time wave)
        (Icc start finish) :=
    testDerivativeContinuous.smul rowContinuous
  have nonlinearTestContinuous :
      ContinuousOn
        (fun time =>
          test time •
            wholeStateVorticityNonlinearCoefficientAt (path time) wave)
        (Icc start finish) :=
    testContinuous.smul nonlinearContinuous
  have viscousRowContinuous :
      ContinuousOn
        (fun time =>
          ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
            path time wave)
        (Icc start finish) :=
    (show ContinuousOn
        (fun _ : Real =>
          ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex))
        (Icc start finish) from continuousOn_const).smul rowContinuous
  have viscousTestContinuous :
      ContinuousOn
        (fun time =>
          test time •
            ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
              path time wave)
        (Icc start finish) :=
    testContinuous.smul viscousRowContinuous
  exact
    ⟨ContinuousOn.intervalIntegrable_of_Icc startLeFinish stateContinuous,
      ContinuousOn.intervalIntegrable_of_Icc startLeFinish nonlinearTestContinuous,
      ContinuousOn.intervalIntegrable_of_Icc startLeFinish viscousTestContinuous⟩

private theorem receipt_physicalWeakRow_absolute_between_eq_boundary
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime joinTime start finish : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (joinLeStart : joinTime ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ joinTime + requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (test : Real → Complex)
    (testSmooth : ContDiff Real ∞ test) :
    (∫ time in start..finish,
        deriv test time •
          wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime) wave) +
      (∫ time in start..finish,
        test time •
          wholeStateVorticityNonlinearCoefficientAt
            (wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime)) wave) -
      (∫ time in start..finish,
        test time •
          ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
            wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime) wave) =
      test finish •
          wholeRestartReceiptPhysicalTrajectory receipt (finish - joinTime) wave -
        test start •
          wholeRestartReceiptPhysicalTrajectory receipt (start - joinTime) wave := by
  have localStartNonneg : 0 ≤ start - joinTime := sub_nonneg.mpr joinLeStart
  have localStartLtFinish : start - joinTime < finish - joinTime :=
    sub_lt_sub_right startLtFinish joinTime
  have localFinishLe : finish - joinTime ≤ requestedTime := by linarith
  let shiftedTest : Real → Complex := fun localTime => test (joinTime + localTime)
  have shiftedTestSmooth : ContDiff Real ∞ shiftedTest := by
    dsimp only [shiftedTest]
    exact testSmooth.comp (contDiff_const.add contDiff_id)
  have localBoundary :=
    receipt_physicalWeakRow_between_eq_boundary receipt
      localStartNonneg localStartLtFinish localFinishLe
      wave waveNe shiftedTest shiftedTestSmooth
  dsimp only [shiftedTest] at localBoundary
  simp_rw [deriv_comp_const_add] at localBoundary
  have stateShift := intervalIntegral.integral_comp_sub_right
    (f := fun localTime : Real =>
      deriv test (joinTime + localTime) •
        wholeRestartReceiptPhysicalTrajectory receipt localTime wave)
    (a := start) (b := finish) joinTime
  have nonlinearShift := intervalIntegral.integral_comp_sub_right
    (f := fun localTime : Real =>
      test (joinTime + localTime) •
        wholeStateVorticityNonlinearCoefficientAt
          (wholeRestartReceiptPhysicalTrajectory receipt localTime) wave)
    (a := start) (b := finish) joinTime
  have viscousShift := intervalIntegral.integral_comp_sub_right
    (f := fun localTime : Real =>
      test (joinTime + localTime) •
        ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
          wholeRestartReceiptPhysicalTrajectory receipt localTime wave)
    (a := start) (b := finish) joinTime
  rw [← stateShift, ← nonlinearShift, ← viscousShift] at localBoundary
  have addSub (time : Real) : joinTime + (time - joinTime) = time := by ring
  simp_rw [addSub] at localBoundary
  exact localBoundary

theorem wholeRestartPrefix_physicalWeakRow_eq_boundary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ (length : Nat) {start finish : Real},
      0 ≤ start →
      start < finish →
      finish ≤ elapsedTime initial length →
      (wave : IntegerWavevector) →
      wave ≠ 0 →
      (test : Real → Complex) →
      ContDiff Real ∞ test →
      (∫ time in start..finish,
          deriv test time •
            wholeRestartPrefixPhysicalTrajectory initial length time wave) +
        (∫ time in start..finish,
          test time •
            wholeStateVorticityNonlinearCoefficientAt
              (wholeRestartPrefixPhysicalTrajectory initial length time) wave) -
        (∫ time in start..finish,
          test time •
            ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
              wholeRestartPrefixPhysicalTrajectory initial length time wave) =
        test finish •
            wholeRestartPrefixPhysicalTrajectory initial length finish wave -
          test start •
            wholeRestartPrefixPhysicalTrajectory initial length start wave := by
  intro length
  induction length with
  | zero =>
      intro start finish startNonneg startLtFinish finishLe
        _wave _waveNe _test _testSmooth
      rw [elapsedTime_zero] at finishLe
      linarith
  | succ length ih =>
      intro start finish startNonneg startLtFinish finishLe
        wave waveNe test testSmooth
      let joinTime := elapsedTime initial length
      let receipt := (run initial length).contact.prefixReceipt
      have joinNonneg : 0 ≤ joinTime :=
        GeneratedWholeRestartCurrent.elapsedTime_nonneg initial length
      have finishLeExpanded :
          finish ≤ joinTime + (run initial length).contact.time.1 := by
        simpa only [joinTime, elapsedTime_succ] using finishLe
      have priorChart
          (time : Real) (timeLeJoin : time ≤ joinTime) :
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
            wholeRestartPrefixPhysicalTrajectory initial length time := by
        simp only [wholeRestartPrefixPhysicalTrajectory]
        exact endpointSplice_of_le
          joinTime
          (wholeRestartPrefixPhysicalTrajectory initial length)
          (wholeRestartReceiptPhysicalTrajectory receipt)
          time timeLeJoin
      have receiptChart
          (time : Real) (joinLeTime : joinTime ≤ time)
          (timeLeExpanded :
            time ≤ joinTime + (run initial length).contact.time.1) :
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
            wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime) := by
        have localMem :
            time - joinTime ∈
              Icc (0 : Real) (run initial length).contact.time.1 :=
          ⟨sub_nonneg.mpr joinLeTime, by linarith⟩
        have chart :=
          wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
            initial length ⟨time - joinTime, localMem⟩
        have addLocal : joinTime + (time - joinTime) = time := by ring
        have prefixEq :
            wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
              receipt.wholePath ⟨time - joinTime, localMem⟩ := by
          simpa only [receipt, joinTime, addLocal] using chart
        calc
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
              receipt.wholePath ⟨time - joinTime, localMem⟩ := prefixEq
          _ = wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime) := by
            unfold wholeRestartReceiptPhysicalTrajectory
            apply congrArg receipt.wholePath
            apply Subtype.ext
            exact congrArg Subtype.val
              (projIcc_of_mem receipt.requestedTimePos.le localMem).symm
      by_cases finishLeJoin : finish ≤ joinTime
      · have prior := ih startNonneg startLtFinish finishLeJoin
          wave waveNe test testSmooth
        have pathEq (time : Real) (timeMem : time ∈ Icc start finish) :=
          priorChart time (timeMem.2.trans finishLeJoin)
        have stateIntegralEq :
            (∫ time in start..finish,
                deriv test time •
                  wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) =
              ∫ time in start..finish,
                deriv test time •
                  wholeRestartPrefixPhysicalTrajectory initial length time wave := by
          apply intervalIntegral.integral_congr
          intro time timeMem
          have timeIcc : time ∈ Icc start finish := by
            simpa [uIcc_of_le startLtFinish.le] using timeMem
          exact congrArg
            (fun state : ComplexVorticityHilbertState =>
              deriv test time • state wave)
            (pathEq time timeIcc)
        have nonlinearIntegralEq :
            (∫ time in start..finish,
                test time •
                  wholeStateVorticityNonlinearCoefficientAt
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1) time)
                    wave) =
              ∫ time in start..finish,
                test time •
                  wholeStateVorticityNonlinearCoefficientAt
                    (wholeRestartPrefixPhysicalTrajectory initial length time) wave := by
          apply intervalIntegral.integral_congr
          intro time timeMem
          have timeIcc : time ∈ Icc start finish := by
            simpa [uIcc_of_le startLtFinish.le] using timeMem
          exact congrArg
            (fun state : ComplexVorticityHilbertState =>
              test time • wholeStateVorticityNonlinearCoefficientAt state wave)
            (pathEq time timeIcc)
        have viscousIntegralEq :
            (∫ time in start..finish,
                test time •
                  ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) =
              ∫ time in start..finish,
                test time •
                  ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                    wholeRestartPrefixPhysicalTrajectory initial length time wave := by
          apply intervalIntegral.integral_congr
          intro time timeMem
          have timeIcc : time ∈ Icc start finish := by
            simpa [uIcc_of_le startLtFinish.le] using timeMem
          exact congrArg
            (fun state : ComplexVorticityHilbertState =>
              test time •
                ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                  state wave)
            (pathEq time timeIcc)
        rw [stateIntegralEq, nonlinearIntegralEq, viscousIntegralEq,
          priorChart finish finishLeJoin,
          priorChart start (startLtFinish.le.trans finishLeJoin)]
        exact prior
      · have joinLtFinish : joinTime < finish := lt_of_not_ge finishLeJoin
        by_cases startLtJoin : start < joinTime
        · have first := ih startNonneg startLtJoin le_rfl
            wave waveNe test testSmooth
          have second :=
            receipt_physicalWeakRow_absolute_between_eq_boundary
              receipt le_rfl joinLtFinish finishLeExpanded
              wave waveNe test testSmooth
          have receiptPathEq
              (time : Real) (timeMem : time ∈ Icc joinTime finish) :=
            receiptChart time timeMem.1 (timeMem.2.trans finishLeExpanded)
          have secondStateIntegralEq :
              (∫ time in joinTime..finish,
                  deriv test time •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) =
                ∫ time in joinTime..finish,
                  deriv test time •
                    wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime) wave := by
            apply intervalIntegral.integral_congr
            intro time timeMem
            have timeIcc : time ∈ Icc joinTime finish := by
              simpa [uIcc_of_le joinLtFinish.le] using timeMem
            exact congrArg
              (fun state : ComplexVorticityHilbertState =>
                deriv test time • state wave)
              (receiptPathEq time timeIcc)
          have secondNonlinearIntegralEq :
              (∫ time in joinTime..finish,
                  test time •
                    wholeStateVorticityNonlinearCoefficientAt
                      (wholeRestartPrefixPhysicalTrajectory initial (length + 1) time)
                      wave) =
                ∫ time in joinTime..finish,
                  test time •
                    wholeStateVorticityNonlinearCoefficientAt
                      (wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime))
                      wave := by
            apply intervalIntegral.integral_congr
            intro time timeMem
            have timeIcc : time ∈ Icc joinTime finish := by
              simpa [uIcc_of_le joinLtFinish.le] using timeMem
            exact congrArg
              (fun state : ComplexVorticityHilbertState =>
                test time • wholeStateVorticityNonlinearCoefficientAt state wave)
              (receiptPathEq time timeIcc)
          have secondViscousIntegralEq :
              (∫ time in joinTime..finish,
                  test time •
                    ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) =
                ∫ time in joinTime..finish,
                  test time •
                    ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                      wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime) wave := by
            apply intervalIntegral.integral_congr
            intro time timeMem
            have timeIcc : time ∈ Icc joinTime finish := by
              simpa [uIcc_of_le joinLtFinish.le] using timeMem
            exact congrArg
              (fun state : ComplexVorticityHilbertState =>
                test time •
                  ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                    state wave)
              (receiptPathEq time timeIcc)
          have secondGlobal :
              (∫ time in joinTime..finish,
                  deriv test time •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) +
                (∫ time in joinTime..finish,
                  test time •
                    wholeStateVorticityNonlinearCoefficientAt
                      (wholeRestartPrefixPhysicalTrajectory initial (length + 1) time)
                      wave) -
                (∫ time in joinTime..finish,
                  test time •
                    ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) =
                test finish •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) finish wave -
                  test joinTime •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) joinTime wave := by
            rw [secondStateIntegralEq, secondNonlinearIntegralEq,
              secondViscousIntegralEq,
              receiptChart finish joinLtFinish.le finishLeExpanded,
              receiptChart joinTime le_rfl (by linarith [receipt.requestedTimePos])]
            simpa only [sub_self] using second
          have firstGlobal :
              (∫ time in start..joinTime,
                  deriv test time •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) +
                (∫ time in start..joinTime,
                  test time •
                    wholeStateVorticityNonlinearCoefficientAt
                      (wholeRestartPrefixPhysicalTrajectory initial (length + 1) time)
                      wave) -
                (∫ time in start..joinTime,
                  test time •
                    ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) =
                test joinTime •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) joinTime wave -
                  test start •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) start wave := by
            rw [priorChart joinTime le_rfl,
              priorChart start startLtJoin.le]
            have firstStateEq :
                (∫ time in start..joinTime,
                    deriv test time •
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) =
                  ∫ time in start..joinTime,
                    deriv test time •
                      wholeRestartPrefixPhysicalTrajectory initial length time wave := by
              apply intervalIntegral.integral_congr
              intro time timeMem
              have timeIcc : time ∈ Icc start joinTime := by
                simpa [uIcc_of_le startLtJoin.le] using timeMem
              exact congrArg
                (fun state : ComplexVorticityHilbertState =>
                  deriv test time • state wave)
                (priorChart time timeIcc.2)
            have firstNonlinearEq :
                (∫ time in start..joinTime,
                    test time •
                      wholeStateVorticityNonlinearCoefficientAt
                        (wholeRestartPrefixPhysicalTrajectory initial (length + 1) time)
                        wave) =
                  ∫ time in start..joinTime,
                    test time •
                      wholeStateVorticityNonlinearCoefficientAt
                        (wholeRestartPrefixPhysicalTrajectory initial length time) wave := by
              apply intervalIntegral.integral_congr
              intro time timeMem
              have timeIcc : time ∈ Icc start joinTime := by
                simpa [uIcc_of_le startLtJoin.le] using timeMem
              exact congrArg
                (fun state : ComplexVorticityHilbertState =>
                  test time • wholeStateVorticityNonlinearCoefficientAt state wave)
                (priorChart time timeIcc.2)
            have firstViscousEq :
                (∫ time in start..joinTime,
                    test time •
                      ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                        wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) =
                  ∫ time in start..joinTime,
                    test time •
                      ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                        wholeRestartPrefixPhysicalTrajectory initial length time wave := by
              apply intervalIntegral.integral_congr
              intro time timeMem
              have timeIcc : time ∈ Icc start joinTime := by
                simpa [uIcc_of_le startLtJoin.le] using timeMem
              exact congrArg
                (fun state : ComplexVorticityHilbertState =>
                  test time •
                    ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                      state wave)
                (priorChart time timeIcc.2)
            rw [firstStateEq, firstNonlinearEq, firstViscousEq]
            exact first
          rcases wholeRestartPrefix_physicalWeakRows_intervalIntegrable
              initial (length + 1) startNonneg startLtJoin.le
                (joinLtFinish.le.trans finishLe) wave test testSmooth with
            ⟨firstStateIntegrable, firstNonlinearIntegrable,
              firstViscousIntegrable⟩
          rcases wholeRestartPrefix_physicalWeakRows_intervalIntegrable
              initial (length + 1) joinNonneg joinLtFinish.le finishLe
                wave test testSmooth with
            ⟨secondStateIntegrable, secondNonlinearIntegrable,
              secondViscousIntegrable⟩
          rw [← intervalIntegral.integral_add_adjacent_intervals
                firstStateIntegrable secondStateIntegrable,
              ← intervalIntegral.integral_add_adjacent_intervals
                firstNonlinearIntegrable secondNonlinearIntegrable,
              ← intervalIntegral.integral_add_adjacent_intervals
                firstViscousIntegrable secondViscousIntegrable]
          calc
            _ =
                ((∫ time in start..joinTime,
                    deriv test time •
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) +
                  (∫ time in start..joinTime,
                    test time •
                      wholeStateVorticityNonlinearCoefficientAt
                        (wholeRestartPrefixPhysicalTrajectory initial (length + 1) time)
                        wave) -
                  (∫ time in start..joinTime,
                    test time •
                      ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                        wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave)) +
                ((∫ time in joinTime..finish,
                    deriv test time •
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) +
                  (∫ time in joinTime..finish,
                    test time •
                      wholeStateVorticityNonlinearCoefficientAt
                        (wholeRestartPrefixPhysicalTrajectory initial (length + 1) time)
                        wave) -
                  (∫ time in joinTime..finish,
                    test time •
                      ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                        wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave)) := by
              abel
            _ =
                (test joinTime •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) joinTime wave -
                  test start •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) start wave) +
                (test finish •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) finish wave -
                  test joinTime •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) joinTime wave) := by
              rw [firstGlobal, secondGlobal]
            _ = _ := by abel
        · have joinLeStart : joinTime ≤ start := le_of_not_gt startLtJoin
          have receiptIdentity :=
            receipt_physicalWeakRow_absolute_between_eq_boundary
              receipt joinLeStart startLtFinish finishLeExpanded
              wave waveNe test testSmooth
          have pathEq (time : Real) (timeMem : time ∈ Icc start finish) :=
            receiptChart time (joinLeStart.trans timeMem.1)
              (timeMem.2.trans finishLeExpanded)
          have stateIntegralEq :
              (∫ time in start..finish,
                  deriv test time •
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) =
                ∫ time in start..finish,
                  deriv test time •
                    wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime) wave := by
            apply intervalIntegral.integral_congr
            intro time timeMem
            have timeIcc : time ∈ Icc start finish := by
              simpa [uIcc_of_le startLtFinish.le] using timeMem
            exact congrArg
              (fun state : ComplexVorticityHilbertState =>
                deriv test time • state wave)
              (pathEq time timeIcc)
          have nonlinearIntegralEq :
              (∫ time in start..finish,
                  test time •
                    wholeStateVorticityNonlinearCoefficientAt
                      (wholeRestartPrefixPhysicalTrajectory initial (length + 1) time)
                      wave) =
                ∫ time in start..finish,
                  test time •
                    wholeStateVorticityNonlinearCoefficientAt
                      (wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime))
                      wave := by
            apply intervalIntegral.integral_congr
            intro time timeMem
            have timeIcc : time ∈ Icc start finish := by
              simpa [uIcc_of_le startLtFinish.le] using timeMem
            exact congrArg
              (fun state : ComplexVorticityHilbertState =>
                test time • wholeStateVorticityNonlinearCoefficientAt state wave)
              (pathEq time timeIcc)
          have viscousIntegralEq :
              (∫ time in start..finish,
                  test time •
                    ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1) time wave) =
                ∫ time in start..finish,
                  test time •
                    ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                      wholeRestartReceiptPhysicalTrajectory receipt (time - joinTime) wave := by
            apply intervalIntegral.integral_congr
            intro time timeMem
            have timeIcc : time ∈ Icc start finish := by
              simpa [uIcc_of_le startLtFinish.le] using timeMem
            exact congrArg
              (fun state : ComplexVorticityHilbertState =>
                test time •
                  ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                    state wave)
              (pathEq time timeIcc)
          rw [stateIntegralEq, nonlinearIntegralEq, viscousIntegralEq,
            receiptChart finish (joinLeStart.trans startLtFinish.le)
              finishLeExpanded,
            receiptChart start joinLeStart
              (startLtFinish.le.trans finishLeExpanded)]
          exact receiptIdentity

theorem wholeRestartPrefix_finiteTrigonometricPhysicalWeakAction_eq_boundary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    {start finish : Real}
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ elapsedTime initial length)
    (testModes : Finset IntegerWavevector)
    (testModesZeroFree : ∀ wave ∈ testModes, wave ≠ 0)
    (testCoefficient : IntegerWavevector → ComplexCoordinateVector)
    (test : Real → Complex)
    (testSmooth : ContDiff Real ∞ test) :
    (∑ wave ∈ testModes,
      complexCoordinateRealInner (testCoefficient wave)
        ((∫ time in start..finish,
            deriv test time •
              wholeRestartPrefixPhysicalTrajectory initial length time wave) +
          (∫ time in start..finish,
            test time •
              wholeStateVorticityNonlinearCoefficientAt
                (wholeRestartPrefixPhysicalTrajectory initial length time) wave) -
          (∫ time in start..finish,
            test time •
              ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                wholeRestartPrefixPhysicalTrajectory initial length time wave))) =
      ∑ wave ∈ testModes,
        complexCoordinateRealInner (testCoefficient wave)
          (test finish •
              wholeRestartPrefixPhysicalTrajectory initial length finish wave -
            test start •
              wholeRestartPrefixPhysicalTrajectory initial length start wave) := by
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [wholeRestartPrefix_physicalWeakRow_eq_boundary
    initial length startNonneg startLtFinish finishLe
    wave (testModesZeroFree wave waveMem) test testSmooth]

theorem wholeRestartPrefix_scaledRecenteredTensorSchwartzWeakAction_eq_boundary
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length radius : Nat)
    {start finish : Real}
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ elapsedTime initial length)
    (spatialTest : Coordinate → 𝓢(ℝ, ℂ))
    (temporalTest : 𝓢(ℝ, ℂ))
    (scale : Real) (scaleNe : scale ≠ 0)
    (spaceCenter : PhysicalSpace)
    (timeCenter : Real)
    (testCoordinate : Coordinate) :
    let scaledTimeTest : Real → Complex := fun time =>
      temporalTest ((time - timeCenter) / scale ^ 2)
    let testCoefficient :
        IntegerWavevector → ComplexCoordinateVector := fun wave =>
      Pi.single testCoordinate
        (recenteredTensorSchwartzFourierCoefficient
          spatialTest scale scaleNe spaceCenter wave)
    (∑ wave ∈ puncturedIntegerWaveFrequencyCube radius,
      complexCoordinateRealInner (testCoefficient wave)
        ((∫ time in start..finish,
            deriv scaledTimeTest time •
              wholeRestartPrefixPhysicalTrajectory initial length time wave) +
          (∫ time in start..finish,
            scaledTimeTest time •
              wholeStateVorticityNonlinearCoefficientAt
                (wholeRestartPrefixPhysicalTrajectory initial length time) wave) -
          (∫ time in start..finish,
            scaledTimeTest time •
              ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
                wholeRestartPrefixPhysicalTrajectory initial length time wave))) =
      ∑ wave ∈ puncturedIntegerWaveFrequencyCube radius,
        complexCoordinateRealInner (testCoefficient wave)
          (scaledTimeTest finish •
              wholeRestartPrefixPhysicalTrajectory initial length finish wave -
            scaledTimeTest start •
              wholeRestartPrefixPhysicalTrajectory initial length start wave) := by
  dsimp only
  apply wholeRestartPrefix_finiteTrigonometricPhysicalWeakAction_eq_boundary
    initial length startNonneg startLtFinish finishLe
      (puncturedIntegerWaveFrequencyCube radius)
  · intro wave waveMem
    intro waveZero
    subst wave
    exact zero_not_mem_puncturedIntegerWaveFrequencyCube radius waveMem
  · fun_prop

private theorem wholeRestartPrefixLowOutputMass_continuousOn
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length radius : Nat) :
    ContinuousOn
      (fun time : Real =>
        wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
          radius
          (wholeRestartPrefixPhysicalTrajectory initial length time))
      (Icc 0 (elapsedTime initial length)) := by
  unfold wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
  apply continuousOn_finsetSum
  intro output _outputMem
  unfold wholeStateVorticityNonlinearNegativeOneEuclideanDensity
  apply ContinuousOn.mul continuousOn_const
  exact complexCoordinateAmplitudeSq_continuous.comp_continuousOn
    (wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
      (wholeRestartPrefixPhysicalTrajectory initial length) output
      0 (elapsedTime initial length)
      (wholeRestartPrefixPhysicalTrajectory_continuousOn initial length)
      (fun time _timeMem =>
        wholeRestartPrefixPhysicalTrajectory_transverse initial length time))

private theorem wholeRestartPrefixVorticityMass_increment_between_le_cubicCeiling
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ (length : Nat) {start finish ceiling : Real},
      0 ≤ start →
      start < finish →
      finish ≤ elapsedTime initial length →
      0 ≤ ceiling →
      (∀ time ∈ Icc start finish,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          ceiling) →
      nu.coeff *
          (wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length finish) -
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length start)) ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          (ceiling ^ 3 * (finish - start)) := by
  intro length
  induction length with
  | zero =>
      intro start finish ceiling startNonneg startLtFinish finishLe
        _ceilingNonneg _massLe
      rw [elapsedTime_zero] at finishLe
      linarith
  | succ length inductionHypothesis =>
      intro start finish ceiling startNonneg startLtFinish finishLe
        ceilingNonneg massLe
      let joinTime := elapsedTime initial length
      let receipt := (run initial length).contact.prefixReceipt
      have joinNonneg : 0 ≤ joinTime :=
        ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
          initial length
      have finishLeExpanded :
          finish ≤ joinTime + (run initial length).contact.time.1 := by
        simpa only [joinTime, elapsedTime_succ] using finishLe
      have priorChart
          (time : Real)
          (timeLeJoin : time ≤ joinTime) :
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
            wholeRestartPrefixPhysicalTrajectory initial length time := by
        simp only [wholeRestartPrefixPhysicalTrajectory]
        exact
          ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice.endpointSplice_of_le
            joinTime
            (wholeRestartPrefixPhysicalTrajectory initial length)
            (wholeRestartReceiptPhysicalTrajectory receipt)
            time timeLeJoin
      have receiptChart
          (time : Real)
          (joinLeTime : joinTime ≤ time)
          (timeLeFinish :
            time ≤ joinTime + (run initial length).contact.time.1) :
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
            receipt.wholePath
              ⟨time - joinTime,
                ⟨sub_nonneg.mpr joinLeTime,
                  by linarith⟩⟩ := by
        let localTime :
            Icc (0 : Real) (run initial length).contact.time.1 :=
          ⟨time - joinTime,
            ⟨sub_nonneg.mpr joinLeTime,
              by linarith⟩⟩
        have chart :=
          wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
            initial length localTime
        have addLocal : joinTime + localTime.1 = time := by
          dsimp only [joinTime, localTime]
          ring
        simpa only [receipt, joinTime, addLocal] using chart
      by_cases finishLeJoin : finish ≤ joinTime
      · have priorMassLe :
            ∀ time ∈ Icc start finish,
              wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
                ceiling := by
          intro time timeMem
          rw [← priorChart time (timeMem.2.trans finishLeJoin)]
          exact massLe time timeMem
        have prior :=
          inductionHypothesis startNonneg startLtFinish finishLeJoin
            ceilingNonneg priorMassLe
        rw [priorChart finish finishLeJoin,
          priorChart start (startLtFinish.le.trans finishLeJoin)]
        exact prior
      · have joinLtFinish : joinTime < finish := lt_of_not_ge finishLeJoin
        by_cases startLtJoin : start < joinTime
        · have firstMassLe :
              ∀ time ∈ Icc start joinTime,
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
                  ceiling := by
            intro time timeMem
            rw [← priorChart time timeMem.2]
            exact massLe time
              ⟨timeMem.1, timeMem.2.trans joinLtFinish.le⟩
          have first :=
            inductionHypothesis startNonneg startLtJoin le_rfl
              ceilingNonneg firstMassLe
          have localFinishPos : 0 < finish - joinTime :=
            sub_pos.mpr joinLtFinish
          have localFinishLe :
              finish - joinTime ≤ (run initial length).contact.time.1 :=
            by linarith
          have secondMassLe :
              ∀ time :
                  Icc (0 : Real) (run initial length).contact.time.1,
                0 ≤ time.1 → time.1 ≤ finish - joinTime →
                wholeVorticityEuclideanMass (receipt.wholePath time) ≤
                  ceiling := by
            intro time _timeNonneg timeLe
            have absoluteMem :
                joinTime + time.1 ∈ Icc start finish := by
              constructor
              · linarith [time.2.1]
              · linarith
            have chart :=
              wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
                initial length time
            have globalBound :
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                      (joinTime + time.1)) ≤ ceiling :=
              massLe _ absoluteMem
            rw [show joinTime = elapsedTime initial length by rfl] at globalBound
            rw [chart] at globalBound
            exact globalBound
          have second :=
            receiptVorticityMass_increment_between_le_cubicCeiling
              receipt (start := 0) (finish := finish - joinTime)
              (ceiling := ceiling) le_rfl localFinishPos localFinishLe
              secondMassLe
          have startEq :=
            priorChart start startLtJoin.le
          have joinPriorEq := priorChart joinTime le_rfl
          have joinReceiptEq := receiptChart joinTime le_rfl
            (by linarith [(run initial length).contact.time_pos])
          have finishReceiptEq := receiptChart finish joinLtFinish.le
            finishLeExpanded
          have firstGlobal :
              nu.coeff *
                  (wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) joinTime) -
                    wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) start)) ≤
                ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                  (ceiling ^ 3 * (joinTime - start)) := by
            simpa only [joinPriorEq, startEq] using first
          have secondGlobal :
              nu.coeff *
                  (wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) finish) -
                    wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) joinTime)) ≤
                ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                  (ceiling ^ 3 * (finish - joinTime)) := by
            rw [finishReceiptEq, joinReceiptEq]
            simpa only [receipt, sub_zero, sub_self] using second
          calc
            nu.coeff *
                (wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) finish) -
                  wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) start)) =
                nu.coeff *
                    (wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) joinTime) -
                      wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) start)) +
                  nu.coeff *
                    (wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) finish) -
                      wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) joinTime)) := by ring
            _ ≤
                ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                    (ceiling ^ 3 * (joinTime - start)) +
                  ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                    (ceiling ^ 3 * (finish - joinTime)) :=
              add_le_add firstGlobal secondGlobal
            _ =
                ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                  (ceiling ^ 3 * (finish - start)) := by ring
        · have joinLeStart : joinTime ≤ start := le_of_not_gt startLtJoin
          have localStartNonneg : 0 ≤ start - joinTime :=
            sub_nonneg.mpr joinLeStart
          have localStartLtFinish :
              start - joinTime < finish - joinTime :=
            sub_lt_sub_right startLtFinish joinTime
          have localFinishLe :
              finish - joinTime ≤ (run initial length).contact.time.1 :=
            by linarith
          have localMassLe :
              ∀ time :
                  Icc (0 : Real) (run initial length).contact.time.1,
                start - joinTime ≤ time.1 →
                time.1 ≤ finish - joinTime →
                wholeVorticityEuclideanMass (receipt.wholePath time) ≤
                  ceiling := by
            intro time startLeTime timeLeFinish
            have absoluteMem :
                joinTime + time.1 ∈ Icc start finish := by
              constructor <;> linarith
            have chart :=
              wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
                initial length time
            have globalBound :
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                      (joinTime + time.1)) ≤ ceiling :=
              massLe _ absoluteMem
            rw [show joinTime = elapsedTime initial length by rfl] at globalBound
            rw [chart] at globalBound
            exact globalBound
          have localEstimate :=
            receiptVorticityMass_increment_between_le_cubicCeiling
              receipt (start := start - joinTime)
              (finish := finish - joinTime) (ceiling := ceiling)
              localStartNonneg localStartLtFinish localFinishLe
              localMassLe
          have durationEq :
              finish - joinTime - (start - joinTime) = finish - start := by
            ring
          rw [durationEq] at localEstimate
          have startReceiptEq := receiptChart start joinLeStart
            (startLtFinish.le.trans finishLeExpanded)
          have finishReceiptEq := receiptChart finish joinLtFinish.le finishLeExpanded
          rw [finishReceiptEq, startReceiptEq]
          simpa only [receipt] using localEstimate

private theorem wholeRestartIcoTangentHalfViscous_add_boundary_le_cubicTime
    (initial : GeneratedWholeRestartCurrent nu)
    (start finish : Nat)
    (startLeFinish : start ≤ finish)
    (ceiling : Real)
    (massBound :
      ∀ index, index ∈ Finset.Ico start finish →
        ∀ᵐ localTime
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1),
          wholeVorticityEuclideanMass
              ((run initial index).nextContact.prefixReceipt.wholePath
                localTime) ≤ ceiling) :
    wholeRestartIcoTangentNegativeOneEuclideanPayment initial start finish +
        (1 / 2 : Real) *
          wholeRestartIcoViscousNegativeOneEuclideanPayment
            initial start finish +
        nu.coeff *
          (restartPhysicalVorticityMass initial finish -
            restartPhysicalVorticityMass initial start) ≤
      ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
        (ceiling ^ 3 *
          (elapsedTime initial (finish + 1) -
            elapsedTime initial (start + 1))) := by
  let cubicConstant : Real :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
  have edgeSigned
      (index : Nat)
      (indexMem : index ∈ Finset.Ico start finish) :
      puncturedEuclideanSpaceTimeSquare
            (run initial index).nextContact.prefixReceipt.wholeTangent +
          (1 / 2 : Real) *
            puncturedEuclideanSpaceTimeSquare
              (receiptViscousNegativeOneState
                (run initial index).nextContact.prefixReceipt) +
          nu.coeff *
            (restartPhysicalVorticityMass initial (index + 1) -
              restartPhysicalVorticityMass initial index) ≤
        cubicConstant *
          (ceiling ^ 3 *
            (run initial index).nextContact.time.1) := by
    have signed :=
      receipt_tangentHalfViscousSquare_add_boundary_le_cubicTime
        (run initial index).nextContact.prefixReceipt
        (massBound index indexMem)
    rw [(run initial index).nextContact_prefix_terminal] at signed
    change
      puncturedEuclideanSpaceTimeSquare
            (run initial index).nextContact.prefixReceipt.wholeTangent +
          (1 / 2 : Real) *
            puncturedEuclideanSpaceTimeSquare
              (receiptViscousNegativeOneState
                (run initial index).nextContact.prefixReceipt) +
          nu.coeff *
            (restartPhysicalVorticityMass initial (index + 1) -
              restartPhysicalVorticityMass initial index) ≤
        cubicConstant *
          (ceiling ^ 3 *
            (run initial index).nextContact.time.1)
    simpa only [cubicConstant, restartPhysicalVorticityMass, run_succ,
      GeneratedWholeRestartCurrent.next] using signed
  have summed := Finset.sum_le_sum edgeSigned
  have boundaryTelescope :
      nu.coeff *
          (∑ index ∈ Finset.Ico start finish,
            (restartPhysicalVorticityMass initial (index + 1) -
              restartPhysicalVorticityMass initial index)) =
        nu.coeff *
          (restartPhysicalVorticityMass initial finish -
            restartPhysicalVorticityMass initial start) := by
    rw [Finset.sum_Ico_eq_sub _ startLeFinish,
      Finset.sum_range_sub, Finset.sum_range_sub]
    ring
  have timeTelescope :
      (∑ index ∈ Finset.Ico start finish,
        (run initial index).nextContact.time.1) =
        elapsedTime initial (finish + 1) -
          elapsedTime initial (start + 1) := by
    have edgeTime (index : Nat) :
        (run initial index).nextContact.time.1 =
          elapsedTime initial (index + 2) -
            elapsedTime initial (index + 1) := by
      rw [elapsedTime_succ]
      have nextTimeEq :
          (run initial (index + 1)).contact.time.1 =
            (run initial index).nextContact.time.1 := by
        rfl
      rw [nextTimeEq]
      ring
    have shiftedTelescope (length : Nat) :
        (∑ index ∈ Finset.range length,
          (elapsedTime initial (index + 2) -
            elapsedTime initial (index + 1))) =
          elapsedTime initial (length + 1) -
            elapsedTime initial 1 := by
      simpa [Nat.add_assoc] using
        Finset.sum_range_sub
          (fun index => elapsedTime initial (index + 1)) length
    simp_rw [edgeTime]
    rw [Finset.sum_Ico_eq_sub _ startLeFinish,
      shiftedTelescope finish, shiftedTelescope start]
    ring
  have cubicTelescope :
      cubicConstant *
          (∑ index ∈ Finset.Ico start finish,
            ceiling ^ 3 * (run initial index).nextContact.time.1) =
        cubicConstant *
          (ceiling ^ 3 *
            (elapsedTime initial (finish + 1) -
              elapsedTime initial (start + 1))) := by
    rw [← Finset.mul_sum, timeTelescope]
  unfold wholeRestartIcoTangentNegativeOneEuclideanPayment
    wholeRestartIcoViscousNegativeOneEuclideanPayment
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at summed
  rw [← Finset.mul_sum] at summed
  rw [← Finset.mul_sum] at summed
  rw [← Finset.mul_sum] at summed
  rw [boundaryTelescope, cubicTelescope] at summed
  simpa only [cubicConstant] using summed

private theorem receipt_halfViscousGradient_add_boundary_between_le_cubicCeiling
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime start finish ceiling : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ requestedTime)
    (massLe :
      ∀ time : Icc (0 : Real) requestedTime,
        start ≤ time.1 → time.1 ≤ finish →
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling) :
    ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
          (∫ time in start..finish,
            wholeStateVorticityGradientMass
              (wholeRestartReceiptPhysicalTrajectory receipt time)) +
        nu.coeff *
          (wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩) -
            wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨start, ⟨startNonneg,
                  startLtFinish.le.trans finishLe⟩⟩)) ≤
      ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
        (ceiling ^ 3 * (finish - start)) := by
  have startLtRequested : start < requestedTime :=
    startLtFinish.trans_le finishLe
  let suffix :=
    positiveTimeSuffixWholeContinuousMildSerrinReceipt
      receipt start startNonneg startLtRequested
  have intervalPos : 0 < finish - start := sub_pos.mpr startLtFinish
  have intervalLe : finish - start ≤ requestedTime - start :=
    sub_le_sub_right finishLe start
  let intervalReceipt :=
    restrictWholeContinuousMildSerrinReceipt
      intervalPos intervalLe suffix
  have intervalMassLe :
      ∀ time : Icc (0 : Real) (finish - start),
        wholeVorticityEuclideanMass
            (intervalReceipt.wholePath time) ≤ ceiling := by
    intro time
    have shiftedLower :
        start ≤
          (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion intervalLe time)).1 := by
      simp only [commonTimeShift_apply, commonTimeInclusion_apply]
      linarith [time.2.1]
    have shiftedUpper :
        (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion intervalLe time)).1 ≤ finish := by
      simp only [commonTimeShift_apply, commonTimeInclusion_apply]
      linarith [time.2.2]
    exact massLe _ shiftedLower shiftedUpper
  have signed :=
    receipt_tangentHalfViscousSquare_add_boundary_le_cubicTime
      intervalReceipt (Filter.Eventually.of_forall intervalMassLe)
  have tangentNonneg :
      0 ≤ puncturedEuclideanSpaceTimeSquare
        intervalReceipt.wholeTangent := by
    exact sq_nonneg _
  have halfViscousBoundary :
      (1 / 2 : Real) *
            puncturedEuclideanSpaceTimeSquare
              (receiptViscousNegativeOneState intervalReceipt) +
          nu.coeff *
            (wholeVorticityEuclideanMass
                (intervalReceipt.wholePath
                  ⟨finish - start, ⟨intervalPos.le, le_rfl⟩⟩) -
              wholeVorticityEuclideanMass
                (receipt.wholePath
                  (wholeContinuousMildSerrinSuffixStartTime receipt start
                    startNonneg startLtRequested))) ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          (ceiling ^ 3 * (finish - start)) := by
    linarith
  have terminalEq :
      intervalReceipt.wholePath
          ⟨finish - start, ⟨intervalPos.le, le_rfl⟩⟩ =
        receipt.wholePath
          ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩ := by
    apply congrArg receipt.wholePath
    apply Subtype.ext
    simp [commonTimeInclusion_apply, commonTimeShift_apply]
  have initialEq :
      receipt.wholePath
          (wholeContinuousMildSerrinSuffixStartTime receipt start
            startNonneg startLtRequested) =
        receipt.wholePath
          ⟨start, ⟨startNonneg, startLtFinish.le.trans finishLe⟩⟩ := by
    apply congrArg receipt.wholePath
    apply Subtype.ext
    rfl
  have localGradientIntegralEq :
      (∫ time,
          wholeStateVorticityGradientMass
            (intervalReceipt.wholePath time)
          ∂(commonTimeMeasure (finish - start))) =
        ∫ time in start..finish,
          wholeStateVorticityGradientMass
            (wholeRestartReceiptPhysicalTrajectory receipt time) := by
    rw [show
      (∫ time,
          wholeStateVorticityGradientMass
            (intervalReceipt.wholePath time)
          ∂(commonTimeMeasure (finish - start))) =
        ∫ time in (0 : Real)..(finish - start),
          wholeStateVorticityGradientMass
            (wholeRestartReceiptPhysicalTrajectory intervalReceipt time) by
        rw [← commonTime_integral_eq_intervalIntegral
          (finish - start) intervalPos.le]
        apply integral_congr_ae
        filter_upwards [] with time
        unfold wholeRestartReceiptPhysicalTrajectory
        rw [projIcc_of_mem intervalPos.le time.2]]
    calc
      (∫ time in (0 : Real)..(finish - start),
          wholeStateVorticityGradientMass
            (wholeRestartReceiptPhysicalTrajectory intervalReceipt time)) =
          ∫ time in (0 : Real)..(finish - start),
            wholeStateVorticityGradientMass
              (wholeRestartReceiptPhysicalTrajectory receipt (start + time)) := by
        apply intervalIntegral.integral_congr
        intro time timeMem
        have timeIcc : time ∈ Icc (0 : Real) (finish - start) := by
          simpa [uIcc_of_le intervalPos.le] using timeMem
        unfold wholeRestartReceiptPhysicalTrajectory
        change
          wholeStateVorticityGradientMass
              (intervalReceipt.wholePath
                (projIcc 0 (finish - start)
                  intervalReceipt.requestedTimePos.le time)) =
            wholeStateVorticityGradientMass
              (receipt.wholePath
                (projIcc 0 requestedTime receipt.requestedTimePos.le
                  (start + time)))
        rw [projIcc_of_mem intervalReceipt.requestedTimePos.le timeIcc,
          projIcc_of_mem receipt.requestedTimePos.le
            (show start + time ∈ Icc (0 : Real) requestedTime by
              exact ⟨add_nonneg startNonneg timeIcc.1,
                by linarith [timeIcc.2]⟩)]
        change
          wholeStateVorticityGradientMass
              (intervalReceipt.wholePath ⟨time, timeIcc⟩) =
            wholeStateVorticityGradientMass
              (receipt.wholePath ⟨start + time, _⟩)
        rfl
      _ = ∫ time in start..finish,
          wholeStateVorticityGradientMass
            (wholeRestartReceiptPhysicalTrajectory receipt time) := by
        have shifted :=
          intervalIntegral.integral_comp_add_left
            (f := fun time : Real =>
              wholeStateVorticityGradientMass
                (wholeRestartReceiptPhysicalTrajectory receipt time))
            (a := 0) (b := finish - start) start
        convert shifted using 1
        ring_nf
  have viscousEq :=
    receiptViscousNegativeOneEuclideanSquare_eq_gradient intervalReceipt
  rw [viscousEq, terminalEq, localGradientIntegralEq] at halfViscousBoundary
  have initialMassEq := congrArg wholeVorticityEuclideanMass initialEq
  calc
    ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
            (∫ time in start..finish,
              wholeStateVorticityGradientMass
                (wholeRestartReceiptPhysicalTrajectory receipt time)) +
          nu.coeff *
            (wholeVorticityEuclideanMass
                (receipt.wholePath
                  ⟨finish,
                    ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩) -
              wholeVorticityEuclideanMass
                (receipt.wholePath
                  ⟨start, ⟨startNonneg,
                    startLtFinish.le.trans finishLe⟩⟩)) =
        (1 / 2 : Real) *
            (nu.coeff ^ 2 * (2 * Real.pi) ^ 2 *
              (∫ time in start..finish,
                wholeStateVorticityGradientMass
                  (wholeRestartReceiptPhysicalTrajectory receipt time))) +
          nu.coeff *
            (wholeVorticityEuclideanMass
                (receipt.wholePath
                  ⟨finish,
                    ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩) -
              wholeVorticityEuclideanMass
                (receipt.wholePath
                  (wholeContinuousMildSerrinSuffixStartTime receipt start
                    startNonneg startLtRequested))) := by
      rw [initialMassEq]
      ring
    _ ≤ _ := halfViscousBoundary

private theorem receiptGradientMass_intervalIntegrable
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime start finish : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (startNonneg : 0 ≤ start)
    (startLeFinish : start ≤ finish)
    (finishLe : finish ≤ requestedTime) :
    IntervalIntegrable
      (fun time =>
        wholeStateVorticityGradientMass
          (wholeRestartReceiptPhysicalTrajectory receipt time))
      volume start finish := by
  let viscousConstant := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let gradient : Icc (0 : Real) requestedTime → Real := fun time =>
    wholeStateVorticityGradientMass (receipt.wholePath time)
  have viscousConstantPos : 0 < viscousConstant := by
    dsimp only [viscousConstant]
    exact mul_pos
      (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
  have mappedViscousSquareIntegrable :
      Integrable
        (fun time =>
          ‖puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState receipt) time‖ ^ 2)
        (commonTimeMeasure requestedTime) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (MeasureTheory.Lp.memLp
        (puncturedEuclideanSpaceTimeState
          (receiptViscousNegativeOneState receipt))).integrable_norm_rpow
        (by norm_num) (by norm_num)
  have weightedGradientIntegrable :
      Integrable (fun time => viscousConstant * gradient time)
        (commonTimeMeasure requestedTime) := by
    apply mappedViscousSquareIntegrable.congr
    filter_upwards [
      receiptViscousNegativeOneEuclideanMass_ae_eq_gradient receipt] with
        time pointEq
    simpa only [viscousConstant, gradient] using pointEq
  have gradientIntegrable :
      Integrable gradient (commonTimeMeasure requestedTime) := by
    have scaled := weightedGradientIntegrable.const_mul viscousConstant⁻¹
    apply scaled.congr
    filter_upwards [] with time
    dsimp only [gradient]
    change
      viscousConstant⁻¹ *
          (viscousConstant *
            wholeStateVorticityGradientMass (receipt.wholePath time)) = _
    field_simp [viscousConstantPos.ne']
  have zeroExtensionIntegrable :
      IntervalIntegrable
        (ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport.commonTimeZeroExtension
          requestedTime gradient)
        volume 0 requestedTime :=
    ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall.commonTimeZeroExtension_intervalIntegrable_of_integrable
      requestedTime receipt.requestedTimePos.le gradient gradientIntegrable
  have fullIntegrable :
      IntervalIntegrable
        (fun time =>
          wholeStateVorticityGradientMass
            (wholeRestartReceiptPhysicalTrajectory receipt time))
        volume 0 requestedTime := by
    apply zeroExtensionIntegrable.congr
    intro time timeMem
    have timeIoc : time ∈ Ioc (0 : Real) requestedTime := by
      simpa [uIoc_of_le receipt.requestedTimePos.le] using timeMem
    have timeIcc : time ∈ Icc (0 : Real) requestedTime := by
      exact ⟨timeIoc.1.le, timeIoc.2⟩
    rw [
      ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport.commonTimeZeroExtension_of_mem
        requestedTime gradient time timeIcc]
    dsimp only [gradient]
    unfold wholeRestartReceiptPhysicalTrajectory
    have projectionEq :
        projIcc 0 requestedTime receipt.requestedTimePos.le time =
          ⟨time, timeIcc⟩ := by
      apply Subtype.ext
      simp [projIcc_of_mem receipt.requestedTimePos.le timeIcc]
    rw [projectionEq]
  apply fullIntegrable.mono_set
  rw [uIcc_of_le startLeFinish, uIcc_of_le receipt.requestedTimePos.le]
  exact Icc_subset_Icc startNonneg finishLe

private theorem real_add_sq_le_durationWeighted
    (left right leftDuration rightDuration : Real)
    (leftDurationPos : 0 < leftDuration)
    (rightDurationPos : 0 < rightDuration) :
    (left + right) ^ 2 ≤
      (leftDuration + rightDuration) *
        (left ^ 2 / leftDuration + right ^ 2 / rightDuration) := by
  have denominatorPos : 0 < leftDuration * rightDuration :=
    mul_pos leftDurationPos rightDurationPos
  have rhsEq :
      (leftDuration + rightDuration) *
          (left ^ 2 / leftDuration + right ^ 2 / rightDuration) =
        ((leftDuration + rightDuration) *
          (rightDuration * left ^ 2 + leftDuration * right ^ 2)) /
            (leftDuration * rightDuration) := by
    field_simp [leftDurationPos.ne', rightDurationPos.ne']
  rw [rhsEq, le_div_iff₀ denominatorPos]
  nlinarith [sq_nonneg (rightDuration * left - leftDuration * right)]

private theorem complexNormSq_add_le_durationWeighted
    (left right : Complex)
    (leftDuration rightDuration : Real)
    (leftDurationPos : 0 < leftDuration)
    (rightDurationPos : 0 < rightDuration) :
    Complex.normSq (left + right) ≤
      (leftDuration + rightDuration) *
        (Complex.normSq left / leftDuration +
          Complex.normSq right / rightDuration) := by
  have realPart :=
    real_add_sq_le_durationWeighted
      left.re right.re leftDuration rightDuration
        leftDurationPos rightDurationPos
  have imaginaryPart :=
    real_add_sq_le_durationWeighted
      left.im right.im leftDuration rightDuration
        leftDurationPos rightDurationPos
  calc
    Complex.normSq (left + right) =
        (left.re + right.re) ^ 2 + (left.im + right.im) ^ 2 := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
      ring
    _ ≤
        (leftDuration + rightDuration) *
            (left.re ^ 2 / leftDuration + right.re ^ 2 / rightDuration) +
          (leftDuration + rightDuration) *
            (left.im ^ 2 / leftDuration + right.im ^ 2 / rightDuration) :=
      add_le_add realPart imaginaryPart
    _ =
        (leftDuration + rightDuration) *
          (Complex.normSq left / leftDuration +
            Complex.normSq right / rightDuration) := by
      simp only [Complex.normSq_apply]
      ring

private theorem complexCoordinateAmplitudeSq_add_le_durationWeighted
    (left right : ComplexCoordinateVector)
    (leftDuration rightDuration : Real)
    (leftDurationPos : 0 < leftDuration)
    (rightDurationPos : 0 < rightDuration) :
    complexCoordinateAmplitudeSq (left + right) ≤
      (leftDuration + rightDuration) *
        (complexCoordinateAmplitudeSq left / leftDuration +
          complexCoordinateAmplitudeSq right / rightDuration) := by
  unfold complexCoordinateAmplitudeSq
  calc
    (∑ coordinate : Coordinate,
        Complex.normSq ((left + right) coordinate)) ≤
        ∑ coordinate : Coordinate,
          (leftDuration + rightDuration) *
            (Complex.normSq (left coordinate) / leftDuration +
              Complex.normSq (right coordinate) / rightDuration) := by
      apply Finset.sum_le_sum
      intro coordinate _coordinateMem
      simpa only [Pi.add_apply] using
        complexNormSq_add_le_durationWeighted
          (left coordinate) (right coordinate)
            leftDuration rightDuration leftDurationPos rightDurationPos
    _ = (leftDuration + rightDuration) *
        ((∑ coordinate : Coordinate, Complex.normSq (left coordinate)) /
            leftDuration +
          (∑ coordinate : Coordinate, Complex.normSq (right coordinate)) /
            rightDuration) := by
      rw [← Finset.mul_sum]
      simp_rw [Finset.sum_add_distrib, Finset.sum_div]

private theorem receiptFiniteBandWindowEnergy
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime start finish ceiling : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (observed : Finset IntegerWavevector)
    (zeroFree : ∀ wave ∈ observed, wave ≠ 0)
    (multiplier : Real)
    (multiplierNonneg : 0 ≤ multiplier)
    (multiplierLe : ∀ wave ∈ observed,
      integerWaveViscousMultiplier wave ≤ multiplier)
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ requestedTime)
    (massLe :
      ∀ time : Icc (0 : Real) requestedTime,
        start ≤ time.1 → time.1 ≤ finish →
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling) :
    ∃ energy : Real,
      0 ≤ energy ∧
      energy + nu.coeff *
          (wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩) -
            wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨start, ⟨startNonneg, startLtFinish.le.trans finishLe⟩⟩)) ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          (ceiling ^ 3 * (finish - start)) ∧
      IntervalIntegrable
          (fun time =>
            wholeStateVorticityGradientMass
              (wholeRestartReceiptPhysicalTrajectory receipt time))
          volume start finish ∧
      ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
          (∫ time in start..finish,
            wholeStateVorticityGradientMass
              (wholeRestartReceiptPhysicalTrajectory receipt time)) ≤
        energy ∧
      (∑ wave ∈ observed,
          complexCoordinateAmplitudeSq
            (receipt.wholePath
                  ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩ wave -
              receipt.wholePath
                  ⟨start, ⟨startNonneg, startLtFinish.le.trans finishLe⟩⟩ wave)) ≤
        3 * (finish - start) * multiplier * energy := by
  have startLtRequested : start < requestedTime :=
    startLtFinish.trans_le finishLe
  let suffix := positiveTimeSuffixWholeContinuousMildSerrinReceipt
    receipt start startNonneg startLtRequested
  have durationPos : 0 < finish - start := sub_pos.mpr startLtFinish
  have durationLe : finish - start ≤ requestedTime - start :=
    sub_le_sub_right finishLe start
  let window := restrictWholeContinuousMildSerrinReceipt
    durationPos durationLe suffix
  have windowMassLe :
      ∀ time : Icc (0 : Real) (finish - start),
        wholeVorticityEuclideanMass (window.wholePath time) ≤ ceiling := by
    intro time
    have shiftedLower :
        start ≤ (commonTimeShift startNonneg
          (startLtFinish.le.trans finishLe)
          (commonTimeInclusion durationLe time)).1 := by
      simp only [commonTimeShift_apply, commonTimeInclusion_apply]
      linarith [time.2.1]
    have shiftedUpper :
        (commonTimeShift startNonneg
          (startLtFinish.le.trans finishLe)
          (commonTimeInclusion durationLe time)).1 ≤ finish := by
      simp only [commonTimeShift_apply, commonTimeInclusion_apply]
      linarith [time.2.2]
    exact massLe _ shiftedLower shiftedUpper
  let zero : Icc (0 : Real) (finish - start) :=
    ⟨0, ⟨le_rfl, durationPos.le⟩⟩
  let terminal : Icc (0 : Real) (finish - start) :=
    ⟨finish - start, ⟨durationPos.le, le_rfl⟩⟩
  have initialEq :
      window.wholePath zero =
        receipt.wholePath
          ⟨start, ⟨startNonneg, startLtFinish.le.trans finishLe⟩⟩ := by
    calc
      window.wholePath zero = suffix.wholePath
          (commonTimeInclusion durationLe zero) := rfl
      _ = receipt.wholePath
          (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion durationLe zero)) := rfl
      _ = _ := by
        apply congrArg receipt.wholePath
        apply Subtype.ext
        simp [zero, commonTimeShift_apply, commonTimeInclusion_apply]
  have terminalEq :
      window.wholePath terminal =
        receipt.wholePath
          ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩ := by
    calc
      window.wholePath terminal = suffix.wholePath
          (commonTimeInclusion durationLe terminal) := rfl
      _ = receipt.wholePath
          (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion durationLe terminal)) := rfl
      _ = _ := by
        apply congrArg receipt.wholePath
        apply Subtype.ext
        simp [terminal, commonTimeShift_apply, commonTimeInclusion_apply]
  let energy : Real :=
    puncturedEuclideanSpaceTimeSquare window.wholeTangent +
      (1 / 2 : Real) *
        puncturedEuclideanSpaceTimeSquare
          (receiptViscousNegativeOneState window)
  have energyNonneg : 0 ≤ energy := by
    dsimp only [energy]
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have signed :=
    receipt_tangentHalfViscousSquare_add_boundary_le_cubicTime
      window (Filter.Eventually.of_forall windowMassLe)
  have signed' :
      energy + nu.coeff *
          (wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩) -
            wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨start, ⟨startNonneg, startLtFinish.le.trans finishLe⟩⟩)) ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          (ceiling ^ 3 * (finish - start)) := by
    have initialMassEq :
        wholeVorticityEuclideanMass
            (receipt.wholePath
              (wholeContinuousMildSerrinSuffixStartTime receipt start
                startNonneg startLtRequested)) =
          wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨start, ⟨startNonneg, startLtFinish.le.trans finishLe⟩⟩) := by
      apply congrArg wholeVorticityEuclideanMass
      apply congrArg receipt.wholePath
      apply Subtype.ext
      rfl
    calc
      energy + nu.coeff *
            (wholeVorticityEuclideanMass
                (receipt.wholePath
                  ⟨finish,
                    ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩) -
              wholeVorticityEuclideanMass
                (receipt.wholePath
                  ⟨start,
                    ⟨startNonneg, startLtFinish.le.trans finishLe⟩⟩)) =
          energy + nu.coeff *
            (wholeVorticityEuclideanMass (window.wholePath terminal) -
              wholeVorticityEuclideanMass
                (receipt.wholePath
                  (wholeContinuousMildSerrinSuffixStartTime receipt start
                    startNonneg startLtRequested))) := by
        rw [terminalEq, initialMassEq]
      _ ≤ _ := by
        simpa only [energy, terminal] using signed
  have gradientIntegrable :=
    receiptGradientMass_intervalIntegrable receipt startNonneg
      startLtFinish.le finishLe
  have localGradientIntegralEq :
      (∫ time,
          wholeStateVorticityGradientMass (window.wholePath time)
          ∂(commonTimeMeasure (finish - start))) =
        ∫ time in start..finish,
          wholeStateVorticityGradientMass
            (wholeRestartReceiptPhysicalTrajectory receipt time) := by
    rw [show
      (∫ time,
          wholeStateVorticityGradientMass (window.wholePath time)
          ∂(commonTimeMeasure (finish - start))) =
        ∫ time in (0 : Real)..(finish - start),
          wholeStateVorticityGradientMass
            (wholeRestartReceiptPhysicalTrajectory window time) by
        rw [← commonTime_integral_eq_intervalIntegral
          (finish - start) durationPos.le]
        apply integral_congr_ae
        filter_upwards [] with time
        unfold wholeRestartReceiptPhysicalTrajectory
        rw [projIcc_of_mem durationPos.le time.2]]
    calc
      (∫ time in (0 : Real)..(finish - start),
          wholeStateVorticityGradientMass
            (wholeRestartReceiptPhysicalTrajectory window time)) =
          ∫ time in (0 : Real)..(finish - start),
            wholeStateVorticityGradientMass
              (wholeRestartReceiptPhysicalTrajectory receipt (start + time)) := by
        apply intervalIntegral.integral_congr
        intro time timeMem
        have timeIcc : time ∈ Icc (0 : Real) (finish - start) := by
          simpa [uIcc_of_le durationPos.le] using timeMem
        unfold wholeRestartReceiptPhysicalTrajectory
        change
          wholeStateVorticityGradientMass
              (window.wholePath
                (projIcc 0 (finish - start)
                  window.requestedTimePos.le time)) =
            wholeStateVorticityGradientMass
              (receipt.wholePath
                (projIcc 0 requestedTime receipt.requestedTimePos.le
                  (start + time)))
        rw [projIcc_of_mem window.requestedTimePos.le timeIcc,
          projIcc_of_mem receipt.requestedTimePos.le
            (show start + time ∈ Icc (0 : Real) requestedTime by
              exact ⟨add_nonneg startNonneg timeIcc.1,
                by linarith [timeIcc.2]⟩)]
        change
          wholeStateVorticityGradientMass
              (window.wholePath ⟨time, timeIcc⟩) =
            wholeStateVorticityGradientMass
              (receipt.wholePath ⟨start + time, _⟩)
        rfl
      _ = ∫ time in start..finish,
          wholeStateVorticityGradientMass
            (wholeRestartReceiptPhysicalTrajectory receipt time) := by
        have shifted :=
          intervalIntegral.integral_comp_add_left
            (f := fun time : Real =>
              wholeStateVorticityGradientMass
                (wholeRestartReceiptPhysicalTrajectory receipt time))
            (a := 0) (b := finish - start) start
        convert shifted using 1
        ring_nf
  have halfGradientLeEnergy :
      ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
          (∫ time in start..finish,
            wholeStateVorticityGradientMass
              (wholeRestartReceiptPhysicalTrajectory receipt time)) ≤
        energy := by
    have viscousEq :=
      receiptViscousNegativeOneEuclideanSquare_eq_gradient window
    have tangentNonneg :
        0 ≤ puncturedEuclideanSpaceTimeSquare window.wholeTangent :=
      sq_nonneg _
    dsimp only [energy]
    rw [viscousEq, localGradientIntegralEq]
    linarith
  have localModulus :=
    receiptFiniteInventory_timeIncrement_euclideanSq_le_multiplierCeiling
      window observed zeroFree multiplier multiplierNonneg multiplierLe
      zero terminal durationPos.le
  have localModulus' :
      (∑ wave ∈ observed,
          complexCoordinateAmplitudeSq
            (window.wholePath terminal wave - window.wholePath zero wave)) ≤
        3 * (finish - start) * multiplier *
          puncturedEuclideanSpaceTimeSquare window.wholeTangent := by
    simpa only [terminal, zero, sub_zero] using localModulus
  have tangentLeEnergy :
      puncturedEuclideanSpaceTimeSquare window.wholeTangent ≤ energy := by
    dsimp only [energy]
    have viscousNonneg :
        0 ≤ puncturedEuclideanSpaceTimeSquare
          (receiptViscousNegativeOneState window) := sq_nonneg _
    linarith
  have factorNonneg : 0 ≤ 3 * (finish - start) * multiplier := by
    positivity
  have modulus' :
      (∑ wave ∈ observed,
          complexCoordinateAmplitudeSq
            (receipt.wholePath
                  ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩ wave -
              receipt.wholePath
                  ⟨start, ⟨startNonneg, startLtFinish.le.trans finishLe⟩⟩ wave)) ≤
        3 * (finish - start) * multiplier * energy := by
    rw [← terminalEq, ← initialEq]
    exact localModulus'.trans
      (mul_le_mul_of_nonneg_left tangentLeEnergy factorNonneg)
  exact ⟨energy, energyNonneg, signed', gradientIntegrable,
    halfGradientLeEnergy, modulus'⟩

theorem wholeRestartPrefixFiniteBandWindowEnergy
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ (length : Nat) {start finish ceiling : Real}
      (observed : Finset IntegerWavevector),
      0 ≤ start →
      start < finish →
      finish ≤ elapsedTime initial length →
      (∀ wave ∈ observed, wave ≠ 0) →
      (multiplier : Real) →
      0 ≤ multiplier →
      (∀ wave ∈ observed,
        integerWaveViscousMultiplier wave ≤ multiplier) →
      (∀ time ∈ Icc start finish,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          ceiling) →
      ∃ energy : Real,
        0 ≤ energy ∧
        energy + nu.coeff *
            (wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length finish) -
              wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length start)) ≤
          ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
              (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
            (ceiling ^ 3 * (finish - start)) ∧
        IntervalIntegrable
            (fun time =>
              wholeStateVorticityGradientMass
                (wholeRestartPrefixPhysicalTrajectory initial length time))
            volume start finish ∧
        ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
            (∫ time in start..finish,
              wholeStateVorticityGradientMass
                (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
          energy ∧
        (∑ wave ∈ observed,
            complexCoordinateAmplitudeSq
              (wholeRestartPrefixPhysicalTrajectory initial length finish wave -
                wholeRestartPrefixPhysicalTrajectory initial length start wave)) ≤
          3 * (finish - start) * multiplier * energy := by
  intro length
  induction length with
  | zero =>
      intro start finish ceiling observed startNonneg startLtFinish finishLe
        _zeroFree _multiplier _multiplierNonneg _multiplierLe _massLe
      rw [elapsedTime_zero] at finishLe
      linarith
  | succ length ih =>
      intro start finish ceiling observed startNonneg startLtFinish finishLe
        zeroFree multiplier multiplierNonneg multiplierLe massLe
      let joinTime := elapsedTime initial length
      let receipt := (run initial length).contact.prefixReceipt
      have finishLeExpanded :
          finish ≤ joinTime + (run initial length).contact.time.1 := by
        simpa only [joinTime, elapsedTime_succ] using finishLe
      have priorChart
          (time : Real) (timeLeJoin : time ≤ joinTime) :
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
            wholeRestartPrefixPhysicalTrajectory initial length time := by
        simp only [wholeRestartPrefixPhysicalTrajectory]
        exact
          ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice.endpointSplice_of_le
            joinTime
            (wholeRestartPrefixPhysicalTrajectory initial length)
            (wholeRestartReceiptPhysicalTrajectory receipt)
            time timeLeJoin
      have receiptChart
          (time : Real) (joinLeTime : joinTime ≤ time)
          (timeLeFinish :
            time ≤ joinTime + (run initial length).contact.time.1) :
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
            receipt.wholePath
              ⟨time - joinTime,
                ⟨sub_nonneg.mpr joinLeTime, by linarith⟩⟩ := by
        let localTime : Icc (0 : Real) (run initial length).contact.time.1 :=
          ⟨time - joinTime,
            ⟨sub_nonneg.mpr joinLeTime, by linarith⟩⟩
        have chart :=
          wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
            initial length localTime
        have addLocal : joinTime + localTime.1 = time := by
          dsimp only [joinTime, localTime]
          ring
        simpa only [receipt, joinTime, addLocal] using chart
      by_cases finishLeJoin : finish ≤ joinTime
      · have priorMassLe :
            ∀ time ∈ Icc start finish,
              wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
                ceiling := by
          intro time timeMem
          rw [← priorChart time (timeMem.2.trans finishLeJoin)]
          exact massLe time timeMem
        rcases ih (start := start) (finish := finish) (ceiling := ceiling)
            observed startNonneg startLtFinish finishLeJoin zeroFree
            multiplier multiplierNonneg multiplierLe priorMassLe with
          ⟨energy, energyNonneg, signed, priorGradientIntegrable,
            priorGradientLe, modulus⟩
        have globalGradientIntegrable :
            IntervalIntegrable
              (fun time =>
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial
                    (length + 1) time))
              volume start finish := by
          apply priorGradientIntegrable.congr
          intro time timeMem
          have timeIoc : time ∈ Ioc start finish := by
            simpa [uIoc_of_le startLtFinish.le] using timeMem
          exact congrArg wholeStateVorticityGradientMass
            (priorChart time (timeIoc.2.trans finishLeJoin)).symm
        have gradientIntegralEq :
            (∫ time in start..finish,
              wholeStateVorticityGradientMass
                (wholeRestartPrefixPhysicalTrajectory initial
                  (length + 1) time)) =
              ∫ time in start..finish,
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time) := by
          apply intervalIntegral.integral_congr
          intro time timeMem
          have timeIcc : time ∈ Icc start finish := by
            simpa [uIcc_of_le startLtFinish.le] using timeMem
          exact congrArg wholeStateVorticityGradientMass
            (priorChart time (timeIcc.2.trans finishLeJoin))
        refine ⟨energy, energyNonneg, ?_, globalGradientIntegrable, ?_, ?_⟩
        · rw [priorChart finish finishLeJoin,
            priorChart start (startLtFinish.le.trans finishLeJoin)]
          exact signed
        · rw [gradientIntegralEq]
          exact priorGradientLe
        · rw [priorChart finish finishLeJoin,
            priorChart start (startLtFinish.le.trans finishLeJoin)]
          exact modulus
      · have joinLtFinish : joinTime < finish := lt_of_not_ge finishLeJoin
        by_cases startLtJoin : start < joinTime
        · have firstMassLe :
              ∀ time ∈ Icc start joinTime,
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
                  ceiling := by
            intro time timeMem
            rw [← priorChart time timeMem.2]
            exact massLe time
              ⟨timeMem.1, timeMem.2.trans joinLtFinish.le⟩
          rcases ih (start := start) (finish := joinTime) (ceiling := ceiling)
              observed startNonneg startLtJoin le_rfl zeroFree
              multiplier multiplierNonneg multiplierLe firstMassLe with
            ⟨firstEnergy, firstEnergyNonneg, firstSigned,
              firstGradientIntegrable, firstGradientLe, firstModulus⟩
          have localFinishPos : 0 < finish - joinTime :=
            sub_pos.mpr joinLtFinish
          have localFinishLe :
              finish - joinTime ≤ (run initial length).contact.time.1 := by
            linarith
          have secondMassLe :
              ∀ time : Icc (0 : Real) (run initial length).contact.time.1,
                0 ≤ time.1 → time.1 ≤ finish - joinTime →
                wholeVorticityEuclideanMass (receipt.wholePath time) ≤
                  ceiling := by
            intro time _timeNonneg timeLe
            have absoluteMem : joinTime + time.1 ∈ Icc start finish := by
              constructor
              · linarith [time.2.1]
              · linarith
            have globalBound := massLe _ absoluteMem
            have chart := receiptChart (joinTime + time.1)
              (by linarith [time.2.1]) (by linarith [time.2.2])
            rw [chart] at globalBound
            convert globalBound using 1
            apply congrArg wholeVorticityEuclideanMass
            apply congrArg receipt.wholePath
            apply Subtype.ext
            ring
          rcases receiptFiniteBandWindowEnergy receipt observed zeroFree
              multiplier multiplierNonneg multiplierLe le_rfl
              localFinishPos localFinishLe secondMassLe with
            ⟨secondEnergy, secondEnergyNonneg, secondSigned,
              secondGradientIntegrable, secondGradientLe, secondModulus⟩
          have startEq := priorChart start startLtJoin.le
          have joinPriorEq := priorChart joinTime le_rfl
          have joinReceiptEq := receiptChart joinTime le_rfl
            (by linarith [(run initial length).contact.time_pos])
          have finishReceiptEq := receiptChart finish joinLtFinish.le
            finishLeExpanded
          have firstSignedGlobal :
              firstEnergy + nu.coeff *
                  (wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) joinTime) -
                    wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) start)) ≤
                ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                  (ceiling ^ 3 * (joinTime - start)) := by
            simpa only [joinPriorEq, startEq] using firstSigned
          have secondSignedGlobal :
              secondEnergy + nu.coeff *
                  (wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) finish) -
                    wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) joinTime)) ≤
                ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                  (ceiling ^ 3 * (finish - joinTime)) := by
            rw [finishReceiptEq, joinReceiptEq]
            simpa only [receipt, sub_zero, sub_self] using secondSigned
          let energy := firstEnergy + secondEnergy
          have energyNonneg : 0 ≤ energy :=
            add_nonneg firstEnergyNonneg secondEnergyNonneg
          have signedGlobal :
              energy + nu.coeff *
                  (wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) finish) -
                    wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) start)) ≤
                ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                  (ceiling ^ 3 * (finish - start)) := by
            dsimp only [energy]
            calc
              firstEnergy + secondEnergy + nu.coeff *
                    (wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) finish) -
                      wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) start)) =
                  (firstEnergy + nu.coeff *
                    (wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) joinTime) -
                      wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) start))) +
                  (secondEnergy + nu.coeff *
                    (wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) finish) -
                      wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) joinTime))) := by ring
              _ ≤
                  ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                      (ceiling ^ 3 * (joinTime - start)) +
                    ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                      (ceiling ^ 3 * (finish - joinTime)) :=
                add_le_add firstSignedGlobal secondSignedGlobal
              _ = _ := by ring
          have firstGradientIntegrableGlobal :
              IntervalIntegrable
                (fun time =>
                  wholeStateVorticityGradientMass
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time))
                volume start joinTime := by
            apply firstGradientIntegrable.congr
            intro time timeMem
            have timeIoc : time ∈ Ioc start joinTime := by
              simpa [uIoc_of_le startLtJoin.le] using timeMem
            exact congrArg wholeStateVorticityGradientMass
              (priorChart time timeIoc.2).symm
          have firstGradientIntegralEq :
              (∫ time in start..joinTime,
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial
                    (length + 1) time)) =
                ∫ time in start..joinTime,
                  wholeStateVorticityGradientMass
                    (wholeRestartPrefixPhysicalTrajectory initial length time) := by
            apply intervalIntegral.integral_congr
            intro time timeMem
            have timeIcc : time ∈ Icc start joinTime := by
              simpa [uIcc_of_le startLtJoin.le] using timeMem
            exact congrArg wholeStateVorticityGradientMass
              (priorChart time timeIcc.2)
          have shiftedSecondGradientIntegrable :
              IntervalIntegrable
                (fun time =>
                  wholeStateVorticityGradientMass
                    (wholeRestartReceiptPhysicalTrajectory receipt
                      (time - joinTime)))
                volume joinTime finish := by
            have shifted :=
              secondGradientIntegrable.comp_sub_right joinTime
            convert shifted using 1 <;> ring
          have secondGradientIntegrableGlobal :
              IntervalIntegrable
                (fun time =>
                  wholeStateVorticityGradientMass
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time))
                volume joinTime finish := by
            apply shiftedSecondGradientIntegrable.congr
            intro time timeMem
            have timeIoc : time ∈ Ioc joinTime finish := by
              simpa [uIoc_of_le joinLtFinish.le] using timeMem
            have localMem :
                time - joinTime ∈
                  Icc (0 : Real) (run initial length).contact.time.1 := by
              constructor
              · exact sub_nonneg.mpr timeIoc.1.le
              · linarith [timeIoc.2, finishLeExpanded]
            change
              wholeStateVorticityGradientMass
                  (wholeRestartReceiptPhysicalTrajectory receipt
                    (time - joinTime)) =
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial
                    (length + 1) time)
            unfold wholeRestartReceiptPhysicalTrajectory
            rw [projIcc_of_mem receipt.requestedTimePos.le localMem]
            exact congrArg wholeStateVorticityGradientMass
              (receiptChart time timeIoc.1.le
                (timeIoc.2.trans finishLeExpanded)).symm
          have secondGradientIntegralEq :
              (∫ time in joinTime..finish,
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial
                    (length + 1) time)) =
                ∫ time in (0 : Real)..(finish - joinTime),
                  wholeStateVorticityGradientMass
                    (wholeRestartReceiptPhysicalTrajectory receipt time) := by
            calc
              (∫ time in joinTime..finish,
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial
                    (length + 1) time)) =
                  ∫ time in joinTime..finish,
                    wholeStateVorticityGradientMass
                      (wholeRestartReceiptPhysicalTrajectory receipt
                        (time - joinTime)) := by
                apply intervalIntegral.integral_congr
                intro time timeMem
                have timeIcc : time ∈ Icc joinTime finish := by
                  simpa [uIcc_of_le joinLtFinish.le] using timeMem
                have localMem :
                    time - joinTime ∈
                      Icc (0 : Real) (run initial length).contact.time.1 := by
                  constructor
                  · exact sub_nonneg.mpr timeIcc.1
                  · linarith [timeIcc.2, finishLeExpanded]
                change
                  wholeStateVorticityGradientMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time) =
                    wholeStateVorticityGradientMass
                      (wholeRestartReceiptPhysicalTrajectory receipt
                        (time - joinTime))
                unfold wholeRestartReceiptPhysicalTrajectory
                rw [projIcc_of_mem receipt.requestedTimePos.le localMem]
                exact congrArg wholeStateVorticityGradientMass
                  (receiptChart time timeIcc.1
                    (timeIcc.2.trans finishLeExpanded))
              _ = ∫ time in (0 : Real)..(finish - joinTime),
                  wholeStateVorticityGradientMass
                    (wholeRestartReceiptPhysicalTrajectory receipt time) := by
                simpa only [sub_self] using
                  (intervalIntegral.integral_comp_sub_right
                    (f := fun localTime : Real =>
                      wholeStateVorticityGradientMass
                        (wholeRestartReceiptPhysicalTrajectory receipt localTime))
                    (a := joinTime) (b := finish) joinTime)
          have gradientIntegrableGlobal :=
            firstGradientIntegrableGlobal.trans
              secondGradientIntegrableGlobal
          have gradientLeGlobal :
              ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
                  (∫ time in start..finish,
                    wholeStateVorticityGradientMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time)) ≤
                energy := by
            rw [← intervalIntegral.integral_add_adjacent_intervals
              firstGradientIntegrableGlobal secondGradientIntegrableGlobal]
            rw [firstGradientIntegralEq, secondGradientIntegralEq]
            dsimp only [energy]
            linarith
          let firstDuration := joinTime - start
          let secondDuration := finish - joinTime
          have firstDurationPos : 0 < firstDuration :=
            sub_pos.mpr startLtJoin
          have secondDurationPos : 0 < secondDuration :=
            sub_pos.mpr joinLtFinish
          have firstModulusGlobal :
              (∑ wave ∈ observed,
                  complexCoordinateAmplitudeSq
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          joinTime wave -
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          start wave)) ≤
                3 * firstDuration * multiplier * firstEnergy := by
            simpa only [firstDuration, joinPriorEq, startEq] using firstModulus
          have secondModulusGlobal :
              (∑ wave ∈ observed,
                  complexCoordinateAmplitudeSq
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          finish wave -
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          joinTime wave)) ≤
                3 * secondDuration * multiplier * secondEnergy := by
            rw [finishReceiptEq, joinReceiptEq]
            simpa only [secondDuration, receipt, sub_zero, sub_self] using
              secondModulus
          have firstQuotient :
              (∑ wave ∈ observed,
                  complexCoordinateAmplitudeSq
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          joinTime wave -
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          start wave)) / firstDuration ≤
                3 * multiplier * firstEnergy := by
            rw [div_le_iff₀ firstDurationPos]
            calc
              _ ≤ 3 * firstDuration * multiplier * firstEnergy :=
                firstModulusGlobal
              _ = 3 * multiplier * firstEnergy * firstDuration := by ring
          have secondQuotient :
              (∑ wave ∈ observed,
                  complexCoordinateAmplitudeSq
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          finish wave -
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          joinTime wave)) / secondDuration ≤
                3 * multiplier * secondEnergy := by
            rw [div_le_iff₀ secondDurationPos]
            calc
              _ ≤ 3 * secondDuration * multiplier * secondEnergy :=
                secondModulusGlobal
              _ = 3 * multiplier * secondEnergy * secondDuration := by ring
          have combinedPoint (wave : IntegerWavevector) :
              complexCoordinateAmplitudeSq
                  (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                        finish wave -
                    wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                        start wave) ≤
                (firstDuration + secondDuration) *
                  (complexCoordinateAmplitudeSq
                      (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                            finish wave -
                        wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                            joinTime wave) / secondDuration +
                    complexCoordinateAmplitudeSq
                      (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                            joinTime wave -
                        wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                            start wave) / firstDuration) := by
            rw [show
              wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                    finish wave -
                  wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                    start wave =
                (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                    finish wave -
                  wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                    joinTime wave) +
                (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                    joinTime wave -
                  wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                    start wave) by abel]
            simpa only [add_comm firstDuration secondDuration] using
              complexCoordinateAmplitudeSq_add_le_durationWeighted
                (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                    finish wave -
                  wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                    joinTime wave)
                (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                    joinTime wave -
                  wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                    start wave)
                secondDuration firstDuration secondDurationPos firstDurationPos
          have combinedSum :
              (∑ wave ∈ observed,
                  complexCoordinateAmplitudeSq
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          finish wave -
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          start wave)) ≤
                (firstDuration + secondDuration) *
                  ((∑ wave ∈ observed,
                      complexCoordinateAmplitudeSq
                        (wholeRestartPrefixPhysicalTrajectory initial
                              (length + 1) finish wave -
                          wholeRestartPrefixPhysicalTrajectory initial
                              (length + 1) joinTime wave)) / secondDuration +
                    (∑ wave ∈ observed,
                      complexCoordinateAmplitudeSq
                        (wholeRestartPrefixPhysicalTrajectory initial
                              (length + 1) joinTime wave -
                          wholeRestartPrefixPhysicalTrajectory initial
                              (length + 1) start wave)) / firstDuration) := by
            calc
              _ ≤ ∑ wave ∈ observed,
                  (firstDuration + secondDuration) *
                    (complexCoordinateAmplitudeSq
                        (wholeRestartPrefixPhysicalTrajectory initial
                              (length + 1) finish wave -
                          wholeRestartPrefixPhysicalTrajectory initial
                              (length + 1) joinTime wave) / secondDuration +
                      complexCoordinateAmplitudeSq
                        (wholeRestartPrefixPhysicalTrajectory initial
                              (length + 1) joinTime wave -
                          wholeRestartPrefixPhysicalTrajectory initial
                              (length + 1) start wave) / firstDuration) := by
                apply Finset.sum_le_sum
                intro wave _waveMem
                exact combinedPoint wave
              _ = _ := by
                rw [← Finset.mul_sum]
                simp_rw [Finset.sum_add_distrib, Finset.sum_div]
          have durationSum :
              firstDuration + secondDuration = finish - start := by
            dsimp only [firstDuration, secondDuration]
            ring
          have combinedModulus :
              (∑ wave ∈ observed,
                  complexCoordinateAmplitudeSq
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          finish wave -
                      wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                          start wave)) ≤
                3 * (finish - start) * multiplier * energy := by
            calc
              _ ≤
                  (firstDuration + secondDuration) *
                    ((∑ wave ∈ observed,
                        complexCoordinateAmplitudeSq
                          (wholeRestartPrefixPhysicalTrajectory initial
                                (length + 1) finish wave -
                            wholeRestartPrefixPhysicalTrajectory initial
                                (length + 1) joinTime wave)) / secondDuration +
                      (∑ wave ∈ observed,
                        complexCoordinateAmplitudeSq
                          (wholeRestartPrefixPhysicalTrajectory initial
                                (length + 1) joinTime wave -
                            wholeRestartPrefixPhysicalTrajectory initial
                                (length + 1) start wave)) / firstDuration) :=
                combinedSum
              _ ≤ (firstDuration + secondDuration) *
                    (3 * multiplier * secondEnergy +
                      3 * multiplier * firstEnergy) := by
                gcongr
              _ = 3 * (finish - start) * multiplier * energy := by
                rw [durationSum]
                dsimp only [energy]
                ring
          exact ⟨energy, energyNonneg, signedGlobal,
            gradientIntegrableGlobal, gradientLeGlobal, combinedModulus⟩
        · have joinLeStart : joinTime ≤ start := le_of_not_gt startLtJoin
          have localStartNonneg : 0 ≤ start - joinTime :=
            sub_nonneg.mpr joinLeStart
          have localStartLtFinish :
              start - joinTime < finish - joinTime :=
            sub_lt_sub_right startLtFinish joinTime
          have localFinishLe :
              finish - joinTime ≤ (run initial length).contact.time.1 := by
            linarith
          have localMassLe :
              ∀ time : Icc (0 : Real) (run initial length).contact.time.1,
                start - joinTime ≤ time.1 →
                time.1 ≤ finish - joinTime →
                wholeVorticityEuclideanMass (receipt.wholePath time) ≤
                  ceiling := by
            intro time startLeTime timeLeFinish
            have absoluteMem : joinTime + time.1 ∈ Icc start finish := by
              constructor <;> linarith
            have globalBound := massLe _ absoluteMem
            have chart := receiptChart (joinTime + time.1)
              (by linarith) (by linarith [time.2.2])
            rw [chart] at globalBound
            convert globalBound using 1
            apply congrArg wholeVorticityEuclideanMass
            apply congrArg receipt.wholePath
            apply Subtype.ext
            ring
          rcases receiptFiniteBandWindowEnergy receipt observed zeroFree
              multiplier multiplierNonneg multiplierLe localStartNonneg
              localStartLtFinish localFinishLe localMassLe with
            ⟨energy, energyNonneg, signed, localGradientIntegrable,
              localGradientLe, modulus⟩
          have startReceiptEq := receiptChart start joinLeStart
            (startLtFinish.le.trans finishLeExpanded)
          have finishReceiptEq := receiptChart finish joinLtFinish.le
            finishLeExpanded
          have shiftedGradientIntegrable :
              IntervalIntegrable
                (fun time =>
                  wholeStateVorticityGradientMass
                    (wholeRestartReceiptPhysicalTrajectory receipt
                      (time - joinTime)))
                volume start finish := by
            have shifted := localGradientIntegrable.comp_sub_right joinTime
            convert shifted using 1 <;> ring
          have globalGradientIntegrable :
              IntervalIntegrable
                (fun time =>
                  wholeStateVorticityGradientMass
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time))
                volume start finish := by
            apply shiftedGradientIntegrable.congr
            intro time timeMem
            have timeIoc : time ∈ Ioc start finish := by
              simpa [uIoc_of_le startLtFinish.le] using timeMem
            have localMem :
                time - joinTime ∈
                  Icc (0 : Real) (run initial length).contact.time.1 := by
              constructor
              · exact sub_nonneg.mpr (joinLeStart.trans timeIoc.1.le)
              · linarith [timeIoc.2, finishLeExpanded]
            change
              wholeStateVorticityGradientMass
                  (wholeRestartReceiptPhysicalTrajectory receipt
                    (time - joinTime)) =
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial
                    (length + 1) time)
            unfold wholeRestartReceiptPhysicalTrajectory
            rw [projIcc_of_mem receipt.requestedTimePos.le localMem]
            exact congrArg wholeStateVorticityGradientMass
              (receiptChart time (joinLeStart.trans timeIoc.1.le)
                (timeIoc.2.trans finishLeExpanded)).symm
          have gradientIntegralEq :
              (∫ time in start..finish,
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial
                    (length + 1) time)) =
                ∫ time in start - joinTime..finish - joinTime,
                  wholeStateVorticityGradientMass
                    (wholeRestartReceiptPhysicalTrajectory receipt time) := by
            calc
              (∫ time in start..finish,
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial
                    (length + 1) time)) =
                  ∫ time in start..finish,
                    wholeStateVorticityGradientMass
                      (wholeRestartReceiptPhysicalTrajectory receipt
                        (time - joinTime)) := by
                apply intervalIntegral.integral_congr
                intro time timeMem
                have timeIcc : time ∈ Icc start finish := by
                  simpa [uIcc_of_le startLtFinish.le] using timeMem
                have localMem :
                    time - joinTime ∈
                      Icc (0 : Real) (run initial length).contact.time.1 := by
                  constructor
                  · exact sub_nonneg.mpr (joinLeStart.trans timeIcc.1)
                  · linarith [timeIcc.2, finishLeExpanded]
                change
                  wholeStateVorticityGradientMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time) =
                    wholeStateVorticityGradientMass
                      (wholeRestartReceiptPhysicalTrajectory receipt
                        (time - joinTime))
                unfold wholeRestartReceiptPhysicalTrajectory
                rw [projIcc_of_mem receipt.requestedTimePos.le localMem]
                exact congrArg wholeStateVorticityGradientMass
                  (receiptChart time (joinLeStart.trans timeIcc.1)
                    (timeIcc.2.trans finishLeExpanded))
              _ = ∫ time in start - joinTime..finish - joinTime,
                  wholeStateVorticityGradientMass
                    (wholeRestartReceiptPhysicalTrajectory receipt time) := by
                exact intervalIntegral.integral_comp_sub_right
                  (f := fun localTime : Real =>
                    wholeStateVorticityGradientMass
                      (wholeRestartReceiptPhysicalTrajectory receipt localTime))
                  (a := start) (b := finish) joinTime
          refine ⟨energy, energyNonneg, ?_, globalGradientIntegrable,
            ?_, ?_⟩
          · rw [finishReceiptEq, startReceiptEq]
            convert signed using 1
            all_goals ring
          · rw [gradientIntegralEq]
            exact localGradientLe
          · rw [finishReceiptEq, startReceiptEq]
            convert modulus using 1
            all_goals ring

private theorem wholeRestartPrefixFiniteBandTimeModulus_of_massBand
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    {start finish lower ceiling : Real}
    (observed : Finset IntegerWavevector)
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ elapsedTime initial length)
    (zeroFree : ∀ wave ∈ observed, wave ≠ 0)
    (multiplier : Real)
    (multiplierNonneg : 0 ≤ multiplier)
    (multiplierLe : ∀ wave ∈ observed,
      integerWaveViscousMultiplier wave ≤ multiplier)
    (massBand :
      ∀ time ∈ Icc start finish,
        lower ≤ wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
            ceiling) :
    (∑ wave ∈ observed,
        complexCoordinateAmplitudeSq
          (wholeRestartPrefixPhysicalTrajectory initial length finish wave -
            wholeRestartPrefixPhysicalTrajectory initial length start wave)) ≤
      3 * (finish - start) * multiplier *
        (((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
              (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
            (ceiling ^ 3 * (finish - start)) +
          nu.coeff * (ceiling - lower)) := by
  have massLe :
      ∀ time ∈ Icc start finish,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          ceiling := fun time timeMem => (massBand time timeMem).2
  rcases wholeRestartPrefixFiniteBandWindowEnergy initial length observed
      startNonneg startLtFinish finishLe zeroFree multiplier
      multiplierNonneg multiplierLe massLe with
    ⟨energy, _energyNonneg, signed, _gradientIntegrable, _gradientLe,
      modulus⟩
  have startUpper := (massBand start ⟨le_rfl, startLtFinish.le⟩).2
  have finishLower := (massBand finish ⟨startLtFinish.le, le_rfl⟩).1
  have boundaryLower :
      lower - ceiling ≤
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length finish) -
          wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length start) := by
    linarith
  have energyUpper :
      energy ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
              (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
            (ceiling ^ 3 * (finish - start)) +
          nu.coeff * (ceiling - lower) := by
    have scaledBoundary :=
      mul_le_mul_of_nonneg_left boundaryLower nu.coeff_pos.le
    linarith
  have factorNonneg :
      0 ≤ 3 * (finish - start) * multiplier := by positivity
  exact modulus.trans
    (mul_le_mul_of_nonneg_left energyUpper factorNonneg)

theorem wholeRestartPrefixScaleCriticalWindowBudget
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    {start finish level : Real}
    (levelPos : 0 < level)
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ elapsedTime initial length)
    (massBand :
      ∀ time ∈ Icc start finish,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
            level) :
    IntervalIntegrable
        (fun time =>
          wholeStateVorticityGradientMass
            (wholeRestartPrefixPhysicalTrajectory initial length time))
        volume start finish ∧
      (((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
          (level⁻¹ *
            ∫ time in start..finish,
              wholeStateVorticityGradientMass
                (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
              (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
            (level ^ 2 * (finish - start)) +
          nu.coeff / 2) ∧
      ∀ (observed : Finset IntegerWavevector)
        (_zeroFree : ∀ wave ∈ observed, wave ≠ 0)
        (multiplier : Real)
        (_multiplierNonneg : 0 ≤ multiplier)
        (_multiplierLe : ∀ wave ∈ observed,
          integerWaveViscousMultiplier wave ≤ multiplier)
        (windowStart windowFinish : Real),
        windowStart ∈ Icc start finish →
        windowFinish ∈ Icc start finish →
        windowStart < windowFinish →
        level⁻¹ *
            (∑ wave ∈ observed,
              complexCoordinateAmplitudeSq
                (wholeRestartPrefixPhysicalTrajectory initial length
                      windowFinish wave -
                  wholeRestartPrefixPhysicalTrajectory initial length
                      windowStart wave)) ≤
          3 * (level ^ 2 * (windowFinish - windowStart)) *
            ((level ^ 2)⁻¹ * multiplier) *
            (((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                  (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                (level ^ 2 * (windowFinish - windowStart)) +
              nu.coeff / 2) := by
  let cubicConstant : Real :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
  have massLe :
      ∀ time ∈ Icc start finish,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          level := fun time timeMem => (massBand time timeMem).2
  rcases wholeRestartPrefixFiniteBandWindowEnergy initial length
      (∅ : Finset IntegerWavevector) startNonneg startLtFinish finishLe
      (by simp) 0 (by norm_num) (by simp) massLe with
    ⟨energy, _energyNonneg, signedEnergy, gradientIntegrable,
      gradientLe, _emptyModulus⟩
  have boundaryLower :
      -(level / 2) ≤
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length finish) -
          wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length start) := by
    have startUpper :=
      (massBand start ⟨le_rfl, startLtFinish.le⟩).2
    have finishLower :=
      (massBand finish ⟨startLtFinish.le, le_rfl⟩).1
    linarith
  have energyUpper :
      energy ≤
        cubicConstant * (level ^ 3 * (finish - start)) +
          nu.coeff * (level / 2) := by
    have scaledBoundary :=
      mul_le_mul_of_nonneg_left boundaryLower nu.coeff_pos.le
    have signedCubic :
        energy + nu.coeff *
            (wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length finish) -
              wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length start)) ≤
          cubicConstant * (level ^ 3 * (finish - start)) := by
      simpa only [cubicConstant] using signedEnergy
    linarith
  have normalizedEnergyUpper :
      level⁻¹ * energy ≤
        cubicConstant * (level ^ 2 * (finish - start)) + nu.coeff / 2 := by
    have scaled := mul_le_mul_of_nonneg_left energyUpper
      (inv_nonneg.mpr levelPos.le)
    calc
      level⁻¹ * energy ≤
          level⁻¹ *
            (cubicConstant * (level ^ 3 * (finish - start)) +
              nu.coeff * (level / 2)) := scaled
      _ = cubicConstant * (level ^ 2 * (finish - start)) +
            nu.coeff / 2 := by
        field_simp [levelPos.ne']
  have normalizedGradientLe :
      ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
          (level⁻¹ *
            ∫ time in start..finish,
              wholeStateVorticityGradientMass
                (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
        cubicConstant * (level ^ 2 * (finish - start)) + nu.coeff / 2 := by
    have scaled := mul_le_mul_of_nonneg_left gradientLe
      (inv_nonneg.mpr levelPos.le)
    calc
      ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
            (level⁻¹ *
              ∫ time in start..finish,
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time)) =
          level⁻¹ *
            (((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
              ∫ time in start..finish,
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time)) := by
        ring
      _ ≤ level⁻¹ * energy := scaled
      _ ≤ cubicConstant * (level ^ 2 * (finish - start)) +
            nu.coeff / 2 := normalizedEnergyUpper
  refine ⟨gradientIntegrable, ?_, ?_⟩
  · simpa only [cubicConstant] using normalizedGradientLe
  · intro observed zeroFree multiplier multiplierNonneg multiplierLe
      windowStart windowFinish windowStartMem windowFinishMem windowLt
    have windowStartNonneg : 0 ≤ windowStart :=
      startNonneg.trans windowStartMem.1
    have windowFinishLe : windowFinish ≤ elapsedTime initial length :=
      windowFinishMem.2.trans finishLe
    have windowBand :
        ∀ time ∈ Icc windowStart windowFinish,
          level / 2 ≤
              wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length time) ∧
            wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
              level := by
      intro time timeMem
      exact massBand time
        ⟨windowStartMem.1.trans timeMem.1,
          timeMem.2.trans windowFinishMem.2⟩
    have rawModulus :=
      wholeRestartPrefixFiniteBandTimeModulus_of_massBand
        initial length (start := windowStart) (finish := windowFinish)
        (lower := level / 2) (ceiling := level) observed
        windowStartNonneg windowLt windowFinishLe zeroFree multiplier
        multiplierNonneg multiplierLe windowBand
    have scaledModulus :=
      mul_le_mul_of_nonneg_left rawModulus
        (inv_nonneg.mpr levelPos.le)
    calc
      level⁻¹ *
            (∑ wave ∈ observed,
              complexCoordinateAmplitudeSq
                (wholeRestartPrefixPhysicalTrajectory initial length
                      windowFinish wave -
                  wholeRestartPrefixPhysicalTrajectory initial length
                      windowStart wave)) ≤
          level⁻¹ *
            (3 * (windowFinish - windowStart) * multiplier *
              (cubicConstant *
                  (level ^ 3 * (windowFinish - windowStart)) +
                nu.coeff * (level - level / 2))) := by
        simpa only [cubicConstant] using scaledModulus
      _ = 3 * (level ^ 2 * (windowFinish - windowStart)) *
            ((level ^ 2)⁻¹ * multiplier) *
            (cubicConstant *
                (level ^ 2 * (windowFinish - windowStart)) +
              nu.coeff / 2) := by
        field_simp [levelPos.ne']
        ring

theorem wholeRestartPrefixScaleCriticalPrehistoryWindowBudget
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    {start finish level : Real}
    (levelPos : 0 < level)
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ elapsedTime initial length)
    (massLe :
      ∀ time ∈ Icc start finish,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          level + 2) :
    IntervalIntegrable
        (fun time =>
          wholeStateVorticityGradientMass
            (wholeRestartPrefixPhysicalTrajectory initial length time))
        volume start finish ∧
      (((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
          (level⁻¹ *
            ∫ time in start..finish,
              wholeStateVorticityGradientMass
                (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
        level⁻¹ *
          (((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
              ((level + 2) ^ 3 * (finish - start)) +
            nu.coeff * (level + 2))) ∧
      ∀ (observed : Finset IntegerWavevector)
        (_zeroFree : ∀ wave ∈ observed, wave ≠ 0)
        (multiplier : Real)
        (_multiplierNonneg : 0 ≤ multiplier)
        (_multiplierLe : ∀ wave ∈ observed,
          integerWaveViscousMultiplier wave ≤ multiplier)
        (windowStart windowFinish : Real),
        windowStart ∈ Icc start finish →
        windowFinish ∈ Icc start finish →
        windowStart < windowFinish →
        level⁻¹ *
            (∑ wave ∈ observed,
              complexCoordinateAmplitudeSq
                (wholeRestartPrefixPhysicalTrajectory initial length
                      windowFinish wave -
                  wholeRestartPrefixPhysicalTrajectory initial length
                      windowStart wave)) ≤
          3 * (level ^ 2 * (windowFinish - windowStart)) *
            ((level ^ 2)⁻¹ * multiplier) *
            (level⁻¹ *
              (((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                  ((level + 2) ^ 3 * (windowFinish - windowStart)) +
                nu.coeff * (level + 2))) := by
  let cubicConstant : Real :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
  rcases wholeRestartPrefixFiniteBandWindowEnergy initial length
      (∅ : Finset IntegerWavevector) startNonneg startLtFinish finishLe
      (by simp) 0 (by norm_num) (by simp) massLe with
    ⟨energy, _energyNonneg, signedEnergy, gradientIntegrable,
      gradientLe, _emptyModulus⟩
  have boundaryLower :
      -(level + 2) ≤
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length finish) -
          wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length start) := by
    have startUpper := massLe start ⟨le_rfl, startLtFinish.le⟩
    have finishNonneg := wholeVorticityEuclideanMass_nonneg
      (wholeRestartPrefixPhysicalTrajectory initial length finish)
    linarith
  have energyUpper :
      energy ≤
        cubicConstant * ((level + 2) ^ 3 * (finish - start)) +
          nu.coeff * (level + 2) := by
    have scaledBoundary :=
      mul_le_mul_of_nonneg_left boundaryLower nu.coeff_pos.le
    have signedCubic :
        energy + nu.coeff *
            (wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length finish) -
              wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length start)) ≤
          cubicConstant * ((level + 2) ^ 3 * (finish - start)) := by
      simpa only [cubicConstant] using signedEnergy
    linarith
  have normalizedGradientLe :
      ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
          (level⁻¹ *
            ∫ time in start..finish,
              wholeStateVorticityGradientMass
                (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
        level⁻¹ *
          (cubicConstant * ((level + 2) ^ 3 * (finish - start)) +
            nu.coeff * (level + 2)) := by
    calc
      ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
            (level⁻¹ *
              ∫ time in start..finish,
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time)) =
          level⁻¹ *
            (((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
              ∫ time in start..finish,
                wholeStateVorticityGradientMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time)) := by
        ring
      _ ≤ level⁻¹ * energy :=
        mul_le_mul_of_nonneg_left gradientLe (inv_nonneg.mpr levelPos.le)
      _ ≤ level⁻¹ *
          (cubicConstant * ((level + 2) ^ 3 * (finish - start)) +
            nu.coeff * (level + 2)) :=
        mul_le_mul_of_nonneg_left energyUpper (inv_nonneg.mpr levelPos.le)
  refine ⟨gradientIntegrable, ?_, ?_⟩
  · simpa only [cubicConstant] using normalizedGradientLe
  · intro observed zeroFree multiplier multiplierNonneg multiplierLe
      windowStart windowFinish windowStartMem windowFinishMem windowLt
    have windowStartNonneg : 0 ≤ windowStart :=
      startNonneg.trans windowStartMem.1
    have windowFinishLe : windowFinish ≤ elapsedTime initial length :=
      windowFinishMem.2.trans finishLe
    have windowMassLe :
        ∀ time ∈ Icc windowStart windowFinish,
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
            level + 2 := by
      intro time timeMem
      exact massLe time
        ⟨windowStartMem.1.trans timeMem.1,
          timeMem.2.trans windowFinishMem.2⟩
    rcases wholeRestartPrefixFiniteBandWindowEnergy initial length observed
        windowStartNonneg windowLt windowFinishLe zeroFree multiplier
        multiplierNonneg multiplierLe windowMassLe with
      ⟨windowEnergy, _windowEnergyNonneg, windowSigned,
        _windowGradientIntegrable, _windowGradientLe, windowModulus⟩
    have windowBoundaryLower :
        -(level + 2) ≤
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length
                windowFinish) -
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length
                windowStart) := by
      have windowStartUpper :=
        windowMassLe windowStart ⟨le_rfl, windowLt.le⟩
      have windowFinishNonneg := wholeVorticityEuclideanMass_nonneg
        (wholeRestartPrefixPhysicalTrajectory initial length windowFinish)
      linarith
    have windowEnergyUpper :
        windowEnergy ≤
          cubicConstant *
              ((level + 2) ^ 3 * (windowFinish - windowStart)) +
            nu.coeff * (level + 2) := by
      have scaledBoundary :=
        mul_le_mul_of_nonneg_left windowBoundaryLower nu.coeff_pos.le
      have windowSignedCubic :
          windowEnergy + nu.coeff *
              (wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length
                    windowFinish) -
                wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length
                    windowStart)) ≤
            cubicConstant *
              ((level + 2) ^ 3 * (windowFinish - windowStart)) := by
        simpa only [cubicConstant] using windowSigned
      linarith
    have factorNonneg :
        0 ≤ 3 * (windowFinish - windowStart) * multiplier := by
      positivity
    have rawModulus := windowModulus.trans
      (mul_le_mul_of_nonneg_left windowEnergyUpper factorNonneg)
    have scaledModulus := mul_le_mul_of_nonneg_left rawModulus
      (inv_nonneg.mpr levelPos.le)
    calc
      level⁻¹ *
            (∑ wave ∈ observed,
              complexCoordinateAmplitudeSq
                (wholeRestartPrefixPhysicalTrajectory initial length
                      windowFinish wave -
                  wholeRestartPrefixPhysicalTrajectory initial length
                      windowStart wave)) ≤
          level⁻¹ *
            (3 * (windowFinish - windowStart) * multiplier *
              (cubicConstant *
                  ((level + 2) ^ 3 * (windowFinish - windowStart)) +
                nu.coeff * (level + 2))) := scaledModulus
      _ = 3 * (level ^ 2 * (windowFinish - windowStart)) *
            ((level ^ 2)⁻¹ * multiplier) *
            (level⁻¹ *
              (cubicConstant *
                  ((level + 2) ^ 3 * (windowFinish - windowStart)) +
                nu.coeff * (level + 2))) := by
        field_simp [levelPos.ne']

private theorem wholeRestartPrefixSuccLowOutputIntegral_eq_receipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index radius : Nat)
    {start finish : Real}
    (joinLeStart : elapsedTime initial index ≤ start)
    (startLeFinish : start ≤ finish)
    (finishLe : finish ≤ elapsedTime initial (index + 1)) :
    (∫ time in start..finish,
        wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
          radius
          (wholeRestartPrefixPhysicalTrajectory initial (index + 1) time)) =
      ∫ localTime in
          start - elapsedTime initial index..
            finish - elapsedTime initial index,
        wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
          radius
          (wholeRestartReceiptPhysicalTrajectory
            (run initial index).contact.prefixReceipt localTime) := by
  let joinTime := elapsedTime initial index
  let receipt := (run initial index).contact.prefixReceipt
  have finishLeExpanded :
      finish ≤ joinTime + (run initial index).contact.time.1 := by
    simpa only [joinTime, elapsedTime_succ] using finishLe
  calc
    (∫ time in start..finish,
        wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
          radius
          (wholeRestartPrefixPhysicalTrajectory initial (index + 1) time)) =
        ∫ time in start..finish,
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
            radius
            (wholeRestartReceiptPhysicalTrajectory
              receipt (time - joinTime)) := by
      apply intervalIntegral.integral_congr
      intro time timeMem
      have timeIcc : time ∈ Icc start finish := by
        simpa [uIcc_of_le startLeFinish] using timeMem
      let localTime :
          Icc (0 : Real) (run initial index).contact.time.1 :=
        ⟨time - joinTime,
          ⟨sub_nonneg.mpr (joinLeStart.trans timeIcc.1),
            by linarith [timeIcc.2, finishLeExpanded]⟩⟩
      have chart :=
        wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
          initial index localTime
      have absoluteEq : joinTime + localTime.1 = time := by
        dsimp only [localTime]
        ring
      unfold wholeRestartReceiptPhysicalTrajectory
      change
        wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
            radius
              (wholeRestartPrefixPhysicalTrajectory initial (index + 1) time) =
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
            radius
              (receipt.wholePath
                (projIcc 0 (run initial index).contact.time.1
                  (run initial index).contact.prefixReceipt.requestedTimePos.le
                  (time - joinTime)))
      rw [projIcc_of_mem
        (run initial index).contact.prefixReceipt.requestedTimePos.le
        localTime.2]
      rw [← chart]
      simp only [joinTime, absoluteEq]
    _ = ∫ localTime in
          start - elapsedTime initial index..
            finish - elapsedTime initial index,
        wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
          radius
          (wholeRestartReceiptPhysicalTrajectory
            (run initial index).contact.prefixReceipt localTime) := by
      simpa only [joinTime, receipt] using
        (intervalIntegral.integral_comp_sub_right
          (f := fun localTime : Real =>
            wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
              radius
              (wholeRestartReceiptPhysicalTrajectory receipt localTime))
          (a := start) (b := finish) joinTime)

private theorem wholeRestartPrefixVorticityMass_increment_between_le_lowOutputPayment
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ (length radius : Nat) {start finish ceiling : Real},
      0 ≤ start →
      start < finish →
      finish ≤ elapsedTime initial length →
      0 ≤ ceiling →
      (0 < radius) →
      (4368 * biotSavartSerrinConstant * ceiling ≤
        (radius : Real) * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) →
      (∀ time ∈ Icc start finish,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          ceiling) →
      nu.coeff *
          (wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length finish) -
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length start)) ≤
        ∫ time in start..finish,
          wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
            radius
            (wholeRestartPrefixPhysicalTrajectory initial length time) := by
  intro length
  induction length with
  | zero =>
      intro radius start finish ceiling startNonneg startLtFinish finishLe
        _ceilingNonneg _radiusPos _radiusAbsorbs _massLe
      rw [elapsedTime_zero] at finishLe
      linarith
  | succ length inductionHypothesis =>
      intro radius start finish ceiling startNonneg startLtFinish finishLe
        ceilingNonneg radiusPos radiusAbsorbs massLe
      let joinTime := elapsedTime initial length
      let receipt := (run initial length).contact.prefixReceipt
      have joinNonneg : 0 ≤ joinTime :=
        ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
          initial length
      have finishLeExpanded :
          finish ≤ joinTime + (run initial length).contact.time.1 := by
        simpa only [joinTime, elapsedTime_succ] using finishLe
      have priorChart
          (time : Real)
          (timeLeJoin : time ≤ joinTime) :
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
            wholeRestartPrefixPhysicalTrajectory initial length time := by
        simp only [wholeRestartPrefixPhysicalTrajectory]
        exact endpointSplice_of_le
          joinTime
          (wholeRestartPrefixPhysicalTrajectory initial length)
          (wholeRestartReceiptPhysicalTrajectory receipt)
          time timeLeJoin
      have receiptChart
          (time : Real)
          (joinLeTime : joinTime ≤ time)
          (timeLeFinish :
            time ≤ joinTime + (run initial length).contact.time.1) :
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
            receipt.wholePath
              ⟨time - joinTime,
                ⟨sub_nonneg.mpr joinLeTime,
                  by linarith⟩⟩ := by
        let localTime :
            Icc (0 : Real) (run initial length).contact.time.1 :=
          ⟨time - joinTime,
            ⟨sub_nonneg.mpr joinLeTime,
              by linarith⟩⟩
        have chart :=
          wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
            initial length localTime
        have addLocal : joinTime + localTime.1 = time := by
          dsimp only [joinTime, localTime]
          ring
        simpa only [receipt, joinTime, addLocal] using chart
      by_cases finishLeJoin : finish ≤ joinTime
      · have priorMassLe :
            ∀ time ∈ Icc start finish,
              wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
                ceiling := by
          intro time timeMem
          rw [← priorChart time (timeMem.2.trans finishLeJoin)]
          exact massLe time timeMem
        have prior :=
          inductionHypothesis radius startNonneg startLtFinish finishLeJoin
            ceilingNonneg radiusPos radiusAbsorbs priorMassLe
        have priorIntegralEq :
            (∫ time in start..finish,
                wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                  radius
                  (wholeRestartPrefixPhysicalTrajectory initial
                    (length + 1) time)) =
              ∫ time in start..finish,
                wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                  radius
                  (wholeRestartPrefixPhysicalTrajectory initial length time) := by
          apply intervalIntegral.integral_congr
          intro time timeMem
          have timeIcc : time ∈ Icc start finish := by
            simpa [uIcc_of_le startLtFinish.le] using timeMem
          change
            wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                radius
                (wholeRestartPrefixPhysicalTrajectory initial
                  (length + 1) time) =
              wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                radius
                (wholeRestartPrefixPhysicalTrajectory initial length time)
          rw [priorChart time (timeIcc.2.trans finishLeJoin)]
        rw [priorIntegralEq,
          priorChart finish finishLeJoin,
          priorChart start (startLtFinish.le.trans finishLeJoin)]
        exact prior
      · have joinLtFinish : joinTime < finish := lt_of_not_ge finishLeJoin
        by_cases startLtJoin : start < joinTime
        · have firstMassLe :
              ∀ time ∈ Icc start joinTime,
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
                  ceiling := by
            intro time timeMem
            rw [← priorChart time timeMem.2]
            exact massLe time
              ⟨timeMem.1, timeMem.2.trans joinLtFinish.le⟩
          have first :=
            inductionHypothesis radius startNonneg startLtJoin le_rfl
              ceilingNonneg radiusPos radiusAbsorbs firstMassLe
          have localFinishPos : 0 < finish - joinTime :=
            sub_pos.mpr joinLtFinish
          have localFinishLe :
              finish - joinTime ≤ (run initial length).contact.time.1 :=
            by linarith
          have secondMassLe :
              ∀ time :
                  Icc (0 : Real) (run initial length).contact.time.1,
                0 ≤ time.1 → time.1 ≤ finish - joinTime →
                wholeVorticityEuclideanMass (receipt.wholePath time) ≤
                  ceiling := by
            intro time _timeNonneg timeLe
            have absoluteMem :
                joinTime + time.1 ∈ Icc start finish := by
              constructor
              · linarith [time.2.1]
              · linarith
            have chart :=
              wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
                initial length time
            have globalBound :
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                      (joinTime + time.1)) ≤ ceiling :=
              massLe _ absoluteMem
            rw [show joinTime = elapsedTime initial length by rfl] at globalBound
            rw [chart] at globalBound
            exact globalBound
          have second :=
            receiptVorticityMass_increment_between_le_lowOutputPayment
              receipt (start := 0) (finish := finish - joinTime)
              (ceiling := ceiling) le_rfl localFinishPos localFinishLe
              radius radiusPos secondMassLe radiusAbsorbs
          have startEq := priorChart start startLtJoin.le
          have joinPriorEq := priorChart joinTime le_rfl
          have joinReceiptEq := receiptChart joinTime le_rfl
            (by linarith [(run initial length).contact.time_pos])
          have finishReceiptEq := receiptChart finish joinLtFinish.le
            finishLeExpanded
          have firstGlobal :
              nu.coeff *
                  (wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) joinTime) -
                    wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) start)) ≤
                ∫ time in start..joinTime,
                  wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                    radius
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time) := by
            have firstIntegralEq :
                (∫ time in start..joinTime,
                    wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                      radius
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time)) =
                  ∫ time in start..joinTime,
                    wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                      radius
                      (wholeRestartPrefixPhysicalTrajectory initial length time) := by
              apply intervalIntegral.integral_congr
              intro time timeMem
              have timeIcc : time ∈ Icc start joinTime := by
                simpa [uIcc_of_le startLtJoin.le] using timeMem
              change
                wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                    radius
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time) =
                  wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                    radius
                    (wholeRestartPrefixPhysicalTrajectory initial length time)
              rw [priorChart time timeIcc.2]
            rw [firstIntegralEq, joinPriorEq, startEq]
            exact first
          have secondIntegralEq :=
            wholeRestartPrefixSuccLowOutputIntegral_eq_receipt
              initial length radius le_rfl joinLtFinish.le finishLe
          have secondGlobal :
              nu.coeff *
                  (wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) finish) -
                    wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) joinTime)) ≤
                ∫ time in joinTime..finish,
                  wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                    radius
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time) := by
            rw [secondIntegralEq, finishReceiptEq, joinReceiptEq]
            simpa only [receipt, sub_zero, sub_self] using second
          have fullContinuous :=
            wholeRestartPrefixLowOutputMass_continuousOn
              initial (length + 1) radius
          have firstIntegrable :
              IntervalIntegrable
                (fun time : Real =>
                  wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                    radius
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time)) volume start joinTime :=
            ContinuousOn.intervalIntegrable_of_Icc startLtJoin.le
              (fullContinuous.mono
                (Icc_subset_Icc startNonneg
                  (joinLtFinish.le.trans finishLe)))
          have secondIntegrable :
              IntervalIntegrable
                (fun time : Real =>
                  wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                    radius
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time)) volume joinTime finish :=
            ContinuousOn.intervalIntegrable_of_Icc joinLtFinish.le
              (fullContinuous.mono
                (Icc_subset_Icc joinNonneg finishLe))
          calc
            nu.coeff *
                (wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) finish) -
                  wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) start)) =
                nu.coeff *
                    (wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) joinTime) -
                      wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) start)) +
                  nu.coeff *
                    (wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) finish) -
                      wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) joinTime)) := by ring
            _ ≤
                (∫ time in start..joinTime,
                  wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                    radius
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time)) +
                ∫ time in joinTime..finish,
                  wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                    radius
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time) :=
              add_le_add firstGlobal secondGlobal
            _ = ∫ time in start..finish,
                  wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass
                    radius
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time) :=
              intervalIntegral.integral_add_adjacent_intervals
                firstIntegrable secondIntegrable
        · have joinLeStart : joinTime ≤ start := le_of_not_gt startLtJoin
          have localStartNonneg : 0 ≤ start - joinTime :=
            sub_nonneg.mpr joinLeStart
          have localStartLtFinish :
              start - joinTime < finish - joinTime :=
            sub_lt_sub_right startLtFinish joinTime
          have localFinishLe :
              finish - joinTime ≤ (run initial length).contact.time.1 :=
            by linarith
          have localMassLe :
              ∀ time :
                  Icc (0 : Real) (run initial length).contact.time.1,
                start - joinTime ≤ time.1 →
                time.1 ≤ finish - joinTime →
                wholeVorticityEuclideanMass (receipt.wholePath time) ≤
                  ceiling := by
            intro time startLeTime timeLeFinish
            have absoluteMem :
                joinTime + time.1 ∈ Icc start finish := by
              constructor <;> linarith
            have chart :=
              wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
                initial length time
            have globalBound :
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial (length + 1)
                      (joinTime + time.1)) ≤ ceiling :=
              massLe _ absoluteMem
            rw [show joinTime = elapsedTime initial length by rfl] at globalBound
            rw [chart] at globalBound
            exact globalBound
          have localEstimate :=
            receiptVorticityMass_increment_between_le_lowOutputPayment
              receipt (start := start - joinTime)
              (finish := finish - joinTime) (ceiling := ceiling)
              localStartNonneg localStartLtFinish localFinishLe
              radius radiusPos localMassLe radiusAbsorbs
          have startReceiptEq := receiptChart start joinLeStart
            (startLtFinish.le.trans finishLeExpanded)
          have finishReceiptEq := receiptChart finish joinLtFinish.le
            finishLeExpanded
          have integralEq :=
            wholeRestartPrefixSuccLowOutputIntegral_eq_receipt
              initial length radius joinLeStart startLtFinish.le finishLe
          rw [integralEq, finishReceiptEq, startReceiptEq]
          simpa only [receipt] using localEstimate

/-- Every positive source level contains a last-hit actual parabolic window
whose vorticity mass remains in the critical dyadic band and whose
inverse-square time span is paid by the same whole NS receipt law. -/
theorem sourceGeneratedNativeAccumulationScaleCriticalLastHitWindow
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (level : Real)
    (levelPos : 0 < level)
    (initialLeHalf :
      restartPhysicalVorticityMass initial 0 ≤ level / 2) :
    ∃ start finish : Nat, ∃ beginTime endTime : Real,
      start < finish ∧
      beginTime ∈
        Icc (elapsedTime initial (start + 1))
          (elapsedTime initial (finish + 1)) ∧
      endTime ∈
        Icc (elapsedTime initial (start + 1))
          (elapsedTime initial (finish + 1)) ∧
      beginTime < endTime ∧
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
            beginTime) = level / 2 ∧
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
            endTime) = level ∧
      (∀ time ∈ Icc beginTime endTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ≤ level) ∧
      (∀ time ∈
          Icc (elapsedTime initial 1)
            (elapsedTime initial (finish + 1)),
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
              time) ≤
          level + 2) ∧
      nu.coeff ^ 3 * (2 * Real.pi) ^ 2 ≤
        (9 * 1557504 * biotSavartSerrinConstant ^ 2) *
          (level ^ 2 * (endTime - beginTime)) := by
  obtain ⟨start, finish, startLtFinish, _elapsedLt,
      startMassLe, finishMassGe, _inverseAction,
      _interiorCeiling, prehistoryCeiling, _cubicSpan, _normalizedSpan,
      _chart⟩ :=
    sourceGeneratedNativeAccumulationInverseLevelActualIcoNonlinearAction
      initial elapsedBounded level levelPos initialLeHalf
  obtain ⟨beginTime, endTime, beginMem, endMem, beginLtEnd,
      beginMass, endMass, interiorMass⟩ :=
    actualPrefix_lastHit_vorticityMass_window
      initial level levelPos start finish startLtFinish
        startMassLe finishMassGe
  have beginNonneg : 0 ≤ beginTime := by
    exact
      (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
        initial (start + 1)).trans beginMem.1
  have cubic :=
    wholeRestartPrefixVorticityMass_increment_between_le_cubicCeiling
      initial (finish + 1) beginNonneg beginLtEnd endMem.2
        levelPos.le (fun time timeMem => (interiorMass time timeMem).2)
  rw [beginMass, endMass] at cubic
  let scaleConstant : Real :=
    9 * 1557504 * biotSavartSerrinConstant ^ 2
  let denominator : Real :=
    2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
  have denominatorPos : 0 < denominator := by
    dsimp only [denominator]
    exact mul_pos (by norm_num)
      (mul_pos (sq_pos_of_pos nu.coeff_pos)
        (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)))
  have scaled :=
    mul_le_mul_of_nonneg_left cubic denominatorPos.le
  have scaledClean :
      nu.coeff ^ 3 * (2 * Real.pi) ^ 2 * level ≤
        scaleConstant * (level ^ 3 * (endTime - beginTime)) := by
    calc
      nu.coeff ^ 3 * (2 * Real.pi) ^ 2 * level =
          denominator * (nu.coeff * (level - level / 2)) := by
        dsimp only [denominator]
        ring
      _ ≤ denominator *
          ((scaleConstant / denominator) *
            (level ^ 3 * (endTime - beginTime))) := by
        simpa only [scaleConstant, denominator] using scaled
      _ = scaleConstant *
          (level ^ 3 * (endTime - beginTime)) := by
        field_simp [ne_of_gt denominatorPos]
  have normalizedSpan :
      nu.coeff ^ 3 * (2 * Real.pi) ^ 2 ≤
        scaleConstant * (level ^ 2 * (endTime - beginTime)) := by
    apply le_of_mul_le_mul_right _ levelPos
    calc
      (nu.coeff ^ 3 * (2 * Real.pi) ^ 2) * level =
          nu.coeff ^ 3 * (2 * Real.pi) ^ 2 * level := by ring
      _ ≤ scaleConstant *
          (level ^ 3 * (endTime - beginTime)) := scaledClean
      _ = (scaleConstant *
          (level ^ 2 * (endTime - beginTime))) * level := by ring
  exact ⟨start, finish, beginTime, endTime, startLtFinish,
    beginMem, endMem, beginLtEnd, beginMass, endMass,
    interiorMass, prehistoryCeiling,
    by simpa only [scaleConstant] using normalizedSpan⟩

/-- A source last-hit band contains a fixed normalized interior time window.
Every finite Fourier band on that window obeys the scale-invariant time
modulus generated by the same finite whole-PDE prefix. -/
theorem sourceGeneratedNativeAccumulationScaleCriticalFixedWindowTimeModulus
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (level : Real)
    (levelPos : 0 < level)
    (initialLeHalf :
      restartPhysicalVorticityMass initial 0 ≤ level / 2) :
    let cubicSpanConstant : Real :=
      9 * 1557504 * biotSavartSerrinConstant ^ 2
    let fixedHalfWindow : Real :=
      nu.coeff ^ 3 * (2 * Real.pi) ^ 2 /
        (4 * cubicSpanConstant)
    ∃ length : Nat, ∃ leftTime rightTime : Real,
      0 < fixedHalfWindow ∧
      0 ≤ leftTime ∧
      leftTime < rightTime ∧
      rightTime ≤ elapsedTime initial length ∧
      level ^ 2 * (rightTime - leftTime) = 2 * fixedHalfWindow ∧
      (∀ time ∈ Icc leftTime rightTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
            level) ∧
      ∀ (observed : Finset IntegerWavevector)
        (_zeroFree : ∀ wave ∈ observed, wave ≠ 0)
        (multiplier : Real)
        (_multiplierNonneg : 0 ≤ multiplier)
        (_multiplierLe : ∀ wave ∈ observed,
          integerWaveViscousMultiplier wave ≤ multiplier)
        (startTime finishTime : Real),
        startTime ∈ Icc leftTime rightTime →
        finishTime ∈ Icc leftTime rightTime →
        startTime < finishTime →
        level⁻¹ *
            (∑ wave ∈ observed,
              complexCoordinateAmplitudeSq
                (wholeRestartPrefixPhysicalTrajectory initial length
                      finishTime wave -
                  wholeRestartPrefixPhysicalTrajectory initial length
                      startTime wave)) ≤
          3 * (level ^ 2 * (finishTime - startTime)) *
            ((level ^ 2)⁻¹ * multiplier) *
            (((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                (level ^ 2 * (finishTime - startTime)) +
              nu.coeff / 2) := by
  dsimp only
  let cubicSpanConstant : Real :=
    9 * 1557504 * biotSavartSerrinConstant ^ 2
  let fixedHalfWindow : Real :=
    nu.coeff ^ 3 * (2 * Real.pi) ^ 2 /
      (4 * cubicSpanConstant)
  obtain ⟨start, finish, beginTime, endTime, _startLtFinish,
      beginMem, endMem, beginLtEnd, _beginMass, _endMass,
      interiorMass, _prehistoryCeiling, scaleSpan⟩ :=
    sourceGeneratedNativeAccumulationScaleCriticalLastHitWindow
      initial elapsedBounded level levelPos initialLeHalf
  have cubicSpanConstantPos : 0 < cubicSpanConstant := by
    dsimp only [cubicSpanConstant]
    exact mul_pos (mul_pos (by norm_num) (by norm_num))
      (sq_pos_of_pos biotSavartSerrinConstant_pos)
  have fixedHalfWindowPos : 0 < fixedHalfWindow := by
    dsimp only [fixedHalfWindow]
    exact div_pos
      (mul_pos (pow_pos nu.coeff_pos 3)
        (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)))
      (mul_pos (by norm_num) cubicSpanConstantPos)
  have normalizedSpan :
      nu.coeff ^ 3 * (2 * Real.pi) ^ 2 / cubicSpanConstant ≤
        level ^ 2 * (endTime - beginTime) := by
    apply (div_le_iff₀ cubicSpanConstantPos).2
    calc
      nu.coeff ^ 3 * (2 * Real.pi) ^ 2 ≤
          cubicSpanConstant * (level ^ 2 * (endTime - beginTime)) := by
        simpa only [cubicSpanConstant] using scaleSpan
      _ = (level ^ 2 * (endTime - beginTime)) * cubicSpanConstant :=
        mul_comm _ _
  have fourFixedHalfWindow :
      4 * fixedHalfWindow =
        nu.coeff ^ 3 * (2 * Real.pi) ^ 2 / cubicSpanConstant := by
    dsimp only [fixedHalfWindow]
    field_simp [cubicSpanConstantPos.ne']
  have twoFixedHalfWindowLe :
      2 * fixedHalfWindow ≤ level ^ 2 * (endTime - beginTime) := by
    rw [← fourFixedHalfWindow] at normalizedSpan
    linarith
  have levelSqPos : 0 < level ^ 2 := sq_pos_of_pos levelPos
  have marginLeSpan :
      2 * fixedHalfWindow / level ^ 2 ≤ endTime - beginTime := by
    apply (div_le_iff₀ levelSqPos).2
    simpa only [mul_comm] using twoFixedHalfWindowLe
  have normalizedHalfWindowPos :
      0 < fixedHalfWindow / level ^ 2 :=
    div_pos fixedHalfWindowPos levelSqPos
  have halfMarginLe :
      fixedHalfWindow / level ^ 2 ≤
        (endTime - beginTime) / 2 := by
    have twiceHalfWindow :
        2 * (fixedHalfWindow / level ^ 2) =
          2 * fixedHalfWindow / level ^ 2 := by ring
    linarith
  let centerTime : Real := (beginTime + endTime) / 2
  let leftTime : Real := centerTime - fixedHalfWindow / level ^ 2
  let rightTime : Real := centerTime + fixedHalfWindow / level ^ 2
  have beginLeLeft : beginTime ≤ leftTime := by
    dsimp only [leftTime, centerTime]
    linarith [halfMarginLe]
  have rightLeEnd : rightTime ≤ endTime := by
    dsimp only [rightTime, centerTime]
    linarith [halfMarginLe]
  have leftLtRight : leftTime < rightTime := by
    dsimp only [leftTime, rightTime]
    linarith
  have beginNonneg : 0 ≤ beginTime :=
    (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
      initial (start + 1)).trans beginMem.1
  have leftNonneg : 0 ≤ leftTime := beginNonneg.trans beginLeLeft
  have rightLeElapsed :
      rightTime ≤ elapsedTime initial (finish + 1) :=
    rightLeEnd.trans endMem.2
  have normalizedDuration :
      level ^ 2 * (rightTime - leftTime) = 2 * fixedHalfWindow := by
    dsimp only [leftTime, rightTime]
    field_simp [levelPos.ne']
    ring
  have fixedWindowBand :
      ∀ time ∈ Icc leftTime rightTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ≤ level := by
    intro time timeMem
    exact interiorMass time
      ⟨beginLeLeft.trans timeMem.1, timeMem.2.trans rightLeEnd⟩
  refine ⟨finish + 1, leftTime, rightTime, fixedHalfWindowPos,
    leftNonneg, leftLtRight, rightLeElapsed, normalizedDuration,
    fixedWindowBand, ?_⟩
  intro observed zeroFree multiplier multiplierNonneg multiplierLe
    startTime finishTime startMem finishMem startLtFinish
  have startNonneg : 0 ≤ startTime := leftNonneg.trans startMem.1
  have finishLeElapsed :
      finishTime ≤ elapsedTime initial (finish + 1) :=
    finishMem.2.trans rightLeElapsed
  have sourceBand :
      ∀ time ∈ Icc startTime finishTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ≤ level := by
    intro time timeMem
    exact fixedWindowBand time
      ⟨startMem.1.trans timeMem.1, timeMem.2.trans finishMem.2⟩
  have rawModulus :=
    wholeRestartPrefixFiniteBandTimeModulus_of_massBand
      initial (finish + 1) (start := startTime) (finish := finishTime)
      (lower := level / 2) (ceiling := level) observed
      startNonneg startLtFinish finishLeElapsed zeroFree multiplier
      multiplierNonneg multiplierLe sourceBand
  have scaledModulus :=
    mul_le_mul_of_nonneg_left rawModulus (inv_nonneg.mpr levelPos.le)
  calc
    level⁻¹ *
          (∑ wave ∈ observed,
            complexCoordinateAmplitudeSq
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                    finishTime wave -
                wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                    startTime wave)) ≤
        level⁻¹ *
          (3 * (finishTime - startTime) * multiplier *
            (((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                (level ^ 3 * (finishTime - startTime)) +
              nu.coeff * (level - level / 2))) := scaledModulus
    _ = 3 * (level ^ 2 * (finishTime - startTime)) *
          ((level ^ 2)⁻¹ * multiplier) *
          (((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
              (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
              (level ^ 2 * (finishTime - startTime)) +
            nu.coeff / 2) := by
      field_simp [levelPos.ne']
      ring

private theorem lastHitWindow_generates_actualNondecreasingSubreceipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    (beginTime endTime : Real)
    (beginNonneg : 0 ≤ beginTime)
    (beginLtEnd : beginTime < endTime)
    (endLe : endTime ≤ elapsedTime initial length)
    (massLeEnd :
      ∀ time ∈ Icc beginTime endTime,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length endTime)) :
    ∃ edge : Nat,
    ∃ segmentInitial : ComplexVorticityHilbertState,
    ∃ segmentTime : Real,
    ∃ segmentTimePos : 0 < segmentTime,
    ∃ segmentReceipt :
        WholeContinuousMildSerrinReceipt nu segmentInitial segmentTime,
    ∃ absoluteTime : Icc (0 : Real) segmentTime → Real,
      edge < length ∧
      (∀ localTime,
        absoluteTime localTime ∈ Icc beginTime endTime ∧
        segmentReceipt.wholePath localTime =
          wholeRestartPrefixPhysicalTrajectory initial length
            (absoluteTime localTime)) ∧
      wholeVorticityEuclideanMass segmentInitial ≤
        wholeVorticityEuclideanMass
          (segmentReceipt.wholePath
            ⟨segmentTime, ⟨segmentTimePos.le, le_rfl⟩⟩) := by
  have endPos : 0 < endTime := beginNonneg.trans_lt beginLtEnd
  obtain ⟨edge, ⟨edgeLt, endWindow⟩, _edgeUnique⟩ :=
    wholeRestartPhysicalWindow_existsUnique initial
      (length := length) (time := endTime) ⟨endPos, endLe⟩
  change
    elapsedTime initial edge < endTime ∧
      endTime ≤ elapsedTime initial (edge + 1) at endWindow
  let joinTime : Real := elapsedTime initial edge
  let segmentStart : Real := max beginTime joinTime
  let localStart : Real := segmentStart - joinTime
  let localFinish : Real := endTime - joinTime
  have joinLtEnd : joinTime < endTime := endWindow.1
  have segmentStartLtEnd : segmentStart < endTime := by
    exact max_lt beginLtEnd joinLtEnd
  have segmentStartLeEnd : segmentStart ≤ endTime := segmentStartLtEnd.le
  have beginLeSegmentStart : beginTime ≤ segmentStart := le_max_left _ _
  have joinLeSegmentStart : joinTime ≤ segmentStart := le_max_right _ _
  have localStartNonneg : 0 ≤ localStart := sub_nonneg.mpr joinLeSegmentStart
  have localStartLtFinish : localStart < localFinish := by
    dsimp only [localStart, localFinish]
    linarith
  have localFinishLe :
      localFinish ≤ (run initial edge).contact.time.1 := by
    dsimp only [localFinish, joinTime]
    rw [elapsedTime_succ] at endWindow
    linarith [endWindow.2]
  let sourceReceipt := (run initial edge).contact.prefixReceipt
  have localStartLtSource :
      localStart < (run initial edge).contact.time.1 :=
    localStartLtFinish.trans_le localFinishLe
  let suffixReceipt :=
    positiveTimeSuffixWholeContinuousMildSerrinReceipt
      sourceReceipt localStart localStartNonneg localStartLtSource
  have segmentTimePos : 0 < localFinish - localStart :=
    sub_pos.mpr localStartLtFinish
  have segmentTimeLe :
      localFinish - localStart ≤
        (run initial edge).contact.time.1 - localStart :=
    sub_le_sub_right localFinishLe localStart
  let segmentReceipt :=
    restrictWholeContinuousMildSerrinReceipt
      segmentTimePos segmentTimeLe suffixReceipt
  let absoluteTime : Icc (0 : Real) (localFinish - localStart) → Real :=
    fun localTime => segmentStart + localTime.1
  have absoluteTimeMem
      (localTime : Icc (0 : Real) (localFinish - localStart)) :
      absoluteTime localTime ∈ Icc beginTime endTime := by
    constructor
    · exact beginLeSegmentStart.trans
        (le_add_of_nonneg_right localTime.2.1)
    · dsimp only [absoluteTime]
      have localUpper := localTime.2.2
      dsimp only [localFinish, localStart, segmentStart, joinTime] at localUpper ⊢
      linarith
  have localSourceTime
      (localTime : Icc (0 : Real) (localFinish - localStart)) :
      localStart + localTime.1 ∈
        Icc (0 : Real) (run initial edge).contact.time.1 := by
    constructor
    · exact add_nonneg localStartNonneg localTime.2.1
    · have localUpper := localTime.2.2
      linarith
  have pathEq
      (localTime : Icc (0 : Real) (localFinish - localStart)) :
      segmentReceipt.wholePath localTime =
        wholeRestartPrefixPhysicalTrajectory initial length
          (absoluteTime localTime) := by
    let sourceLocalTime :
        Icc (0 : Real) (run initial edge).contact.time.1 :=
      ⟨localStart + localTime.1, localSourceTime localTime⟩
    have absoluteEq :
        absoluteTime localTime =
          elapsedTime initial edge + sourceLocalTime.1 := by
      dsimp only [absoluteTime, sourceLocalTime, localStart, segmentStart,
        joinTime]
      ring
    have absoluteLeShort :
        absoluteTime localTime ≤ elapsedTime initial (edge + 1) := by
      rw [absoluteEq, elapsedTime_succ]
      change
        elapsedTime initial edge + (localStart + localTime.1) ≤
          elapsedTime initial edge + (run initial edge).contact.time.1
      simpa only [add_comm] using
        add_le_add_left (localSourceTime localTime).2
          (elapsedTime initial edge)
    have prefixEq :
        wholeRestartPrefixPhysicalTrajectory initial length
            (absoluteTime localTime) =
          wholeRestartPrefixPhysicalTrajectory initial (edge + 1)
            (absoluteTime localTime) := by
      exact wholeRestartPrefixPhysicalTrajectory_eq_of_le initial
        (Nat.succ_le_of_lt edgeLt) absoluteLeShort
    have sourceChart :=
      wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
        initial edge sourceLocalTime
    rw [prefixEq, absoluteEq, sourceChart]
    rfl
  have endpointNondecreasing :
      wholeVorticityEuclideanMass
          (sourceReceipt.wholePath
            (wholeContinuousMildSerrinSuffixStartTime sourceReceipt
              localStart localStartNonneg localStartLtSource)) ≤
        wholeVorticityEuclideanMass
          (segmentReceipt.wholePath
            ⟨localFinish - localStart,
              ⟨segmentTimePos.le, le_rfl⟩⟩) := by
    let zero : Icc (0 : Real) (localFinish - localStart) :=
      ⟨0, ⟨le_rfl, segmentTimePos.le⟩⟩
    let terminal : Icc (0 : Real) (localFinish - localStart) :=
      ⟨localFinish - localStart, ⟨segmentTimePos.le, le_rfl⟩⟩
    have initialEq :
        segmentReceipt.wholePath zero =
          sourceReceipt.wholePath
            (wholeContinuousMildSerrinSuffixStartTime sourceReceipt
              localStart localStartNonneg localStartLtSource) :=
      segmentReceipt.wholePath_initial
    have terminalAbsoluteEq : absoluteTime terminal = endTime := by
      dsimp only [absoluteTime, terminal, localFinish, localStart,
        segmentStart, joinTime]
      ring
    calc
      wholeVorticityEuclideanMass
          (sourceReceipt.wholePath
            (wholeContinuousMildSerrinSuffixStartTime sourceReceipt
              localStart localStartNonneg localStartLtSource)) =
          wholeVorticityEuclideanMass
            (segmentReceipt.wholePath zero) :=
        congrArg wholeVorticityEuclideanMass initialEq.symm
      _ = wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length
              (absoluteTime zero)) :=
        congrArg wholeVorticityEuclideanMass (pathEq zero)
      _ ≤ wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length endTime) :=
        massLeEnd _ (absoluteTimeMem zero)
      _ = wholeVorticityEuclideanMass
            (segmentReceipt.wholePath terminal) := by
        apply congrArg wholeVorticityEuclideanMass
        exact ((pathEq terminal).trans
          (congrArg
            (wholeRestartPrefixPhysicalTrajectory initial length)
            terminalAbsoluteEq)).symm
  exact ⟨edge,
    sourceReceipt.wholePath
      (wholeContinuousMildSerrinSuffixStartTime sourceReceipt
        localStart localStartNonneg localStartLtSource),
    localFinish - localStart, segmentTimePos,
    segmentReceipt, absoluteTime, edgeLt,
    fun localTime => ⟨absoluteTimeMem localTime, pathEq localTime⟩,
    endpointNondecreasing⟩

/-- A source last-hit band generates an actual subreceipt whose endpoint is
nondecreasing.  The same subreceipt therefore selects a nonvanishing state
with a scale-critical tangent/gradient budget; its path still commutes with
the original finite whole-PDE prefix. -/
theorem sourceGeneratedNativeAccumulationScaleCriticalLastHitTangentGradientState
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (level : Real)
    (levelPos : 0 < level)
    (initialLeHalf :
      restartPhysicalVorticityMass initial 0 ≤ level / 2) :
    let tangentGradientConstant : Real :=
      (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
        (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
    ∃ start finish edge : Nat,
    ∃ beginTime endTime : Real,
    ∃ segmentInitial : ComplexVorticityHilbertState,
    ∃ segmentTime : Real,
    ∃ segmentTimePos : 0 < segmentTime,
    ∃ segmentReceipt :
        WholeContinuousMildSerrinReceipt nu segmentInitial segmentTime,
    ∃ absoluteTime : Icc (0 : Real) segmentTime → Real,
    ∃ sample : Icc (0 : Real) segmentTime,
      start < finish ∧
      beginTime ∈
        Icc (elapsedTime initial (start + 1))
          (elapsedTime initial (finish + 1)) ∧
      endTime ∈
        Icc (elapsedTime initial (start + 1))
          (elapsedTime initial (finish + 1)) ∧
      beginTime < endTime ∧
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
            beginTime) = level / 2 ∧
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
            endTime) = level ∧
      (∀ time ∈ Icc beginTime endTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ≤ level) ∧
      nu.coeff ^ 3 * (2 * Real.pi) ^ 2 ≤
        (9 * 1557504 * biotSavartSerrinConstant ^ 2) *
          (level ^ 2 * (endTime - beginTime)) ∧
      edge < finish + 1 ∧
      (∀ localTime,
        absoluteTime localTime ∈ Icc beginTime endTime ∧
        segmentReceipt.wholePath localTime =
          wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
            (absoluteTime localTime)) ∧
      wholeVorticityEuclideanMass segmentInitial ≤
        wholeVorticityEuclideanMass
          (segmentReceipt.wholePath
            ⟨segmentTime, ⟨segmentTimePos.le, le_rfl⟩⟩) ∧
      1 / 2 ≤ level⁻¹ *
        wholeVorticityEuclideanMass (segmentReceipt.wholePath sample) ∧
      level⁻¹ *
          wholeVorticityEuclideanMass (segmentReceipt.wholePath sample) ≤ 1 ∧
      (Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (segmentReceipt.wholePath sample wave)) ∧
      (level ^ 3)⁻¹ *
          (‖puncturedEuclideanSpaceTimeState
                segmentReceipt.wholeTangent sample‖ ^ 2 +
            ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
              wholeStateVorticityGradientMass
                (segmentReceipt.wholePath sample)) ≤
        tangentGradientConstant := by
  dsimp only
  obtain ⟨start, finish, beginTime, endTime, startLtFinish,
      beginMem, endMem, beginLtEnd, beginMass, endMass,
      interiorMass, _prehistoryCeiling, scaleSpan⟩ :=
    sourceGeneratedNativeAccumulationScaleCriticalLastHitWindow
      initial elapsedBounded level levelPos initialLeHalf
  have beginNonneg : 0 ≤ beginTime :=
    (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
      initial (start + 1)).trans beginMem.1
  have massLeEnd :
      ∀ time ∈ Icc beginTime endTime,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
              time) ≤
          wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
              endTime) := by
    intro time timeMem
    calc
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1) time) ≤
          level := (interiorMass time timeMem).2
      _ = wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
            endTime) := endMass.symm
  obtain ⟨edge, segmentInitial, segmentTime, segmentTimePos,
      segmentReceipt, absoluteTime, edgeLt, pathChart,
      endpointNondecreasing⟩ :=
    lastHitWindow_generates_actualNondecreasingSubreceipt
      initial (finish + 1) beginTime endTime beginNonneg beginLtEnd
        endMem.2 massLeEnd
  have segmentBand (localTime : Icc (0 : Real) segmentTime) :
      level / 2 ≤
          wholeVorticityEuclideanMass
            (segmentReceipt.wholePath localTime) ∧
        wholeVorticityEuclideanMass
            (segmentReceipt.wholePath localTime) ≤ level := by
    rw [(pathChart localTime).2]
    exact interiorMass _ (pathChart localTime).1
  have sampleExists :=
    receipt_exists_scaleCriticalTangentGradientState
      segmentReceipt
      (Filter.Eventually.of_forall fun localTime =>
        (segmentBand localTime).2)
      endpointNondecreasing
  obtain ⟨sample, sampleGradientSummable, sampleBudget⟩ := sampleExists
  have normalizedMassLower :
      1 / 2 ≤ level⁻¹ *
        wholeVorticityEuclideanMass (segmentReceipt.wholePath sample) := by
    calc
      1 / 2 = level⁻¹ * (level / 2) := by
        field_simp [levelPos.ne']
      _ ≤ level⁻¹ *
          wholeVorticityEuclideanMass (segmentReceipt.wholePath sample) :=
        mul_le_mul_of_nonneg_left (segmentBand sample).1
          (inv_nonneg.mpr levelPos.le)
  have normalizedMassUpper :
      level⁻¹ *
          wholeVorticityEuclideanMass (segmentReceipt.wholePath sample) ≤ 1 := by
    calc
      level⁻¹ *
          wholeVorticityEuclideanMass (segmentReceipt.wholePath sample) ≤
          level⁻¹ * level :=
        mul_le_mul_of_nonneg_left (segmentBand sample).2
          (inv_nonneg.mpr levelPos.le)
      _ = 1 := by field_simp [levelPos.ne']
  have normalizedBudget :
      (level ^ 3)⁻¹ *
          (‖puncturedEuclideanSpaceTimeState
                segmentReceipt.wholeTangent sample‖ ^ 2 +
            ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
              wholeStateVorticityGradientMass
                (segmentReceipt.wholePath sample)) ≤
        (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) := by
    calc
      (level ^ 3)⁻¹ *
          (‖puncturedEuclideanSpaceTimeState
                segmentReceipt.wholeTangent sample‖ ^ 2 +
            ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
              wholeStateVorticityGradientMass
                (segmentReceipt.wholePath sample)) ≤
          (level ^ 3)⁻¹ *
            (((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
              (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) * level ^ 3) :=
        mul_le_mul_of_nonneg_left sampleBudget
          (inv_nonneg.mpr (pow_nonneg levelPos.le 3))
      _ = (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) := by
        field_simp [levelPos.ne']
  exact ⟨start, finish, edge, beginTime, endTime, segmentInitial,
    segmentTime, segmentTimePos, segmentReceipt, absoluteTime, sample,
    startLtFinish, beginMem, endMem, beginLtEnd, beginMass, endMass,
    interiorMass, scaleSpan, edgeLt, pathChart, endpointNondecreasing,
    normalizedMassLower, normalizedMassUpper, sampleGradientSummable,
    normalizedBudget⟩

/-- Every source-generated last-hit window exposes a fixed positive amount
of its mass growth in a finite output cube whose radius grows at most
linearly with the source level. -/
theorem sourceGeneratedNativeAccumulationScaleCriticalLowOutputActionBlock
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (level : Real)
    (levelPos : 0 < level)
    (initialLeHalf :
      restartPhysicalVorticityMass initial 0 ≤ level / 2) :
    ∃ start finish radius : Nat, ∃ beginTime endTime : Real,
      start < finish ∧
      0 < radius ∧
      (radius : Real) ≤
        (4368 * biotSavartSerrinConstant * level) /
            (nu.coeff ^ 2 * (2 * Real.pi) ^ 2) + 2 ∧
      beginTime ∈
        Icc (elapsedTime initial (start + 1))
          (elapsedTime initial (finish + 1)) ∧
      endTime ∈
        Icc (elapsedTime initial (start + 1))
          (elapsedTime initial (finish + 1)) ∧
      beginTime < endTime ∧
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
            beginTime) = level / 2 ∧
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
            endTime) = level ∧
      (∀ time ∈ Icc beginTime endTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ≤ level) ∧
      nu.coeff ^ 3 * (2 * Real.pi) ^ 2 ≤
        (9 * 1557504 * biotSavartSerrinConstant ^ 2) *
          (level ^ 2 * (endTime - beginTime)) ∧
      nu.coeff * (level / 2) ≤
        ∫ time in beginTime..endTime,
          ∑ output ∈ integerWaveFrequencyCube (2 * radius),
            (integerWaveViscousMultiplier output)⁻¹ *
              complexCoordinateAmplitudeSq
                (wholeStateVorticityNonlinearCoefficientAt
                  (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                    time)
                  output) := by
  obtain ⟨start, finish, beginTime, endTime, startLtFinish,
      beginMem, endMem, beginLtEnd, beginMass, endMass,
      interiorMass, _prehistoryCeiling, scaleSpan⟩ :=
    sourceGeneratedNativeAccumulationScaleCriticalLastHitWindow
      initial elapsedBounded level levelPos initialLeHalf
  let viscousConstant := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let numerator := 4368 * biotSavartSerrinConstant * level
  let ratio := numerator / viscousConstant
  let radius := Nat.ceil ratio + 1
  have viscousConstantPos : 0 < viscousConstant := by
    unfold viscousConstant
    exact mul_pos
      (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
  have numeratorNonneg : 0 ≤ numerator := by
    unfold numerator
    exact mul_nonneg
      (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
      levelPos.le
  have ratioNonneg : 0 ≤ ratio := by
    exact div_nonneg numeratorNonneg viscousConstantPos.le
  have radiusPos : 0 < radius := by
    unfold radius
    omega
  have ratioLeRadius : ratio ≤ (radius : Real) := by
    calc
      ratio ≤ (Nat.ceil ratio : Real) := Nat.le_ceil ratio
      _ ≤ (radius : Real) := by
        have ceilLe : Nat.ceil ratio ≤ radius := by
          unfold radius
          omega
        exact_mod_cast ceilLe
  have radiusUpper : (radius : Real) ≤ ratio + 2 := by
    have ceilLt : (Nat.ceil ratio : Real) < ratio + 1 :=
      Nat.ceil_lt_add_one ratioNonneg
    unfold radius
    push_cast
    linarith
  have numeratorEq : numerator = ratio * viscousConstant := by
    unfold ratio
    field_simp [viscousConstantPos.ne']
  have radiusAbsorbs :
      4368 * biotSavartSerrinConstant * level ≤
        (radius : Real) * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2) := by
    change numerator ≤ (radius : Real) * viscousConstant
    rw [numeratorEq]
    exact mul_le_mul_of_nonneg_right ratioLeRadius viscousConstantPos.le
  have beginNonneg : 0 ≤ beginTime := by
    exact
      (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
        initial (start + 1)).trans beginMem.1
  have lowOutputPayment :=
    wholeRestartPrefixVorticityMass_increment_between_le_lowOutputPayment
      initial (finish + 1) radius beginNonneg beginLtEnd endMem.2
        levelPos.le radiusPos radiusAbsorbs
        (fun time timeMem => (interiorMass time timeMem).2)
  rw [beginMass, endMass] at lowOutputPayment
  have normalizedPayment :
      nu.coeff * (level / 2) ≤
        ∫ time in beginTime..endTime,
          ∑ output ∈ integerWaveFrequencyCube (2 * radius),
            (integerWaveViscousMultiplier output)⁻¹ *
              complexCoordinateAmplitudeSq
                (wholeStateVorticityNonlinearCoefficientAt
                  (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                    time)
                  output) := by
    simpa only [wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass,
      wholeStateVorticityNonlinearNegativeOneEuclideanDensity,
      show level - level / 2 = level / 2 by ring] using lowOutputPayment
  refine ⟨start, finish, radius, beginTime, endTime, startLtFinish,
    radiusPos, ?_, beginMem, endMem, beginLtEnd, beginMass, endMass,
    interiorMass, scaleSpan, normalizedPayment⟩
  simpa only [ratio, numerator, viscousConstant] using radiusUpper

private theorem intervalIntegral_exists_strict_first_hit
    (density : Real → Real)
    {beginTime endTime target : Real}
    (beginLeEnd : beginTime ≤ endTime)
    (densityContinuous : ContinuousOn density (Icc beginTime endTime))
    (targetPos : 0 < target)
    (targetLe : target ≤ ∫ time in beginTime..endTime, density time) :
    ∃ cutTime ∈ Icc beginTime endTime,
      beginTime < cutTime ∧
      (∫ time in beginTime..cutTime, density time) = target := by
  let primitive : Real → Real := fun cutTime =>
    ∫ time in Ioc beginTime cutTime, density time
  have densityIntegrable :
      IntegrableOn density (Icc beginTime endTime) volume :=
    densityContinuous.integrableOn_Icc
  have primitiveContinuous :
      ContinuousOn primitive (Icc beginTime endTime) :=
    intervalIntegral.continuousOn_primitive densityIntegrable
  have primitiveAtBegin : primitive beginTime = 0 := by
    simp [primitive]
  have primitiveAtEnd :
      primitive endTime =
        ∫ time in beginTime..endTime, density time := by
    rw [intervalIntegral.integral_of_le beginLeEnd]
  have targetMem : target ∈ Icc (primitive beginTime) (primitive endTime) := by
    rw [primitiveAtBegin, primitiveAtEnd]
    exact ⟨targetPos.le, targetLe⟩
  obtain ⟨cutTime, cutMem, cutEq⟩ :=
    intermediate_value_Icc beginLeEnd primitiveContinuous targetMem
  have hit :
      (∫ time in beginTime..cutTime, density time) = target := by
    rw [intervalIntegral.integral_of_le cutMem.1]
    exact cutEq
  have beginLtCut : beginTime < cutTime := by
    apply lt_of_le_of_ne cutMem.1
    intro beginEqCut
    rw [← beginEqCut] at hit
    simp at hit
    linarith
  exact ⟨cutTime, cutMem, beginLtCut, hit⟩

/-- The actual last-hit block has a canonical nonzero observation after the
source level is used as the Fourier scale.  The cumulative cut is selected
from the same low-output NS action.  Its normalized finite Dirac measure has
fixed mass and is supported in one level-independent frequency cube; neither
the cut, the measure, nor a nonzero row is supplied by the caller. -/
theorem sourceGeneratedNativeAccumulationScaleCriticalFixedFrequencyObservation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (level : Real)
    (levelOne : 1 ≤ level)
    (initialLeHalf :
      restartPhysicalVorticityMass initial 0 ≤ level / 2) :
    let frequencySlope : Real :=
      (4368 * biotSavartSerrinConstant) /
        (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
    ∃ start finish radius : Nat, ∃ beginTime cutTime : Real,
      start < finish ∧
      0 < radius ∧
      (radius : Real) ≤ frequencySlope * level + 2 ∧
      beginTime ∈
        Icc (elapsedTime initial (start + 1))
          (elapsedTime initial (finish + 1)) ∧
      cutTime ∈ Icc beginTime (elapsedTime initial (finish + 1)) ∧
      beginTime < cutTime ∧
      (∀ time ∈ Icc beginTime cutTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ≤ level) ∧
      (∫ time in beginTime..cutTime,
        ∑ output ∈ integerWaveFrequencyCube (2 * radius),
          (integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (wholeStateVorticityNonlinearCoefficientAt
                (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                  time)
                output)) = nu.coeff * (level / 4) ∧
      ∃ observation : Measure PhysicalSpace,
        observation =
          ∑ output ∈ integerWaveFrequencyCube (2 * radius),
            ENNReal.ofReal
                (level⁻¹ *
                  ∫ time in beginTime..cutTime,
                    (integerWaveViscousMultiplier output)⁻¹ *
                      complexCoordinateAmplitudeSq
                        (wholeStateVorticityNonlinearCoefficientAt
                          (wholeRestartPrefixPhysicalTrajectory initial
                            (finish + 1) time)
                          output)) •
              Measure.dirac
                (WithLp.toLp 2 fun coordinate =>
                  (output coordinate : Real) / level) ∧
        (observation Set.univ).toReal = nu.coeff / 4 ∧
        observation
          {frequency : PhysicalSpace |
            ∃ coordinate : Coordinate,
              2 * (frequencySlope + 2) < |frequency coordinate|} = 0 := by
  dsimp only
  have levelPos : 0 < level :=
    lt_of_lt_of_le zero_lt_one levelOne
  obtain ⟨start, finish, radius, beginTime, endTime,
      startLtFinish, radiusPos, radiusUpper, beginMem, endMem,
      beginLtEnd, _beginMass, _endMass, interiorMass,
      _scaleSpan, lowOutputAction⟩ :=
    sourceGeneratedNativeAccumulationScaleCriticalLowOutputActionBlock
      initial elapsedBounded level levelPos initialLeHalf
  let frequencySlope : Real :=
    (4368 * biotSavartSerrinConstant) /
      (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
  have radiusLinear :
      (radius : Real) ≤ frequencySlope * level + 2 := by
    calc
      (radius : Real) ≤
          (4368 * biotSavartSerrinConstant * level) /
              (nu.coeff ^ 2 * (2 * Real.pi) ^ 2) + 2 := radiusUpper
      _ = frequencySlope * level + 2 := by
        unfold frequencySlope
        ring
  let density : IntegerWavevector → Real → Real := fun output time =>
    (integerWaveViscousMultiplier output)⁻¹ *
      complexCoordinateAmplitudeSq
        (wholeStateVorticityNonlinearCoefficientAt
          (wholeRestartPrefixPhysicalTrajectory initial (finish + 1) time)
          output)
  let totalDensity : Real → Real := fun time =>
    ∑ output ∈ integerWaveFrequencyCube (2 * radius), density output time
  have beginNonneg : 0 ≤ beginTime :=
    (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
      initial (start + 1)).trans beginMem.1
  have intervalSubset :
      Icc beginTime endTime ⊆
        Icc 0 (elapsedTime initial (finish + 1)) :=
    Icc_subset_Icc beginNonneg endMem.2
  have totalDensityContinuous :
      ContinuousOn totalDensity (Icc beginTime endTime) := by
    have sourceContinuous :=
      (wholeRestartPrefixLowOutputMass_continuousOn
        initial (finish + 1) radius).mono intervalSubset
    simpa only [totalDensity, density,
      wholeStateVorticityNonlinearNegativeOneEuclideanLowOutputMass,
      wholeStateVorticityNonlinearNegativeOneEuclideanDensity] using
        sourceContinuous
  let target : Real := nu.coeff * (level / 4)
  have targetPos : 0 < target := by
    unfold target
    exact mul_pos nu.coeff_pos (div_pos levelPos (by norm_num))
  have targetLe :
      target ≤ ∫ time in beginTime..endTime, totalDensity time := by
    have halfLe : target ≤ nu.coeff * (level / 2) := by
      unfold target
      nlinarith [nu.coeff_pos, levelPos]
    exact halfLe.trans (by
      simpa only [totalDensity, density] using lowOutputAction)
  obtain ⟨cutTime, cutMem, beginLtCut, cutHit⟩ :=
    intervalIntegral_exists_strict_first_hit totalDensity beginLtEnd.le
      totalDensityContinuous targetPos targetLe
  have densityContinuous :
      ∀ output ∈ integerWaveFrequencyCube (2 * radius),
        ContinuousOn (density output) (Icc beginTime cutTime) := by
    intro output _outputMem
    unfold density
    apply ContinuousOn.mul continuousOn_const
    exact complexCoordinateAmplitudeSq_continuous.comp_continuousOn
      (wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
        (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)) output
        beginTime cutTime
        ((wholeRestartPrefixPhysicalTrajectory_continuousOn
          initial (finish + 1)).mono
            (Icc_subset_Icc beginNonneg
              (cutMem.2.trans endMem.2)))
        (fun time _timeMem =>
          wholeRestartPrefixPhysicalTrajectory_transverse
            initial (finish + 1) time))
  have densityNonneg :
      ∀ output ∈ integerWaveFrequencyCube (2 * radius),
        ∀ time ∈ Icc beginTime cutTime, 0 ≤ density output time := by
    intro output _outputMem time _timeMem
    unfold density
    exact mul_nonneg
      (inv_nonneg.mpr (by
        unfold integerWaveViscousMultiplier
        exact mul_nonneg (sq_nonneg _)
          (integerWaveNormSq_nonneg output)))
      (complexCoordinateAmplitudeSq_nonneg _)
  let outputs := integerWaveFrequencyCube (2 * radius)
  let weight : IntegerWavevector → Real := fun output =>
    level⁻¹ * ∫ time in beginTime..cutTime, density output time
  let location : IntegerWavevector → PhysicalSpace := fun output =>
    WithLp.toLp 2 fun coordinate => (output coordinate : Real) / level
  let observation : Measure PhysicalSpace :=
    ∑ output ∈ outputs,
      ENNReal.ofReal (weight output) • Measure.dirac (location output)
  have densityIntervalIntegrable :
      ∀ output ∈ outputs,
        IntervalIntegrable (density output) volume beginTime cutTime := by
    intro output outputMem
    exact ContinuousOn.intervalIntegrable_of_Icc cutMem.1
      (densityContinuous output (by simpa only [outputs] using outputMem))
  have weightNonneg : ∀ output ∈ outputs, 0 ≤ weight output := by
    intro output outputMem
    unfold weight
    exact mul_nonneg (inv_nonneg.mpr levelPos.le)
      (intervalIntegral.integral_nonneg cutMem.1 fun time timeMem =>
        densityNonneg output (by simpa only [outputs] using outputMem)
          time timeMem)
  have observationMass :
      (observation Set.univ).toReal = level⁻¹ * target := by
    unfold observation
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, Measure.dirac_apply',
      MeasurableSet.univ, Set.indicator_of_mem, Set.mem_univ,
      smul_eq_mul]
    simp_rw [Pi.one_apply, mul_one]
    rw [ENNReal.toReal_sum]
    · rw [show
        (∑ output ∈ outputs,
            (ENNReal.ofReal (weight output)).toReal) =
          ∑ output ∈ outputs, weight output by
        apply Finset.sum_congr rfl
        intro output outputMem
        exact ENNReal.toReal_ofReal (weightNonneg output outputMem)]
      unfold weight
      rw [← Finset.mul_sum]
      rw [← intervalIntegral.integral_finsetSum densityIntervalIntegrable]
      exact congrArg (fun value : Real => level⁻¹ * value) cutHit
    · intro output _outputMem
      exact ENNReal.ofReal_ne_top
  have observationMassNormalized :
      (observation Set.univ).toReal = nu.coeff / 4 := by
    rw [observationMass]
    unfold target
    field_simp [levelPos.ne']
  have observationSupport :
      observation
          {frequency : PhysicalSpace |
            ∃ coordinate : Coordinate,
              2 * (frequencySlope + 2) < |frequency coordinate|} = 0 := by
    let fixedCube : Set PhysicalSpace :=
      {frequency |
        ∀ coordinate : Coordinate,
          |frequency coordinate| ≤ 2 * (frequencySlope + 2)}
    have fixedCubeMeasurable : MeasurableSet fixedCube := by
      apply IsClosed.measurableSet
      unfold fixedCube
      simp only [setOf_forall]
      apply isClosed_iInter
      intro coordinate
      exact isClosed_le
        (continuous_abs.comp
          (PiLp.continuous_apply 2 (fun _ : Coordinate => Real) coordinate))
        continuous_const
    have outsideEq :
        {frequency : PhysicalSpace |
          ∃ coordinate : Coordinate,
            2 * (frequencySlope + 2) < |frequency coordinate|} =
          fixedCubeᶜ := by
      ext frequency
      simp [fixedCube, not_le]
    rw [outsideEq]
    unfold observation
    rw [Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro output outputMem
    rw [Measure.smul_apply,
      Measure.dirac_apply' _ fixedCubeMeasurable.compl]
    have concreteOutputMem :
        output ∈ integerWaveFrequencyCube (2 * radius) := by
      simpa only [outputs] using outputMem
    have outputBound (coordinate : Coordinate) :
        |(output coordinate : Real)| ≤ 2 * (radius : Real) := by
      rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at concreteOutputMem
      have coordinateBounds :=
        Finset.mem_Icc.mp (concreteOutputMem coordinate)
      rw [abs_le]
      constructor
      · exact_mod_cast coordinateBounds.1
      · exact_mod_cast coordinateBounds.2
    have locationInFixedCube : location output ∈ fixedCube := by
      intro coordinate
      change |(output coordinate : Real) / level| ≤ _
      rw [abs_div, abs_of_pos levelPos]
      apply (div_le_iff₀ levelPos).2
      calc
        |(output coordinate : Real)| ≤ 2 * (radius : Real) :=
          outputBound coordinate
        _ ≤ 2 * (frequencySlope + 2) * level := by
          nlinarith [radiusLinear]
    simp [locationInFixedCube]
  have cutInActualInterval :
      cutTime ∈ Icc beginTime (elapsedTime initial (finish + 1)) :=
    ⟨cutMem.1, cutMem.2.trans endMem.2⟩
  have cutInteriorMass :
      ∀ time ∈ Icc beginTime cutTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                time) ≤ level := by
    intro time timeMem
    exact interiorMass time ⟨timeMem.1, timeMem.2.trans cutMem.2⟩
  have cutHitExpanded :
      (∫ time in beginTime..cutTime,
        ∑ output ∈ integerWaveFrequencyCube (2 * radius),
          (integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (wholeStateVorticityNonlinearCoefficientAt
                (wholeRestartPrefixPhysicalTrajectory initial (finish + 1)
                  time)
                output)) = nu.coeff * (level / 4) := by
    simpa only [totalDensity, density, target] using cutHit
  refine ⟨start, finish, radius, beginTime, cutTime,
    startLtFinish, radiusPos, radiusLinear, beginMem, cutInActualInterval,
    beginLtCut, cutInteriorMass, cutHitExpanded, observation, ?_,
    observationMassNormalized, observationSupport⟩
  rfl

theorem observation_divergence_forces_times_to_accumulation
    {accumulationTime : Real}
    (time : Nat → Ico (0 : Real) accumulationTime)
    (observable : Ico (0 : Real) accumulationTime → Real)
    (observableContinuous : Continuous observable)
    (observableDiverges :
      Tendsto (fun index => observable (time index)) atTop atTop) :
    Tendsto (fun index => (time index : Real)) atTop
      (nhds accumulationTime) := by
  rw [tendsto_order]
  constructor
  · intro lower lowerLt
    by_cases lowerNeg : lower < 0
    · filter_upwards [] with index
      exact lowerNeg.trans_le (time index).2.1
    · have lowerNonneg : 0 ≤ lower := le_of_not_gt lowerNeg
      let inclusion : Icc (0 : Real) lower → Ico (0 : Real) accumulationTime :=
        fun point => ⟨point.1, point.2.1, point.2.2.trans_lt lowerLt⟩
      let restricted : Icc (0 : Real) lower → Real :=
        fun point => observable (inclusion point)
      have inclusionContinuous : Continuous inclusion := by
        exact continuous_subtype_val.subtype_mk _
      have restrictedContinuous : Continuous restricted :=
        observableContinuous.comp inclusionContinuous
      have rangeBounded : BddAbove (Set.range restricted) :=
        (isCompact_range restrictedContinuous).bddAbove
      obtain ⟨bound, boundSpec⟩ := rangeBounded
      have eventuallyLarge :=
        (tendsto_atTop.1 observableDiverges) (bound + 1)
      filter_upwards [eventuallyLarge] with index indexLarge
      by_contra timeNotAbove
      have timeLe : (time index : Real) ≤ lower :=
        le_of_not_gt timeNotAbove
      let point : Icc (0 : Real) lower :=
        ⟨(time index : Real), (time index).2.1, timeLe⟩
      have valueLe : observable (time index) ≤ bound := by
        change restricted point ≤ bound
        exact boundSpec (Set.mem_range_self point)
      linarith
  · intro upper accumulationLtUpper
    filter_upwards [] with index
    exact (time index).2.2.trans accumulationLtUpper

/-- Canonical increasing source levels select actual low-output action
windows whose two physical endpoints are cofinal at the original
accumulation time. -/
theorem
    sourceGeneratedNativeAccumulationScaleCriticalLowOutputActionBlocks_tendsto_accumulation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∃ level : Nat → Real,
      level = (fun index : Nat =>
        4 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index) ∧
      ∃ finish radius : Nat → Nat,
        ∃ beginTime cutTime : Nat → Real,
          (∀ index,
            0 < radius index ∧
            (radius index : Real) ≤
              ((4368 * biotSavartSerrinConstant) /
                    (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) * level index + 2 ∧
            beginTime index ∈
              Icc 0 (elapsedTime initial (finish index + 1)) ∧
            cutTime index ∈
              Icc (beginTime index)
                (elapsedTime initial (finish index + 1)) ∧
            beginTime index < cutTime index ∧
            (∀ time ∈ Icc (beginTime index) (cutTime index),
              level index / 2 ≤
                  wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (finish index + 1) time) ∧
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (finish index + 1) time) ≤ level index) ∧
            (∫ time in beginTime index..cutTime index,
              ∑ output ∈ integerWaveFrequencyCube (2 * radius index),
                (integerWaveViscousMultiplier output)⁻¹ *
                  complexCoordinateAmplitudeSq
                    (wholeStateVorticityNonlinearCoefficientAt
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (finish index + 1) time)
                      output)) = nu.coeff * (level index / 4)) ∧
          Tendsto beginTime atTop
            (nhds (wholeRestartVelocityAccumulationTime initial)) ∧
          Tendsto cutTime atTop
            (nhds (wholeRestartVelocityAccumulationTime initial)) ∧
          ∃ selector : Nat → Nat,
            selector 0 = 0 ∧
            StrictMono selector ∧
            (∀ index,
              cutTime (selector index) <
                beginTime (selector (index + 1))) ∧
            Tendsto (fun index => beginTime (selector index)) atTop
              (nhds (wholeRestartVelocityAccumulationTime initial)) ∧
            Tendsto (fun index => cutTime (selector index)) atTop
              (nhds (wholeRestartVelocityAccumulationTime initial)) := by
  let level : Nat → Real := fun index =>
    4 * (|restartPhysicalVorticityMass initial 0| + 1) *
      (4 : Real) ^ index
  have levelOne (index : Nat) : 1 ≤ level index := by
    have massFactor :
        1 ≤ |restartPhysicalVorticityMass initial 0| + 1 := by
      linarith [abs_nonneg (restartPhysicalVorticityMass initial 0)]
    have powerFactor : 1 ≤ (4 : Real) ^ index :=
      one_le_pow₀ (by norm_num)
    dsimp only [level]
    calc
      1 ≤ 4 * 1 * 1 := by norm_num
      _ ≤ 4 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index := by gcongr
  have initialLeHalf (index : Nat) :
      restartPhysicalVorticityMass initial 0 ≤ level index / 2 := by
    have massLeAbs :
        restartPhysicalVorticityMass initial 0 ≤
          |restartPhysicalVorticityMass initial 0| :=
      le_abs_self _
    have massAbsNonneg : 0 ≤ |restartPhysicalVorticityMass initial 0| :=
      abs_nonneg _
    have powerFactor : 1 ≤ (4 : Real) ^ index :=
      one_le_pow₀ (by norm_num)
    calc
      restartPhysicalVorticityMass initial 0 ≤
          |restartPhysicalVorticityMass initial 0| := massLeAbs
      _ ≤ 2 * (|restartPhysicalVorticityMass initial 0| + 1) * 1 := by
        nlinarith
      _ ≤ 2 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index := by gcongr
      _ = level index / 2 := by
        dsimp only [level]
        ring
  have generated (index : Nat) :=
    sourceGeneratedNativeAccumulationScaleCriticalFixedFrequencyObservation
      initial elapsedBounded (level index) (levelOne index)
        (initialLeHalf index)
  choose start finish radius beginTime cutTime specifications using generated
  have blockSpecifications (index : Nat) :
      0 < radius index ∧
      (radius index : Real) ≤
        ((4368 * biotSavartSerrinConstant) /
              (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) * level index + 2 ∧
      beginTime index ∈
        Icc 0 (elapsedTime initial (finish index + 1)) ∧
      cutTime index ∈
        Icc (beginTime index) (elapsedTime initial (finish index + 1)) ∧
      beginTime index < cutTime index ∧
      (∀ time ∈ Icc (beginTime index) (cutTime index),
        level index / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial
                (finish index + 1) time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial
                (finish index + 1) time) ≤ level index) ∧
      (∫ time in beginTime index..cutTime index,
        ∑ output ∈ integerWaveFrequencyCube (2 * radius index),
          (integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (wholeStateVorticityNonlinearCoefficientAt
                (wholeRestartPrefixPhysicalTrajectory initial
                  (finish index + 1) time)
                output)) = nu.coeff * (level index / 4) := by
    rcases specifications index with
      ⟨_startLtFinish, radiusPos, radiusUpper, beginMem, cutMem,
        beginLtCut, interiorMass, actionHit, _observation⟩
    have beginNonneg : 0 ≤ beginTime index :=
      (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
        initial (start index + 1)).trans beginMem.1
    exact ⟨radiusPos, radiusUpper, ⟨beginNonneg, beginMem.2⟩,
      cutMem, beginLtCut, interiorMass, actionHit⟩
  let massObservable :
      Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) → Real :=
    fun time =>
      wholeVorticityEuclideanMass
        (wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded time)
  have massObservableContinuous : Continuous massObservable := by
    exact continuous_wholeVorticityEuclideanMass.comp
      (wholeRestartBoundedPreAccumulationPhysicalTrajectory_continuous
        initial elapsedBounded)
  let beginPoint : Nat →
      Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) :=
    fun index =>
      ⟨beginTime index,
        (blockSpecifications index).2.2.1.1,
        (blockSpecifications index).2.2.1.2.trans_lt
          (elapsedTime_lt_wholeRestartVelocityAccumulationTime
            initial elapsedBounded (finish index + 1))⟩
  let cutPoint : Nat →
      Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) :=
    fun index =>
      ⟨cutTime index,
        (blockSpecifications index).2.2.1.1.trans
          (blockSpecifications index).2.2.2.1.1,
        (blockSpecifications index).2.2.2.1.2.trans_lt
          (elapsedTime_lt_wholeRestartVelocityAccumulationTime
            initial elapsedBounded (finish index + 1))⟩
  have beginMassLower (index : Nat) :
      level index / 2 ≤ massObservable (beginPoint index) := by
    have beginInterior :=
      (blockSpecifications index).2.2.2.2.2.1
        (beginTime index)
        ⟨le_rfl, (blockSpecifications index).2.2.2.1.1⟩
    dsimp only [massObservable, beginPoint]
    rw [wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
      initial elapsedBounded _ (finish index + 1)
      (blockSpecifications index).2.2.1.2]
    exact beginInterior.1
  have cutMassLower (index : Nat) :
      level index / 2 ≤ massObservable (cutPoint index) := by
    have cutInterior :=
      (blockSpecifications index).2.2.2.2.2.1
        (cutTime index)
        ⟨(blockSpecifications index).2.2.2.1.1, le_rfl⟩
    dsimp only [massObservable, cutPoint]
    rw [wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
      initial elapsedBounded _ (finish index + 1)
      (blockSpecifications index).2.2.2.1.2]
    exact cutInterior.1
  have levelHalfDiverges :
      Tendsto (fun index => level index / 2) atTop atTop := by
    have powerDiverges :
        Tendsto (fun index : Nat => (4 : Real) ^ index) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have coefficientPos :
        0 < 2 * (|restartPhysicalVorticityMass initial 0| + 1) := by
      positivity
    have scaled := powerDiverges.const_mul_atTop coefficientPos
    convert scaled using 1
    funext index
    dsimp only [level]
    ring
  have beginMassDiverges :
      Tendsto (fun index => massObservable (beginPoint index)) atTop atTop := by
    rw [tendsto_atTop] at levelHalfDiverges ⊢
    intro bound
    filter_upwards [levelHalfDiverges bound] with index levelLarge
    exact levelLarge.trans (beginMassLower index)
  have cutMassDiverges :
      Tendsto (fun index => massObservable (cutPoint index)) atTop atTop := by
    rw [tendsto_atTop] at levelHalfDiverges ⊢
    intro bound
    filter_upwards [levelHalfDiverges bound] with index levelLarge
    exact levelLarge.trans (cutMassLower index)
  have beginTendsto :=
    observation_divergence_forces_times_to_accumulation
      beginPoint massObservable massObservableContinuous beginMassDiverges
  have cutTendsto :=
    observation_divergence_forces_times_to_accumulation
      cutPoint massObservable massObservableContinuous cutMassDiverges
  have cutLtAccumulation (index : Nat) :
      cutTime index < wholeRestartVelocityAccumulationTime initial :=
    (blockSpecifications index).2.2.2.1.2.trans_lt
      (elapsedTime_lt_wholeRestartVelocityAccumulationTime
        initial elapsedBounded (finish index + 1))
  have existsSeparatedLater (index cursor : Nat) :
      ∃ later : Nat,
        cursor < later ∧ cutTime index < beginTime later := by
    have separatedEventually :
        ∀ᶠ later : Nat in atTop,
          cutTime index < beginTime later :=
      (tendsto_order.1 beginTendsto).1
        (cutTime index) (cutLtAccumulation index)
    have cursorEventually :
        ∀ᶠ later : Nat in atTop, cursor < later :=
      eventually_gt_atTop cursor
    exact (cursorEventually.and separatedEventually).exists
  let nextIndex : Nat → Nat := fun cursor =>
    Nat.find (existsSeparatedLater cursor cursor)
  have nextIndexSpec (cursor : Nat) :
      cursor < nextIndex cursor ∧
        cutTime cursor < beginTime (nextIndex cursor) := by
    simpa only [nextIndex] using
      Nat.find_spec (existsSeparatedLater cursor cursor)
  let selector : Nat → Nat := fun index =>
    Nat.rec 0 (fun _ cursor => nextIndex cursor) index
  have selectorZero : selector 0 = 0 := rfl
  have selectorSucc (index : Nat) :
      selector (index + 1) = nextIndex (selector index) := by
    simp only [selector]
  have selectorLtSucc (index : Nat) :
      selector index < selector (index + 1) := by
    rw [selectorSucc]
    exact (nextIndexSpec (selector index)).1
  have selectorStrictMono : StrictMono selector :=
    strictMono_nat_of_lt_succ selectorLtSucc
  have separated (index : Nat) :
      cutTime (selector index) < beginTime (selector (index + 1)) := by
    rw [selectorSucc]
    exact (nextIndexSpec (selector index)).2
  have selectedBeginTendsto :
      Tendsto (fun index => beginTime (selector index)) atTop
        (nhds (wholeRestartVelocityAccumulationTime initial)) :=
    beginTendsto.comp selectorStrictMono.tendsto_atTop
  have selectedCutTendsto :
      Tendsto (fun index => cutTime (selector index)) atTop
        (nhds (wholeRestartVelocityAccumulationTime initial)) :=
    cutTendsto.comp selectorStrictMono.tendsto_atTop
  refine ⟨level, rfl, finish, radius, beginTime, cutTime,
    blockSpecifications, ?_, ?_, selector, selectorZero,
    selectorStrictMono, separated, selectedBeginTendsto,
    selectedCutTendsto⟩
  · simpa only [beginPoint] using beginTendsto
  · simpa only [cutPoint] using cutTendsto

/-- Geometric source levels turn the first-hit finite-input payments into
normalized whole prehistories.  Their terminal contacts approach the original
accumulation time, while the parabolically rescaled backward horizons diverge
and a fixed finite-input action survives on every scale. -/
theorem
    sourceGeneratedNativeAccumulationScaleCriticalFiniteInputWholePrehistories
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let frequencySlope : Real :=
      (4368 * biotSavartSerrinConstant) /
        (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
    ∃ level : Nat → Real,
      level = (fun index : Nat =>
        4 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index) ∧
      ∃ finish radius : Nat → Nat,
        (∀ index,
          4 ≤ level index ∧
          0 < finish index ∧
          0 < radius index ∧
          level index ≤
            restartPhysicalVorticityMass initial (finish index) ∧
          restartPhysicalVorticityMass initial (finish index) <
            level index + 2 ∧
          (level index + 2)⁻¹ * (radius index : Real) ≤
            frequencySlope + 1 ∧
          (level index + 2)⁻¹ * level index ≤
            (level index + 2)⁻¹ *
              restartPhysicalVorticityMass initial (finish index) ∧
          (level index + 2)⁻¹ *
              restartPhysicalVorticityMass initial (finish index) < 1 ∧
          (∀ edge, edge ∈ Finset.range (finish index) →
            ∀ᵐ localTime
                ∂(commonTimeMeasure
                  (run initial edge).nextContact.time.1),
              (level index + 2)⁻¹ *
                  wholeVorticityEuclideanMass
                    ((run initial edge).nextContact.prefixReceipt.wholePath
                      localTime) <
                1) ∧
          nu.coeff / 8 ≤
            (level index + 2)⁻¹ *
              (∑ edge ∈ Finset.range (finish index),
                ∫ localTime,
                  ∑ output ∈
                      finiteVorticityPairOutputSupport
                        (integerWaveFrequencyCube (radius index)),
                    (integerWaveViscousMultiplier output)⁻¹ *
                      complexCoordinateAmplitudeSq
                        (wholeStateVorticityNonlinearCoefficientAt
                          (complexSharpSupportProjection
                            (integerWaveFrequencyCube (radius index))
                            ((run initial edge).nextContact.prefixReceipt.wholePath
                              localTime))
                          output)
                  ∂(commonTimeMeasure
                    (run initial edge).nextContact.time.1))) ∧
        Tendsto
          (fun index => elapsedTime initial (finish index + 1))
          atTop (nhds (wholeRestartVelocityAccumulationTime initial)) ∧
        Tendsto
          (fun index =>
            (level index + 2) ^ 2 *
              elapsedTime initial (finish index + 1))
          atTop atTop := by
  dsimp only
  let level : Nat → Real := fun index =>
    4 * (|restartPhysicalVorticityMass initial 0| + 1) *
      (4 : Real) ^ index
  have levelFour (index : Nat) : 4 ≤ level index := by
    have massFactor :
        1 ≤ |restartPhysicalVorticityMass initial 0| + 1 := by
      linarith [abs_nonneg (restartPhysicalVorticityMass initial 0)]
    have powerFactor : 1 ≤ (4 : Real) ^ index :=
      one_le_pow₀ (by norm_num)
    dsimp only [level]
    calc
      4 = 4 * 1 * 1 := by norm_num
      _ ≤ 4 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index := by gcongr
  have levelPos (index : Nat) : 0 < level index :=
    lt_of_lt_of_le (by norm_num) (levelFour index)
  have initialLeHalf (index : Nat) :
      restartPhysicalVorticityMass initial 0 ≤ level index / 2 := by
    have massLeAbs :
        restartPhysicalVorticityMass initial 0 ≤
          |restartPhysicalVorticityMass initial 0| :=
      le_abs_self _
    have powerFactor : 1 ≤ (4 : Real) ^ index :=
      one_le_pow₀ (by norm_num)
    calc
      restartPhysicalVorticityMass initial 0 ≤
          |restartPhysicalVorticityMass initial 0| := massLeAbs
      _ ≤ 2 * (|restartPhysicalVorticityMass initial 0| + 1) * 1 := by
        nlinarith [abs_nonneg (restartPhysicalVorticityMass initial 0)]
      _ ≤ 2 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index := by gcongr
      _ = level index / 2 := by
        dsimp only [level]
        ring
  have generated (index : Nat) :=
    sourceGeneratedNativeAccumulationFirstLevelActualPrefixFiniteInputOutputAction
      initial elapsedBounded (level index) (levelPos index)
        (initialLeHalf index)
  choose finish radius specifications using generated
  let frequencySlope : Real :=
    (4368 * biotSavartSerrinConstant) /
      (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
  let finiteInputOutputPayment : Nat → Real := fun index =>
    ∑ edge ∈ Finset.range (finish index),
      ∫ localTime,
        ∑ output ∈
            finiteVorticityPairOutputSupport
              (integerWaveFrequencyCube (radius index)),
          (integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (wholeStateVorticityNonlinearCoefficientAt
                (complexSharpSupportProjection
                  (integerWaveFrequencyCube (radius index))
                  ((run initial edge).nextContact.prefixReceipt.wholePath
                    localTime))
                output)
        ∂(commonTimeMeasure (run initial edge).nextContact.time.1)
  have normalizedSpecifications (index : Nat) :
      4 ≤ level index ∧
      0 < finish index ∧
      0 < radius index ∧
      level index ≤
        restartPhysicalVorticityMass initial (finish index) ∧
      restartPhysicalVorticityMass initial (finish index) <
        level index + 2 ∧
      (level index + 2)⁻¹ * (radius index : Real) ≤
        frequencySlope + 1 ∧
      (level index + 2)⁻¹ * level index ≤
        (level index + 2)⁻¹ *
          restartPhysicalVorticityMass initial (finish index) ∧
      (level index + 2)⁻¹ *
          restartPhysicalVorticityMass initial (finish index) < 1 ∧
      (∀ edge, edge ∈ Finset.range (finish index) →
        ∀ᵐ localTime
            ∂(commonTimeMeasure
              (run initial edge).nextContact.time.1),
          (level index + 2)⁻¹ *
              wholeVorticityEuclideanMass
                ((run initial edge).nextContact.prefixReceipt.wholePath
                  localTime) <
            1) ∧
      nu.coeff / 8 ≤
        (level index + 2)⁻¹ * finiteInputOutputPayment index := by
    rcases specifications index with
      ⟨finishPos, radiusPos, finishMassLower, finishMassUpper,
        radiusUpper, interiorMass, finitePayment⟩
    have scalePos : 0 < level index + 2 := by
      linarith [levelPos index]
    have radiusLinear :
        (radius index : Real) ≤
          frequencySlope * (level index + 2) + 2 := by
      calc
        (radius index : Real) ≤
            (4368 * biotSavartSerrinConstant * (level index + 2)) /
                (nu.coeff ^ 2 * (2 * Real.pi) ^ 2) + 2 :=
          radiusUpper
        _ = frequencySlope * (level index + 2) + 2 := by
          unfold frequencySlope
          ring
    have twoDivLe : 2 / (level index + 2) ≤ 1 := by
      apply (div_le_iff₀ scalePos).2
      linarith [levelFour index]
    have normalizedRadius :
        (level index + 2)⁻¹ * (radius index : Real) ≤
          frequencySlope + 1 := by
      calc
        (level index + 2)⁻¹ * (radius index : Real) ≤
            (level index + 2)⁻¹ *
              (frequencySlope * (level index + 2) + 2) :=
          mul_le_mul_of_nonneg_left radiusLinear
            (inv_nonneg.mpr scalePos.le)
        _ = frequencySlope + 2 / (level index + 2) := by
          field_simp [scalePos.ne']
        _ ≤ frequencySlope + 1 := by linarith
    have normalizedFinishLower :
        (level index + 2)⁻¹ * level index ≤
          (level index + 2)⁻¹ *
            restartPhysicalVorticityMass initial (finish index) :=
      mul_le_mul_of_nonneg_left finishMassLower
        (inv_nonneg.mpr scalePos.le)
    have normalizedFinishUpper :
        (level index + 2)⁻¹ *
            restartPhysicalVorticityMass initial (finish index) < 1 := by
      calc
        (level index + 2)⁻¹ *
              restartPhysicalVorticityMass initial (finish index) <
            (level index + 2)⁻¹ * (level index + 2) :=
          mul_lt_mul_of_pos_left finishMassUpper (inv_pos.mpr scalePos)
        _ = 1 := by field_simp [scalePos.ne']
    have normalizedInterior :
        ∀ edge, edge ∈ Finset.range (finish index) →
          ∀ᵐ localTime
              ∂(commonTimeMeasure
                (run initial edge).nextContact.time.1),
            (level index + 2)⁻¹ *
                wholeVorticityEuclideanMass
                  ((run initial edge).nextContact.prefixReceipt.wholePath
                    localTime) <
              1 := by
      intro edge edgeMem
      filter_upwards [interiorMass edge edgeMem] with localTime massLt
      calc
        (level index + 2)⁻¹ *
              wholeVorticityEuclideanMass
                ((run initial edge).nextContact.prefixReceipt.wholePath
                  localTime) <
            (level index + 2)⁻¹ * (level index + 2) :=
          mul_lt_mul_of_pos_left massLt (inv_pos.mpr scalePos)
        _ = 1 := by field_simp [scalePos.ne']
    have normalizedPayment :
        nu.coeff / 8 ≤
          (level index + 2)⁻¹ * finiteInputOutputPayment index := by
      change
        nu.coeff * (level index / 2) ≤
          2 * finiteInputOutputPayment index at finitePayment
      rw [show
        (level index + 2)⁻¹ * finiteInputOutputPayment index =
          finiteInputOutputPayment index / (level index + 2) by
        ring]
      rw [le_div_iff₀ scalePos]
      nlinarith [nu.coeff_pos, levelFour index]
    exact
      ⟨levelFour index, finishPos, radiusPos, finishMassLower,
        finishMassUpper, normalizedRadius, normalizedFinishLower,
        normalizedFinishUpper, normalizedInterior, normalizedPayment⟩
  have levelTendsto : Tendsto level atTop atTop := by
    have powerTendsto :
        Tendsto (fun index : Nat => (4 : Real) ^ index) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have coefficientPos :
        0 < 4 * (|restartPhysicalVorticityMass initial 0| + 1) := by
      positivity
    exact powerTendsto.const_mul_atTop coefficientPos
  let massObservable :
      Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) → Real :=
    fun time =>
      wholeVorticityEuclideanMass
        (wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded time)
  have massObservableContinuous : Continuous massObservable :=
    continuous_wholeVorticityEuclideanMass.comp
      (wholeRestartBoundedPreAccumulationPhysicalTrajectory_continuous
        initial elapsedBounded)
  let finishPoint : Nat →
      Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) :=
    fun index =>
      wholeRestartContactEndpointPreAccumulationTime
        initial elapsedBounded (finish index)
  have finishPointState (index : Nat) :
      wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded (finishPoint index) =
        (run initial (finish index)).contact.physicalState := by
    dsimp only [finishPoint, wholeRestartContactEndpointPreAccumulationTime]
    rw [wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
      initial elapsedBounded _ (finish index + 1) le_rfl]
    change
      wholeRestartPrefixPhysicalTrajectory initial (finish index + 1)
          (elapsedTime initial (finish index + 1)) =
        (run initial (finish index)).contact.physicalState
    rw [wholeRestartPrefixPhysicalTrajectory_endpoint,
      run_succ_initialState]
  have finishMassDiverges :
      Tendsto (fun index => massObservable (finishPoint index))
        atTop atTop := by
    rw [tendsto_atTop]
    intro requested
    have levelEventually := (tendsto_atTop.1 levelTendsto) requested
    filter_upwards [levelEventually] with index levelLarge
    have finishLower := (specifications index).2.2.1
    dsimp only [massObservable]
    rw [finishPointState]
    exact levelLarge.trans finishLower
  have finishTendstoRaw :=
    observation_divergence_forces_times_to_accumulation
      finishPoint massObservable massObservableContinuous finishMassDiverges
  have finishTendsto :
      Tendsto (fun index => elapsedTime initial (finish index + 1))
        atTop (nhds (wholeRestartVelocityAccumulationTime initial)) := by
    simpa only [finishPoint,
      wholeRestartContactEndpointPreAccumulationTime] using finishTendstoRaw
  have accumulationPos :
      0 < wholeRestartVelocityAccumulationTime initial := by
    have elapsedNonneg :=
      ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
        initial 1
    have elapsedLt :=
      elapsedTime_lt_wholeRestartVelocityAccumulationTime
        initial elapsedBounded 1
    linarith
  have horizonTendsto :
      Tendsto
        (fun index =>
          (level index + 2) ^ 2 *
            elapsedTime initial (finish index + 1))
        atTop atTop := by
    let halfAccumulation :=
      wholeRestartVelocityAccumulationTime initial / 2
    have halfPos : 0 < halfAccumulation := by
      dsimp only [halfAccumulation]
      linarith
    have timeEventually :
        ∀ᶠ index : Nat in atTop,
          halfAccumulation <
            elapsedTime initial (finish index + 1) :=
      (tendsto_order.1 finishTendsto).1 halfAccumulation (by
        dsimp only [halfAccumulation]
        linarith)
    rw [tendsto_atTop]
    intro requested
    have levelEventually :=
      (tendsto_atTop.1 levelTendsto) (requested / halfAccumulation)
    filter_upwards [timeEventually, levelEventually] with
      index timeLower levelLower
    have scaleLower :
        level index ≤ (level index + 2) ^ 2 := by
      nlinarith [levelFour index]
    calc
      requested = halfAccumulation * (requested / halfAccumulation) := by
        field_simp [halfPos.ne']
      _ ≤ halfAccumulation * level index :=
        mul_le_mul_of_nonneg_left levelLower halfPos.le
      _ ≤ halfAccumulation * (level index + 2) ^ 2 :=
        mul_le_mul_of_nonneg_left scaleLower halfPos.le
      _ ≤ elapsedTime initial (finish index + 1) *
            (level index + 2) ^ 2 :=
        mul_le_mul_of_nonneg_right timeLower.le (sq_nonneg _)
      _ = (level index + 2) ^ 2 *
            elapsedTime initial (finish index + 1) := by ring
  refine ⟨level, rfl, finish, radius, ?_, finishTendsto,
    horizonTendsto⟩
  intro index
  simpa only [frequencySlope, finiteInputOutputPayment] using
    normalizedSpecifications index

private theorem receiptFiniteInputOutputAction_parabolicScale
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (inputModes outputModes : Finset IntegerWavevector)
    (scale : Real)
    (scalePos : 0 < scale) :
    (∫ scaledTime in 0..requestedTime / scale ^ 2,
      ∑ output ∈ outputModes,
        (scale ^ 3)⁻¹ *
          (scale ^ 2 * integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (finiteStateVorticityNonlinearCoefficientAt inputModes
                ((scale ^ 2 : Real) •
                  receipt.wholePath
                    (Set.projIcc 0 requestedTime
                      receipt.requestedTimePos.le
                      (scale ^ 2 * scaledTime)))
                output)) =
      scale *
        ∫ localTime,
          ∑ output ∈ outputModes,
            (integerWaveViscousMultiplier output)⁻¹ *
              complexCoordinateAmplitudeSq
                (wholeStateVorticityNonlinearCoefficientAt
                  (complexSharpSupportProjection inputModes
                    (receipt.wholePath localTime))
                  output)
          ∂(commonTimeMeasure requestedTime) := by
  let extendedPath : Real → ComplexVorticityHilbertState := fun time =>
    receipt.wholePath
      (Set.projIcc 0 requestedTime receipt.requestedTimePos.le time)
  let density : Real → Real := fun time =>
    ∑ output ∈ outputModes,
      (integerWaveViscousMultiplier output)⁻¹ *
        complexCoordinateAmplitudeSq
          (finiteStateVorticityNonlinearCoefficientAt inputModes
            (extendedPath time) output)
  have scaled :=
    finiteInputOutputNonlinearAction_parabolicScale
      inputModes outputModes extendedPath 0 requestedTime scale scalePos
  have commonEq :
      (∫ localTime,
        ∑ output ∈ outputModes,
          (integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (wholeStateVorticityNonlinearCoefficientAt
                (complexSharpSupportProjection inputModes
                  (receipt.wholePath localTime))
                output)
        ∂(commonTimeMeasure requestedTime)) =
      ∫ time in 0..requestedTime, density time := by
    calc
      (∫ localTime,
        ∑ output ∈ outputModes,
          (integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (wholeStateVorticityNonlinearCoefficientAt
                (complexSharpSupportProjection inputModes
                  (receipt.wholePath localTime))
                output)
        ∂(commonTimeMeasure requestedTime)) =
          ∫ localTime, density localTime.1
            ∂(commonTimeMeasure requestedTime) := by
              apply integral_congr_ae
              filter_upwards [] with localTime
              dsimp only [density, extendedPath]
              rw [Set.projIcc_of_mem receipt.requestedTimePos.le localTime.2]
              apply Finset.sum_congr rfl
              intro output _
              rw [wholeStateVorticityNonlinearCoefficientAt_projection_eq_finite]
      _ = ∫ time in 0..requestedTime, density time :=
        commonTime_integral_eq_intervalIntegral
          requestedTime receipt.requestedTimePos.le density
  rw [commonEq]
  simpa only [zero_add, sub_zero, density, extendedPath] using scaled

private theorem receiptWholeRow_parabolicScale_ae
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (scale : Real)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      ((scale : Complex) ^ 4) •
          receipt.rowTangent wave waveNe time =
        wholeStateVorticityNonlinearCoefficientAt
            ((scale ^ 2 : Real) • receipt.wholePath time) wave -
          (nu.coeff *
              (scale ^ 2 * integerWaveViscousMultiplier wave)) •
            ((scale ^ 2 : Complex) • receipt.wholePath time wave) := by
  filter_upwards [receipt.rowTangent_eq_unforced_ae wave waveNe,
    receipt.wholePath_eq_transverse_ae] with time tangentEq pathEq
  rw [tangentEq, ← pathEq,
    wholeStateVorticityBilinearCoefficientAt_self,
    smul_sub,
    wholeStateVorticityNonlinearCoefficientAt_real_smul]
  congr 1
  · rw [show (scale : Complex) ^ 4 =
        ((scale ^ 2 : Real) : Complex) ^ 2 by
      push_cast
      ring]
  · ext coordinate
    change
      (scale : Complex) ^ 4 *
          ((nu.coeff * integerWaveViscousMultiplier wave : Real) *
            receipt.wholePath time wave coordinate) =
        (nu.coeff * (scale ^ 2 * integerWaveViscousMultiplier wave) : Real) *
          ((scale ^ 2 : Complex) * receipt.wholePath time wave coordinate)
    push_cast
    ring

/-- The original source-selected finite-input prehistories commute with the
Navier--Stokes parabolic scale.  The finite projection remains an observer:
the actual whole receipt independently supplies the scaled row equation. -/
theorem
    sourceGeneratedNativeAccumulationParabolicallyScaledFiniteInputWholePrehistories
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let frequencySlope : Real :=
      (4368 * biotSavartSerrinConstant) /
        (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
    ∃ level : Nat → Real,
      level = (fun index : Nat =>
        4 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index) ∧
      ∃ finish radius : Nat → Nat,
      ∃ scale : Nat → Real,
        scale = (fun index => (level index + 2)⁻¹) ∧
        (∀ index,
          0 < scale index ∧
          scale index * (radius index : Real) ≤ frequencySlope + 1 ∧
          scale index * level index ≤
            (scale index ^ 3)⁻¹ *
              wholeVorticityEuclideanMass
                ((scale index ^ 2 : Real) •
                  (run initial (finish index)).contact.physicalState) ∧
          (scale index ^ 3)⁻¹ *
              wholeVorticityEuclideanMass
                ((scale index ^ 2 : Real) •
                  (run initial (finish index)).contact.physicalState) < 1 ∧
          (∀ edge, edge ∈ Finset.range (finish index) →
            (∀ᵐ localTime
                ∂(commonTimeMeasure
                  (run initial edge).nextContact.time.1),
              (scale index ^ 3)⁻¹ *
                  wholeVorticityEuclideanMass
                    ((scale index ^ 2 : Real) •
                      (run initial edge).nextContact.prefixReceipt.wholePath
                        localTime) < 1) ∧
            (∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0),
              ∀ᵐ localTime
                  ∂(commonTimeMeasure
                    (run initial edge).nextContact.time.1),
                ((scale index : Complex) ^ 4) •
                    (run initial edge).nextContact.prefixReceipt.rowTangent
                      wave waveNe localTime =
                  wholeStateVorticityNonlinearCoefficientAt
                      ((scale index ^ 2 : Real) •
                        (run initial edge).nextContact.prefixReceipt.wholePath
                          localTime) wave -
                    (nu.coeff *
                        (scale index ^ 2 *
                          integerWaveViscousMultiplier wave)) •
                      ((scale index ^ 2 : Complex) •
                        (run initial edge).nextContact.prefixReceipt.wholePath
                          localTime wave)) ∧
            (∀ localTime center shift x,
              (scale index ^ 2 : Real) •
                  finiteRealComplexFourierField
                    (integerWaveFrequencyCube (radius index))
                    ((run initial edge).nextContact.prefixReceipt.wholePath
                      localTime)
                    (center + scale index •
                      (x + (scale index)⁻¹ • latticeShift shift)) =
                (scale index ^ 2 : Real) •
                  finiteRealComplexFourierField
                    (integerWaveFrequencyCube (radius index))
                    ((run initial edge).nextContact.prefixReceipt.wholePath
                      localTime)
                    (center + scale index • x))) ∧
          nu.coeff / 8 ≤
            ∑ edge ∈ Finset.range (finish index),
              ∫ scaledTime in 0..
                  (run initial edge).nextContact.time.1 / scale index ^ 2,
                ∑ output ∈
                    finiteVorticityPairOutputSupport
                      (integerWaveFrequencyCube (radius index)),
                  (scale index ^ 3)⁻¹ *
                    (scale index ^ 2 *
                      integerWaveViscousMultiplier output)⁻¹ *
                    complexCoordinateAmplitudeSq
                      (finiteStateVorticityNonlinearCoefficientAt
                        (integerWaveFrequencyCube (radius index))
                        ((scale index ^ 2 : Real) •
                          (run initial edge).nextContact.prefixReceipt.wholePath
                            (Set.projIcc 0
                              (run initial edge).nextContact.time.1
                              (run initial edge).nextContact.time_pos.le
                              (scale index ^ 2 * scaledTime)))
                        output)) ∧
        Tendsto
          (fun index => elapsedTime initial (finish index + 1))
          atTop (nhds (wholeRestartVelocityAccumulationTime initial)) ∧
        Tendsto
          (fun index =>
            elapsedTime initial (finish index + 1) / scale index ^ 2)
          atTop atTop := by
  dsimp only
  obtain ⟨level, levelEq, finish, radius, specifications,
      finishTendsto, horizonTendsto⟩ :=
    sourceGeneratedNativeAccumulationScaleCriticalFiniteInputWholePrehistories
      initial elapsedBounded
  let scale : Nat → Real := fun index => (level index + 2)⁻¹
  refine ⟨level, levelEq, finish, radius, scale, rfl, ?_,
    finishTendsto, ?_⟩
  · intro index
    rcases specifications index with
      ⟨levelFour, _finishPos, _radiusPos, _finishMassLower,
        _finishMassUpper, radiusBound, terminalLower,
        terminalUpper, interiorMass, actionLower⟩
    have denominatorPos : 0 < level index + 2 := by linarith
    have scalePos : 0 < scale index := by
      dsimp only [scale]
      exact inv_pos.mpr denominatorPos
    have terminalScale :=
      (wholeVorticityMass_gradient_parabolicScale
        (scale index) scalePos
        (run initial (finish index)).contact.physicalState).1
    have terminalScaled :
        (scale index ^ 3)⁻¹ *
            wholeVorticityEuclideanMass
              ((scale index ^ 2 : Real) •
                (run initial (finish index)).contact.physicalState) =
          scale index *
            restartPhysicalVorticityMass initial (finish index) := by
      simpa only [restartPhysicalVorticityMass] using terminalScale
    have edgeFacts (edge : Nat)
        (edgeMem : edge ∈ Finset.range (finish index)) :
        (∀ᵐ localTime
            ∂(commonTimeMeasure
              (run initial edge).nextContact.time.1),
          (scale index ^ 3)⁻¹ *
              wholeVorticityEuclideanMass
                ((scale index ^ 2 : Real) •
                  (run initial edge).nextContact.prefixReceipt.wholePath
                    localTime) < 1) ∧
        (∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0),
          ∀ᵐ localTime
              ∂(commonTimeMeasure
                (run initial edge).nextContact.time.1),
            ((scale index : Complex) ^ 4) •
                (run initial edge).nextContact.prefixReceipt.rowTangent
                  wave waveNe localTime =
              wholeStateVorticityNonlinearCoefficientAt
                  ((scale index ^ 2 : Real) •
                    (run initial edge).nextContact.prefixReceipt.wholePath
                      localTime) wave -
                (nu.coeff *
                    (scale index ^ 2 *
                      integerWaveViscousMultiplier wave)) •
                  ((scale index ^ 2 : Complex) •
                    (run initial edge).nextContact.prefixReceipt.wholePath
                      localTime wave)) ∧
        (∀ localTime center shift x,
          (scale index ^ 2 : Real) •
              finiteRealComplexFourierField
                (integerWaveFrequencyCube (radius index))
                ((run initial edge).nextContact.prefixReceipt.wholePath
                  localTime)
                (center + scale index •
                  (x + (scale index)⁻¹ • latticeShift shift)) =
            (scale index ^ 2 : Real) •
              finiteRealComplexFourierField
                (integerWaveFrequencyCube (radius index))
                ((run initial edge).nextContact.prefixReceipt.wholePath
                  localTime)
                (center + scale index • x)) := by
      refine ⟨?_, ?_, ?_⟩
      · filter_upwards [interiorMass edge edgeMem] with localTime massLt
        rw [(wholeVorticityMass_gradient_parabolicScale
          (scale index) scalePos
          ((run initial edge).nextContact.prefixReceipt.wholePath
            localTime)).1]
        exact massLt
      · intro wave waveNe
        exact receiptWholeRow_parabolicScale_ae
          (run initial edge).nextContact.prefixReceipt
          (scale index) wave waveNe
      · intro localTime center shift x
        exact finiteRealComplexFourierField_parabolicScale_expandedPeriodic
          (integerWaveFrequencyCube (radius index))
          ((run initial edge).nextContact.prefixReceipt.wholePath localTime)
          (scale index) scalePos center shift x
    have actionSumEq :
        (∑ edge ∈ Finset.range (finish index),
          ∫ scaledTime in 0..
              (run initial edge).nextContact.time.1 / scale index ^ 2,
            ∑ output ∈
                finiteVorticityPairOutputSupport
                  (integerWaveFrequencyCube (radius index)),
              (scale index ^ 3)⁻¹ *
                (scale index ^ 2 *
                  integerWaveViscousMultiplier output)⁻¹ *
                complexCoordinateAmplitudeSq
                  (finiteStateVorticityNonlinearCoefficientAt
                    (integerWaveFrequencyCube (radius index))
                    ((scale index ^ 2 : Real) •
                      (run initial edge).nextContact.prefixReceipt.wholePath
                        (Set.projIcc 0
                          (run initial edge).nextContact.time.1
                          (run initial edge).nextContact.time_pos.le
                          (scale index ^ 2 * scaledTime)))
                    output)) =
          scale index *
            (∑ edge ∈ Finset.range (finish index),
              ∫ localTime,
                ∑ output ∈
                    finiteVorticityPairOutputSupport
                      (integerWaveFrequencyCube (radius index)),
                  (integerWaveViscousMultiplier output)⁻¹ *
                    complexCoordinateAmplitudeSq
                      (wholeStateVorticityNonlinearCoefficientAt
                        (complexSharpSupportProjection
                          (integerWaveFrequencyCube (radius index))
                          ((run initial edge).nextContact.prefixReceipt.wholePath
                            localTime))
                        output)
                ∂(commonTimeMeasure
                  (run initial edge).nextContact.time.1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro edge _edgeMem
      exact receiptFiniteInputOutputAction_parabolicScale
        (run initial edge).nextContact.prefixReceipt
        (integerWaveFrequencyCube (radius index))
        (finiteVorticityPairOutputSupport
          (integerWaveFrequencyCube (radius index)))
        (scale index) scalePos
    refine ⟨scalePos, ?_, ?_, ?_, edgeFacts, ?_⟩
    · simpa only [scale] using radiusBound
    · rw [terminalScaled]
      simpa only [scale] using terminalLower
    · rw [terminalScaled]
      simpa only [scale] using terminalUpper
    · rw [actionSumEq]
      simpa only [scale] using actionLower
  · convert horizonTendsto using 1
    funext index
    have denominatorPos : 0 < level index + 2 := by
      have := (specifications index).1
      linarith
    dsimp only [scale]
    field_simp [denominatorPos.ne']

/-- Geometric source levels select nonvanishing actual states on the original
pre-accumulation trajectory.  Each state comes from a literal subreceipt of a
last-hit band and simultaneously obeys the normalized tangent/gradient cubic
budget. -/
theorem
    sourceGeneratedNativeAccumulationScaleCriticalTangentGradientStates_tendsto_accumulation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let tangentGradientConstant : Real :=
      (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
        (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
    ∃ level : Nat → Real,
      level = (fun index : Nat =>
        4 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index) ∧
      ∃ segmentInitial : Nat → ComplexVorticityHilbertState,
      ∃ segmentTime : Nat → Real,
      ∃ segmentReceipt :
          (index : Nat) → WholeContinuousMildSerrinReceipt nu
            (segmentInitial index) (segmentTime index),
      ∃ sample :
          (index : Nat) → Icc (0 : Real) (segmentTime index),
      ∃ actualPoint :
          Nat → Ico (0 : Real)
            (wholeRestartVelocityAccumulationTime initial),
        (∀ index,
          4 ≤ level index ∧
          1 / 2 ≤ (level index)⁻¹ *
            wholeVorticityEuclideanMass
              ((segmentReceipt index).wholePath (sample index)) ∧
          (level index)⁻¹ *
              wholeVorticityEuclideanMass
                ((segmentReceipt index).wholePath (sample index)) ≤ 1 ∧
          (Summable fun wave : IntegerWavevector =>
            integerWaveNormSq wave *
              complexCoordinateAmplitudeSq
                ((segmentReceipt index).wholePath (sample index) wave)) ∧
          ((level index) ^ 3)⁻¹ *
              (‖puncturedEuclideanSpaceTimeState
                    (segmentReceipt index).wholeTangent (sample index)‖ ^ 2 +
                ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
                  wholeStateVorticityGradientMass
                    ((segmentReceipt index).wholePath (sample index))) ≤
            tangentGradientConstant ∧
          (segmentReceipt index).wholePath (sample index) =
            wholeRestartBoundedPreAccumulationPhysicalTrajectory
              initial elapsedBounded (actualPoint index)) ∧
        Tendsto (fun index => (actualPoint index : Real)) atTop
          (nhds (wholeRestartVelocityAccumulationTime initial)) := by
  dsimp only
  let level : Nat → Real := fun index =>
    4 * (|restartPhysicalVorticityMass initial 0| + 1) *
      (4 : Real) ^ index
  have levelFour (index : Nat) : 4 ≤ level index := by
    have massFactor :
        1 ≤ |restartPhysicalVorticityMass initial 0| + 1 := by
      linarith [abs_nonneg (restartPhysicalVorticityMass initial 0)]
    have powerFactor : 1 ≤ (4 : Real) ^ index :=
      one_le_pow₀ (by norm_num)
    dsimp only [level]
    calc
      4 = 4 * 1 * 1 := by norm_num
      _ ≤ 4 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index := by gcongr
  have levelPos (index : Nat) : 0 < level index :=
    lt_of_lt_of_le (by norm_num) (levelFour index)
  have initialLeHalf (index : Nat) :
      restartPhysicalVorticityMass initial 0 ≤ level index / 2 := by
    have powerFactor : 1 ≤ (4 : Real) ^ index :=
      one_le_pow₀ (by norm_num)
    calc
      restartPhysicalVorticityMass initial 0 ≤
          |restartPhysicalVorticityMass initial 0| := le_abs_self _
      _ ≤ 2 * (|restartPhysicalVorticityMass initial 0| + 1) * 1 := by
        nlinarith [abs_nonneg (restartPhysicalVorticityMass initial 0)]
      _ ≤ 2 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index := by gcongr
      _ = level index / 2 := by
        dsimp only [level]
        ring
  have generated (index : Nat) :=
    sourceGeneratedNativeAccumulationScaleCriticalLastHitTangentGradientState
      initial elapsedBounded (level index) (levelPos index)
        (initialLeHalf index)
  choose start finish edge beginTime endTime segmentInitial segmentTime
    _segmentTimePos segmentReceipt absoluteTime sample specifications
      using generated
  have sampleAbsoluteNonneg (index : Nat) :
      0 ≤ absoluteTime index (sample index) := by
    rcases specifications index with
      ⟨_startLtFinish, beginMem, _endMem, _beginLtEnd,
        _beginMass, _endMass, _interiorMass, _scaleSpan, _edgeLt,
        pathChart, _endpointNondecreasing, _massLower, _massUpper,
        _gradientSummable, _budget⟩
    exact
      (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
        initial (start index + 1)).trans
          (beginMem.1.trans (pathChart (sample index)).1.1)
  have sampleAbsoluteLtAccumulation (index : Nat) :
      absoluteTime index (sample index) <
        wholeRestartVelocityAccumulationTime initial := by
    rcases specifications index with
      ⟨_startLtFinish, _beginMem, endMem, _beginLtEnd,
        _beginMass, _endMass, _interiorMass, _scaleSpan, _edgeLt,
        pathChart, _endpointNondecreasing, _massLower, _massUpper,
        _gradientSummable, _budget⟩
    exact (pathChart (sample index)).1.2.trans_lt
      (endMem.2.trans_lt
        (elapsedTime_lt_wholeRestartVelocityAccumulationTime
          initial elapsedBounded (finish index + 1)))
  let actualPoint :
      Nat → Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) :=
    fun index =>
      ⟨absoluteTime index (sample index), sampleAbsoluteNonneg index,
        sampleAbsoluteLtAccumulation index⟩
  have stateSpecifications (index : Nat) :
      4 ≤ level index ∧
      1 / 2 ≤ (level index)⁻¹ *
        wholeVorticityEuclideanMass
          ((segmentReceipt index).wholePath (sample index)) ∧
      (level index)⁻¹ *
          wholeVorticityEuclideanMass
            ((segmentReceipt index).wholePath (sample index)) ≤ 1 ∧
      (Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            ((segmentReceipt index).wholePath (sample index) wave)) ∧
      ((level index) ^ 3)⁻¹ *
          (‖puncturedEuclideanSpaceTimeState
                (segmentReceipt index).wholeTangent (sample index)‖ ^ 2 +
            ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
              wholeStateVorticityGradientMass
                ((segmentReceipt index).wholePath (sample index))) ≤
        (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) ∧
      (segmentReceipt index).wholePath (sample index) =
        wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded (actualPoint index) := by
    rcases specifications index with
      ⟨_startLtFinish, _beginMem, endMem, _beginLtEnd,
        _beginMass, _endMass, _interiorMass, _scaleSpan, _edgeLt,
        pathChart, _endpointNondecreasing, massLower, massUpper,
        gradientSummable, budget⟩
    have prefixEq := (pathChart (sample index)).2
    have boundedEq :=
      wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
        initial elapsedBounded (actualPoint index) (finish index + 1)
          ((pathChart (sample index)).1.2.trans endMem.2)
    exact ⟨levelFour index, massLower, massUpper, gradientSummable, budget,
      prefixEq.trans boundedEq.symm⟩
  let massObservable :
      Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) → Real :=
    fun time =>
      wholeVorticityEuclideanMass
        (wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded time)
  have massObservableContinuous : Continuous massObservable :=
    continuous_wholeVorticityEuclideanMass.comp
      (wholeRestartBoundedPreAccumulationPhysicalTrajectory_continuous
        initial elapsedBounded)
  have levelTendsto : Tendsto level atTop atTop := by
    have powerTendsto :
        Tendsto (fun index : Nat => (4 : Real) ^ index) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have coefficientPos :
        0 < 4 * (|restartPhysicalVorticityMass initial 0| + 1) := by
      positivity
    exact powerTendsto.const_mul_atTop coefficientPos
  have levelHalfTendsto :
      Tendsto (fun index => level index / 2) atTop atTop := by
    convert levelTendsto.const_mul_atTop (by norm_num : (0 : Real) < 1 / 2)
      using 1
    funext index
    ring
  have massLower (index : Nat) :
      level index / 2 ≤ massObservable (actualPoint index) := by
    have normalizedLower := (stateSpecifications index).2.1
    have rawLower :
        level index / 2 ≤
          wholeVorticityEuclideanMass
            ((segmentReceipt index).wholePath (sample index)) := by
      calc
        level index / 2 = level index * (1 / 2) := by ring
        _ ≤ level index *
            ((level index)⁻¹ *
              wholeVorticityEuclideanMass
                ((segmentReceipt index).wholePath (sample index))) :=
          mul_le_mul_of_nonneg_left normalizedLower (levelPos index).le
        _ = wholeVorticityEuclideanMass
            ((segmentReceipt index).wholePath (sample index)) := by
          field_simp [(levelPos index).ne']
    unfold massObservable
    rw [← (stateSpecifications index).2.2.2.2.2]
    exact rawLower
  have massDiverges :
      Tendsto (fun index => massObservable (actualPoint index))
        atTop atTop := by
    rw [tendsto_atTop] at levelHalfTendsto ⊢
    intro bound
    filter_upwards [levelHalfTendsto bound] with index levelLarge
    exact levelLarge.trans (massLower index)
  have pointTendsto :=
    observation_divergence_forces_times_to_accumulation
      actualPoint massObservable massObservableContinuous massDiverges
  exact ⟨level, rfl, segmentInitial, segmentTime, segmentReceipt, sample,
    actualPoint, stateSpecifications, pointTendsto⟩

/-- The same actual source states retain a fixed normalized vorticity mass in
a source-selected Fourier inventory whose physical radius is uniformly
bounded after the parabolic normalization. -/
theorem
    sourceGeneratedNativeAccumulationScaleCriticalFiniteBandStates_tendsto_accumulation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let tangentGradientConstant : Real :=
      (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
        (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
    let gradientConstant : Real :=
      (2 * tangentGradientConstant) /
        (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
    ∃ level : Nat → Real,
      level = (fun index : Nat =>
        4 * (|restartPhysicalVorticityMass initial 0| + 1) *
          (4 : Real) ^ index) ∧
      ∃ segmentInitial : Nat → ComplexVorticityHilbertState,
      ∃ segmentTime : Nat → Real,
      ∃ segmentReceipt :
          (index : Nat) → WholeContinuousMildSerrinReceipt nu
            (segmentInitial index) (segmentTime index),
      ∃ sample :
          (index : Nat) → Icc (0 : Real) (segmentTime index),
      ∃ actualPoint :
          Nat → Ico (0 : Real)
            (wholeRestartVelocityAccumulationTime initial),
      ∃ radius : Nat → Nat,
        (∀ index,
          4 ≤ level index ∧
          1 / 2 ≤ (level index)⁻¹ *
            wholeVorticityEuclideanMass
              ((segmentReceipt index).wholePath (sample index)) ∧
          (level index)⁻¹ *
              wholeVorticityEuclideanMass
                ((segmentReceipt index).wholePath (sample index)) ≤ 1 ∧
          (Summable fun wave : IntegerWavevector =>
            integerWaveNormSq wave *
              complexCoordinateAmplitudeSq
                ((segmentReceipt index).wholePath (sample index) wave)) ∧
          ((level index) ^ 3)⁻¹ *
              (‖puncturedEuclideanSpaceTimeState
                    (segmentReceipt index).wholeTangent (sample index)‖ ^ 2 +
                ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
                  wholeStateVorticityGradientMass
                    ((segmentReceipt index).wholePath (sample index))) ≤
            tangentGradientConstant ∧
          ((level index) ^ 3)⁻¹ *
              wholeStateVorticityGradientMass
                ((segmentReceipt index).wholePath (sample index)) ≤
            gradientConstant ∧
          0 < radius index ∧
          3 / 8 ≤ (level index)⁻¹ *
            wholeVorticityEuclideanMass
              (complexSharpSupportProjection
                (wholeRestartModes (radius index))
                ((segmentReceipt index).wholePath (sample index))) ∧
          (level index)⁻¹ * (radius index : Real) ≤
            8 * (gradientConstant + 1) + 1 ∧
          (segmentReceipt index).wholePath (sample index) =
            wholeRestartBoundedPreAccumulationPhysicalTrajectory
              initial elapsedBounded (actualPoint index)) ∧
        Tendsto (fun index => (actualPoint index : Real)) atTop
          (nhds (wholeRestartVelocityAccumulationTime initial)) := by
  dsimp only
  obtain ⟨level, levelEq, segmentInitial, segmentTime, segmentReceipt,
      sample, actualPoint, specifications, pointTendsto⟩ :=
    sourceGeneratedNativeAccumulationScaleCriticalTangentGradientStates_tendsto_accumulation
      initial elapsedBounded
  let tangentGradientConstant : Real :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
  let viscousConstant : Real := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let gradientConstant : Real :=
    (2 * tangentGradientConstant) / viscousConstant
  let ratio : Nat → Real := fun index =>
    8 * (gradientConstant + 1) * level index
  let radius : Nat → Nat := fun index => Nat.ceil (ratio index) + 1
  have viscousConstantPos : 0 < viscousConstant := by
    dsimp only [viscousConstant]
    exact mul_pos
      (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
  have tangentGradientConstantNonneg :
      0 ≤ tangentGradientConstant := by
    dsimp only [tangentGradientConstant]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (by norm_num))
        (sq_nonneg biotSavartSerrinConstant))
      (mul_nonneg (by norm_num) viscousConstantPos.le)
  have gradientConstantNonneg : 0 ≤ gradientConstant := by
    dsimp only [gradientConstant]
    exact div_nonneg
      (mul_nonneg (by norm_num) tangentGradientConstantNonneg)
      viscousConstantPos.le
  refine ⟨level, levelEq, segmentInitial, segmentTime, segmentReceipt,
    sample, actualPoint, radius, ?_, pointTendsto⟩
  intro index
  rcases specifications index with
    ⟨levelFour, massLower, massUpper, gradientSummable, budget,
      stateEq⟩
  have levelPos : 0 < level index :=
    lt_of_lt_of_le (by norm_num) levelFour
  have levelCubePos : 0 < (level index) ^ 3 := pow_pos levelPos 3
  have tangentNonneg :
      0 ≤ ‖puncturedEuclideanSpaceTimeState
        (segmentReceipt index).wholeTangent (sample index)‖ ^ 2 :=
    sq_nonneg _
  have gradientMassNonneg :
      0 ≤ wholeStateVorticityGradientMass
        ((segmentReceipt index).wholePath (sample index)) := by
    unfold wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  have halfViscousPos : 0 < viscousConstant / 2 := by positivity
  have scaledGradientWeighted :
      (viscousConstant / 2) *
          (((level index) ^ 3)⁻¹ *
            wholeStateVorticityGradientMass
              ((segmentReceipt index).wholePath (sample index))) ≤
        tangentGradientConstant := by
    calc
      (viscousConstant / 2) *
            (((level index) ^ 3)⁻¹ *
              wholeStateVorticityGradientMass
                ((segmentReceipt index).wholePath (sample index))) =
          ((level index) ^ 3)⁻¹ *
            ((viscousConstant / 2) *
              wholeStateVorticityGradientMass
                ((segmentReceipt index).wholePath (sample index))) := by
        ring
      _ ≤ ((level index) ^ 3)⁻¹ *
          (‖puncturedEuclideanSpaceTimeState
                (segmentReceipt index).wholeTangent (sample index)‖ ^ 2 +
            (viscousConstant / 2) *
              wholeStateVorticityGradientMass
                ((segmentReceipt index).wholePath (sample index))) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left tangentNonneg)
          (inv_nonneg.mpr levelCubePos.le)
      _ ≤ tangentGradientConstant := by
        simpa only [viscousConstant] using budget
  have halfViscousGradientConstant :
      (viscousConstant / 2) * gradientConstant =
        tangentGradientConstant := by
    dsimp only [gradientConstant]
    field_simp [viscousConstantPos.ne']
  have scaledGradient :
      ((level index) ^ 3)⁻¹ *
          wholeStateVorticityGradientMass
            ((segmentReceipt index).wholePath (sample index)) ≤
        gradientConstant := by
    apply (mul_le_mul_iff_of_pos_left halfViscousPos).mp
    rw [halfViscousGradientConstant]
    exact scaledGradientWeighted
  have gradientMassLe :
      wholeStateVorticityGradientMass
          ((segmentReceipt index).wholePath (sample index)) ≤
        gradientConstant * (level index) ^ 3 := by
    have unscaled := (inv_mul_le_iff₀ levelCubePos).mp scaledGradient
    simpa only [mul_comm] using unscaled
  have ratioNonneg : 0 ≤ ratio index := by
    dsimp only [ratio]
    positivity
  have radiusPos : 0 < radius index := by
    dsimp only [radius]
    omega
  have ratioLeRadius : ratio index ≤ (radius index : Real) := by
    calc
      ratio index ≤ (Nat.ceil (ratio index) : Real) :=
        Nat.le_ceil (ratio index)
      _ ≤ (radius index : Real) := by
        dsimp only [radius]
        push_cast
        linarith
  have radiusUpper : (radius index : Real) ≤ ratio index + 2 := by
    have ceilLt : (Nat.ceil (ratio index) : Real) < ratio index + 1 :=
      Nat.ceil_lt_add_one ratioNonneg
    dsimp only [radius]
    push_cast
    linarith
  have normalizedRadius :
      (level index)⁻¹ * (radius index : Real) ≤
        8 * (gradientConstant + 1) + 1 := by
    calc
      (level index)⁻¹ * (radius index : Real) ≤
          (level index)⁻¹ * (ratio index + 2) :=
        mul_le_mul_of_nonneg_left radiusUpper (inv_nonneg.mpr levelPos.le)
      _ = 8 * (gradientConstant + 1) + 2 / level index := by
        dsimp only [ratio]
        field_simp [levelPos.ne']
      _ ≤ 8 * (gradientConstant + 1) + 1 := by
        have twoLeLevel : (2 : Real) ≤ level index := by linarith
        have twoDivLeOne : 2 / level index ≤ 1 :=
          (div_le_one levelPos).mpr twoLeLevel
        linarith
  have radiusSqPos : 0 < (radius index : Real) ^ 2 := by
    positivity
  have ratioSqLeRadiusSq : (ratio index) ^ 2 ≤ (radius index : Real) ^ 2 :=
    (sq_le_sq₀ ratioNonneg (by positivity)).2 ratioLeRadius
  have coefficientLe :
      gradientConstant ≤ 8 * (gradientConstant + 1) ^ 2 := by
    nlinarith [sq_nonneg (gradientConstant + 1)]
  have gradientScaledLeRadiusPayment :
      gradientConstant * (level index) ^ 3 ≤
        (level index / 8) * (radius index : Real) ^ 2 := by
    have coefficientScaled :
        gradientConstant * (level index) ^ 3 ≤
          (8 * (gradientConstant + 1) ^ 2) * (level index) ^ 3 :=
      mul_le_mul_of_nonneg_right coefficientLe levelCubePos.le
    have ratioPayment :
        (8 * (gradientConstant + 1) ^ 2) * (level index) ^ 3 =
          (level index / 8) * (ratio index) ^ 2 := by
      dsimp only [ratio]
      ring
    rw [ratioPayment] at coefficientScaled
    exact coefficientScaled.trans
      (mul_le_mul_of_nonneg_left ratioSqLeRadiusSq
        (div_nonneg levelPos.le (by norm_num)))
  have tailLe :
      wholeVorticityEuclideanMass
          (complexSharpSupportProjection
              (wholeRestartModes (radius index))
              ((segmentReceipt index).wholePath (sample index)) -
            (segmentReceipt index).wholePath (sample index)) ≤
        level index / 8 := by
    have tailGradient :=
      wholeVorticity_puncturedCubeTail_le_gradient_div_sq
        ((segmentReceipt index).wholePath (sample index))
        ((segmentReceipt index).wholePath_zero_row (sample index))
        gradientSummable (radius index) radiusPos
    refine tailGradient.trans ?_
    apply (div_le_iff₀ radiusSqPos).2
    exact gradientMassLe.trans gradientScaledLeRadiusPayment
  have massRawLower :
      level index / 2 ≤
        wholeVorticityEuclideanMass
          ((segmentReceipt index).wholePath (sample index)) := by
    calc
      level index / 2 = level index * (1 / 2) := by ring
      _ ≤ level index *
          ((level index)⁻¹ *
            wholeVorticityEuclideanMass
              ((segmentReceipt index).wholePath (sample index))) :=
        mul_le_mul_of_nonneg_left massLower levelPos.le
      _ = wholeVorticityEuclideanMass
          ((segmentReceipt index).wholePath (sample index)) := by
        field_simp [levelPos.ne']
  have massSplit :=
    wholeVorticityEuclideanMass_eq_projection_add_complement
      (wholeRestartModes (radius index))
      ((segmentReceipt index).wholePath (sample index))
  have projectedRawLower :
      3 * level index / 8 ≤
        wholeVorticityEuclideanMass
          (complexSharpSupportProjection
            (wholeRestartModes (radius index))
            ((segmentReceipt index).wholePath (sample index))) := by
    linarith
  have projectedLower :
      3 / 8 ≤ (level index)⁻¹ *
        wholeVorticityEuclideanMass
          (complexSharpSupportProjection
            (wholeRestartModes (radius index))
            ((segmentReceipt index).wholePath (sample index))) := by
    calc
      3 / 8 = (level index)⁻¹ * (3 * level index / 8) := by
        field_simp [levelPos.ne']
      _ ≤ (level index)⁻¹ *
          wholeVorticityEuclideanMass
            (complexSharpSupportProjection
              (wholeRestartModes (radius index))
              ((segmentReceipt index).wholePath (sample index))) :=
        mul_le_mul_of_nonneg_left projectedRawLower
          (inv_nonneg.mpr levelPos.le)
  exact ⟨levelFour, massLower, massUpper, gradientSummable, budget,
    scaledGradient, radiusPos, projectedLower, normalizedRadius, stateEq⟩

/-- On one fixed Fourier inventory, the high-frequency parabolic trace is
settled exactly by the same NS tangent, viscous, nonlinear and endpoint
enstrophy ledger. -/
theorem wholeRestartIcoHighFrequencyProjectedParabolicTrace_exactSettlement
    (initial : GeneratedWholeRestartCurrent nu)
    (radius start finish : Nat)
    (startLeFinish : start ≤ finish) :
    (∑ index ∈ Finset.Ico start finish,
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt radius) +
        nu.coeff *
          (finiteStateVorticityCoefficientEnstrophy
                (wholeRestartModes radius)
                (run initial finish).contact.physicalState -
            finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes radius)
              (run initial start).contact.physicalState) +
        wholeRestartIcoTangentNegativeOneEuclideanPayment
          initial start finish +
        wholeRestartIcoViscousNegativeOneEuclideanPayment
          initial start finish =
      wholeRestartIcoNonlinearNegativeOneEuclideanPayment
        initial start finish := by
  have trace :=
    wholeRestartIcoHighFrequencyProjectedParabolicTrace_telescope
      initial radius start finish startLeFinish
  have startSplit :=
    restartPhysicalVorticityMass_eq_low_add_tail
      initial start radius
  have finishSplit :=
    restartPhysicalVorticityMass_eq_low_add_tail
      initial finish radius
  rw [← finiteStateVorticityCoefficientEnstrophy_eq_projectionMass]
    at startSplit finishSplit
  have euclidean :=
    wholeRestartIcoNonlinearNegativeOneEuclideanPayment_balance
      initial start finish startLeFinish
  change
    wholeRestartIcoNonlinearNegativeOneEuclideanPayment initial start finish +
        nu.coeff * restartPhysicalVorticityMass initial start =
      wholeRestartIcoTangentNegativeOneEuclideanPayment initial start finish +
        wholeRestartIcoViscousNegativeOneEuclideanPayment initial start finish +
        nu.coeff * restartPhysicalVorticityMass initial finish at euclidean
  linear_combination
    -euclidean + nu.coeff * startSplit -
      nu.coeff * finishSplit + trace

/-- The signed literal cross-incidence prefix is settled on the original
NS ledger after subtracting the independently summable pair diagonal.  The
remaining projected trace is already identified, receipt by receipt, with
literal triad work, viscous-rate differences, and the output viscous debit
by `receiptHighFrequencyProjectedParabolicTrace_eq_literalTriadViscousRateBalance`.
-/
theorem nativeAccumulationLiteralCrossActionPrefix_exactWholeLedgerSettlement
    (initial : GeneratedWholeRestartCurrent nu)
    (radius length : Nat) :
    nativeAccumulationSymmetricVorticityPairLiteralCrossActionPrefix
        initial length =
      (∑ index ∈ Finset.Ico 0 length,
          receiptHighFrequencyProjectedParabolicTrace
            (run initial index).nextContact.prefixReceipt radius) +
        nu.coeff *
          (finiteStateVorticityCoefficientEnstrophy
                (wholeRestartModes radius)
                (run initial length).contact.physicalState -
            finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes radius)
              (run initial 0).contact.physicalState) +
        wholeRestartIcoTangentNegativeOneEuclideanPayment
          initial 0 length +
        wholeRestartIcoViscousNegativeOneEuclideanPayment
          initial 0 length -
        nativeAccumulationSymmetricVorticityPairDiagonalActionPrefix
          initial length := by
  have settlement :=
    wholeRestartIcoHighFrequencyProjectedParabolicTrace_exactSettlement
      initial radius 0 length (Nat.zero_le length)
  have polarization :=
    nativeAccumulationNonlinearNegativeOneActionPrefix_eq_diagonal_add_literalCross
      initial length
  unfold nativeAccumulationNonlinearNegativeOneActionPrefix at polarization
  linarith

/-- Across the source selector's moving inventories, every fixed-block
settlement accumulates exactly.  Changing the inventory leaves precisely the
intermediate annular coefficient mass on the nonlinear side. -/
theorem sourceGeneratedNativeAccumulationCofinalMovingCutoff_exactSettlement
    (initial : GeneratedWholeRestartCurrent nu)
    (contactIndex : Nat → Nat)
    (contactIndexStrictMono : StrictMono contactIndex)
    (length : Nat) :
    (∑ step ∈ Finset.range (length + 1),
      ∑ index ∈ Finset.Ico (contactIndex step) (contactIndex (step + 1)),
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt
          (2 * (contactIndex step + 1))) +
        nu.coeff *
          (finiteStateVorticityCoefficientEnstrophy
                (wholeRestartModes (2 * (contactIndex length + 1)))
                (run initial (contactIndex (length + 1))).contact.physicalState -
            finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes (2 * (contactIndex 0 + 1)))
              (run initial (contactIndex 0)).contact.physicalState) +
        (∑ step ∈ Finset.range (length + 1),
          (wholeRestartIcoTangentNegativeOneEuclideanPayment
              initial (contactIndex step) (contactIndex (step + 1)) +
            wholeRestartIcoViscousNegativeOneEuclideanPayment
              initial (contactIndex step) (contactIndex (step + 1)))) =
      (∑ step ∈ Finset.range (length + 1),
        wholeRestartIcoNonlinearNegativeOneEuclideanPayment
          initial (contactIndex step) (contactIndex (step + 1))) +
        nu.coeff *
          (∑ step ∈ Finset.range length,
            finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
                wholeRestartModes (2 * (contactIndex step + 1)))
              (run initial (contactIndex (step + 1))).contact.physicalState) := by
  let radius : Nat → Nat := fun step => 2 * (contactIndex step + 1)
  let lowMass : Nat → Nat → Real := fun step index =>
    finiteStateVorticityCoefficientEnstrophy
      (wholeRestartModes (radius step))
      (run initial index).contact.physicalState
  let annularMass : Nat → Real := fun step =>
    finiteStateVorticityCoefficientEnstrophy
      (wholeRestartModes (radius (step + 1)) \
        wholeRestartModes (radius step))
      (run initial (contactIndex (step + 1))).contact.physicalState
  let traceBlock : Nat → Real := fun step =>
    ∑ index ∈ Finset.Ico (contactIndex step) (contactIndex (step + 1)),
      receiptHighFrequencyProjectedParabolicTrace
        (run initial index).nextContact.prefixReceipt (radius step)
  let tangentBlock : Nat → Real := fun step =>
    wholeRestartIcoTangentNegativeOneEuclideanPayment
      initial (contactIndex step) (contactIndex (step + 1))
  let viscousBlock : Nat → Real := fun step =>
    wholeRestartIcoViscousNegativeOneEuclideanPayment
      initial (contactIndex step) (contactIndex (step + 1))
  let nonlinearBlock : Nat → Real := fun step =>
    wholeRestartIcoNonlinearNegativeOneEuclideanPayment
      initial (contactIndex step) (contactIndex (step + 1))
  change
    (∑ step ∈ Finset.range (length + 1), traceBlock step) +
        nu.coeff *
          (lowMass length (contactIndex (length + 1)) -
            lowMass 0 (contactIndex 0)) +
        (∑ step ∈ Finset.range (length + 1),
          (tangentBlock step + viscousBlock step)) =
      (∑ step ∈ Finset.range (length + 1), nonlinearBlock step) +
        nu.coeff *
          (∑ step ∈ Finset.range length, annularMass step)
  have radiusStepLe (step : Nat) : radius step ≤ radius (step + 1) := by
    dsimp only [radius]
    exact Nat.mul_le_mul_left 2
      (Nat.add_le_add_right
        (contactIndexStrictMono (Nat.lt_succ_self step)).le 1)
  have annularEq (step : Nat) :
      lowMass (step + 1) (contactIndex (step + 1)) -
          lowMass step (contactIndex (step + 1)) =
        annularMass step := by
    have tailEq :=
      restartPhysicalHighFrequencyTailMass_sub_eq_projectedAnnularMass
        initial (contactIndex (step + 1)) (radiusStepLe step)
    have smallerSplit :=
      restartPhysicalVorticityMass_eq_low_add_tail
        initial (contactIndex (step + 1)) (radius step)
    have largerSplit :=
      restartPhysicalVorticityMass_eq_low_add_tail
        initial (contactIndex (step + 1)) (radius (step + 1))
    rw [← finiteStateVorticityCoefficientEnstrophy_eq_projectionMass]
      at smallerSplit largerSplit
    change
      restartPhysicalHighFrequencyTailMass
            initial (contactIndex (step + 1)) (radius step) -
          restartPhysicalHighFrequencyTailMass
            initial (contactIndex (step + 1)) (radius (step + 1)) =
        annularMass step at tailEq
    change
      restartPhysicalVorticityMass initial (contactIndex (step + 1)) =
        lowMass step (contactIndex (step + 1)) +
          restartPhysicalHighFrequencyTailMass
            initial (contactIndex (step + 1)) (radius step) at smallerSplit
    change
      restartPhysicalVorticityMass initial (contactIndex (step + 1)) =
        lowMass (step + 1) (contactIndex (step + 1)) +
          restartPhysicalHighFrequencyTailMass
            initial (contactIndex (step + 1)) (radius (step + 1)) at largerSplit
    linarith
  have lowTelescope :
      (∑ step ∈ Finset.range (length + 1),
        (lowMass step (contactIndex (step + 1)) -
          lowMass step (contactIndex step))) =
        lowMass length (contactIndex (length + 1)) -
          lowMass 0 (contactIndex 0) -
        ∑ step ∈ Finset.range length, annularMass step := by
    induction length with
    | zero =>
        simp
    | succ length inductionHypothesis =>
        rw [Finset.sum_range_succ, inductionHypothesis]
        rw [Finset.sum_range_succ]
        have annular := annularEq length
        ring_nf at annular ⊢
        linarith
  have blockEq (step : Nat) :
      traceBlock step +
          nu.coeff *
            (lowMass step (contactIndex (step + 1)) -
              lowMass step (contactIndex step)) +
          tangentBlock step +
          viscousBlock step =
        nonlinearBlock step := by
    exact
      wholeRestartIcoHighFrequencyProjectedParabolicTrace_exactSettlement
        initial (radius step) (contactIndex step) (contactIndex (step + 1))
        (contactIndexStrictMono (Nat.lt_succ_self step)).le
  have summed :
      (∑ step ∈ Finset.range (length + 1),
        (traceBlock step +
          nu.coeff *
            (lowMass step (contactIndex (step + 1)) -
              lowMass step (contactIndex step)) +
          tangentBlock step +
          viscousBlock step)) =
        ∑ step ∈ Finset.range (length + 1), nonlinearBlock step := by
    apply Finset.sum_congr rfl
    intro step _stepMem
    exact blockEq step
  rw [Finset.sum_add_distrib] at summed
  rw [Finset.sum_add_distrib] at summed
  rw [Finset.sum_add_distrib] at summed
  rw [← Finset.mul_sum] at summed
  rw [Finset.sum_add_distrib]
  linear_combination summed - nu.coeff * lowTelescope

/-- The bounded analytic failure is consumed by the chronological whole-PDE
action, while its separately anchored original-root cofinal occurrence
executes the source-generated physical next current and its first whole write.
The local bounded fibre supplies the failure, never the occurrence or next. -/
theorem sourceGeneratedNativeAccumulationNonlinearAction_rootCofinalPhysicalExecution
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let failure :=
      sourceGeneratedNativeAccumulationVorticityFailure
        initial elapsedBounded
    let endpoint :=
      sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial
    let slice := sourceGeneratedNativeTemporalPositiveTimeH1Slice initial
    let next :=
      generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
        initial failure.rootCofinalOccurrence
    Tendsto
        (nativeAccumulationNonlinearNegativeOneActionPrefix initial)
        atTop atTop ∧
      0 < next.duration ∧
      next.receipt.wholePath
          ⟨0, ⟨le_rfl, next.receipt.requestedTimePos.le⟩⟩ =
        slice.vorticityState ∧
      ∀ wave : IntegerWavevector,
        biotSavartVelocityCoefficient wave (next.initialState wave) =
          endpoint.wholePath slice.time wave := by
  dsimp only
  constructor
  · exact
      nativeAccumulationNonlinearNegativeOneActionPrefix_tendsto_atTop_of_elapsedTime_bddAbove
        initial elapsedBounded
  · rw [sourceGeneratedNativeAccumulationVorticityFailure_physicalNext
      initial elapsedBounded]
    exact sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent
      initial

/-- The bounded strong-face failure is an effect of the same original finite
whole-PDE prefix whose cofinal occurrence writes the first physical successor.
The temporal successor has positive registered-occurrence identity, and the
physical next current immediately emits its own first native write.  Every
transition in the conclusion is read from one of the two fixed source
compilers. -/
theorem sourceGeneratedNativeAccumulationStrongFaceFailure_actualWholePDEEffect
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let root := nativeTemporalAuthoritativeRoot initial
    let cofinalVisit : LawfulWorldStateAt root :=
      .cofinal (nativeTemporalCofinalVisit initial)
    let nextVisit : LawfulWorldStateAt root :=
      (nativeTemporalCofinalNextCurrent initial).visit
    let difference : RootTotalReality.RootDifference root :=
      (cofinalVisit, nextVisit)
    let entryAnswerAndNext :=
      nativeTemporalCofinalCausalAnswerAndNext initial
    let physicalNext :=
      generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
        initial (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence
    let nextRoot := nativeTemporalRoot physicalNext
    let firstVisit : SourceNativeTemporalVisitAt nextRoot :=
      .finite nextRoot.toRoot.initialVisit
    ActualDifferenceAt (RootTotalReality.semantics root) difference ∧
      (RootTotalReality.semantics root).StructuralIdentityAt difference ∧
      (root.toLedgerRoot.generatedAtTemporalVisit cofinalVisit).wholeLedgerWriteBack =
        nativeTemporalCofinalWrite initial ∧
      entryAnswerAndNext.answer =
        (nativeTemporalGalerkinEntryAuthority initial 0).toLedgerReadout ∧
      (∀ (start finish : Nat), start ≤ finish →
        wholeRestartIcoNonlinearNegativeOneEuclideanPayment
              initial start finish +
            nu.coeff * wholeVorticityEuclideanMass
              (run initial start).contact.physicalState =
          wholeRestartIcoTangentNegativeOneEuclideanPayment
                initial start finish +
              wholeRestartIcoViscousNegativeOneEuclideanPayment
                initial start finish +
            nu.coeff * wholeVorticityEuclideanMass
              (run initial finish).contact.physicalState) ∧
      (∀ endpoint : ComplexVorticityHilbertState,
        ¬ Tendsto
          (fun index => (run initial index).contact.physicalState)
          atTop (nhds endpoint)) ∧
      (∀ index : Nat,
        (run initial index).contact.physicalState =
          wholeRestartBlockTransportedInitialState initial 0 index +
            nativeAccumulationNonlinearDuhamelPrefix initial index) ∧
      Tendsto
        (nativeAccumulationNonlinearNegativeOneActionPrefix initial)
        atTop atTop ∧
      (nextRoot.generatedAtTemporalVisit firstVisit).occurrence =
        nativeTemporalEmitted physicalNext (.finite 0) ∧
      ((nextRoot.generatedAtTemporalVisit firstVisit).wholeLedgerWriteBack =
        nativeTemporalGeneratedLedgerEvolution physicalNext
          (nativeTemporalEmitted physicalNext (.finite 0))) ∧
      ∃ contactIndex : Nat → Nat,
        contactIndex 0 = 0 ∧
          StrictMono contactIndex ∧
          ∀ step : Nat,
            let radius := 2 * (contactIndex step + 1)
            let interval :=
              Finset.Ico (contactIndex step) (contactIndex (step + 1))
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
  have grounded :=
    sourceGeneratedNativeTemporalCofinalExactStrongFaceExit_grounded
      initial elapsedBounded
  dsimp only at grounded
  rcases grounded with
    ⟨_nextCurrent, actual, structural, _writeEq, strongFaceFails⟩
  have cofinalTraceEffect :
      ∃ contactIndex : Nat → Nat,
        contactIndex 0 = 0 ∧
          StrictMono contactIndex ∧
          ∀ step : Nat,
            let radius := 2 * (contactIndex step + 1)
            let interval :=
              Finset.Ico (contactIndex step) (contactIndex (step + 1))
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
    have cofinalTrace :=
      sourceGeneratedNativeAccumulationCofinalHighFrequencyProjectedParabolicTrace
        initial elapsedBounded
    dsimp only at cofinalTrace
    rcases cofinalTrace with
      ⟨_occurrenceEq, contactIndex, contactIndexZero,
        contactIndexStrictMono, blockTrace⟩
    refine
      ⟨contactIndex, contactIndexZero, contactIndexStrictMono, ?_⟩
    intro step
    exact (blockTrace step).2.2
  refine
    ⟨actual, structural,
      nativeTemporalCofinalAuthority_generates_write initial,
      nativeTemporalCofinalCausalAnswer_payload_eq_targetReadout initial,
      wholeRestartIcoNonlinearNegativeOneEuclideanPayment_balance initial,
      strongFaceFails, ?_,
      nativeAccumulationNonlinearNegativeOneActionPrefix_tendsto_atTop_of_elapsedTime_bddAbove
        initial elapsedBounded,
      rfl, rfl, cofinalTraceEffect⟩
  intro index
  exact
    run_contact_eq_transportedInitial_add_nativeAccumulationNonlinearDuhamelPrefix
      initial index

/-! ## Original-selector kinetic settlement of the moving cofinal shell -/

private def nativeAccumulationFiniteVelocityAnnularMass
    (smaller larger : Nat)
    (state : WholeRestartVelocityEndpointState) : Real :=
  ∑ wave ∈
      wholeRestartNonzeroModes larger \ wholeRestartNonzeroModes smaller,
    ‖state wave‖ ^ 2

private theorem nativeAccumulationKineticFiniteProjection_norm_sq
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartVelocityEndpointState) :
    ‖wholeRestartKineticFiniteProjection modes state‖ ^ 2 =
      ∑ wave ∈ modes, ‖state wave‖ ^ 2 := by
  classical
  unfold wholeRestartKineticFiniteProjection
  have normSum :=
    lp.norm_sum_single
      (p := (2 : ENNReal)) (by norm_num)
      (fun wave : NonzeroIntegerWavevector => state wave) modes
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at normSum
  exact normSum

private theorem nativeAccumulationFiniteVelocityAnnularMass_nonneg
    (smaller larger : Nat)
    (state : WholeRestartVelocityEndpointState) :
    0 ≤ nativeAccumulationFiniteVelocityAnnularMass smaller larger state := by
  unfold nativeAccumulationFiniteVelocityAnnularMass
  exact Finset.sum_nonneg fun wave _waveMem => sq_nonneg ‖state wave‖

private theorem
    nativeAccumulationKineticFiniteProjection_norm_sq_eq_add_annularMass
    {smaller larger : Nat}
    (radiusLe : smaller ≤ larger)
    (state : WholeRestartVelocityEndpointState) :
    ‖wholeRestartKineticFiniteProjection
        (wholeRestartNonzeroModes larger) state‖ ^ 2 =
      ‖wholeRestartKineticFiniteProjection
          (wholeRestartNonzeroModes smaller) state‖ ^ 2 +
        nativeAccumulationFiniteVelocityAnnularMass smaller larger state := by
  rw [nativeAccumulationKineticFiniteProjection_norm_sq,
    nativeAccumulationKineticFiniteProjection_norm_sq]
  unfold nativeAccumulationFiniteVelocityAnnularMass
  have split :=
    Finset.sum_sdiff
      (f := fun wave : NonzeroIntegerWavevector => ‖state wave‖ ^ 2)
      (wholeRestartNonzeroModes_mono radiusLe)
  calc
    (∑ wave ∈ wholeRestartNonzeroModes larger, ‖state wave‖ ^ 2) =
        (∑ wave ∈
            wholeRestartNonzeroModes larger \
              wholeRestartNonzeroModes smaller,
            ‖state wave‖ ^ 2) +
          ∑ wave ∈ wholeRestartNonzeroModes smaller,
            ‖state wave‖ ^ 2 := split.symm
    _ =
        (∑ wave ∈ wholeRestartNonzeroModes smaller,
            ‖state wave‖ ^ 2) +
          ∑ wave ∈
            wholeRestartNonzeroModes larger \
              wholeRestartNonzeroModes smaller,
            ‖state wave‖ ^ 2 := by ring

private theorem nativeAccumulationFiniteVelocityAnnularMass_range_eq_mass_sub
    (radii : Nat → Nat)
    (radiusStep : ∀ step, radii step ≤ radii (step + 1))
    (state : WholeRestartVelocityEndpointState) :
    ∀ length : Nat,
      (∑ step ∈ Finset.range length,
          nativeAccumulationFiniteVelocityAnnularMass
            (radii step) (radii (step + 1)) state) =
        ‖wholeRestartKineticFiniteProjection
            (wholeRestartNonzeroModes (radii length)) state‖ ^ 2 -
          ‖wholeRestartKineticFiniteProjection
            (wholeRestartNonzeroModes (radii 0)) state‖ ^ 2
  | 0 => by simp
  | length + 1 => by
      rw [Finset.sum_range_succ,
        nativeAccumulationFiniteVelocityAnnularMass_range_eq_mass_sub
          radii radiusStep state length]
      have split :=
        nativeAccumulationKineticFiniteProjection_norm_sq_eq_add_annularMass
          (radiusStep length) state
      linarith

private theorem nativeAccumulationFiniteVelocityAnnularMass_Ico_le_norm_sq
    (radii : Nat → Nat)
    (radiusStep : ∀ step, radii step ≤ radii (step + 1))
    (state : WholeRestartVelocityEndpointState)
    (start finish : Nat)
    (startLeFinish : start ≤ finish) :
    (∑ step ∈ Finset.Ico start finish,
        nativeAccumulationFiniteVelocityAnnularMass
          (radii step) (radii (step + 1)) state) ≤
      ‖state‖ ^ 2 := by
  have intervalEq :
      (∑ step ∈ Finset.Ico start finish,
          nativeAccumulationFiniteVelocityAnnularMass
            (radii step) (radii (step + 1)) state) =
        ‖wholeRestartKineticFiniteProjection
              (wholeRestartNonzeroModes (radii finish)) state‖ ^ 2 -
          ‖wholeRestartKineticFiniteProjection
              (wholeRestartNonzeroModes (radii start)) state‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sub _ startLeFinish,
      nativeAccumulationFiniteVelocityAnnularMass_range_eq_mass_sub
        radii radiusStep state finish,
      nativeAccumulationFiniteVelocityAnnularMass_range_eq_mass_sub
        radii radiusStep state start]
    ring
  have tailNonnegative :
      0 ≤
        ‖wholeRestartKineticFiniteTail
          (wholeRestartNonzeroModes (radii finish)) state‖ ^ 2 :=
    sq_nonneg _
  rw [wholeRestartKineticFiniteTail_norm_sq] at tailNonnegative
  have initialProjectionNonnegative :
      0 ≤
        ‖wholeRestartKineticFiniteProjection
          (wholeRestartNonzeroModes (radii start)) state‖ ^ 2 :=
    sq_nonneg _
  rw [intervalEq]
  linarith

private theorem nativeAccumulation_norm_sq_le_two_add_two_sub
    {E : Type*}
    [NormedAddCommGroup E]
    (left right : E) :
    ‖left‖ ^ 2 ≤ 2 * ‖right‖ ^ 2 + 2 * ‖left - right‖ ^ 2 := by
  have normLe : ‖left‖ ≤ ‖right‖ + ‖left - right‖ := by
    calc
      ‖left‖ = ‖right + (left - right)‖ := by
        congr 1
        abel
      _ ≤ ‖right‖ + ‖left - right‖ := norm_add_le _ _
  have squareLe :
      ‖left‖ ^ 2 ≤ (‖right‖ + ‖left - right‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 normLe
  calc
    ‖left‖ ^ 2 ≤ (‖right‖ + ‖left - right‖) ^ 2 := squareLe
    _ ≤ 2 * ‖right‖ ^ 2 + 2 * ‖left - right‖ ^ 2 := by
      nlinarith [sq_nonneg (‖right‖ - ‖left - right‖)]

private theorem nativeAccumulationKineticFiniteProjection_sub
    (modes : Finset NonzeroIntegerWavevector)
    (left right : WholeRestartVelocityEndpointState) :
    wholeRestartKineticFiniteProjection modes (left - right) =
      wholeRestartKineticFiniteProjection modes left -
        wholeRestartKineticFiniteProjection modes right := by
  classical
  unfold wholeRestartKineticFiniteProjection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro wave _waveMem
  rw [show (left - right) wave = left wave - right wave by rfl,
    lp.single_sub]

private theorem nativeAccumulationKineticFiniteProjection_norm_sq_le
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartVelocityEndpointState) :
    ‖wholeRestartKineticFiniteProjection modes state‖ ^ 2 ≤
      ‖state‖ ^ 2 := by
  have tailNonneg :
      0 ≤ ‖wholeRestartKineticFiniteTail modes state‖ ^ 2 :=
    sq_nonneg _
  rw [wholeRestartKineticFiniteTail_norm_sq] at tailNonneg
  linarith

private theorem
    nativeAccumulationFiniteVelocityAnnularMass_le_endpoint_add_error
    (smaller larger : Nat)
    (state endpoint : WholeRestartVelocityEndpointState) :
    nativeAccumulationFiniteVelocityAnnularMass smaller larger state ≤
      2 * nativeAccumulationFiniteVelocityAnnularMass
          smaller larger endpoint +
        2 * ‖state - endpoint‖ ^ 2 := by
  let modes :=
    wholeRestartNonzeroModes larger \ wholeRestartNonzeroModes smaller
  have projected := nativeAccumulation_norm_sq_le_two_add_two_sub
    (wholeRestartKineticFiniteProjection modes state)
    (wholeRestartKineticFiniteProjection modes endpoint)
  have differenceEq :
    wholeRestartKineticFiniteProjection modes state -
          wholeRestartKineticFiniteProjection modes endpoint =
        wholeRestartKineticFiniteProjection modes (state - endpoint) := by
    exact
      (nativeAccumulationKineticFiniteProjection_sub
        modes state endpoint).symm
  have differenceLe :=
    nativeAccumulationKineticFiniteProjection_norm_sq_le
      modes (state - endpoint)
  rw [differenceEq] at projected
  change
    nativeAccumulationFiniteVelocityAnnularMass smaller larger state ≤
      2 * nativeAccumulationFiniteVelocityAnnularMass
          smaller larger endpoint +
        2 * ‖state - endpoint‖ ^ 2
  unfold nativeAccumulationFiniteVelocityAnnularMass
  rw [← nativeAccumulationKineticFiniteProjection_norm_sq,
    ← nativeAccumulationKineticFiniteProjection_norm_sq]
  exact projected.trans (by gcongr)

private theorem
    nativeAccumulation_sum_nonzeroShell_eq_sum_wholeShell
    (smaller larger : Nat)
    (value : IntegerWavevector → Real) :
    (∑ wave ∈
        wholeRestartNonzeroModes larger \ wholeRestartNonzeroModes smaller,
      value wave.1) =
      ∑ wave ∈ wholeRestartModes larger \ wholeRestartModes smaller,
        value wave := by
  classical
  refine Finset.sum_bij (fun indexed _ => indexed.1) ?_ ?_ ?_ ?_
  · intro indexed indexedMem
    rw [Finset.mem_sdiff] at indexedMem ⊢
    exact
      ⟨(mem_wholeRestartNonzeroModes larger indexed).1 indexedMem.1,
        fun smallerMem => indexedMem.2
          ((mem_wholeRestartNonzeroModes smaller indexed).2 smallerMem)⟩
  · intro left leftMem right rightMem valueEq
    exact Subtype.ext valueEq
  · intro wave waveMem
    have waveLarger : wave ∈ wholeRestartModes larger :=
      (Finset.mem_sdiff.mp waveMem).1
    have waveNe : wave ≠ 0 := by
      rw [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
        Finset.mem_erase] at waveLarger
      exact waveLarger.1
    let indexed : NonzeroIntegerWavevector := ⟨wave, waveNe⟩
    refine ⟨indexed, ?_, rfl⟩
    rw [Finset.mem_sdiff]
    exact
      ⟨(mem_wholeRestartNonzeroModes larger indexed).2 waveLarger,
        fun smallerMem => (Finset.mem_sdiff.mp waveMem).2
          ((mem_wholeRestartNonzeroModes smaller indexed).1 smallerMem)⟩
  · intro indexed _indexedMem
    rfl

private theorem
    contactFiniteWeightedVorticityShell_eq_nativeAccumulationAnnularMass
    (initial : GeneratedWholeRestartCurrent nu)
    (index smaller larger : Nat) :
    (∑ wave ∈ wholeRestartModes larger \ wholeRestartModes smaller,
      complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState wave) /
        integerWaveViscousMultiplier wave) =
      nativeAccumulationFiniteVelocityAnnularMass smaller larger
        (wholeRestartContactVelocityState initial index) := by
  rw [← nativeAccumulation_sum_nonzeroShell_eq_sum_wholeShell]
  unfold nativeAccumulationFiniteVelocityAnnularMass
  apply Finset.sum_congr rfl
  intro wave _waveMem
  exact
    (puncturedWholeVelocityEuclideanCoefficient_norm_sq
      (run initial index).contact.physicalState
      (run initial index).contact.transverse wave).symm

private theorem
    wholeRestartContactVelocityState_tendsto_endpoint_of_kineticDefect_eq_zero
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (defectZero :
      wholeRestartKineticWeakEndpointDefect initial
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0) :
    let weak :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.endpointReceipt
    Tendsto
      (wholeRestartContactVelocityState initial)
      atTop (nhds weak.velocityEndpoint) := by
  dsimp only
  have trajectoryTendsto :=
    wholeRestartBoundedPreAccumulationVelocityTrajectory_tendsto_endpoint_of_kineticDefect_eq_zero
      initial elapsedBounded defectZero
  have contactTimeTendsto :=
    wholeRestartContactEndpointPreAccumulationTime_tendsto_atTop
      initial elapsedBounded
  have composed := trajectoryTendsto.comp contactTimeTendsto
  simpa only [Function.comp_def,
    wholeRestartBoundedPreAccumulationVelocityTrajectory_contactEndpoint] using
      composed

/-- If the generated kinetic endpoint has no missing kinetic mass, the
original high-frequency selector can be chosen without a second extraction:
every block still carries the exact projected strong-face responsibility,
while both literal endpoint inventories of its moving shell are summable.
The conclusion is stated in the original vorticity coordinates, not in an
auxiliary velocity-observer carrier. -/
theorem
    zeroKineticDefect_generates_originalCofinalMovingShellSettlement
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (defectZero :
      wholeRestartKineticWeakEndpointDefect initial
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0) :
    ∃ contactIndex : Nat → Nat,
      contactIndex 0 = 0 ∧
        StrictMono contactIndex ∧
        (∀ step : Nat,
          nu.coeff <
            ∑ index ∈ Finset.Ico
                (contactIndex step) (contactIndex (step + 1)),
              receiptHighFrequencyProjectedParabolicTrace
                (run initial index).nextContact.prefixReceipt
                (2 * (contactIndex step + 1))) ∧
        Summable (fun step =>
          ∑ wave ∈
              wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
                wholeRestartModes (2 * (contactIndex step + 1)),
            complexCoordinateAmplitudeSq
                ((run initial (contactIndex (step + 1))).contact.physicalState
                  wave) /
              integerWaveViscousMultiplier wave) ∧
        Summable (fun step =>
          ∑ wave ∈
              wholeRestartModes (2 * (contactIndex (step + 1) + 1)) \
                wholeRestartModes (2 * (contactIndex step + 1)),
            complexCoordinateAmplitudeSq
                ((run initial (contactIndex (step + 2))).contact.physicalState
                  wave) /
              integerWaveViscousMultiplier wave) := by
  let weak :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).family.endpointReceipt
  let endpoint := weak.velocityEndpoint
  let contactError : Nat → Real := fun index =>
    ‖wholeRestartContactVelocityState initial index - endpoint‖ ^ 2
  have contactTendsto :
      Tendsto (wholeRestartContactVelocityState initial) atTop
        (nhds endpoint) := by
    simpa only [endpoint, weak] using
      wholeRestartContactVelocityState_tendsto_endpoint_of_kineticDefect_eq_zero
        initial elapsedBounded defectZero
  have contactErrorTendsto : Tendsto contactError atTop (nhds 0) := by
    simpa only [contactError, sub_self, norm_zero,
      zero_pow (by norm_num : (2 : Nat) ≠ 0)] using
      (contactTendsto.sub_const endpoint).norm.pow 2
  have existsLater (step cursor : Nat) :
      ∃ later : Nat,
        cursor < later ∧
          restartPhysicalHighFrequencyTailMass
                initial cursor (2 * (cursor + 1)) + 1 <
            restartPhysicalHighFrequencyTailMass
              initial later (2 * (cursor + 1)) ∧
          contactError later < ((1 : Real) / 2) ^ step := by
    let currentMass :=
      restartPhysicalHighFrequencyTailMass
        initial cursor (2 * (cursor + 1))
    have tailEventually :
        ∀ᶠ index : Nat in atTop,
          currentMass + 2 ≤
            restartPhysicalHighFrequencyTailMass
              initial index (2 * (cursor + 1)) :=
      tendsto_atTop.1
        (tendsto_restartPhysicalHighFrequencyTailMass_atTop_of_elapsedTime_bddAbove
          initial elapsedBounded (2 * (cursor + 1)))
        (currentMass + 2)
    have errorEventually :
        ∀ᶠ index : Nat in atTop,
          contactError index < ((1 : Real) / 2) ^ step :=
      (tendsto_order.1 contactErrorTendsto).2
        (((1 : Real) / 2) ^ step) (by positivity)
    obtain ⟨threshold, thresholdSpec⟩ :=
      eventually_atTop.1 (tailEventually.and errorEventually)
    let later := max (cursor + 1) threshold
    have specifications :=
      thresholdSpec later (Nat.le_max_right _ _)
    refine ⟨later, ?_, ?_, specifications.2⟩
    · exact (Nat.lt_succ_self cursor).trans_le (Nat.le_max_left _ _)
    · dsimp only [currentMass] at specifications ⊢
      linarith
  let nextIndex : Nat → Nat → Nat := fun step cursor =>
    Nat.find (existsLater step cursor)
  have nextIndex_spec (step cursor : Nat) :
      cursor < nextIndex step cursor ∧
        restartPhysicalHighFrequencyTailMass
              initial cursor (2 * (cursor + 1)) + 1 <
          restartPhysicalHighFrequencyTailMass
            initial (nextIndex step cursor) (2 * (cursor + 1)) ∧
        contactError (nextIndex step cursor) <
          ((1 : Real) / 2) ^ step := by
    simpa only [nextIndex] using Nat.find_spec (existsLater step cursor)
  let contactIndex : Nat → Nat := fun step =>
    Nat.rec 0 (fun step cursor => nextIndex step cursor) step
  have contactIndex_zero : contactIndex 0 = 0 := rfl
  have contactIndex_succ (step : Nat) :
      contactIndex (step + 1) = nextIndex step (contactIndex step) := by
    simp only [contactIndex]
  have contactIndex_lt_succ (step : Nat) :
      contactIndex step < contactIndex (step + 1) := by
    rw [contactIndex_succ]
    exact (nextIndex_spec step (contactIndex step)).1
  have contactIndex_strictMono : StrictMono contactIndex :=
    strictMono_nat_of_lt_succ contactIndex_lt_succ
  have tailGap (step : Nat) :
      restartPhysicalHighFrequencyTailMass
            initial (contactIndex step) (2 * (contactIndex step + 1)) + 1 <
        restartPhysicalHighFrequencyTailMass
          initial (contactIndex (step + 1))
            (2 * (contactIndex step + 1)) := by
    rw [contactIndex_succ]
    exact (nextIndex_spec step (contactIndex step)).2.1
  have errorAtSucc (step : Nat) :
      contactError (contactIndex (step + 1)) ≤
        ((1 : Real) / 2) ^ step := by
    rw [contactIndex_succ]
    exact (nextIndex_spec step (contactIndex step)).2.2.le
  have tracePositive (step : Nat) :
      nu.coeff <
        ∑ index ∈ Finset.Ico
            (contactIndex step) (contactIndex (step + 1)),
          receiptHighFrequencyProjectedParabolicTrace
            (run initial index).nextContact.prefixReceipt
            (2 * (contactIndex step + 1)) := by
    rw [wholeRestartIcoHighFrequencyProjectedParabolicTrace_telescope
      initial (2 * (contactIndex step + 1))
      (contactIndex step) (contactIndex (step + 1))
      (contactIndex_lt_succ step).le]
    nlinarith [nu.coeff_pos, tailGap step]
  let radius : Nat → Nat := fun step => 2 * (contactIndex step + 1)
  have radiusStep : ∀ step, radius step ≤ radius (step + 1) := by
    intro step
    dsimp only [radius]
    exact Nat.mul_le_mul_left 2
      (Nat.add_le_add_right (contactIndex_lt_succ step).le 1)
  have endpointAnnularSummable : Summable fun step =>
      nativeAccumulationFiniteVelocityAnnularMass
        (radius step) (radius (step + 1)) endpoint := by
    apply summable_of_sum_range_le
    · intro step
      exact nativeAccumulationFiniteVelocityAnnularMass_nonneg _ _ _
    · intro length
      simpa only [Nat.Ico_zero_eq_range] using
        nativeAccumulationFiniteVelocityAnnularMass_Ico_le_norm_sq
          radius radiusStep endpoint 0 length (Nat.zero_le length)
  have geometricSummable : Summable fun step : Nat => ((1 : Real) / 2) ^ step :=
    summable_geometric_two
  have startPointwise (step : Nat) :
      nativeAccumulationFiniteVelocityAnnularMass
          (radius step) (radius (step + 1))
          (wholeRestartContactVelocityState
            initial (contactIndex (step + 1))) ≤
        2 * nativeAccumulationFiniteVelocityAnnularMass
            (radius step) (radius (step + 1)) endpoint +
          2 * ((1 : Real) / 2) ^ step := by
    have annularBound :=
      nativeAccumulationFiniteVelocityAnnularMass_le_endpoint_add_error
        (radius step) (radius (step + 1))
        (wholeRestartContactVelocityState
          initial (contactIndex (step + 1))) endpoint
    have errorBound := errorAtSucc step
    dsimp only [contactError] at errorBound
    linarith
  have geometricSuccLe (step : Nat) :
      ((1 : Real) / 2) ^ (step + 1) ≤ ((1 : Real) / 2) ^ step := by
    rw [pow_succ]
    have nonnegative : 0 ≤ ((1 : Real) / 2) ^ step := by positivity
    nlinarith
  have terminalPointwise (step : Nat) :
      nativeAccumulationFiniteVelocityAnnularMass
          (radius step) (radius (step + 1))
          (wholeRestartContactVelocityState
            initial (contactIndex (step + 2))) ≤
        2 * nativeAccumulationFiniteVelocityAnnularMass
            (radius step) (radius (step + 1)) endpoint +
          2 * ((1 : Real) / 2) ^ step := by
    have annularBound :=
      nativeAccumulationFiniteVelocityAnnularMass_le_endpoint_add_error
        (radius step) (radius (step + 1))
        (wholeRestartContactVelocityState
          initial (contactIndex (step + 2))) endpoint
    have errorBound := errorAtSucc (step + 1)
    dsimp only [contactError] at errorBound
    linarith [geometricSuccLe step]
  have upperSummable : Summable fun step =>
      2 * nativeAccumulationFiniteVelocityAnnularMass
          (radius step) (radius (step + 1)) endpoint +
        2 * ((1 : Real) / 2) ^ step :=
    (endpointAnnularSummable.mul_left 2).add
      (geometricSummable.mul_left 2)
  have startSummable : Summable fun step =>
      nativeAccumulationFiniteVelocityAnnularMass
        (radius step) (radius (step + 1))
        (wholeRestartContactVelocityState
          initial (contactIndex (step + 1))) :=
    upperSummable.of_nonneg_of_le
      (fun step => nativeAccumulationFiniteVelocityAnnularMass_nonneg _ _ _)
      startPointwise
  have terminalSummable : Summable fun step =>
      nativeAccumulationFiniteVelocityAnnularMass
        (radius step) (radius (step + 1))
        (wholeRestartContactVelocityState
          initial (contactIndex (step + 2))) :=
    upperSummable.of_nonneg_of_le
      (fun step => nativeAccumulationFiniteVelocityAnnularMass_nonneg _ _ _)
      terminalPointwise
  refine
    ⟨contactIndex, contactIndex_zero, contactIndex_strictMono,
      tracePositive, ?_, ?_⟩
  · apply startSummable.congr
    intro step
    exact
      (contactFiniteWeightedVorticityShell_eq_nativeAccumulationAnnularMass
        initial (contactIndex (step + 1))
        (radius step) (radius (step + 1))).symm
  · apply terminalSummable.congr
    intro step
    exact
      (contactFiniteWeightedVorticityShell_eq_nativeAccumulationAnnularMass
        initial (contactIndex (step + 2))
        (radius step) (radius (step + 1))).symm

/-- The generated kinetic receipt is consumed without a caller-selected
branch.  A positive defect remains the exact whole-carrier residual of the
original source.  In the zero-defect branch, the identical original selector
retains every projected strong-face block and the same moving whole-PDE
telescope pays both endpoint inventories, the normalized viscous debit, and
the normalized signed pair transfer.  No completed-future lineage or revised
law is introduced. -/
theorem
    sourceGeneratedNativeAccumulationCofinalKineticResidual_or_movingShellSettlement
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let receipt := generatedWholeRestartKineticWeakEndpoint initial
    (0 < wholeRestartKineticWeakEndpointDefect initial receipt.endpoint ∧
      ∀ᶠ index : Nat in atTop,
        wholeRestartKineticWeakEndpointDefect initial receipt.endpoint / 2 <
          ‖wholeRestartKineticEndpointResidual initial receipt index‖ ^ 2) ∨
      ∃ contactIndex : Nat → Nat,
        contactIndex 0 = 0 ∧
          StrictMono contactIndex ∧
          let radius : Nat → Nat := fun step =>
            2 * (contactIndex step + 1)
          let shell : Nat → Finset IntegerWavevector := fun step =>
            wholeRestartModes (radius (step + 1)) \
              wholeRestartModes (radius step)
          let startWeighted : Nat → Real := fun step =>
            ∑ wave ∈ shell step,
              complexCoordinateAmplitudeSq
                  ((run initial (contactIndex (step + 1))).contact.physicalState
                    wave) /
                integerWaveViscousMultiplier wave
          let terminalWeighted : Nat → Real := fun step =>
            ∑ wave ∈ shell step,
              complexCoordinateAmplitudeSq
                  ((run initial (contactIndex (step + 2))).contact.physicalState
                    wave) /
                integerWaveViscousMultiplier wave
          let normalizedViscous : Nat → Real := fun step =>
            (∑ index ∈ Finset.Ico
                (contactIndex (step + 1)) (contactIndex (step + 2)),
              actualWholeFiniteViscousPayment
                (run initial index).nextContact.prefixReceipt (shell step)) /
              ((2 * Real.pi) ^ 2 *
                (3 * ((radius (step + 1) : Nat) : Real) ^ 2))
          let normalizedPair : Nat → Real := fun step =>
            |∑ index ∈ Finset.Ico
                (contactIndex (step + 1)) (contactIndex (step + 2)),
              actualWholeFinitePairOccurrenceWork
                (run initial index).nextContact.prefixReceipt (shell step)| /
              ((2 * Real.pi) ^ 2 *
                (3 * ((radius (step + 1) : Nat) : Real) ^ 2))
          (∀ step : Nat,
            nu.coeff <
              ∑ index ∈ Finset.Ico
                  (contactIndex step) (contactIndex (step + 1)),
                receiptHighFrequencyProjectedParabolicTrace
                  (run initial index).nextContact.prefixReceipt
                  (radius step)) ∧
            Summable startWeighted ∧
            Summable terminalWeighted ∧
            Summable normalizedViscous ∧
            Summable normalizedPair := by
  dsimp only
  let receipt := generatedWholeRestartKineticWeakEndpoint initial
  rcases receipt.defect_disposition with defectPositive | zeroDisposition
  · left
    refine ⟨defectPositive, ?_⟩
    exact
      wholeRestartKineticEndpointResidual_eventually_gt_half_defect
        receipt defectPositive
  · right
    have defectZero :
        wholeRestartKineticWeakEndpointDefect initial
          (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
            initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
          0 := by
      change
        wholeRestartKineticWeakEndpointDefect initial
          (generatedWholeRestartKineticWeakEndpoint initial).endpoint = 0
      exact zeroDisposition.1
    obtain ⟨contactIndex, contactIndexZero, contactIndexStrictMono,
        tracePositive, startSummable, terminalSummable⟩ :=
      zeroKineticDefect_generates_originalCofinalMovingShellSettlement
        initial elapsedBounded defectZero
    refine
      ⟨contactIndex, contactIndexZero, contactIndexStrictMono, ?_⟩
    let radius : Nat → Nat := fun step =>
      2 * (contactIndex step + 1)
    let shell : Nat → Finset IntegerWavevector := fun step =>
      wholeRestartModes (radius (step + 1)) \
        wholeRestartModes (radius step)
    let startWeighted : Nat → Real := fun step =>
      ∑ wave ∈ shell step,
        complexCoordinateAmplitudeSq
            ((run initial (contactIndex (step + 1))).contact.physicalState wave) /
          integerWaveViscousMultiplier wave
    let terminalWeighted : Nat → Real := fun step =>
      ∑ wave ∈ shell step,
        complexCoordinateAmplitudeSq
            ((run initial (contactIndex (step + 2))).contact.physicalState wave) /
          integerWaveViscousMultiplier wave
    let normalizedViscous : Nat → Real := fun step =>
      (∑ index ∈ Finset.Ico
          (contactIndex (step + 1)) (contactIndex (step + 2)),
        actualWholeFiniteViscousPayment
          (run initial index).nextContact.prefixReceipt (shell step)) /
        ((2 * Real.pi) ^ 2 *
          (3 * ((radius (step + 1) : Nat) : Real) ^ 2))
    let normalizedPair : Nat → Real := fun step =>
      |∑ index ∈ Finset.Ico
          (contactIndex (step + 1)) (contactIndex (step + 2)),
        actualWholeFinitePairOccurrenceWork
          (run initial index).nextContact.prefixReceipt (shell step)| /
        ((2 * Real.pi) ^ 2 *
          (3 * ((radius (step + 1) : Nat) : Real) ^ 2))
    have startSummable' : Summable startWeighted := by
      simpa only [startWeighted, shell, radius] using startSummable
    have terminalSummable' : Summable terminalWeighted := by
      simpa only [terminalWeighted, shell, radius] using terminalSummable
    have normalizedViscousSummable : Summable normalizedViscous := by
      simpa only [normalizedViscous, shell, radius] using
        summable_nativeAccumulationCofinalMovingNormalizedViscousBlock
          initial contactIndex contactIndexStrictMono
    have normalizedPairLe (step : Nat) :
        normalizedPair step ≤
          terminalWeighted step + startWeighted step +
            normalizedViscous step := by
      have connector :=
        nativeAccumulationCofinalMovingPairTotal_abs_div_cubeWeight_le_weightedEndpoints
          initial contactIndex contactIndexStrictMono step
      dsimp only at connector
      simpa only [normalizedPair, normalizedViscous, terminalWeighted,
        startWeighted, shell, radius] using connector
    have normalizedPairNonneg (step : Nat) : 0 ≤ normalizedPair step := by
      unfold normalizedPair
      exact div_nonneg (abs_nonneg _) (by positivity)
    have normalizedPairSummable : Summable normalizedPair :=
      ((terminalSummable'.add startSummable').add
        normalizedViscousSummable).of_nonneg_of_le
          normalizedPairNonneg normalizedPairLe
    refine ⟨?_, startSummable', terminalSummable',
      normalizedViscousSummable, normalizedPairSummable⟩
    simpa only [radius] using tracePositive

private def finiteInputAutonomousWorkDensity
    (nu : Viscosity)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : Real :=
  2 * nu.coeff *
    ∑ wave ∈ modes,
      complexCoordinateRealInner
        (complexSharpSupportProjection modes state wave)
        (wholeStateVorticityNonlinearCoefficientAt
          (complexSharpSupportProjection modes state) wave)

private def finiteInputProjectionErrorDensity
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : Real :=
  ∑ wave ∈ modes,
    (integerWaveViscousMultiplier wave)⁻¹ *
      complexCoordinateAmplitudeSq
        (wholeStateVorticityNonlinearCoefficientAt state wave -
          wholeStateVorticityNonlinearCoefficientAt
            (complexSharpSupportProjection modes state) wave)

private def finiteInputRateDensity
    (nu : Viscosity)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : Real :=
  finiteInputAutonomousWorkDensity nu modes state -
    nu.coeff ^ 2 *
      ∑ wave ∈ modes,
        integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq (state wave)

private theorem finiteInputProjectionErrorDensity_le_differenceMass
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (radius : Nat) :
    finiteInputProjectionErrorDensity
        (integerWaveFrequencyCube radius) state ≤
      3 * wholeStateVorticityNonlinearDifferenceNegativeOneMass
        (complexSharpSupportProjection
          (integerWaveFrequencyCube radius) state)
        state := by
  let modes := integerWaveFrequencyCube radius
  let projected := complexSharpSupportProjection modes state
  have projectedTransverse : WholeStateTransverse projected :=
    wholeStateTransverse_sharpSupportProjection
      modes state stateTransverse
  have projectedGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (projected wave) :=
    summable_wholeStateVorticityGradientDensity_of_supported
      modes projected
      (complexSharpSupportProjection_supported modes state)
  have differenceGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((projected - state) wave) :=
    summable_wholeStateVorticityGradientDensity_sub
      projected state projectedGradientSummable gradientSummable
  have differenceSummable :=
    summable_wholeStateVorticityNonlinearDifferenceNegativeOneDensity
      projected state projectedTransverse stateTransverse
      projectedGradientSummable gradientSummable
      differenceGradientSummable
  have pointwise (wave : IntegerWavevector) :
      (integerWaveViscousMultiplier wave)⁻¹ *
          complexCoordinateAmplitudeSq
            (wholeStateVorticityNonlinearCoefficientAt state wave -
              wholeStateVorticityNonlinearCoefficientAt projected wave) ≤
        3 * wholeStateVorticityNonlinearDifferenceNegativeOneDensity
          projected state wave := by
    by_cases waveZero : wave = 0
    · subst wave
      simp [wholeStateVorticityNonlinearDifferenceNegativeOneDensity,
        integerWaveViscousMultiplier, integerWaveNormSq]
    · have amplitudeLe :=
        complexCoordinateAmplitudeSq_le_three_mul_norm_sq
          (wholeStateVorticityNonlinearCoefficientAt state wave -
            wholeStateVorticityNonlinearCoefficientAt projected wave)
      have inverseNonneg :
          0 ≤ (integerWaveViscousMultiplier wave)⁻¹ := by
        exact inv_nonneg.mpr (mul_nonneg (sq_nonneg _)
          (integerWaveNormSq_nonneg wave))
      have weighted := mul_le_mul_of_nonneg_left amplitudeLe inverseNonneg
      unfold wholeStateVorticityNonlinearDifferenceNegativeOneDensity
      rw [if_neg waveZero, div_eq_mul_inv]
      have normEq :
          ‖wholeStateVorticityNonlinearCoefficientAt state wave -
              wholeStateVorticityNonlinearCoefficientAt projected wave‖ ^ 2 =
            ‖wholeStateVorticityNonlinearCoefficientAt projected wave -
              wholeStateVorticityNonlinearCoefficientAt state wave‖ ^ 2 := by
        rw [show wholeStateVorticityNonlinearCoefficientAt state wave -
              wholeStateVorticityNonlinearCoefficientAt projected wave =
            -(wholeStateVorticityNonlinearCoefficientAt projected wave -
              wholeStateVorticityNonlinearCoefficientAt state wave) by abel,
          norm_neg]
      rw [normEq] at weighted
      nlinarith
  unfold finiteInputProjectionErrorDensity
  change
    (∑ wave ∈ modes,
      (integerWaveViscousMultiplier wave)⁻¹ *
        complexCoordinateAmplitudeSq
          (wholeStateVorticityNonlinearCoefficientAt state wave -
            wholeStateVorticityNonlinearCoefficientAt projected wave)) ≤ _
  calc
    _ ≤ ∑ wave ∈ modes,
        3 * wholeStateVorticityNonlinearDifferenceNegativeOneDensity
          projected state wave := by
      exact Finset.sum_le_sum fun wave _ => pointwise wave
    _ ≤ ∑' wave : IntegerWavevector,
        3 * wholeStateVorticityNonlinearDifferenceNegativeOneDensity
          projected state wave := by
      exact (differenceSummable.mul_left 3).sum_le_tsum modes
        (fun wave _ => mul_nonneg (by norm_num)
          (wholeStateVorticityNonlinearDifferenceNegativeOneDensity_nonneg
            projected state wave))
    _ = 3 * wholeStateVorticityNonlinearDifferenceNegativeOneMass
        projected state := by
      rw [tsum_mul_left]
      rfl

private theorem finiteInputProjectionErrorDensity_le_agmon
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (radius : Nat)
    (radiusPos : 0 < radius) :
    finiteInputProjectionErrorDensity
        (integerWaveFrequencyCube radius) state ≤
      2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
        wholeVorticityEuclideanMass state *
        wholeStateVorticityGradientMass state := by
  have finiteLe := finiteInputProjectionErrorDensity_le_differenceMass
    state stateTransverse gradientSummable radius
  have agmon :=
    wholeStateVorticityNonlinearDifferenceNegativeOneMass_projection_le_agmon
      state stateTransverse gradientSummable radius radiusPos
  nlinarith [mul_le_mul_of_nonneg_left agmon (by norm_num : (0 : Real) ≤ 3)]

private theorem receipt_finiteInputAutonomousWorkDensity_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    Continuous fun time =>
      finiteInputAutonomousWorkDensity nu modes (receipt.wholePath time) := by
  let projectedPath :
      Icc (0 : Real) requestedTime → ComplexVorticityHilbertState :=
    fun time => complexSharpSupportProjection modes (receipt.wholePath time)
  have projectedPathContinuous : Continuous projectedPath := by
    rw [show projectedPath =
        (sharpSupportProjectionCLM modes) ∘ receipt.wholePath by
      funext time
      exact (sharpSupportProjectionCLM_apply
        modes (receipt.wholePath time)).symm]
    exact (sharpSupportProjectionCLM modes).continuous.comp
      receipt.wholePath.continuous
  have projectedPathTransverse :
      ∀ time, WholeStateTransverse (projectedPath time) := by
    intro time
    exact wholeStateTransverse_sharpSupportProjection
      modes (receipt.wholePath time) (wholePath_transverse receipt time)
  let projectedTransversePath :
      Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
    fun time => ⟨projectedPath time, projectedPathTransverse time⟩
  have projectedTransversePathContinuous :
      Continuous projectedTransversePath :=
    projectedPathContinuous.subtype_mk projectedPathTransverse
  unfold finiteInputAutonomousWorkDensity
  apply continuous_const.mul
  apply continuous_finsetSum
  intro wave _waveMem
  have stateRowContinuous :
      Continuous fun time => projectedPath time wave :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp projectedPathContinuous
  have nonlinearRowContinuous :
      Continuous fun time =>
        wholeStateVorticityNonlinearCoefficientAt
          (projectedPath time) wave := by
    have rowContinuous :
        Continuous fun time =>
          wholeStateVorticityNonlinearCoefficientAt
            (projectedTransversePath time).1 wave :=
      (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
        projectedTransversePathContinuous
    simpa only [projectedTransversePath] using rowContinuous
  exact complexCoordinateRealInner_prod_continuous.comp
    (stateRowContinuous.prodMk nonlinearRowContinuous)

private theorem receipt_finiteInputProjectionErrorDensity_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    Continuous fun time =>
      finiteInputProjectionErrorDensity modes (receipt.wholePath time) := by
  let projectedPath :
      Icc (0 : Real) requestedTime → ComplexVorticityHilbertState :=
    fun time => complexSharpSupportProjection modes (receipt.wholePath time)
  have projectedPathContinuous : Continuous projectedPath := by
    rw [show projectedPath =
        (sharpSupportProjectionCLM modes) ∘ receipt.wholePath by
      funext time
      exact (sharpSupportProjectionCLM_apply
        modes (receipt.wholePath time)).symm]
    exact (sharpSupportProjectionCLM modes).continuous.comp
      receipt.wholePath.continuous
  have projectedPathTransverse :
      ∀ time, WholeStateTransverse (projectedPath time) := by
    intro time
    exact wholeStateTransverse_sharpSupportProjection
      modes (receipt.wholePath time) (wholePath_transverse receipt time)
  let wholeTransversePath :
      Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
    fun time => ⟨receipt.wholePath time, wholePath_transverse receipt time⟩
  let projectedTransversePath :
      Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
    fun time => ⟨projectedPath time, projectedPathTransverse time⟩
  have wholeTransversePathContinuous : Continuous wholeTransversePath :=
    receipt.wholePath.continuous.subtype_mk (wholePath_transverse receipt)
  have projectedTransversePathContinuous :
      Continuous projectedTransversePath :=
    projectedPathContinuous.subtype_mk projectedPathTransverse
  unfold finiteInputProjectionErrorDensity
  apply continuous_finsetSum
  intro wave _waveMem
  have fullRowContinuous :
      Continuous fun time =>
        wholeStateVorticityNonlinearCoefficientAt
          (receipt.wholePath time) wave := by
    have rowContinuous :
        Continuous fun time =>
          wholeStateVorticityNonlinearCoefficientAt
            (wholeTransversePath time).1 wave :=
      (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
        wholeTransversePathContinuous
    simpa only [wholeTransversePath] using rowContinuous
  have projectedRowContinuous :
      Continuous fun time =>
        wholeStateVorticityNonlinearCoefficientAt
          (projectedPath time) wave := by
    have rowContinuous :
        Continuous fun time =>
          wholeStateVorticityNonlinearCoefficientAt
            (projectedTransversePath time).1 wave :=
      (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
        projectedTransversePathContinuous
    simpa only [projectedTransversePath] using rowContinuous
  exact continuous_const.mul
    (complexCoordinateAmplitudeSq_continuous.comp
      (fullRowContinuous.sub projectedRowContinuous))

private theorem receiptFiniteInputWorkEnergy
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime ceiling : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat)
    (radiusPos : 0 < radius)
    (ceilingNonneg : 0 ≤ ceiling)
    (massBound :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling) :
    let modes := integerWaveFrequencyCube radius
    let errorFactor :=
      (4368 * biotSavartSerrinConstant * ceiling * (radius : Real)⁻¹) /
        (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
    ∃ energy : Real,
      0 ≤ energy ∧
      energy + nu.coeff *
          (wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
            wholeVorticityEuclideanMass initialState) ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          (ceiling ^ 3 * requestedTime) ∧
      nu.coeff *
          (finiteStateVorticityCoefficientEnstrophy modes
              (receipt.wholePath
                ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
            finiteStateVorticityCoefficientEnstrophy modes initialState) ≤
        ∫ time,
          (finiteInputRateDensity nu modes
              (receipt.wholePath time) +
            finiteInputProjectionErrorDensity modes
              (receipt.wholePath time))
          ∂(commonTimeMeasure requestedTime) ∧
      (∫ time,
          finiteInputProjectionErrorDensity modes (receipt.wholePath time)
          ∂(commonTimeMeasure requestedTime)) ≤
        errorFactor * energy := by
  dsimp only
  let modes := integerWaveFrequencyCube radius
  let viscousConstant := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let errorFactor :=
    (4368 * biotSavartSerrinConstant * ceiling * (radius : Real)⁻¹) /
      viscousConstant
  let energy :=
    puncturedEuclideanSpaceTimeSquare receipt.wholeTangent +
      (1 / 2 : Real) *
        puncturedEuclideanSpaceTimeSquare
          (receiptViscousNegativeOneState receipt)
  have energyNonneg : 0 ≤ energy := by
    dsimp only [energy]
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have signed :=
    receipt_tangentHalfViscousSquare_add_boundary_le_cubicTime
      receipt massBound
  have settlement :=
    viscosity_mul_actualWholeFiniteNetWork_le_finiteInputNonlinearWork_add_projectionError
      receipt modes
  have workSettlement :
      nu.coeff *
          (finiteStateVorticityCoefficientEnstrophy modes
              (receipt.wholePath
                ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
            finiteStateVorticityCoefficientEnstrophy modes initialState) +
          (nu.coeff / 2) *
            actualWholeFiniteViscousPayment receipt modes ≤
        ∫ time,
          (finiteInputAutonomousWorkDensity nu modes
              (receipt.wholePath time) +
            finiteInputProjectionErrorDensity modes
              (receipt.wholePath time))
          ∂(commonTimeMeasure requestedTime) := by
    rw [actualWholeFiniteNetWork_eq_terminal_sub_initial] at settlement
    simpa only [finiteInputAutonomousWorkDensity,
      finiteInputProjectionErrorDensity, modes] using settlement
  let viscousDensity : Icc (0 : Real) requestedTime → Real := fun time =>
    nu.coeff ^ 2 *
      ∑ wave ∈ modes,
        integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq (receipt.wholePath time wave)
  have autonomousIntegrable :
      Integrable
        (fun time =>
          finiteInputAutonomousWorkDensity nu modes (receipt.wholePath time))
        (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (receipt_finiteInputAutonomousWorkDensity_continuous
          receipt modes).continuousOn)
  have viscousDensityContinuous : Continuous viscousDensity := by
    unfold viscousDensity
    apply continuous_const.mul
    apply continuous_finsetSum
    intro wave _waveMem
    exact continuous_const.mul
      (complexCoordinateAmplitudeSq_continuous.comp
        ((lp.evalCLM ℂ
          (fun _ : IntegerWavevector => ComplexCoordinateVector)
          2 wave).continuous.comp receipt.wholePath.continuous))
  have viscousDensityIntegrable :
      Integrable viscousDensity (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        viscousDensityContinuous.continuousOn)
  have halfViscousEq :
      (nu.coeff / 2) * actualWholeFiniteViscousPayment receipt modes =
        ∫ time, viscousDensity time ∂(commonTimeMeasure requestedTime) := by
    unfold actualWholeFiniteViscousPayment
    calc
      (nu.coeff / 2) *
          (∑ wave ∈ modes, actualWholeRowViscousPayment receipt wave) =
          (nu.coeff / 2) *
            ∑ wave ∈ modes,
              ∫ time, receiptRowViscousPower receipt wave time
                ∂(commonTimeMeasure requestedTime) := by
        apply congrArg ((nu.coeff / 2) * ·)
        apply Finset.sum_congr rfl
        intro wave _waveMem
        exact actualWholeRowViscousPayment_eq_commonTimeIntegral receipt wave
      _ = (nu.coeff / 2) *
          ∫ time,
            ∑ wave ∈ modes, receiptRowViscousPower receipt wave time
            ∂(commonTimeMeasure requestedTime) := by
        congr 1
        rw [integral_finsetSum]
        intro wave _waveMem
        exact receiptRowViscousPower_integrable receipt wave
      _ = ∫ time, viscousDensity time
          ∂(commonTimeMeasure requestedTime) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with time
        unfold viscousDensity receiptRowViscousPower
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro wave _waveMem
        ring
  have rateErrorIntegrable :
      Integrable
        (fun time =>
          finiteInputRateDensity nu modes (receipt.wholePath time) +
            finiteInputProjectionErrorDensity modes (receipt.wholePath time))
        (commonTimeMeasure requestedTime) := by
    have rateIntegrable :
        Integrable
          (fun time =>
            finiteInputRateDensity nu modes (receipt.wholePath time))
          (commonTimeMeasure requestedTime) := by
      have core := autonomousIntegrable.sub viscousDensityIntegrable
      convert core using 1
      funext time
      rfl
    have localErrorIntegrable :
        Integrable
          (fun time =>
            finiteInputProjectionErrorDensity modes (receipt.wholePath time))
          (commonTimeMeasure requestedTime) := by
      simpa only [MeasureTheory.integrableOn_univ] using
        (ContinuousOn.integrableOn_compact isCompact_univ
          (receipt_finiteInputProjectionErrorDensity_continuous
            receipt modes).continuousOn)
    exact rateIntegrable.add localErrorIntegrable
  have rateSplit :
      (∫ time,
          finiteInputAutonomousWorkDensity nu modes (receipt.wholePath time) +
            finiteInputProjectionErrorDensity modes (receipt.wholePath time)
          ∂(commonTimeMeasure requestedTime)) =
        (∫ time,
          finiteInputRateDensity nu modes (receipt.wholePath time) +
            finiteInputProjectionErrorDensity modes (receipt.wholePath time)
          ∂(commonTimeMeasure requestedTime)) +
        ∫ time, viscousDensity time
          ∂(commonTimeMeasure requestedTime) := by
    rw [← integral_add rateErrorIntegrable viscousDensityIntegrable]
    apply integral_congr_ae
    filter_upwards [] with time
    unfold finiteInputRateDensity viscousDensity
    ring
  have rateSettlement :
      nu.coeff *
          (finiteStateVorticityCoefficientEnstrophy modes
              (receipt.wholePath
                ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
            finiteStateVorticityCoefficientEnstrophy modes initialState) ≤
        ∫ time,
          (finiteInputRateDensity nu modes (receipt.wholePath time) +
            finiteInputProjectionErrorDensity modes (receipt.wholePath time))
          ∂(commonTimeMeasure requestedTime) := by
    rw [rateSplit, ← halfViscousEq] at workSettlement
    linarith
  have errorIntegrable :
      Integrable
        (fun time =>
          finiteInputProjectionErrorDensity modes (receipt.wholePath time))
        (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (receipt_finiteInputProjectionErrorDensity_continuous
          receipt modes).continuousOn)
  have viscousConstantPos : 0 < viscousConstant := by
    dsimp only [viscousConstant]
    exact mul_pos (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
  have mappedViscousSquareIntegrable :
      Integrable
        (fun time =>
          ‖puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState receipt) time‖ ^ 2)
        (commonTimeMeasure requestedTime) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (MeasureTheory.Lp.memLp
        (puncturedEuclideanSpaceTimeState
          (receiptViscousNegativeOneState receipt))).integrable_norm_rpow
        (by norm_num) (by norm_num)
  have weightedGradientIntegrable :
      Integrable
        (fun time => viscousConstant *
          wholeStateVorticityGradientMass (receipt.wholePath time))
        (commonTimeMeasure requestedTime) := by
    apply mappedViscousSquareIntegrable.congr
    filter_upwards [
      receiptViscousNegativeOneEuclideanMass_ae_eq_gradient receipt] with
        time pointEq
    simpa only [viscousConstant] using pointEq
  have gradientIntegrable :
      Integrable
        (fun time =>
          wholeStateVorticityGradientMass (receipt.wholePath time))
        (commonTimeMeasure requestedTime) := by
    have scaled := weightedGradientIntegrable.const_mul viscousConstant⁻¹
    apply scaled.congr
    filter_upwards [] with time
    field_simp [viscousConstantPos.ne']
  have scaledGradientIntegrable :
      Integrable
        (fun time =>
          2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
            ceiling *
              wholeStateVorticityGradientMass (receipt.wholePath time))
        (commonTimeMeasure requestedTime) := by
    exact gradientIntegrable.const_mul
      (2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ * ceiling)
  have errorPointwise :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        finiteInputProjectionErrorDensity modes (receipt.wholePath time) ≤
          2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
            ceiling *
              wholeStateVorticityGradientMass (receipt.wholePath time) := by
    filter_upwards [
      receiptPointwiseGradient_ae_summable receipt,
      receiptStateLimit_eq_wholePath_ae receipt,
      massBound] with time gradientSummable stateEq massLe
    have pathGradientSummable :
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (receipt.wholePath time wave) := by
      simpa only [stateEq] using gradientSummable
    have agmon :=
      finiteInputProjectionErrorDensity_le_agmon
        (receipt.wholePath time) (wholePath_transverse receipt time)
        pathGradientSummable radius radiusPos
    have coefficientNonneg :
        0 ≤ 2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        (inv_nonneg.mpr (Nat.cast_nonneg radius))
    exact agmon.trans (by
      calc
        2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
              wholeVorticityEuclideanMass (receipt.wholePath time) *
              wholeStateVorticityGradientMass (receipt.wholePath time) ≤
            2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
              ceiling *
              wholeStateVorticityGradientMass (receipt.wholePath time) := by
          gcongr
          unfold wholeStateVorticityGradientMass
          exact tsum_nonneg fun wave =>
            mul_nonneg (integerWaveNormSq_nonneg wave)
              (complexCoordinateAmplitudeSq_nonneg _)
        _ = _ := by ring)
  have errorIntegralLe :
      (∫ time,
          finiteInputProjectionErrorDensity modes (receipt.wholePath time)
          ∂(commonTimeMeasure requestedTime)) ≤
        2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
          ceiling *
          ∫ time,
            wholeStateVorticityGradientMass (receipt.wholePath time)
            ∂(commonTimeMeasure requestedTime) := by
    calc
      _ ≤ ∫ time,
          2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
            ceiling *
              wholeStateVorticityGradientMass (receipt.wholePath time)
          ∂(commonTimeMeasure requestedTime) :=
        integral_mono_ae errorIntegrable scaledGradientIntegrable
          errorPointwise
      _ = _ := by rw [integral_const_mul]
  have halfGradientLeEnergy :
      (viscousConstant / 2) *
          (∫ time,
            wholeStateVorticityGradientMass (receipt.wholePath time)
            ∂(commonTimeMeasure requestedTime)) ≤
        energy := by
    have viscousEq :=
      receiptViscousNegativeOneEuclideanSquare_eq_gradient receipt
    dsimp only [energy]
    rw [viscousEq]
    dsimp only [viscousConstant]
    have tangentNonneg :
        0 ≤ puncturedEuclideanSpaceTimeSquare receipt.wholeTangent :=
      sq_nonneg _
    linarith
  have errorLeEnergy :
      (∫ time,
          finiteInputProjectionErrorDensity modes (receipt.wholePath time)
          ∂(commonTimeMeasure requestedTime)) ≤
        errorFactor * energy := by
    have coefficientNonneg :
        0 ≤ 4368 * biotSavartSerrinConstant * ceiling *
          (radius : Real)⁻¹ / viscousConstant := by
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
            ceilingNonneg)
          (inv_nonneg.mpr (Nat.cast_nonneg radius)))
        viscousConstantPos.le
    have scaledHalf := mul_le_mul_of_nonneg_left
      halfGradientLeEnergy coefficientNonneg
    calc
      _ ≤ 2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
          ceiling *
          ∫ time,
            wholeStateVorticityGradientMass (receipt.wholePath time)
            ∂(commonTimeMeasure requestedTime) := errorIntegralLe
      _ = (4368 * biotSavartSerrinConstant * ceiling *
            (radius : Real)⁻¹ / viscousConstant) *
          ((viscousConstant / 2) *
            ∫ time,
              wholeStateVorticityGradientMass (receipt.wholePath time)
              ∂(commonTimeMeasure requestedTime)) := by
        field_simp [viscousConstantPos.ne']
        ring
      _ ≤ (4368 * biotSavartSerrinConstant * ceiling *
            (radius : Real)⁻¹ / viscousConstant) * energy := scaledHalf
      _ = errorFactor * energy := by rfl
  refine ⟨energy, energyNonneg, ?_, rateSettlement, errorLeEnergy⟩
  simpa only [energy, viscousConstant] using signed

private theorem receiptFiniteInputWorkEnergyBetween
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime start finish ceiling : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat)
    (radiusPos : 0 < radius)
    (ceilingNonneg : 0 ≤ ceiling)
    (startNonneg : 0 ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ requestedTime)
    (massBound :
      ∀ time : Icc (0 : Real) requestedTime,
        start ≤ time.1 → time.1 ≤ finish →
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling) :
    let modes := integerWaveFrequencyCube radius
    let errorFactor :=
      (4368 * biotSavartSerrinConstant * ceiling * (radius : Real)⁻¹) /
        (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
    ∃ energy : Real,
      0 ≤ energy ∧
      energy + nu.coeff *
          (wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩) -
            wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨start, ⟨startNonneg,
                  startLtFinish.le.trans finishLe⟩⟩)) ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          (ceiling ^ 3 * (finish - start)) ∧
      nu.coeff *
          (finiteStateVorticityCoefficientEnstrophy modes
              (receipt.wholePath
                ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩) -
            finiteStateVorticityCoefficientEnstrophy modes
              (receipt.wholePath
                ⟨start, ⟨startNonneg,
                  startLtFinish.le.trans finishLe⟩⟩)) ≤
        ∫ time in start..finish,
          (finiteInputRateDensity nu modes
              (wholeRestartReceiptPhysicalTrajectory receipt time) +
            finiteInputProjectionErrorDensity modes
              (wholeRestartReceiptPhysicalTrajectory receipt time)) ∧
      (∫ time in start..finish,
          finiteInputProjectionErrorDensity modes
            (wholeRestartReceiptPhysicalTrajectory receipt time)) ≤
        errorFactor * energy := by
  dsimp only
  let modes := integerWaveFrequencyCube radius
  let errorFactor :=
    (4368 * biotSavartSerrinConstant * ceiling * (radius : Real)⁻¹) /
      (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
  have startLtRequested : start < requestedTime :=
    startLtFinish.trans_le finishLe
  let suffix :=
    positiveTimeSuffixWholeContinuousMildSerrinReceipt
      receipt start startNonneg startLtRequested
  have durationPos : 0 < finish - start := sub_pos.mpr startLtFinish
  have durationLe : finish - start ≤ requestedTime - start :=
    sub_le_sub_right finishLe start
  let window :=
    restrictWholeContinuousMildSerrinReceipt
      durationPos durationLe suffix
  have windowMassBound :
      ∀ time : Icc (0 : Real) (finish - start),
        wholeVorticityEuclideanMass (window.wholePath time) ≤ ceiling := by
    intro time
    have shiftedLower :
        start ≤
          (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion durationLe time)).1 := by
      simp only [commonTimeShift_apply, commonTimeInclusion_apply]
      linarith [time.2.1]
    have shiftedUpper :
        (commonTimeShift startNonneg
            (startLtFinish.le.trans finishLe)
            (commonTimeInclusion durationLe time)).1 ≤ finish := by
      simp only [commonTimeShift_apply, commonTimeInclusion_apply]
      linarith [time.2.2]
    exact massBound _ shiftedLower shiftedUpper
  obtain ⟨energy, energyNonneg, signed, rateSettlement, errorLe⟩ :=
    receiptFiniteInputWorkEnergy window radius radiusPos ceilingNonneg
      (Filter.Eventually.of_forall windowMassBound)
  let zero : Icc (0 : Real) (finish - start) :=
    ⟨0, ⟨le_rfl, durationPos.le⟩⟩
  let terminal : Icc (0 : Real) (finish - start) :=
    ⟨finish - start, ⟨durationPos.le, le_rfl⟩⟩
  have terminalEq :
      window.wholePath terminal =
        receipt.wholePath
          ⟨finish, ⟨startNonneg.trans startLtFinish.le, finishLe⟩⟩ := by
    apply congrArg receipt.wholePath
    apply Subtype.ext
    simp [terminal,
      commonTimeInclusion_apply, commonTimeShift_apply]
  have stateIntegralEq (density : ComplexVorticityHilbertState → Real) :
      (∫ time,
          density (window.wholePath time)
          ∂(commonTimeMeasure (finish - start))) =
        ∫ time in start..finish,
          density (wholeRestartReceiptPhysicalTrajectory receipt time) := by
    rw [show
      (∫ time,
          density (window.wholePath time)
          ∂(commonTimeMeasure (finish - start))) =
        ∫ time in (0 : Real)..(finish - start),
          density (wholeRestartReceiptPhysicalTrajectory window time) by
        rw [← commonTime_integral_eq_intervalIntegral
          (finish - start) durationPos.le]
        apply integral_congr_ae
        filter_upwards [] with time
        unfold wholeRestartReceiptPhysicalTrajectory
        rw [projIcc_of_mem durationPos.le time.2]]
    calc
      (∫ time in (0 : Real)..(finish - start),
          density (wholeRestartReceiptPhysicalTrajectory window time)) =
          ∫ time in (0 : Real)..(finish - start),
            density
              (wholeRestartReceiptPhysicalTrajectory receipt
                (start + time)) := by
        apply intervalIntegral.integral_congr
        intro time timeMem
        have timeIcc : time ∈ Icc (0 : Real) (finish - start) := by
          simpa [uIcc_of_le durationPos.le] using timeMem
        unfold wholeRestartReceiptPhysicalTrajectory
        change
          density
              (window.wholePath
                (projIcc 0 (finish - start)
                  window.requestedTimePos.le time)) =
            density
              (receipt.wholePath
                (projIcc 0 requestedTime receipt.requestedTimePos.le
                  (start + time)))
        rw [projIcc_of_mem window.requestedTimePos.le timeIcc,
          projIcc_of_mem receipt.requestedTimePos.le
            (show start + time ∈ Icc (0 : Real) requestedTime by
              exact ⟨add_nonneg startNonneg timeIcc.1,
                by linarith [timeIcc.2]⟩)]
        change
          density (window.wholePath ⟨time, timeIcc⟩) =
            density (receipt.wholePath ⟨start + time, _⟩)
        rfl
      _ = ∫ time in start..finish,
          density (wholeRestartReceiptPhysicalTrajectory receipt time) := by
        have shifted :=
          intervalIntegral.integral_comp_add_left
            (f := fun time : Real =>
              density (wholeRestartReceiptPhysicalTrajectory receipt time))
            (a := 0) (b := finish - start) start
        convert shifted using 1
        ring_nf
  have rateIntegralEq := stateIntegralEq (fun state =>
    finiteInputRateDensity nu modes state +
      finiteInputProjectionErrorDensity modes state)
  have errorIntegralEq := stateIntegralEq
    (finiteInputProjectionErrorDensity modes)
  rw [terminalEq] at signed rateSettlement
  rw [rateIntegralEq] at rateSettlement
  rw [errorIntegralEq] at errorLe
  refine ⟨energy, energyNonneg, ?_, ?_, ?_⟩
  · simpa only [window, suffix,
      restrictWholeContinuousMildSerrinReceipt,
      positiveTimeSuffixWholeContinuousMildSerrinReceipt,
      wholeContinuousMildSerrinSuffixStartTime, add_zero] using signed
  · simpa only [window, suffix, modes,
      restrictWholeContinuousMildSerrinReceipt,
      positiveTimeSuffixWholeContinuousMildSerrinReceipt,
      wholeContinuousMildSerrinSuffixStartTime, add_zero] using rateSettlement
  · simpa only [errorFactor, modes] using errorLe

private theorem
    wholeRestartPrefix_finiteInputAutonomousWorkDensity_continuousOn
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    (modes : Finset IntegerWavevector) :
    ContinuousOn
      (fun time : Real =>
        finiteInputAutonomousWorkDensity nu modes
          (wholeRestartPrefixPhysicalTrajectory initial length time))
      (Icc 0 (elapsedTime initial length)) := by
  let path := wholeRestartPrefixPhysicalTrajectory initial length
  let projectedPath : Real → ComplexVorticityHilbertState := fun time =>
    complexSharpSupportProjection modes (path time)
  have pathContinuous :
      ContinuousOn path (Icc 0 (elapsedTime initial length)) := by
    exact wholeRestartPrefixPhysicalTrajectory_continuousOn initial length
  have projectedContinuous :
      ContinuousOn projectedPath (Icc 0 (elapsedTime initial length)) := by
    rw [show projectedPath = (sharpSupportProjectionCLM modes) ∘ path by
      funext time
      exact (sharpSupportProjectionCLM_apply modes (path time)).symm]
    exact (sharpSupportProjectionCLM modes).continuous.comp_continuousOn
      pathContinuous
  have projectedTransverse :
      ∀ time, WholeStateTransverse (projectedPath time) := by
    intro time
    exact wholeStateTransverse_sharpSupportProjection modes (path time)
      (wholeRestartPrefixPhysicalTrajectory_transverse
        initial length time)
  unfold finiteInputAutonomousWorkDensity
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro wave _waveMem
  have stateRowContinuous :
      ContinuousOn (fun time => projectedPath time wave)
        (Icc 0 (elapsedTime initial length)) :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp_continuousOn projectedContinuous
  have nonlinearRowContinuous :
      ContinuousOn
        (fun time =>
          wholeStateVorticityNonlinearCoefficientAt
            (projectedPath time) wave)
        (Icc 0 (elapsedTime initial length)) :=
    wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
      projectedPath wave 0 (elapsedTime initial length)
      projectedContinuous (fun time _timeMem => projectedTransverse time)
  exact complexCoordinateRealInner_prod_continuous.comp_continuousOn
    (stateRowContinuous.prodMk nonlinearRowContinuous)

private theorem
    wholeRestartPrefix_finiteInputProjectionErrorDensity_continuousOn
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    (modes : Finset IntegerWavevector) :
    ContinuousOn
      (fun time : Real =>
        finiteInputProjectionErrorDensity modes
          (wholeRestartPrefixPhysicalTrajectory initial length time))
      (Icc 0 (elapsedTime initial length)) := by
  let path := wholeRestartPrefixPhysicalTrajectory initial length
  let projectedPath : Real → ComplexVorticityHilbertState := fun time =>
    complexSharpSupportProjection modes (path time)
  have pathContinuous :
      ContinuousOn path (Icc 0 (elapsedTime initial length)) := by
    exact wholeRestartPrefixPhysicalTrajectory_continuousOn initial length
  have projectedContinuous :
      ContinuousOn projectedPath (Icc 0 (elapsedTime initial length)) := by
    rw [show projectedPath = (sharpSupportProjectionCLM modes) ∘ path by
      funext time
      exact (sharpSupportProjectionCLM_apply modes (path time)).symm]
    exact (sharpSupportProjectionCLM modes).continuous.comp_continuousOn
      pathContinuous
  have pathTransverse : ∀ time, WholeStateTransverse (path time) := by
    intro time
    exact wholeRestartPrefixPhysicalTrajectory_transverse
      initial length time
  have projectedTransverse :
      ∀ time, WholeStateTransverse (projectedPath time) := by
    intro time
    exact wholeStateTransverse_sharpSupportProjection modes (path time)
      (pathTransverse time)
  unfold finiteInputProjectionErrorDensity
  apply continuousOn_finsetSum
  intro wave _waveMem
  have fullRowContinuous :
      ContinuousOn
        (fun time =>
          wholeStateVorticityNonlinearCoefficientAt (path time) wave)
        (Icc 0 (elapsedTime initial length)) :=
    wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
      path wave 0 (elapsedTime initial length) pathContinuous
      (fun time _timeMem => pathTransverse time)
  have projectedRowContinuous :
      ContinuousOn
        (fun time =>
          wholeStateVorticityNonlinearCoefficientAt
            (projectedPath time) wave)
        (Icc 0 (elapsedTime initial length)) :=
    wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
      projectedPath wave 0 (elapsedTime initial length)
      projectedContinuous (fun time _timeMem => projectedTransverse time)
  exact ContinuousOn.mul continuousOn_const
    (complexCoordinateAmplitudeSq_continuous.comp_continuousOn
      (fullRowContinuous.sub projectedRowContinuous))

private theorem wholeRestartPrefix_finiteInputRateDensity_continuousOn
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    (modes : Finset IntegerWavevector) :
    ContinuousOn
      (fun time : Real =>
        finiteInputRateDensity nu modes
          (wholeRestartPrefixPhysicalTrajectory initial length time))
      (Icc 0 (elapsedTime initial length)) := by
  have autonomousContinuous :=
    wholeRestartPrefix_finiteInputAutonomousWorkDensity_continuousOn
      initial length modes
  have pathContinuous :=
    wholeRestartPrefixPhysicalTrajectory_continuousOn initial length
  unfold finiteInputRateDensity finiteInputAutonomousWorkDensity
  apply ContinuousOn.sub autonomousContinuous
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro wave _waveMem
  apply ContinuousOn.mul continuousOn_const
  exact complexCoordinateAmplitudeSq_continuous.comp_continuousOn
    ((lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp_continuousOn pathContinuous)

private theorem wholeRestartPrefixSuccStateIntegral_eq_receipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (density : ComplexVorticityHilbertState → Real)
    {start finish : Real}
    (joinLeStart : elapsedTime initial index ≤ start)
    (startLeFinish : start ≤ finish)
    (finishLe : finish ≤ elapsedTime initial (index + 1)) :
    (∫ time in start..finish,
        density
          (wholeRestartPrefixPhysicalTrajectory initial (index + 1) time)) =
      ∫ localTime in
          start - elapsedTime initial index..
            finish - elapsedTime initial index,
        density
          (wholeRestartReceiptPhysicalTrajectory
            (run initial index).contact.prefixReceipt localTime) := by
  let joinTime := elapsedTime initial index
  let receipt := (run initial index).contact.prefixReceipt
  have finishLeExpanded :
      finish ≤ joinTime + (run initial index).contact.time.1 := by
    simpa only [joinTime, elapsedTime_succ] using finishLe
  calc
    (∫ time in start..finish,
        density
          (wholeRestartPrefixPhysicalTrajectory initial (index + 1) time)) =
        ∫ time in start..finish,
          density
            (wholeRestartReceiptPhysicalTrajectory
              receipt (time - joinTime)) := by
      apply intervalIntegral.integral_congr
      intro time timeMem
      have timeIcc : time ∈ Icc start finish := by
        simpa [uIcc_of_le startLeFinish] using timeMem
      let localTime :
          Icc (0 : Real) (run initial index).contact.time.1 :=
        ⟨time - joinTime,
          ⟨sub_nonneg.mpr (joinLeStart.trans timeIcc.1),
            by linarith [timeIcc.2, finishLeExpanded]⟩⟩
      have chart :=
        wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
          initial index localTime
      have absoluteEq : joinTime + localTime.1 = time := by
        dsimp only [localTime]
        ring
      unfold wholeRestartReceiptPhysicalTrajectory
      change
        density
            (wholeRestartPrefixPhysicalTrajectory initial (index + 1) time) =
          density
            (receipt.wholePath
              (projIcc 0 (run initial index).contact.time.1
                (run initial index).contact.prefixReceipt.requestedTimePos.le
                (time - joinTime)))
      rw [projIcc_of_mem
        (run initial index).contact.prefixReceipt.requestedTimePos.le
        localTime.2]
      rw [← chart]
      simp only [joinTime, absoluteEq]
    _ = ∫ localTime in
          start - elapsedTime initial index..
            finish - elapsedTime initial index,
        density
          (wholeRestartReceiptPhysicalTrajectory
            (run initial index).contact.prefixReceipt localTime) := by
      simpa only [joinTime, receipt] using
        (intervalIntegral.integral_comp_sub_right
          (f := fun localTime : Real =>
            density
              (wholeRestartReceiptPhysicalTrajectory receipt localTime))
          (a := start) (b := finish) joinTime)

private theorem wholeRestartPrefixFiniteInputWorkEnergy
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ (length radius : Nat) {start finish ceiling : Real},
      0 ≤ start →
      start < finish →
      finish ≤ elapsedTime initial length →
      0 ≤ ceiling →
      0 < radius →
      (∀ time ∈ Icc start finish,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          ceiling) →
      let modes := integerWaveFrequencyCube radius
      let errorFactor :=
        (4368 * biotSavartSerrinConstant * ceiling * (radius : Real)⁻¹) /
          (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
      ∃ energy : Real,
        0 ≤ energy ∧
        energy + nu.coeff *
            (wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length finish) -
              wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length start)) ≤
          ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
              (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
            (ceiling ^ 3 * (finish - start)) ∧
        nu.coeff *
            (finiteStateVorticityCoefficientEnstrophy modes
                (wholeRestartPrefixPhysicalTrajectory initial length finish) -
              finiteStateVorticityCoefficientEnstrophy modes
                (wholeRestartPrefixPhysicalTrajectory initial length start)) ≤
          ∫ time in start..finish,
            (finiteInputRateDensity nu modes
                (wholeRestartPrefixPhysicalTrajectory initial length time) +
              finiteInputProjectionErrorDensity modes
                (wholeRestartPrefixPhysicalTrajectory initial length time)) ∧
        (∫ time in start..finish,
            finiteInputProjectionErrorDensity modes
              (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
          errorFactor * energy := by
  intro length
  induction length with
  | zero =>
      intro radius start finish ceiling startNonneg startLtFinish finishLe
        _ceilingNonneg _radiusPos _massLe
      rw [elapsedTime_zero] at finishLe
      linarith
  | succ length ih =>
      intro radius start finish ceiling startNonneg startLtFinish finishLe
        ceilingNonneg radiusPos massLe
      dsimp only
      let modes := integerWaveFrequencyCube radius
      let errorFactor :=
        (4368 * biotSavartSerrinConstant * ceiling * (radius : Real)⁻¹) /
          (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
      let joinTime := elapsedTime initial length
      let receipt := (run initial length).contact.prefixReceipt
      have joinNonneg : 0 ≤ joinTime :=
        ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
          initial length
      have finishLeExpanded :
          finish ≤ joinTime + (run initial length).contact.time.1 := by
        simpa only [joinTime, elapsedTime_succ] using finishLe
      have priorChart
          (time : Real) (timeLeJoin : time ≤ joinTime) :
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
            wholeRestartPrefixPhysicalTrajectory initial length time := by
        simp only [wholeRestartPrefixPhysicalTrajectory]
        exact
          ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice.endpointSplice_of_le
            joinTime
            (wholeRestartPrefixPhysicalTrajectory initial length)
            (wholeRestartReceiptPhysicalTrajectory receipt)
            time timeLeJoin
      have receiptChart
          (time : Real) (joinLeTime : joinTime ≤ time)
          (timeLeExpanded :
            time ≤ joinTime + (run initial length).contact.time.1) :
          wholeRestartPrefixPhysicalTrajectory initial (length + 1) time =
            receipt.wholePath
              ⟨time - joinTime,
                ⟨sub_nonneg.mpr joinLeTime, by linarith⟩⟩ := by
        let localTime :
            Icc (0 : Real) (run initial length).contact.time.1 :=
          ⟨time - joinTime,
            ⟨sub_nonneg.mpr joinLeTime, by linarith⟩⟩
        have chart :=
          wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
            initial length localTime
        have addLocal : joinTime + localTime.1 = time := by
          dsimp only [joinTime, localTime]
          ring
        simpa only [receipt, joinTime, addLocal] using chart
      have priorIntegralEq
          (density : ComplexVorticityHilbertState → Real)
          {left right : Real}
          (leftLeRight : left ≤ right)
          (rightLeJoin : right ≤ joinTime) :
          (∫ time in left..right,
              density
                (wholeRestartPrefixPhysicalTrajectory initial
                  (length + 1) time)) =
            ∫ time in left..right,
              density
                (wholeRestartPrefixPhysicalTrajectory initial length time) := by
        apply intervalIntegral.integral_congr
        intro time timeMem
        have timeIcc : time ∈ Icc left right := by
          simpa [uIcc_of_le leftLeRight] using timeMem
        exact congrArg density
          (priorChart time (timeIcc.2.trans rightLeJoin))
      by_cases finishLeJoin : finish ≤ joinTime
      · have priorMassLe :
            ∀ time ∈ Icc start finish,
              wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
                ceiling := by
          intro time timeMem
          rw [← priorChart time (timeMem.2.trans finishLeJoin)]
          exact massLe time timeMem
        obtain ⟨energy, energyNonneg, signed, rate, error⟩ :=
          ih radius startNonneg startLtFinish finishLeJoin
            ceilingNonneg radiusPos priorMassLe
        have rateIntegralEq := priorIntegralEq
          (fun state =>
            finiteInputRateDensity nu modes state +
              finiteInputProjectionErrorDensity modes state)
          startLtFinish.le finishLeJoin
        have errorIntegralEq := priorIntegralEq
          (finiteInputProjectionErrorDensity modes)
          startLtFinish.le finishLeJoin
        refine ⟨energy, energyNonneg, ?_, ?_, ?_⟩
        · rw [priorChart finish finishLeJoin,
            priorChart start (startLtFinish.le.trans finishLeJoin)]
          simpa only [modes, errorFactor] using signed
        · rw [rateIntegralEq, priorChart finish finishLeJoin,
            priorChart start (startLtFinish.le.trans finishLeJoin)]
          simpa only [modes, errorFactor] using rate
        · rw [errorIntegralEq]
          simpa only [modes, errorFactor] using error
      · have joinLtFinish : joinTime < finish := lt_of_not_ge finishLeJoin
        by_cases startLtJoin : start < joinTime
        · have firstMassLe :
              ∀ time ∈ Icc start joinTime,
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
                  ceiling := by
            intro time timeMem
            rw [← priorChart time timeMem.2]
            exact massLe time
              ⟨timeMem.1, timeMem.2.trans joinLtFinish.le⟩
          obtain ⟨firstEnergy, firstEnergyNonneg, firstSigned,
              firstRate, firstError⟩ :=
            ih radius startNonneg startLtJoin le_rfl
              ceilingNonneg radiusPos firstMassLe
          have localFinishPos : 0 < finish - joinTime :=
            sub_pos.mpr joinLtFinish
          have localFinishLe :
              finish - joinTime ≤ (run initial length).contact.time.1 := by
            linarith
          have secondMassLe :
              ∀ time : Icc (0 : Real) (run initial length).contact.time.1,
                0 ≤ time.1 → time.1 ≤ finish - joinTime →
                wholeVorticityEuclideanMass (receipt.wholePath time) ≤
                  ceiling := by
            intro time _timeNonneg timeLe
            have absoluteMem :
                joinTime + time.1 ∈ Icc start finish := by
              constructor
              · linarith [time.2.1]
              · linarith
            have chart :=
              wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
                initial length time
            have globalBound := massLe _ absoluteMem
            rw [show joinTime = elapsedTime initial length by rfl] at globalBound
            rw [chart] at globalBound
            exact globalBound
          obtain ⟨secondEnergy, secondEnergyNonneg, secondSigned,
              secondRate, secondError⟩ :=
            receiptFiniteInputWorkEnergyBetween receipt radius radiusPos
              ceilingNonneg le_rfl localFinishPos localFinishLe secondMassLe
          have startEq := priorChart start startLtJoin.le
          have joinPriorEq := priorChart joinTime le_rfl
          have joinReceiptEq := receiptChart joinTime le_rfl
            (by linarith [(run initial length).contact.time_pos])
          have finishReceiptEq := receiptChart finish joinLtFinish.le
            finishLeExpanded
          have firstRateIntegralEq := priorIntegralEq
            (fun state =>
              finiteInputRateDensity nu modes state +
                finiteInputProjectionErrorDensity modes state)
            startLtJoin.le le_rfl
          have firstErrorIntegralEq := priorIntegralEq
            (finiteInputProjectionErrorDensity modes)
            startLtJoin.le le_rfl
          have secondRateIntegralEq :=
            wholeRestartPrefixSuccStateIntegral_eq_receipt
              initial length
              (fun state =>
                finiteInputRateDensity nu modes state +
                  finiteInputProjectionErrorDensity modes state)
              le_rfl joinLtFinish.le finishLe
          have secondErrorIntegralEq :=
            wholeRestartPrefixSuccStateIntegral_eq_receipt
              initial length (finiteInputProjectionErrorDensity modes)
              le_rfl joinLtFinish.le finishLe
          have firstSignedGlobal :
              firstEnergy + nu.coeff *
                  (wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) joinTime) -
                    wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) start)) ≤
                ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                  (ceiling ^ 3 * (joinTime - start)) := by
            rw [joinPriorEq, startEq]
            simpa only [modes, errorFactor] using firstSigned
          have secondSignedGlobal :
              secondEnergy + nu.coeff *
                  (wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) finish) -
                    wholeVorticityEuclideanMass
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) joinTime)) ≤
                ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                    (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                  (ceiling ^ 3 * (finish - joinTime)) := by
            rw [finishReceiptEq, joinReceiptEq]
            simpa only [receipt, sub_zero, sub_self, modes, errorFactor] using
              secondSigned
          have firstRateGlobal :
              nu.coeff *
                  (finiteStateVorticityCoefficientEnstrophy modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) joinTime) -
                    finiteStateVorticityCoefficientEnstrophy modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) start)) ≤
                ∫ time in start..joinTime,
                  (finiteInputRateDensity nu modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time) +
                    finiteInputProjectionErrorDensity modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time)) := by
            rw [firstRateIntegralEq, joinPriorEq, startEq]
            simpa only [modes, errorFactor] using firstRate
          have secondRateGlobal :
              nu.coeff *
                  (finiteStateVorticityCoefficientEnstrophy modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) finish) -
                    finiteStateVorticityCoefficientEnstrophy modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) joinTime)) ≤
                ∫ time in joinTime..finish,
                  (finiteInputRateDensity nu modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time) +
                    finiteInputProjectionErrorDensity modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time)) := by
            rw [secondRateIntegralEq, finishReceiptEq, joinReceiptEq]
            simpa only [receipt, sub_zero, sub_self, modes, errorFactor] using
              secondRate
          have firstErrorGlobal :
              (∫ time in start..joinTime,
                  finiteInputProjectionErrorDensity modes
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time)) ≤
                errorFactor * firstEnergy := by
            rw [firstErrorIntegralEq]
            simpa only [modes, errorFactor] using firstError
          have secondErrorGlobal :
              (∫ time in joinTime..finish,
                  finiteInputProjectionErrorDensity modes
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time)) ≤
                errorFactor * secondEnergy := by
            rw [secondErrorIntegralEq]
            simpa only [receipt, sub_zero, sub_self, modes, errorFactor] using
              secondError
          have rateContinuous :=
            (wholeRestartPrefix_finiteInputRateDensity_continuousOn
              initial (length + 1) modes).add
            (wholeRestartPrefix_finiteInputProjectionErrorDensity_continuousOn
              initial (length + 1) modes)
          have errorContinuous :=
            wholeRestartPrefix_finiteInputProjectionErrorDensity_continuousOn
              initial (length + 1) modes
          have firstRateIntegrable :
              IntervalIntegrable
                (fun time : Real =>
                  finiteInputRateDensity nu modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time) +
                    finiteInputProjectionErrorDensity modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time))
                volume start joinTime :=
            ContinuousOn.intervalIntegrable_of_Icc startLtJoin.le
              (rateContinuous.mono
                (Icc_subset_Icc startNonneg
                  (joinLtFinish.le.trans finishLe)))
          have secondRateIntegrable :
              IntervalIntegrable
                (fun time : Real =>
                  finiteInputRateDensity nu modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time) +
                    finiteInputProjectionErrorDensity modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time))
                volume joinTime finish :=
            ContinuousOn.intervalIntegrable_of_Icc joinLtFinish.le
              (rateContinuous.mono
                (Icc_subset_Icc joinNonneg finishLe))
          have firstErrorIntegrable :
              IntervalIntegrable
                (fun time : Real =>
                  finiteInputProjectionErrorDensity modes
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time))
                volume start joinTime :=
            ContinuousOn.intervalIntegrable_of_Icc startLtJoin.le
              (errorContinuous.mono
                (Icc_subset_Icc startNonneg
                  (joinLtFinish.le.trans finishLe)))
          have secondErrorIntegrable :
              IntervalIntegrable
                (fun time : Real =>
                  finiteInputProjectionErrorDensity modes
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time))
                volume joinTime finish :=
            ContinuousOn.intervalIntegrable_of_Icc joinLtFinish.le
              (errorContinuous.mono
                (Icc_subset_Icc joinNonneg finishLe))
          let energy := firstEnergy + secondEnergy
          have energyNonneg : 0 ≤ energy :=
            add_nonneg firstEnergyNonneg secondEnergyNonneg
          refine ⟨energy, energyNonneg, ?_, ?_, ?_⟩
          · dsimp only [energy]
            calc
              firstEnergy + secondEnergy + nu.coeff *
                    (wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) finish) -
                      wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) start)) =
                  (firstEnergy + nu.coeff *
                    (wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) joinTime) -
                      wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) start))) +
                  (secondEnergy + nu.coeff *
                    (wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) finish) -
                      wholeVorticityEuclideanMass
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) joinTime))) := by ring
              _ ≤
                  ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                    (ceiling ^ 3 * (joinTime - start)) +
                  ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
                      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
                    (ceiling ^ 3 * (finish - joinTime)) :=
                add_le_add firstSignedGlobal secondSignedGlobal
              _ = _ := by ring
          · calc
              nu.coeff *
                  (finiteStateVorticityCoefficientEnstrophy modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) finish) -
                    finiteStateVorticityCoefficientEnstrophy modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) start)) =
                  nu.coeff *
                    (finiteStateVorticityCoefficientEnstrophy modes
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) joinTime) -
                      finiteStateVorticityCoefficientEnstrophy modes
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) start)) +
                  nu.coeff *
                    (finiteStateVorticityCoefficientEnstrophy modes
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) finish) -
                      finiteStateVorticityCoefficientEnstrophy modes
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) joinTime)) := by ring
              _ ≤
                  (∫ time in start..joinTime,
                    (finiteInputRateDensity nu modes
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) time) +
                      finiteInputProjectionErrorDensity modes
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) time))) +
                  ∫ time in joinTime..finish,
                    (finiteInputRateDensity nu modes
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) time) +
                      finiteInputProjectionErrorDensity modes
                        (wholeRestartPrefixPhysicalTrajectory initial
                          (length + 1) time)) :=
                add_le_add firstRateGlobal secondRateGlobal
              _ = _ :=
                intervalIntegral.integral_add_adjacent_intervals
                  firstRateIntegrable secondRateIntegrable
          · calc
              (∫ time in start..finish,
                  finiteInputProjectionErrorDensity modes
                    (wholeRestartPrefixPhysicalTrajectory initial
                      (length + 1) time)) =
                  (∫ time in start..joinTime,
                    finiteInputProjectionErrorDensity modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time)) +
                  ∫ time in joinTime..finish,
                    finiteInputProjectionErrorDensity modes
                      (wholeRestartPrefixPhysicalTrajectory initial
                        (length + 1) time) :=
                (intervalIntegral.integral_add_adjacent_intervals
                  firstErrorIntegrable secondErrorIntegrable).symm
              _ ≤ errorFactor * firstEnergy +
                    errorFactor * secondEnergy :=
                add_le_add firstErrorGlobal secondErrorGlobal
              _ = errorFactor * energy := by
                dsimp only [energy]
                ring
        · have joinLeStart : joinTime ≤ start := le_of_not_gt startLtJoin
          have localStartNonneg : 0 ≤ start - joinTime :=
            sub_nonneg.mpr joinLeStart
          have localStartLtFinish :
              start - joinTime < finish - joinTime :=
            sub_lt_sub_right startLtFinish joinTime
          have localFinishLe :
              finish - joinTime ≤ (run initial length).contact.time.1 := by
            linarith
          have localMassLe :
              ∀ time : Icc (0 : Real) (run initial length).contact.time.1,
                start - joinTime ≤ time.1 →
                time.1 ≤ finish - joinTime →
                wholeVorticityEuclideanMass (receipt.wholePath time) ≤
                  ceiling := by
            intro time startLeTime timeLeFinish
            have absoluteMem :
                joinTime + time.1 ∈ Icc start finish := by
              constructor <;> linarith
            have chart :=
              wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
                initial length time
            have globalBound := massLe _ absoluteMem
            rw [show joinTime = elapsedTime initial length by rfl] at globalBound
            rw [chart] at globalBound
            exact globalBound
          obtain ⟨energy, energyNonneg, signed, rate, error⟩ :=
            receiptFiniteInputWorkEnergyBetween receipt radius radiusPos
              ceilingNonneg localStartNonneg localStartLtFinish
              localFinishLe localMassLe
          have startReceiptEq := receiptChart start joinLeStart
            (startLtFinish.le.trans finishLeExpanded)
          have finishReceiptEq := receiptChart finish joinLtFinish.le
            finishLeExpanded
          have rateIntegralEq :=
            wholeRestartPrefixSuccStateIntegral_eq_receipt
              initial length
              (fun state =>
                finiteInputRateDensity nu modes state +
                  finiteInputProjectionErrorDensity modes state)
              joinLeStart startLtFinish.le finishLe
          have errorIntegralEq :=
            wholeRestartPrefixSuccStateIntegral_eq_receipt
              initial length (finiteInputProjectionErrorDensity modes)
              joinLeStart startLtFinish.le finishLe
          refine ⟨energy, energyNonneg, ?_, ?_, ?_⟩
          · rw [finishReceiptEq, startReceiptEq]
            convert signed using 1
            ring
          · rw [rateIntegralEq, finishReceiptEq, startReceiptEq]
            simpa only [receipt, modes, errorFactor] using rate
          · rw [errorIntegralEq]
            simpa only [receipt, modes, errorFactor] using error



private theorem receipt_mass_band_selects_gradient_bound
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime lower ceiling : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (massBand :
      ∀ time : Icc (0 : Real) requestedTime,
        lower ≤ wholeVorticityEuclideanMass (receipt.wholePath time) ∧
          wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling)
    (massNondecreasing :
      wholeVorticityEuclideanMass initialState ≤
        wholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩)) :
    let tangentGradientConstant : Real :=
      (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
        (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
    let gradientConstant : Real :=
      (2 * tangentGradientConstant) /
        (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)
    ∃ sample : Icc (0 : Real) requestedTime,
      lower ≤ wholeVorticityEuclideanMass (receipt.wholePath sample) ∧
      wholeVorticityEuclideanMass (receipt.wholePath sample) ≤ ceiling ∧
      (Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (receipt.wholePath sample wave)) ∧
      wholeStateVorticityGradientMass (receipt.wholePath sample) ≤
        gradientConstant * ceiling ^ 3 := by
  dsimp only
  let viscousConstant : Real := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let tangentGradientConstant : Real :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * viscousConstant)
  let gradientConstant : Real :=
    (2 * tangentGradientConstant) / viscousConstant
  obtain ⟨sample, sampleReality, sampleBudget⟩ :=
    receipt_exists_scaleCriticalTangentGradientState receipt
      (Filter.Eventually.of_forall fun time => (massBand time).2)
      massNondecreasing
  have viscousConstantPos : 0 < viscousConstant := by
    dsimp only [viscousConstant]
    exact mul_pos (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
  have tangentNonneg :
      0 ≤ ‖puncturedEuclideanSpaceTimeState
        receipt.wholeTangent sample‖ ^ 2 := sq_nonneg _
  have weightedGradient :
      (viscousConstant / 2) *
          wholeStateVorticityGradientMass (receipt.wholePath sample) ≤
        tangentGradientConstant * ceiling ^ 3 := by
    dsimp only [tangentGradientConstant, viscousConstant]
      at sampleBudget ⊢
    nlinarith
  have gradientBound :
      wholeStateVorticityGradientMass (receipt.wholePath sample) ≤
        gradientConstant * ceiling ^ 3 := by
    apply (mul_le_mul_iff_of_pos_left
      (show 0 < viscousConstant / 2 by positivity)).mp
    calc
      (viscousConstant / 2) *
          wholeStateVorticityGradientMass (receipt.wholePath sample) ≤
          tangentGradientConstant * ceiling ^ 3 := weightedGradient
      _ = (viscousConstant / 2) *
          (gradientConstant * ceiling ^ 3) := by
        dsimp only [gradientConstant]
        field_simp [viscousConstantPos.ne']
  exact ⟨sample, (massBand sample).1, (massBand sample).2,
    sampleReality, gradientBound⟩
private theorem continuous_mass_path_has_two_separated_good_windows
    {a b level : Real}
    (aLeB : a ≤ b)
    (levelPos : 0 < level)
    (mass : Real → Real)
    (massContinuous : ContinuousOn mass (Icc a b))
    (massStart : mass a = level / 2)
    (massFinish : mass b = level) :
    ∃ lowerStart lowerFinish upperStart upperFinish : Real,
      lowerStart ∈ Icc a b ∧
      lowerFinish ∈ Icc a b ∧
      upperStart ∈ Icc lowerFinish b ∧
      upperFinish ∈ Icc lowerFinish b ∧
      lowerStart < lowerFinish ∧
      lowerFinish < upperStart ∧
      upperStart < upperFinish ∧
      mass lowerStart = 9 * level / 16 ∧
      mass lowerFinish = 5 * level / 8 ∧
      mass upperStart = 3 * level / 4 ∧
      mass upperFinish = 13 * level / 16 ∧
      (∀ time ∈ Icc lowerStart lowerFinish,
        9 * level / 16 ≤ mass time ∧ mass time ≤ 5 * level / 8) ∧
      (∀ time ∈ Icc upperStart upperFinish,
        3 * level / 4 ≤ mass time ∧ mass time ≤ 13 * level / 16) := by
  let step : Real := level / 8
  let lowerShift : Real → Real := fun time => mass time - level / 2
  have stepPos : 0 < step := by dsimp only [step]; positivity
  have lowerShiftContinuous : ContinuousOn lowerShift (Icc a b) := by
    exact massContinuous.sub continuousOn_const
  have lowerShiftStart : lowerShift a ≤ step / 2 := by
    dsimp only [lowerShift, step]
    rw [massStart]
    linarith [levelPos]
  have lowerShiftFinish : step ≤ lowerShift b := by
    dsimp only [lowerShift, step]
    rw [massFinish]
    linarith [levelPos]
  obtain ⟨lowerStart, lowerFinish, lowerStartMem, lowerFinishMem,
      lowerStartLtFinish, lowerStartMass, lowerFinishMass,
      lowerInterior⟩ :=
    continuous_first_last_level_window aLeB stepPos lowerShift
      lowerShiftContinuous lowerShiftStart lowerShiftFinish
  have lowerStartMass' : mass lowerStart = 9 * level / 16 := by
    dsimp only [lowerShift, step] at lowerStartMass
    linarith
  have lowerFinishMass' : mass lowerFinish = 5 * level / 8 := by
    dsimp only [lowerShift, step] at lowerFinishMass
    linarith
  have lowerFinishLtB : lowerFinish < b := by
    apply lt_of_le_of_ne lowerFinishMem.2
    intro finishEq
    subst lowerFinish
    rw [massFinish] at lowerFinishMass'
    nlinarith [levelPos]
  let upperShift : Real → Real :=
    fun time => mass time - 11 * level / 16
  have upperShiftContinuous :
      ContinuousOn upperShift (Icc lowerFinish b) := by
    exact (massContinuous.mono
      (Icc_subset_Icc lowerFinishMem.1 le_rfl)).sub continuousOn_const
  have upperShiftStart : upperShift lowerFinish ≤ step / 2 := by
    dsimp only [upperShift, step]
    rw [lowerFinishMass']
    linarith [levelPos]
  have upperShiftFinish : step ≤ upperShift b := by
    dsimp only [upperShift, step]
    rw [massFinish]
    linarith [levelPos]
  obtain ⟨upperStart, upperFinish, upperStartMem, upperFinishMem,
      upperStartLtFinish, upperStartMass, upperFinishMass,
      upperInterior⟩ :=
    continuous_first_last_level_window lowerFinishLtB.le stepPos
      upperShift upperShiftContinuous upperShiftStart upperShiftFinish
  have upperStartMass' : mass upperStart = 3 * level / 4 := by
    dsimp only [upperShift, step] at upperStartMass
    linarith
  have upperFinishMass' : mass upperFinish = 13 * level / 16 := by
    dsimp only [upperShift, step] at upperFinishMass
    linarith
  have lowerFinishLtUpperStart : lowerFinish < upperStart := by
    apply lt_of_le_of_ne upperStartMem.1
    intro startEq
    subst upperStart
    rw [lowerFinishMass'] at upperStartMass'
    nlinarith [levelPos]
  refine ⟨lowerStart, lowerFinish, upperStart, upperFinish,
    lowerStartMem, lowerFinishMem, upperStartMem, upperFinishMem,
    lowerStartLtFinish, lowerFinishLtUpperStart, upperStartLtFinish,
    lowerStartMass', lowerFinishMass', upperStartMass', upperFinishMass',
    ?_, ?_⟩
  · intro time timeMem
    have shifted := lowerInterior time timeMem
    dsimp only [lowerShift, step] at shifted
    constructor <;> linarith
  · intro time timeMem
    have shifted := upperInterior time timeMem
    dsimp only [upperShift, step] at shifted
    constructor <;> linarith

private theorem separated_good_endpoints_generate_finite_inventory_gap
    (level gradientConstant : Real)
    (levelPos : 0 < level)
    (gradientConstantNonneg : 0 ≤ gradientConstant)
    (lowerState upperState : ComplexVorticityHilbertState)
    (lowerMassUpper :
      wholeVorticityEuclideanMass lowerState ≤ 5 * level / 8)
    (upperMassLower :
      3 * level / 4 ≤ wholeVorticityEuclideanMass upperState)
    (upperGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (upperState wave))
    (upperGradientBound :
      wholeStateVorticityGradientMass upperState ≤
        gradientConstant * level ^ 3) :
    ∃ radius : Nat,
      0 < radius ∧
      8 * (gradientConstant + 1) * level ≤ (radius : Real) ∧
      (radius : Real) ≤ 8 * (gradientConstant + 1) * level + 2 ∧
      7 * level / 64 ≤
        finiteStateVorticityCoefficientEnstrophy
            (integerWaveFrequencyCube radius) upperState -
          finiteStateVorticityCoefficientEnstrophy
            (integerWaveFrequencyCube radius) lowerState := by
  let ratio : Real := 8 * (gradientConstant + 1) * level
  let radius : Nat := Nat.ceil ratio + 1
  have ratioNonneg : 0 ≤ ratio := by
    dsimp only [ratio]
    positivity
  have radiusPos : 0 < radius := by
    dsimp only [radius]
    omega
  have ratioLeRadius : ratio ≤ (radius : Real) := by
    calc
      ratio ≤ (Nat.ceil ratio : Real) := Nat.le_ceil ratio
      _ ≤ (radius : Real) := by
        dsimp only [radius]
        push_cast
        linarith
  have radiusUpper : (radius : Real) ≤ ratio + 2 := by
    have ceilLt : (Nat.ceil ratio : Real) < ratio + 1 :=
      Nat.ceil_lt_add_one ratioNonneg
    dsimp only [radius]
    push_cast
    linarith
  have radiusRealPos : 0 < (radius : Real) := by
    exact_mod_cast radiusPos
  have radiusSqPos : 0 < (radius : Real) ^ 2 := sq_pos_of_pos radiusRealPos
  have coefficientLe :
      gradientConstant ≤ (gradientConstant + 1) ^ 2 := by
    nlinarith [sq_nonneg gradientConstant]
  have gradientPaid :
      wholeStateVorticityGradientMass upperState ≤
        (level / 64) * (radius : Real) ^ 2 := by
    calc
      wholeStateVorticityGradientMass upperState ≤
          gradientConstant * level ^ 3 := upperGradientBound
      _ ≤ (gradientConstant + 1) ^ 2 * level ^ 3 := by
        exact mul_le_mul_of_nonneg_right coefficientLe
          (pow_nonneg levelPos.le 3)
      _ = (level / 64) * ratio ^ 2 := by
        dsimp only [ratio]
        ring
      _ ≤ (level / 64) * (radius : Real) ^ 2 := by
        gcongr
  have tailLe :
      wholeVorticityEuclideanMass
          (complexSharpSupportProjection (integerWaveFrequencyCube radius)
              upperState - upperState) ≤
        level / 64 := by
    apply (mul_le_mul_iff_of_pos_left radiusSqPos).mp
    exact
      (wholeVorticity_cubeComplement_mul_radius_sq_le_gradient
        upperState upperGradientSummable radius).trans
          (by simpa only [mul_comm] using gradientPaid)
  have upperSplit :=
    wholeVorticityEuclideanMass_eq_projection_add_complement
      (integerWaveFrequencyCube radius) upperState
  have upperProjectedLower :
      47 * level / 64 ≤
        wholeVorticityEuclideanMass
          (complexSharpSupportProjection (integerWaveFrequencyCube radius)
            upperState) := by
    nlinarith
  have upperFiniteLower :
      47 * level / 64 ≤
        finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) upperState := by
    rw [finiteStateVorticityCoefficientEnstrophy_eq_projectionMass]
    exact upperProjectedLower
  have lowerFiniteUpper :
      finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) lowerState ≤
        40 * level / 64 := by
    calc
      finiteStateVorticityCoefficientEnstrophy
            (integerWaveFrequencyCube radius) lowerState ≤
          wholeVorticityEuclideanMass lowerState :=
        ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
          (integerWaveFrequencyCube radius) lowerState
      _ ≤ 5 * level / 8 := lowerMassUpper
      _ = 40 * level / 64 := by ring
  refine ⟨radius, radiusPos, ?_, ?_, ?_⟩
  · simpa only [ratio] using ratioLeRadius
  · simpa only [ratio] using radiusUpper
  · nlinarith

/-- Restrict an above-average interval in the last actual prefix row to the
identical positive-time source receipt, preserving its path chart. -/
private theorem wholeRestartPrefix_lastReceiptAverageSubreceipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (density : ComplexVorticityHilbertState → Real)
    (threshold ceiling start finish : Real)
    (joinLeStart : elapsedTime initial index ≤ start)
    (startLtFinish : start < finish)
    (finishLe : finish ≤ elapsedTime initial (index + 1))
    (massLe : ∀ time ∈ Icc start finish,
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial (index + 1) time) ≤
        ceiling)
    (averageHigh :
      threshold * (finish - start) <
        ∫ time in start..finish,
          density
            (wholeRestartPrefixPhysicalTrajectory initial (index + 1) time)) :
    ∃ segmentInitial : ComplexVorticityHilbertState,
    ∃ segmentTime : Real,
    ∃ _segmentTimePos : 0 < segmentTime,
    ∃ segmentReceipt :
        WholeContinuousMildSerrinReceipt nu segmentInitial segmentTime,
    ∃ absoluteTime : Icc (0 : Real) segmentTime → Real,
      (∀ localTime,
        absoluteTime localTime ∈ Icc start finish ∧
        segmentReceipt.wholePath localTime =
          wholeRestartPrefixPhysicalTrajectory initial (index + 1)
            (absoluteTime localTime)) ∧
      (∀ localTime,
        wholeVorticityEuclideanMass (segmentReceipt.wholePath localTime) ≤
          ceiling) ∧
      segmentTime = finish - start ∧
      threshold * segmentTime <
        ∫ localTime,
          density (segmentReceipt.wholePath localTime)
            ∂(commonTimeMeasure segmentTime) := by
  let joinTime := elapsedTime initial index
  let sourceReceipt := (run initial index).contact.prefixReceipt
  let localStart := start - joinTime
  let localFinish := finish - joinTime
  have localStartNonneg : 0 ≤ localStart := by
    dsimp only [localStart, joinTime]
    exact sub_nonneg.mpr joinLeStart
  have localStartLtFinish : localStart < localFinish := by
    dsimp only [localStart, localFinish]
    exact sub_lt_sub_right startLtFinish joinTime
  have localFinishLe :
      localFinish ≤ (run initial index).contact.time.1 := by
    dsimp only [localFinish, joinTime]
    rw [elapsedTime_succ] at finishLe
    linarith
  have localStartLtSource :
      localStart < (run initial index).contact.time.1 :=
    localStartLtFinish.trans_le localFinishLe
  let suffixReceipt :=
    positiveTimeSuffixWholeContinuousMildSerrinReceipt
      sourceReceipt localStart localStartNonneg localStartLtSource
  have segmentTimePos : 0 < localFinish - localStart :=
    sub_pos.mpr localStartLtFinish
  have segmentTimeLe :
      localFinish - localStart ≤
        (run initial index).contact.time.1 - localStart :=
    sub_le_sub_right localFinishLe localStart
  let segmentReceipt :=
    restrictWholeContinuousMildSerrinReceipt
      segmentTimePos segmentTimeLe suffixReceipt
  let absoluteTime : Icc (0 : Real) (localFinish - localStart) → Real :=
    fun localTime => start + localTime.1
  have absoluteTimeMem
      (localTime : Icc (0 : Real) (localFinish - localStart)) :
      absoluteTime localTime ∈ Icc start finish := by
    constructor
    · exact le_add_of_nonneg_right localTime.2.1
    · dsimp only [absoluteTime]
      have localUpper := localTime.2.2
      dsimp only [localFinish, localStart] at localUpper
      linarith
  have sourceLocalTime
      (localTime : Icc (0 : Real) (localFinish - localStart)) :
      localStart + localTime.1 ∈
        Icc (0 : Real) (run initial index).contact.time.1 := by
    constructor
    · exact add_nonneg localStartNonneg localTime.2.1
    · have localUpper := localTime.2.2
      linarith
  have pathEq
      (localTime : Icc (0 : Real) (localFinish - localStart)) :
      segmentReceipt.wholePath localTime =
        wholeRestartPrefixPhysicalTrajectory initial (index + 1)
          (absoluteTime localTime) := by
    let sourceLocal : Icc (0 : Real) (run initial index).contact.time.1 :=
      ⟨localStart + localTime.1, sourceLocalTime localTime⟩
    have absoluteEq :
        absoluteTime localTime =
          elapsedTime initial index + sourceLocal.1 := by
      dsimp only [absoluteTime, sourceLocal, localStart, joinTime]
      ring_nf
    have chart :=
      wholeRestartPrefixPhysicalTrajectory_succ_eq_receipt_chart
        initial index sourceLocal
    rw [absoluteEq, chart]
    apply congrArg sourceReceipt.wholePath
    apply Subtype.ext
    rfl
  have sourceIntegralEq :
      (∫ time in start..finish,
          density
            (wholeRestartPrefixPhysicalTrajectory initial (index + 1) time)) =
        ∫ localTime in localStart..localFinish,
          density
            (wholeRestartReceiptPhysicalTrajectory sourceReceipt localTime) := by
    simpa only [localStart, localFinish, joinTime, sourceReceipt] using
      wholeRestartPrefixSuccStateIntegral_eq_receipt
        initial index density joinLeStart startLtFinish.le finishLe
  have windowIntegralEq :
      (∫ localTime,
          density (segmentReceipt.wholePath localTime)
            ∂(commonTimeMeasure (localFinish - localStart))) =
        ∫ localTime in localStart..localFinish,
          density
            (wholeRestartReceiptPhysicalTrajectory sourceReceipt localTime) := by
    rw [show
      (∫ localTime,
          density (segmentReceipt.wholePath localTime)
            ∂(commonTimeMeasure (localFinish - localStart))) =
        ∫ localTime in (0 : Real)..(localFinish - localStart),
          density
            (wholeRestartReceiptPhysicalTrajectory segmentReceipt localTime) by
        rw [← commonTime_integral_eq_intervalIntegral
          (localFinish - localStart) segmentTimePos.le]
        apply integral_congr_ae
        filter_upwards [] with localTime
        unfold wholeRestartReceiptPhysicalTrajectory
        rw [projIcc_of_mem segmentTimePos.le localTime.2]]
    calc
      (∫ localTime in (0 : Real)..(localFinish - localStart),
          density
            (wholeRestartReceiptPhysicalTrajectory segmentReceipt localTime)) =
          ∫ localTime in (0 : Real)..(localFinish - localStart),
            density
              (wholeRestartReceiptPhysicalTrajectory sourceReceipt
                (localStart + localTime)) := by
        apply intervalIntegral.integral_congr
        intro localTime localTimeMem
        have localTimeIcc :
            localTime ∈ Icc (0 : Real) (localFinish - localStart) := by
          simpa [uIcc_of_le segmentTimePos.le] using localTimeMem
        unfold wholeRestartReceiptPhysicalTrajectory
        change
          density
              (segmentReceipt.wholePath
                (projIcc 0 (localFinish - localStart)
                  segmentReceipt.requestedTimePos.le localTime)) =
            density
              (sourceReceipt.wholePath
                (projIcc 0 (run initial index).contact.time.1
                  sourceReceipt.requestedTimePos.le
                  (localStart + localTime)))
        rw [projIcc_of_mem segmentTimePos.le localTimeIcc]
        have shiftedMem :
            localStart + localTime ∈
              Icc (0 : Real) (run initial index).contact.time.1 :=
          sourceLocalTime ⟨localTime, localTimeIcc⟩
        rw [projIcc_of_mem sourceReceipt.requestedTimePos.le shiftedMem]
        rfl
      _ = ∫ localTime in localStart..localFinish,
          density
            (wholeRestartReceiptPhysicalTrajectory sourceReceipt localTime) := by
        have shifted :=
          intervalIntegral.integral_comp_add_left
            (f := fun localTime : Real =>
              density
                (wholeRestartReceiptPhysicalTrajectory sourceReceipt localTime))
            (a := 0) (b := localFinish - localStart) localStart
        convert shifted using 1
        all_goals ring_nf
  refine ⟨_, localFinish - localStart, segmentTimePos, segmentReceipt,
    absoluteTime, ?_, ?_, ?_, ?_⟩
  · intro localTime
    exact ⟨absoluteTimeMem localTime, pathEq localTime⟩
  · intro localTime
    rw [pathEq localTime]
    exact massLe _ (absoluteTimeMem localTime)
  · dsimp only [localFinish, localStart, joinTime]
    ring_nf
  · rw [windowIntegralEq, ← sourceIntegralEq]
    rw [show localFinish - localStart = finish - start by
      dsimp only [localFinish, localStart, joinTime]
      ring_nf]
    exact averageHigh

private theorem wholeRestartPrefix_rateAverage_selects_actualSubreceipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ (length : Nat)
      (density : ComplexVorticityHilbertState → Real)
      {threshold ceiling start finish : Real},
      0 ≤ start →
      start < finish →
      finish ≤ elapsedTime initial length →
      ContinuousOn
          (fun time => density
            (wholeRestartPrefixPhysicalTrajectory initial length time))
          (Icc start finish) →
      (∀ time ∈ Icc start finish,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          ceiling) →
      threshold * (finish - start) <
        ∫ time in start..finish,
          density
            (wholeRestartPrefixPhysicalTrajectory initial length time) →
      ∃ edge : Nat,
      ∃ segmentInitial : ComplexVorticityHilbertState,
      ∃ segmentTime : Real,
      ∃ _segmentTimePos : 0 < segmentTime,
      ∃ segmentReceipt :
          WholeContinuousMildSerrinReceipt nu segmentInitial segmentTime,
      ∃ absoluteTime : Icc (0 : Real) segmentTime → Real,
        edge < length ∧
        (∀ localTime,
          absoluteTime localTime ∈ Icc start finish ∧
          segmentReceipt.wholePath localTime =
            wholeRestartPrefixPhysicalTrajectory initial length
              (absoluteTime localTime)) ∧
        (∀ localTime,
          wholeVorticityEuclideanMass (segmentReceipt.wholePath localTime) ≤
            ceiling) ∧
        segmentTime ≤ finish - start ∧
        threshold * segmentTime <
          ∫ localTime,
            density (segmentReceipt.wholePath localTime)
              ∂(commonTimeMeasure segmentTime) := by
  intro length
  induction length with
  | zero =>
      intro density threshold ceiling start finish startNonneg startLtFinish
        finishLe _continuous _massLe _averageHigh
      rw [elapsedTime_zero] at finishLe
      linarith
  | succ index ih =>
      intro density threshold ceiling start finish startNonneg startLtFinish
        finishLe densityContinuous massLe averageHigh
      let joinTime := elapsedTime initial index
      have joinNonneg : 0 ≤ joinTime :=
        ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
          initial index
      have priorChart
          (time : Real) (timeLeJoin : time ≤ joinTime) :
          wholeRestartPrefixPhysicalTrajectory initial (index + 1) time =
            wholeRestartPrefixPhysicalTrajectory initial index time := by
        simp only [wholeRestartPrefixPhysicalTrajectory]
        exact
          ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice.endpointSplice_of_le
            joinTime
            (wholeRestartPrefixPhysicalTrajectory initial index)
            (wholeRestartReceiptPhysicalTrajectory
              (run initial index).contact.prefixReceipt)
            time timeLeJoin
      by_cases finishLeJoin : finish ≤ joinTime
      · have priorContinuous :
            ContinuousOn
              (fun time => density
                (wholeRestartPrefixPhysicalTrajectory initial index time))
              (Icc start finish) := by
          apply densityContinuous.congr
          intro time timeMem
          exact congrArg density
            (priorChart time (timeMem.2.trans finishLeJoin)).symm
        have priorMassLe : ∀ time ∈ Icc start finish,
            wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial index time) ≤
              ceiling := by
          intro time timeMem
          have generated := massLe time timeMem
          rw [priorChart time (timeMem.2.trans finishLeJoin)] at generated
          exact generated
        have priorIntegralEq :
            (∫ time in start..finish,
                density
                  (wholeRestartPrefixPhysicalTrajectory initial index time)) =
              ∫ time in start..finish,
                density
                  (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                    time) := by
          apply intervalIntegral.integral_congr
          intro time timeMem
          have timeIcc : time ∈ Icc start finish := by
            simpa [uIcc_of_le startLtFinish.le] using timeMem
          exact congrArg density
            (priorChart time (timeIcc.2.trans finishLeJoin)).symm
        have priorAverage :
            threshold * (finish - start) <
              ∫ time in start..finish,
                density
                  (wholeRestartPrefixPhysicalTrajectory initial index time) := by
          rw [priorIntegralEq]
          exact averageHigh
        obtain ⟨edge, segmentInitial, segmentTime, segmentTimePos,
            segmentReceipt, absoluteTime, edgeLt, chart, segmentMassLe,
            segmentDurationLe, segmentAverage⟩ :=
          ih density startNonneg startLtFinish finishLeJoin priorContinuous
            priorMassLe priorAverage
        refine ⟨edge, segmentInitial, segmentTime, segmentTimePos,
          segmentReceipt, absoluteTime, edgeLt.trans (Nat.lt_succ_self index),
          ?_, segmentMassLe, segmentDurationLe, segmentAverage⟩
        intro localTime
        have generated := chart localTime
        refine ⟨generated.1, generated.2.trans ?_⟩
        exact (priorChart (absoluteTime localTime)
          (generated.1.2.trans finishLeJoin)).symm
      · have joinLtFinish : joinTime < finish := lt_of_not_ge finishLeJoin
        by_cases joinLeStart : joinTime ≤ start
        · obtain ⟨segmentInitial, segmentTime, segmentTimePos,
              segmentReceipt, absoluteTime, chart, segmentMassLe,
              segmentDurationEq, segmentAverage⟩ :=
            wholeRestartPrefix_lastReceiptAverageSubreceipt initial index
              density threshold ceiling start finish joinLeStart
              startLtFinish finishLe massLe averageHigh
          exact ⟨index, segmentInitial, segmentTime, segmentTimePos,
            segmentReceipt, absoluteTime, Nat.lt_succ_self index,
            chart, segmentMassLe, segmentDurationEq.le, segmentAverage⟩
        · have startLtJoin : start < joinTime := lt_of_not_ge joinLeStart
          have leftContinuous :
              ContinuousOn
                (fun time => density
                  (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                    time))
                (Icc start joinTime) :=
            densityContinuous.mono
              (Icc_subset_Icc le_rfl joinLtFinish.le)
          have rightContinuous :
              ContinuousOn
                (fun time => density
                  (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                    time))
                (Icc joinTime finish) :=
            densityContinuous.mono
              (Icc_subset_Icc startLtJoin.le le_rfl)
          have leftIntegrable :
              IntervalIntegrable
                (fun time => density
                  (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                    time)) volume start joinTime :=
            leftContinuous.intervalIntegrable_of_Icc startLtJoin.le
          have rightIntegrable :
              IntervalIntegrable
                (fun time => density
                  (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                    time)) volume joinTime finish :=
            rightContinuous.intervalIntegrable_of_Icc joinLtFinish.le
          have integralSplit :
              (∫ time in start..finish,
                  density
                    (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                      time)) =
                (∫ time in start..joinTime,
                  density
                    (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                      time)) +
                ∫ time in joinTime..finish,
                  density
                    (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                      time) := by
            exact (intervalIntegral.integral_add_adjacent_intervals
              leftIntegrable rightIntegrable).symm
          by_cases leftAverage :
              threshold * (joinTime - start) <
                ∫ time in start..joinTime,
                  density
                    (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                      time)
          · have priorLeftContinuous :
                ContinuousOn
                  (fun time => density
                    (wholeRestartPrefixPhysicalTrajectory initial index time))
                  (Icc start joinTime) := by
              apply leftContinuous.congr
              intro time timeMem
              exact congrArg density (priorChart time timeMem.2).symm
            have priorLeftMass : ∀ time ∈ Icc start joinTime,
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial index time) ≤
                  ceiling := by
              intro time timeMem
              have generated := massLe time
                ⟨timeMem.1, timeMem.2.trans joinLtFinish.le⟩
              rw [priorChart time timeMem.2] at generated
              exact generated
            have priorLeftIntegralEq :
                (∫ time in start..joinTime,
                    density
                      (wholeRestartPrefixPhysicalTrajectory initial index time)) =
                  ∫ time in start..joinTime,
                    density
                      (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                        time) := by
              apply intervalIntegral.integral_congr
              intro time timeMem
              have timeIcc : time ∈ Icc start joinTime := by
                simpa [uIcc_of_le startLtJoin.le] using timeMem
              exact congrArg density (priorChart time timeIcc.2).symm
            have priorLeftAverage :
                threshold * (joinTime - start) <
                  ∫ time in start..joinTime,
                    density
                      (wholeRestartPrefixPhysicalTrajectory initial index time) := by
              rw [priorLeftIntegralEq]
              exact leftAverage
            obtain ⟨edge, segmentInitial, segmentTime, segmentTimePos,
                segmentReceipt, absoluteTime, edgeLt, chart, segmentMassLe,
                segmentDurationLe, segmentAverage⟩ :=
              ih density startNonneg startLtJoin (le_refl joinTime)
                priorLeftContinuous priorLeftMass priorLeftAverage
            refine ⟨edge, segmentInitial, segmentTime, segmentTimePos,
              segmentReceipt, absoluteTime,
              edgeLt.trans (Nat.lt_succ_self index), ?_, segmentMassLe,
              segmentDurationLe.trans
                (sub_le_sub_right joinLtFinish.le start), segmentAverage⟩
            intro localTime
            have generated := chart localTime
            refine ⟨⟨generated.1.1,
              generated.1.2.trans joinLtFinish.le⟩, generated.2.trans ?_⟩
            exact (priorChart (absoluteTime localTime) generated.1.2).symm
          · have rightAverage :
                threshold * (finish - joinTime) <
                  ∫ time in joinTime..finish,
                    density
                      (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                        time) := by
              have leftLe := le_of_not_gt leftAverage
              rw [integralSplit] at averageHigh
              nlinarith
            have rightMass : ∀ time ∈ Icc joinTime finish,
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial (index + 1)
                      time) ≤ ceiling := by
              intro time timeMem
              exact massLe time
                ⟨startLtJoin.le.trans timeMem.1, timeMem.2⟩
            obtain ⟨segmentInitial, segmentTime, segmentTimePos,
                segmentReceipt, absoluteTime, chart, segmentMassLe,
                segmentDurationEq, segmentAverage⟩ :=
              wholeRestartPrefix_lastReceiptAverageSubreceipt initial index
                density threshold ceiling joinTime finish (le_refl joinTime)
                joinLtFinish finishLe rightMass rightAverage
            refine ⟨index, segmentInitial, segmentTime, segmentTimePos,
              segmentReceipt, absoluteTime, Nat.lt_succ_self index, ?_,
              segmentMassLe, ?_, segmentAverage⟩
            intro localTime
            have generated := chart localTime
            exact ⟨⟨startLtJoin.le.trans generated.1.1, generated.1.2⟩,
              generated.2⟩
            rw [segmentDurationEq]
            exact sub_le_sub (le_refl finish) startLtJoin.le

private theorem projectedWork_eq_stretchingWork_of_negClosed
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    (∑ wave ∈ modes,
      complexCoordinateRealInner
        (complexSharpSupportProjection modes state wave)
        (wholeStateVorticityNonlinearCoefficientAt
          (complexSharpSupportProjection modes state) wave)) =
      finiteStateVorticityStretchingWork
        modes (complexSharpSupportProjection modes state) := by
  let projected := complexSharpSupportProjection modes state
  have projectedReality : FiniteStateFourierReality projected := by
    intro wave
    have negMemIff : waveNeg wave ∈ modes ↔ wave ∈ modes := by
      constructor
      · intro negMem
        simpa using negClosed (waveNeg wave) negMem
      · exact negClosed wave
    dsimp only [projected]
    rw [complexSharpSupportProjection_apply,
      complexSharpSupportProjection_apply]
    by_cases waveMem : wave ∈ modes
    · rw [if_pos waveMem, if_pos (negMemIff.mpr waveMem), reality]
    · rw [if_neg waveMem, if_neg (not_congr negMemIff |>.mpr waveMem)]
      exact vectorConj_zero.symm
  change
    (∑ wave ∈ modes,
      complexCoordinateRealInner (projected wave)
        (wholeStateVorticityNonlinearCoefficientAt projected wave)) =
      finiteStateVorticityStretchingWork modes projected
  rw [← finiteStateVorticityNonlinearWork_eq_stretchingWork
    modes negClosed projected projectedReality]
  unfold finiteStateVorticityNonlinearWork
  apply Finset.sum_congr rfl
  intro wave _waveMem
  congr 1
  rw [show projected = complexSharpSupportProjection modes state by rfl,
    wholeStateVorticityNonlinearCoefficientAt_projection_eq_finite]
  symm
  exact finiteStateVorticityNonlinearCoefficientAt_projection_of_subset
    (Finset.Subset.rfl) state wave
private theorem
    integerWaveFrequencyCube_projectedWork_eq_puncturedStretchingWork
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (reality : FiniteStateFourierReality state) :
    (∑ wave ∈ integerWaveFrequencyCube radius,
      complexCoordinateRealInner
        (complexSharpSupportProjection
          (integerWaveFrequencyCube radius) state wave)
        (wholeStateVorticityNonlinearCoefficientAt
          (complexSharpSupportProjection
            (integerWaveFrequencyCube radius) state) wave)) =
      finiteStateVorticityStretchingWork
        (wholeRestartModes radius)
        (complexSharpSupportProjection (wholeRestartModes radius) state) := by
  let fullModes := integerWaveFrequencyCube radius
  let modes := wholeRestartModes radius
  let projected := complexSharpSupportProjection modes state
  have projectionEq :
      complexSharpSupportProjection fullModes state = projected := by
    dsimp only [fullModes, modes, projected, wholeRestartModes,
      puncturedIntegerWaveFrequencyCube]
    exact (complexSharpSupportProjection_erase_zero_eq
      (integerWaveFrequencyCube radius) state zeroRow).symm
  have zeroMem : (0 : IntegerWavevector) ∈ fullModes := by
    dsimp only [fullModes]
    simp [integerWaveFrequencyCube, Fintype.mem_piFinset]
  have zeroTerm :
      complexCoordinateRealInner (projected 0)
        (wholeStateVorticityNonlinearCoefficientAt projected 0) = 0 := by
    have projectedZero : projected 0 = 0 := by
      dsimp only [projected, modes, wholeRestartModes,
        puncturedIntegerWaveFrequencyCube]
      simp [complexSharpSupportProjection_apply]
    rw [projectedZero]
    simp [complexCoordinateRealInner]
  have negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes := by
    intro wave waveMem
    dsimp only [modes, wholeRestartModes]
    exact puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
  change
    (∑ wave ∈ fullModes,
      complexCoordinateRealInner
        ((complexSharpSupportProjection fullModes state) wave)
        (wholeStateVorticityNonlinearCoefficientAt
          (complexSharpSupportProjection fullModes state) wave)) =
      finiteStateVorticityStretchingWork modes projected
  rw [projectionEq]
  let work : IntegerWavevector → Real := fun wave =>
    complexCoordinateRealInner (projected wave)
      (wholeStateVorticityNonlinearCoefficientAt projected wave)
  have workZero : work 0 = 0 := by
    exact zeroTerm
  calc
    (∑ wave ∈ fullModes,
        complexCoordinateRealInner (projected wave)
          (wholeStateVorticityNonlinearCoefficientAt projected wave)) =
        ∑ wave ∈ fullModes.erase 0,
          complexCoordinateRealInner (projected wave)
            (wholeStateVorticityNonlinearCoefficientAt projected wave) := by
      have eraseAdd :=
        Finset.sum_erase_add (s := fullModes) (f := work) zeroMem
      rw [workZero, add_zero] at eraseAdd
      exact eraseAdd.symm
    _ = ∑ wave ∈ modes,
          complexCoordinateRealInner (projected wave)
            (wholeStateVorticityNonlinearCoefficientAt projected wave) := by
      rfl
    _ = finiteStateVorticityStretchingWork modes projected := by
      exact projectedWork_eq_stretchingWork_of_negClosed
        modes negClosed state reality

private theorem integerWaveFrequencyCube_viscousSum_eq_puncturedEnstrophy
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (_zeroRow : state 0 = 0) :
    (∑ wave ∈ integerWaveFrequencyCube radius,
      integerWaveViscousMultiplier wave *
        complexCoordinateAmplitudeSq (state wave)) =
      (2 * Real.pi) ^ 2 *
        finiteStateVorticityEnstrophyMass
          (wholeRestartModes radius)
          (complexSharpSupportProjection (wholeRestartModes radius) state) := by
  let fullModes := integerWaveFrequencyCube radius
  let modes := wholeRestartModes radius
  let projected := complexSharpSupportProjection modes state
  let density : IntegerWavevector → Real := fun wave =>
    integerWaveViscousMultiplier wave *
      complexCoordinateAmplitudeSq (state wave)
  have zeroMem : (0 : IntegerWavevector) ∈ fullModes := by
    dsimp only [fullModes]
    simp [integerWaveFrequencyCube, Fintype.mem_piFinset]
  have densityZero : density 0 = 0 := by
    dsimp only [density, integerWaveViscousMultiplier]
    simp [integerWaveNormSq]
  calc
    (∑ wave ∈ integerWaveFrequencyCube radius,
        integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq (state wave)) =
        ∑ wave ∈ fullModes, density wave := by rfl
    _ = ∑ wave ∈ fullModes.erase 0, density wave := by
      have erased := Finset.sum_erase_add (s := fullModes)
        (f := density) zeroMem
      rw [densityZero, add_zero] at erased
      exact erased.symm
    _ = (2 * Real.pi) ^ 2 *
        finiteStateVorticityEnstrophyMass modes projected := by
      unfold finiteStateVorticityEnstrophyMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave waveMem
      have waveMemModes : wave ∈ modes := by
        simpa only [modes, fullModes, wholeRestartModes,
          puncturedIntegerWaveFrequencyCube] using waveMem
      dsimp only [density, integerWaveViscousMultiplier, projected]
      rw [complexSharpSupportProjection_apply, if_pos waveMemModes]
      ring

private theorem finiteInputRateDensity_eq_puncturedStretchingRate
    (nu : Viscosity)
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (reality : FiniteStateFourierReality state) :
    finiteInputRateDensity nu (integerWaveFrequencyCube radius) state =
      2 * nu.coeff *
        (finiteStateVorticityStretchingWork
            (wholeRestartModes radius)
            (complexSharpSupportProjection (wholeRestartModes radius) state) -
          (nu.coeff * (2 * Real.pi) ^ 2 / 2) *
            finiteStateVorticityEnstrophyMass
              (wholeRestartModes radius)
              (complexSharpSupportProjection
                (wholeRestartModes radius) state)) := by
  unfold finiteInputRateDensity finiteInputAutonomousWorkDensity
  rw [integerWaveFrequencyCube_projectedWork_eq_puncturedStretchingWork
      radius state zeroRow reality,
    integerWaveFrequencyCube_viscousSum_eq_puncturedEnstrophy
      radius state zeroRow]
  ring

private theorem receipt_finiteInputRateDensity_ae_eq_puncturedStretchingRate
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      finiteInputRateDensity nu (integerWaveFrequencyCube radius)
          (receipt.wholePath time) =
        2 * nu.coeff *
          (finiteStateVorticityStretchingWork
              (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (receipt.wholePath time)) -
            (nu.coeff * (2 * Real.pi) ^ 2 / 2) *
              finiteStateVorticityEnstrophyMass
                (wholeRestartModes radius)
                (complexSharpSupportProjection (wholeRestartModes radius)
                  (receipt.wholePath time))) := by
  filter_upwards [wholePath_fourierReality_ae receipt] with time reality
  exact finiteInputRateDensity_eq_puncturedStretchingRate
    nu radius (receipt.wholePath time) (receipt.wholePath_zero_row time) reality

private theorem receipt_finiteInputRateDensity_integral_eq_puncturedStretchingRate
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat) :
    (∫ time,
        finiteInputRateDensity nu (integerWaveFrequencyCube radius)
          (receipt.wholePath time)
        ∂(commonTimeMeasure requestedTime)) =
      ∫ time,
        2 * nu.coeff *
          (finiteStateVorticityStretchingWork
              (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (receipt.wholePath time)) -
            (nu.coeff * (2 * Real.pi) ^ 2 / 2) *
              finiteStateVorticityEnstrophyMass
                (wholeRestartModes radius)
                (complexSharpSupportProjection (wholeRestartModes radius)
                  (receipt.wholePath time)))
        ∂(commonTimeMeasure requestedTime) := by
  apply integral_congr_ae
  exact receipt_finiteInputRateDensity_ae_eq_puncturedStretchingRate
    receipt radius

/-- A source-generated last-hit window contains two separated actual states
and a common finite input cube on which the retained nonlinear rate pays a
fixed fraction of the source level.  The projection error and the viscous
debit are both settled by the same whole-prefix NS ledger. -/
private theorem sourceGeneratedNativeAccumulationScaleCriticalFiniteInputRateQuantum
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (level : Real)
    (levelPos : 0 < level)
    (initialLeHalf :
      restartPhysicalVorticityMass initial 0 ≤ level / 2) :
    let viscousConstant : Real :=
      nu.coeff ^ 2 * (2 * Real.pi) ^ 2
    let cubicConstant : Real :=
      (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
        (2 * viscousConstant)
    let gradientConstant : Real :=
      (2 * cubicConstant) / viscousConstant
    let errorSlope : Real :=
      (128 * 4368 * biotSavartSerrinConstant * cubicConstant) /
        (7 * nu.coeff * viscousConstant)
    ∃ length radius : Nat, ∃ lowerTime upperTime : Real,
      0 ≤ lowerTime ∧
      lowerTime < upperTime ∧
      upperTime ≤ elapsedTime initial length ∧
      (∀ time ∈
          Icc (elapsedTime initial 1) (elapsedTime initial length),
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          level + 2) ∧
      0 < radius ∧
      (8 * (gradientConstant +
            errorSlope * (level ^ 2 * (upperTime - lowerTime)) / 8 + 1) *
          level ≤ (radius : Real)) ∧
      ((radius : Real) ≤
        8 * (gradientConstant +
            errorSlope * (level ^ 2 * (upperTime - lowerTime)) / 8 + 1) *
          level + 2) ∧
      (7 * level / 64 ≤
        finiteStateVorticityCoefficientEnstrophy
            (integerWaveFrequencyCube radius)
            (wholeRestartPrefixPhysicalTrajectory initial length upperTime) -
          finiteStateVorticityCoefficientEnstrophy
            (integerWaveFrequencyCube radius)
            (wholeRestartPrefixPhysicalTrajectory initial length lowerTime)) ∧
      (∀ time ∈ Icc lowerTime upperTime,
        level / 2 ≤ wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ∧
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          level) ∧
      nu.coeff / (8 * cubicConstant) ≤
        level ^ 2 * (upperTime - lowerTime) ∧
      7 * nu.coeff * level / 128 ≤
        ∫ time in lowerTime..upperTime,
          finiteInputRateDensity nu (integerWaveFrequencyCube radius)
            (wholeRestartPrefixPhysicalTrajectory initial length time) := by
  dsimp only
  let viscousConstant : Real :=
    nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let cubicConstant : Real :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * viscousConstant)
  let gradientConstant : Real :=
    (2 * cubicConstant) / viscousConstant
  let errorSlope : Real :=
    (128 * 4368 * biotSavartSerrinConstant * cubicConstant) /
      (7 * nu.coeff * viscousConstant)
  have viscousConstantPos : 0 < viscousConstant := by
    dsimp only [viscousConstant]
    exact mul_pos (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
  have cubicConstantNonneg : 0 ≤ cubicConstant := by
    dsimp only [cubicConstant]
    positivity
  have cubicConstantPos : 0 < cubicConstant := by
    dsimp only [cubicConstant]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) (by norm_num))
        (sq_pos_of_pos biotSavartSerrinConstant_pos))
      (mul_pos (by norm_num) viscousConstantPos)
  have gradientConstantNonneg : 0 ≤ gradientConstant := by
    dsimp only [gradientConstant]
    positivity
  have errorSlopeNonneg : 0 ≤ errorSlope := by
    dsimp only [errorSlope]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (by norm_num))
          biotSavartSerrinConstant_nonneg)
        cubicConstantNonneg)
      (mul_nonneg
        (mul_nonneg (by norm_num) nu.coeff_pos.le)
        viscousConstantPos.le)
  obtain ⟨_start, finish, beginTime, endTime, _startLtFinish,
      beginMem, endMem, beginLtEnd, beginMass, endMass,
      interiorMass, prehistoryCeiling, _scaleSpan⟩ :=
    sourceGeneratedNativeAccumulationScaleCriticalLastHitWindow
      initial elapsedBounded level levelPos initialLeHalf
  let length : Nat := finish + 1
  let mass : Real → Real := fun time =>
    wholeVorticityEuclideanMass
      (wholeRestartPrefixPhysicalTrajectory initial length time)
  have beginNonneg : 0 ≤ beginTime :=
    (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory.elapsedTime_nonneg
      initial (_start + 1)).trans beginMem.1
  have massContinuous : ContinuousOn mass (Icc beginTime endTime) := by
    exact continuous_wholeVorticityEuclideanMass.comp_continuousOn
      ((wholeRestartPrefixPhysicalTrajectory_continuousOn initial length).mono
        (Icc_subset_Icc beginNonneg endMem.2))
  obtain ⟨lowerStart, lowerFinish, upperStart, upperFinish,
      lowerStartMem, lowerFinishMem, upperStartMem, upperFinishMem,
      lowerStartLtFinish, lowerFinishLtUpperStart, upperStartLtFinish,
      lowerStartMass, lowerFinishMass, upperStartMass, upperFinishMass,
      lowerInterior, upperInterior⟩ :=
    continuous_mass_path_has_two_separated_good_windows
      beginLtEnd.le levelPos mass massContinuous beginMass endMass
  have upperStartNonneg : 0 ≤ upperStart :=
    beginNonneg.trans
      (lowerFinishMem.1.trans upperStartMem.1)
  have upperFinishLe : upperFinish ≤ elapsedTime initial length :=
    upperFinishMem.2.trans endMem.2
  have upperMassLeEnd :
      ∀ time ∈ Icc upperStart upperFinish,
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length upperFinish) := by
    intro time timeMem
    dsimp only [mass] at upperInterior upperFinishMass
    rw [upperFinishMass]
    exact (upperInterior time timeMem).2
  obtain ⟨edge, segmentInitial, segmentTime, segmentTimePos,
      segmentReceipt, absoluteTime, edgeLt, pathChart,
      endpointNondecreasing⟩ :=
    lastHitWindow_generates_actualNondecreasingSubreceipt
      initial length upperStart upperFinish upperStartNonneg
        upperStartLtFinish upperFinishLe upperMassLeEnd
  have segmentMassBand (localTime : Icc (0 : Real) segmentTime) :
      3 * level / 4 ≤
          wholeVorticityEuclideanMass
            (segmentReceipt.wholePath localTime) ∧
        wholeVorticityEuclideanMass
            (segmentReceipt.wholePath localTime) ≤ 13 * level / 16 := by
    rw [(pathChart localTime).2]
    dsimp only [mass] at upperInterior
    exact upperInterior _ (pathChart localTime).1
  obtain ⟨sample, sampleMassLower, sampleMassUpper,
      sampleGradientSummable, sampleGradientBound⟩ :=
    receipt_mass_band_selects_gradient_bound segmentReceipt
      segmentMassBand endpointNondecreasing
  let lowerTime : Real := lowerFinish
  let upperTime : Real := absoluteTime sample
  have lowerNonneg : 0 ≤ lowerTime :=
    beginNonneg.trans lowerFinishMem.1
  have lowerLtUpper : lowerTime < upperTime := by
    dsimp only [lowerTime, upperTime]
    exact lowerFinishLtUpperStart.trans_le (pathChart sample).1.1
  have upperLeElapsed : upperTime ≤ elapsedTime initial length := by
    dsimp only [upperTime]
    exact (pathChart sample).1.2.trans upperFinishLe
  have upperPathEq :
      segmentReceipt.wholePath sample =
        wholeRestartPrefixPhysicalTrajectory initial length upperTime := by
    exact (pathChart sample).2
  have lowerMassEq :
      wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial length lowerTime) =
        5 * level / 8 := by
    simpa only [mass, lowerTime] using lowerFinishMass
  have upperMassLower :
      3 * level / 4 ≤
        wholeVorticityEuclideanMass
          (wholeRestartPrefixPhysicalTrajectory initial length upperTime) := by
    rw [← upperPathEq]
    exact sampleMassLower
  have upperGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (wholeRestartPrefixPhysicalTrajectory initial length upperTime wave) := by
    simpa only [← upperPathEq] using sampleGradientSummable
  have sampleGradientBound' :
      wholeStateVorticityGradientMass
          (wholeRestartPrefixPhysicalTrajectory initial length upperTime) ≤
        gradientConstant * (13 * level / 16) ^ 3 := by
    rw [← upperPathEq]
    simpa only [gradientConstant, cubicConstant, viscousConstant] using
      sampleGradientBound
  let normalizedDuration : Real := level ^ 2 * (upperTime - lowerTime)
  have normalizedDurationPos : 0 < normalizedDuration := by
    dsimp only [normalizedDuration]
    exact mul_pos (sq_pos_of_pos levelPos) (sub_pos.mpr lowerLtUpper)
  let adjustedGradientConstant : Real :=
    gradientConstant + errorSlope * normalizedDuration / 8
  have adjustedGradientConstantNonneg : 0 ≤ adjustedGradientConstant := by
    dsimp only [adjustedGradientConstant]
    positivity
  have upperGradientBound :
      wholeStateVorticityGradientMass
          (wholeRestartPrefixPhysicalTrajectory initial length upperTime) ≤
        adjustedGradientConstant * level ^ 3 := by
    calc
      wholeStateVorticityGradientMass
            (wholeRestartPrefixPhysicalTrajectory initial length upperTime) ≤
          gradientConstant * (13 * level / 16) ^ 3 :=
        sampleGradientBound'
      _ ≤ gradientConstant * level ^ 3 := by
        gcongr
        nlinarith
      _ ≤ adjustedGradientConstant * level ^ 3 := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right
            (div_nonneg
              (mul_nonneg errorSlopeNonneg normalizedDurationPos.le)
              (by norm_num)))
          (pow_nonneg levelPos.le 3)
  obtain ⟨radius, radiusPos, radiusLower, radiusUpper, finiteGap⟩ :=
    separated_good_endpoints_generate_finite_inventory_gap
      level adjustedGradientConstant levelPos adjustedGradientConstantNonneg
      (wholeRestartPrefixPhysicalTrajectory initial length lowerTime)
      (wholeRestartPrefixPhysicalTrajectory initial length upperTime)
      (by rw [lowerMassEq]) upperMassLower upperGradientSummable
      upperGradientBound
  let modes := integerWaveFrequencyCube radius
  have sourceMassBand :
      ∀ time ∈ Icc lowerTime upperTime,
        level / 2 ≤ wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ∧
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          level := by
    intro time timeMem
    exact interiorMass time
      ⟨lowerFinishMem.1.trans timeMem.1,
        timeMem.2.trans ((pathChart sample).1.2.trans upperFinishMem.2)⟩
  obtain ⟨energy, energyNonneg, signedEnergy, rateWithError,
      projectionError⟩ :=
    wholeRestartPrefixFiniteInputWorkEnergy initial length radius lowerNonneg
      lowerLtUpper upperLeElapsed levelPos.le radiusPos
        (fun time timeMem => (sourceMassBand time timeMem).2)
  have massGain :
      level / 8 ≤
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length upperTime) -
          wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length lowerTime) := by
    rw [lowerMassEq]
    linarith
  have energyLe : energy ≤ cubicConstant * normalizedDuration * level := by
    have massGainNonneg :
        0 ≤ nu.coeff *
          (wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length upperTime) -
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length lowerTime)) := by
      exact mul_nonneg nu.coeff_pos.le
        ((div_nonneg levelPos.le (by norm_num)).trans massGain)
    have raw :
        energy ≤ cubicConstant *
          (level ^ 3 * (upperTime - lowerTime)) := by
      simpa only [cubicConstant, viscousConstant] using
        signedEnergy.trans' (le_add_of_nonneg_right massGainNonneg)
    calc
      energy ≤ cubicConstant *
          (level ^ 3 * (upperTime - lowerTime)) := raw
      _ = cubicConstant * normalizedDuration * level := by
        dsimp only [normalizedDuration]
        ring
  have normalizedDurationLower :
      nu.coeff / (8 * cubicConstant) ≤ normalizedDuration := by
    have scaledMassGain :
        nu.coeff * (level / 8) ≤
          nu.coeff *
            (wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length upperTime) -
              wholeVorticityEuclideanMass
                (wholeRestartPrefixPhysicalTrajectory initial length lowerTime)) :=
      mul_le_mul_of_nonneg_left massGain nu.coeff_pos.le
    have paid :
        nu.coeff * (level / 8) ≤
          cubicConstant * normalizedDuration * level := by
      calc
        nu.coeff * (level / 8) ≤
            nu.coeff *
              (wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length upperTime) -
                wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length lowerTime)) :=
          scaledMassGain
        _ ≤ energy + nu.coeff *
              (wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length upperTime) -
                wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length lowerTime)) :=
          le_add_of_nonneg_left energyNonneg
        _ ≤ cubicConstant * normalizedDuration * level := by
          calc
            _ ≤ cubicConstant *
                (level ^ 3 * (upperTime - lowerTime)) := by
              simpa only [cubicConstant, viscousConstant] using signedEnergy
            _ = cubicConstant * normalizedDuration * level := by
              dsimp only [normalizedDuration]
              ring
    have paidNormalized :
        nu.coeff / 8 ≤ cubicConstant * normalizedDuration := by
      apply le_of_mul_le_mul_right _ levelPos
      calc
        (nu.coeff / 8) * level = nu.coeff * (level / 8) := by ring
        _ ≤ cubicConstant * normalizedDuration * level := paid
    calc
      nu.coeff / (8 * cubicConstant) =
          (nu.coeff / 8) / cubicConstant := by ring
      _ ≤ normalizedDuration :=
        (div_le_iff₀ cubicConstantPos).2
          (by simpa only [mul_comm] using paidNormalized)
  have radiusRealPos : 0 < (radius : Real) := by
    exact_mod_cast radiusPos
  have errorRadiusLower :
      errorSlope * normalizedDuration * level ≤ (radius : Real) := by
    calc
      errorSlope * normalizedDuration * level =
          8 * (errorSlope * normalizedDuration / 8) * level := by ring
      _ ≤ 8 * adjustedGradientConstant * level := by
        gcongr
        dsimp only [adjustedGradientConstant]
        linarith [gradientConstantNonneg]
      _ ≤ 8 * (adjustedGradientConstant + 1) * level := by
        gcongr
        linarith
      _ ≤ (radius : Real) := radiusLower
  have errorFactorNonneg :
      0 ≤
        (4368 * biotSavartSerrinConstant * level * (radius : Real)⁻¹) /
          viscousConstant := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
          levelPos.le)
        (inv_nonneg.mpr radiusRealPos.le))
      viscousConstantPos.le
  have errorIntegralLeEnergy :
      (∫ time in lowerTime..upperTime,
          finiteInputProjectionErrorDensity modes
            (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
        ((4368 * biotSavartSerrinConstant * level * (radius : Real)⁻¹) /
          viscousConstant) * energy := by
    simpa only [modes, viscousConstant] using projectionError
  have errorIntegralLeRaw :
      (∫ time in lowerTime..upperTime,
          finiteInputProjectionErrorDensity modes
            (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
        ((4368 * biotSavartSerrinConstant * level * (radius : Real)⁻¹) /
          viscousConstant) *
          (cubicConstant * normalizedDuration * level) :=
    errorIntegralLeEnergy.trans
      (mul_le_mul_of_nonneg_left energyLe errorFactorNonneg)
  have errorIntegralLe :
      (∫ time in lowerTime..upperTime,
          finiteInputProjectionErrorDensity modes
            (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
        7 * nu.coeff * level / 128 := by
    apply errorIntegralLeRaw.trans
    rw [show
      ((4368 * biotSavartSerrinConstant * level * (radius : Real)⁻¹) /
          viscousConstant) *
          (cubicConstant * normalizedDuration * level) =
        (4368 * biotSavartSerrinConstant * level *
          (cubicConstant * normalizedDuration * level)) /
            ((radius : Real) * viscousConstant) by
      field_simp [radiusRealPos.ne', viscousConstantPos.ne']]
    rw [div_le_iff₀ (mul_pos radiusRealPos viscousConstantPos)]
    have multiplierNonneg :
        0 ≤ (7 * nu.coeff * level / 128) * viscousConstant :=
      mul_nonneg
        (div_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) nu.coeff_pos.le)
            levelPos.le)
          (by norm_num))
        viscousConstantPos.le
    have scaled :=
      mul_le_mul_of_nonneg_right errorRadiusLower multiplierNonneg
    calc
      4368 * biotSavartSerrinConstant * level *
            (cubicConstant * normalizedDuration * level) =
          (errorSlope * normalizedDuration * level) *
            ((7 * nu.coeff * level / 128) * viscousConstant) := by
        dsimp only [errorSlope]
        field_simp [nu.coeff_pos.ne', viscousConstantPos.ne']
      _ ≤ (radius : Real) *
            ((7 * nu.coeff * level / 128) * viscousConstant) := scaled
      _ = (7 * nu.coeff * level / 128) *
            ((radius : Real) * viscousConstant) := by ring
  have rateContinuous :=
    wholeRestartPrefix_finiteInputRateDensity_continuousOn
      initial length modes
  have errorContinuous :=
    wholeRestartPrefix_finiteInputProjectionErrorDensity_continuousOn
      initial length modes
  have rateIntegrable :
      IntervalIntegrable
        (fun time : Real =>
          finiteInputRateDensity nu modes
            (wholeRestartPrefixPhysicalTrajectory initial length time))
        volume lowerTime upperTime :=
    ContinuousOn.intervalIntegrable_of_Icc lowerLtUpper.le
      (rateContinuous.mono (Icc_subset_Icc lowerNonneg upperLeElapsed))
  have errorIntegrable :
      IntervalIntegrable
        (fun time : Real =>
          finiteInputProjectionErrorDensity modes
            (wholeRestartPrefixPhysicalTrajectory initial length time))
        volume lowerTime upperTime :=
    ContinuousOn.intervalIntegrable_of_Icc lowerLtUpper.le
      (errorContinuous.mono (Icc_subset_Icc lowerNonneg upperLeElapsed))
  have integralSplit :
      (∫ time in lowerTime..upperTime,
          (finiteInputRateDensity nu modes
              (wholeRestartPrefixPhysicalTrajectory initial length time) +
            finiteInputProjectionErrorDensity modes
              (wholeRestartPrefixPhysicalTrajectory initial length time))) =
        (∫ time in lowerTime..upperTime,
          finiteInputRateDensity nu modes
            (wholeRestartPrefixPhysicalTrajectory initial length time)) +
        ∫ time in lowerTime..upperTime,
          finiteInputProjectionErrorDensity modes
            (wholeRestartPrefixPhysicalTrajectory initial length time) := by
    exact intervalIntegral.integral_add rateIntegrable errorIntegrable
  have rateLower :
      7 * nu.coeff * level / 128 ≤
        ∫ time in lowerTime..upperTime,
          finiteInputRateDensity nu modes
            (wholeRestartPrefixPhysicalTrajectory initial length time) := by
    have paidGap :
        7 * nu.coeff * level / 64 ≤
          nu.coeff *
            (finiteStateVorticityCoefficientEnstrophy modes
                (wholeRestartPrefixPhysicalTrajectory initial length upperTime) -
              finiteStateVorticityCoefficientEnstrophy modes
                (wholeRestartPrefixPhysicalTrajectory initial length lowerTime)) := by
      calc
        7 * nu.coeff * level / 64 = nu.coeff * (7 * level / 64) := by
          ring
        _ ≤ nu.coeff *
            (finiteStateVorticityCoefficientEnstrophy modes
                (wholeRestartPrefixPhysicalTrajectory initial length upperTime) -
              finiteStateVorticityCoefficientEnstrophy modes
                (wholeRestartPrefixPhysicalTrajectory initial length lowerTime)) := by
          simpa only [modes] using
            mul_le_mul_of_nonneg_left finiteGap nu.coeff_pos.le
    rw [integralSplit] at rateWithError
    linarith
  refine ⟨length, radius, lowerTime, upperTime, lowerNonneg, lowerLtUpper,
    upperLeElapsed, ?_, radiusPos, ?_, ?_, finiteGap, sourceMassBand,
    normalizedDurationLower, ?_⟩
  · simpa only [length] using prehistoryCeiling
  · simpa only [adjustedGradientConstant, normalizedDuration] using radiusLower
  · simpa only [adjustedGradientConstant, normalizedDuration] using radiusUpper
  · simpa only [modes] using rateLower

/-- A positive source level generates one actual suffix/restrict NS receipt
whose finite punctured vorticity projection carries a strictly positive
scale-critical stretching-minus-viscous rate.  Its time, mass band, Fourier
radius, and path chart all come from the same original whole restart prefix. -/
theorem sourceGeneratedNativeAccumulationScaleCriticalActualStretchingRate
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (level : Real)
    (levelPos : 0 < level)
    (initialLeHalf :
      restartPhysicalVorticityMass initial 0 ≤ level / 2) :
    let viscousConstant : Real :=
      nu.coeff ^ 2 * (2 * Real.pi) ^ 2
    let cubicConstant : Real :=
      (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
        (2 * viscousConstant)
    let gradientConstant : Real :=
      (2 * cubicConstant) / viscousConstant
    let errorSlope : Real :=
      (128 * 4368 * biotSavartSerrinConstant * cubicConstant) /
        (7 * nu.coeff * viscousConstant)
    ∃ length edge radius : Nat,
    ∃ lowerTime upperTime normalizedDuration : Real,
    ∃ segmentInitial : ComplexVorticityHilbertState,
    ∃ segmentTime : Real,
    ∃ _segmentTimePos : 0 < segmentTime,
    ∃ segmentReceipt :
        WholeContinuousMildSerrinReceipt nu segmentInitial segmentTime,
    ∃ absoluteTime : Icc (0 : Real) segmentTime → Real,
      0 ≤ lowerTime ∧
      lowerTime < upperTime ∧
      upperTime ≤ elapsedTime initial length ∧
      (∀ time ∈
          Icc (elapsedTime initial 1) (elapsedTime initial length),
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          level + 2) ∧
      normalizedDuration = level ^ 2 * (upperTime - lowerTime) ∧
      0 < normalizedDuration ∧
      nu.coeff / (8 * cubicConstant) ≤ normalizedDuration ∧
      edge < length ∧
      0 < radius ∧
      8 * (gradientConstant + errorSlope * normalizedDuration / 8 + 1) *
          level ≤ (radius : Real) ∧
      segmentTime ≤ normalizedDuration / level ^ 2 ∧
      (radius : Real) ≤
        8 * (gradientConstant + errorSlope * normalizedDuration / 8 + 1) *
            level + 2 ∧
      (∀ localTime,
        absoluteTime localTime ∈ Icc lowerTime upperTime ∧
        segmentReceipt.wholePath localTime =
          wholeRestartPrefixPhysicalTrajectory initial length
            (absoluteTime localTime)) ∧
      (∀ time ∈ Icc lowerTime upperTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
            level) ∧
      (∀ localTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (segmentReceipt.wholePath localTime) ∧
          wholeVorticityEuclideanMass
              (segmentReceipt.wholePath localTime) ≤ level) ∧
      (7 / (512 * normalizedDuration)) * level ^ 3 * segmentTime <
        ∫ localTime,
          (finiteStateVorticityStretchingWork (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (segmentReceipt.wholePath localTime)) -
            (nu.coeff * (2 * Real.pi) ^ 2 / 2) *
              finiteStateVorticityEnstrophyMass (wholeRestartModes radius)
                (complexSharpSupportProjection (wholeRestartModes radius)
                  (segmentReceipt.wholePath localTime)))
          ∂(commonTimeMeasure segmentTime) := by
  dsimp only
  let viscousConstant : Real :=
    nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let cubicConstant : Real :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * viscousConstant)
  let gradientConstant : Real :=
    (2 * cubicConstant) / viscousConstant
  let errorSlope : Real :=
    (128 * 4368 * biotSavartSerrinConstant * cubicConstant) /
      (7 * nu.coeff * viscousConstant)
  obtain ⟨length, radius, lowerTime, upperTime, lowerNonneg,
      lowerLtUpper, upperLeElapsed, prehistoryCeiling, radiusPos,
      radiusLower, radiusUpper, _finiteGap, sourceMassBand,
      normalizedDurationLower, globalRate⟩ :=
    sourceGeneratedNativeAccumulationScaleCriticalFiniteInputRateQuantum
      initial elapsedBounded level levelPos initialLeHalf
  let modes := integerWaveFrequencyCube radius
  let normalizedDuration : Real := level ^ 2 * (upperTime - lowerTime)
  have normalizedDurationPos : 0 < normalizedDuration := by
    dsimp only [normalizedDuration]
    exact mul_pos (sq_pos_of_pos levelPos) (sub_pos.mpr lowerLtUpper)
  let privateThreshold : Real :=
    7 * nu.coeff * level ^ 3 / (256 * normalizedDuration)
  have globalAverageHigh :
      privateThreshold * (upperTime - lowerTime) <
        ∫ time in lowerTime..upperTime,
          finiteInputRateDensity nu modes
            (wholeRestartPrefixPhysicalTrajectory initial length time) := by
    calc
      privateThreshold * (upperTime - lowerTime) =
          7 * nu.coeff * level / 256 := by
        dsimp only [privateThreshold, normalizedDuration]
        field_simp [levelPos.ne', (sub_pos.mpr lowerLtUpper).ne']
      _ < 7 * nu.coeff * level / 128 := by
        have positive : 0 < 7 * nu.coeff * level :=
          mul_pos (mul_pos (by norm_num) nu.coeff_pos) levelPos
        linarith
      _ ≤ ∫ time in lowerTime..upperTime,
          finiteInputRateDensity nu modes
            (wholeRestartPrefixPhysicalTrajectory initial length time) := by
        simpa only [modes] using globalRate
  have densityContinuous :
      ContinuousOn
        (fun time =>
          finiteInputRateDensity nu modes
            (wholeRestartPrefixPhysicalTrajectory initial length time))
        (Icc lowerTime upperTime) :=
    (wholeRestartPrefix_finiteInputRateDensity_continuousOn
      initial length modes).mono
        (Icc_subset_Icc lowerNonneg upperLeElapsed)
  obtain ⟨edge, segmentInitial, segmentTime, segmentTimePos,
      segmentReceipt, absoluteTime, edgeLt, pathChart, segmentMassLe,
      segmentDurationLe, segmentPrivateRate⟩ :=
    wholeRestartPrefix_rateAverage_selects_actualSubreceipt initial length
      (finiteInputRateDensity nu modes)
      (threshold := privateThreshold) (ceiling := level)
      (start := lowerTime) (finish := upperTime)
      lowerNonneg lowerLtUpper upperLeElapsed densityContinuous
      (fun time timeMem => (sourceMassBand time timeMem).2)
      globalAverageHigh
  have segmentDurationScaled :
      segmentTime ≤ normalizedDuration / level ^ 2 := by
    calc
      segmentTime ≤ upperTime - lowerTime := segmentDurationLe
      _ = normalizedDuration / level ^ 2 := by
        dsimp only [normalizedDuration]
        field_simp [levelPos.ne']
  have segmentMassBand :
      ∀ localTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (segmentReceipt.wholePath localTime) ∧
          wholeVorticityEuclideanMass
              (segmentReceipt.wholePath localTime) ≤ level := by
    intro localTime
    rw [(pathChart localTime).2]
    exact sourceMassBand _ (pathChart localTime).1
  let canonicalRate : ComplexVorticityHilbertState → Real := fun state =>
    finiteStateVorticityStretchingWork (wholeRestartModes radius)
        (complexSharpSupportProjection (wholeRestartModes radius) state) -
      (nu.coeff * (2 * Real.pi) ^ 2 / 2) *
        finiteStateVorticityEnstrophyMass (wholeRestartModes radius)
          (complexSharpSupportProjection (wholeRestartModes radius) state)
  have privateIntegralEq :
      (∫ localTime,
          finiteInputRateDensity nu modes
            (segmentReceipt.wholePath localTime)
          ∂(commonTimeMeasure segmentTime)) =
        2 * nu.coeff *
          ∫ localTime,
            canonicalRate (segmentReceipt.wholePath localTime)
            ∂(commonTimeMeasure segmentTime) := by
    calc
      (∫ localTime,
          finiteInputRateDensity nu modes
            (segmentReceipt.wholePath localTime)
          ∂(commonTimeMeasure segmentTime)) =
          ∫ localTime,
            2 * nu.coeff * canonicalRate (segmentReceipt.wholePath localTime)
            ∂(commonTimeMeasure segmentTime) := by
        simpa only [modes, canonicalRate] using
          receipt_finiteInputRateDensity_integral_eq_puncturedStretchingRate
            segmentReceipt radius
      _ = 2 * nu.coeff *
          ∫ localTime,
            canonicalRate (segmentReceipt.wholePath localTime)
            ∂(commonTimeMeasure segmentTime) := by
        rw [integral_const_mul]
  have canonicalRateLower :
      (7 / (512 * normalizedDuration)) * level ^ 3 * segmentTime <
        ∫ localTime,
          canonicalRate (segmentReceipt.wholePath localTime)
          ∂(commonTimeMeasure segmentTime) := by
    have scaled :
        2 * nu.coeff *
            ((7 / (512 * normalizedDuration)) * level ^ 3 * segmentTime) <
          2 * nu.coeff *
            ∫ localTime,
              canonicalRate (segmentReceipt.wholePath localTime)
              ∂(commonTimeMeasure segmentTime) := by
      calc
        2 * nu.coeff *
              ((7 / (512 * normalizedDuration)) * level ^ 3 * segmentTime) =
            privateThreshold * segmentTime := by
          dsimp only [privateThreshold]
          field_simp [normalizedDurationPos.ne']
          ring
        _ < ∫ localTime,
            finiteInputRateDensity nu modes
              (segmentReceipt.wholePath localTime)
            ∂(commonTimeMeasure segmentTime) := segmentPrivateRate
        _ = 2 * nu.coeff *
            ∫ localTime,
              canonicalRate (segmentReceipt.wholePath localTime)
              ∂(commonTimeMeasure segmentTime) := privateIntegralEq
    have scalePos : (0 : Real) < 2 * nu.coeff :=
      mul_pos (by norm_num) nu.coeff_pos
    exact lt_of_mul_lt_mul_left scaled scalePos.le
  refine ⟨length, edge, radius, lowerTime, upperTime, normalizedDuration,
    segmentInitial, segmentTime, segmentTimePos, segmentReceipt, absoluteTime,
    lowerNonneg, lowerLtUpper, upperLeElapsed, prehistoryCeiling, rfl,
    normalizedDurationPos,
    ?_, edgeLt, radiusPos, ?_, segmentDurationScaled, ?_, pathChart,
    sourceMassBand, segmentMassBand, ?_⟩
  · simpa only [normalizedDuration, cubicConstant, viscousConstant] using
      normalizedDurationLower
  · simpa only [normalizedDuration, gradientConstant, cubicConstant,
      viscousConstant, errorSlope] using radiusLower
  · simpa only [normalizedDuration, gradientConstant, cubicConstant,
      viscousConstant, errorSlope] using radiusUpper
  · simpa only [canonicalRate] using canonicalRateLower

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
end NavierStokes
end SaturationMonoid
