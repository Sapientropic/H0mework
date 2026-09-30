import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinPositiveTimeSuffix
import H0mework.NavierStokes.Restart.NativeAccumulationVorticityCourt
import H0mework.NavierStokes.Restart.SerrinActionExhaustion

/-!
# A complete Serrin receipt lands at the native accumulation contact

If the native physical clock is bounded, one whole mild/Serrin receipt from
the original initial state whose horizon extends past the generated
accumulation time is forced, by same-law uniqueness, to contain every native
contact.  Its continuity therefore produces the forbidden strong whole-
vorticity landing.

The public receipt mouth below uses the canonical horizon `T + 1`.  It asks
for no crossing index, overlap equality, endpoint, convergence certificate,
or landing target.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCompleteSerrinLanding

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinPositiveTimeSuffix
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationVorticityCourt
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSerrinActionExhaustion

noncomputable section

private theorem wholeContinuousMildSerrin_overlap_of_initial_eq
    {nu : Viscosity}
    {smallInitial bigInitial : ComplexVorticityHilbertState}
    {smallTime bigTime : Real}
    (initialEq : smallInitial = bigInitial)
    (small : WholeContinuousMildSerrinReceipt
      nu smallInitial smallTime)
    (big : WholeContinuousMildSerrinReceipt
      nu bigInitial bigTime)
    (timeLe : smallTime ≤ bigTime) :
    small.wholePath =
      big.wholePath.compContinuous (commonTimeInclusion timeLe) := by
  subst bigInitial
  exact wholeContinuousMildSerrin_overlap small big timeLe

/-- Canonical standard horizon strictly past the generated accumulation
time. -/
def completeSerrinAccumulationHorizon
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Real :=
  wholeRestartVelocityAccumulationTime initial + 1

theorem completeSerrinAccumulationHorizon_pos
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    0 < completeSerrinAccumulationHorizon initial := by
  have accumulationPos :
      0 < wholeRestartVelocityAccumulationTime initial := by
    simpa only [elapsedTime_zero] using
      elapsedTime_lt_wholeRestartVelocityAccumulationTime
        initial elapsedBounded 0
  unfold completeSerrinAccumulationHorizon
  linarith

private def completeSerrinElapsedPoint
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : Nat) :
    Icc (0 : Real) (completeSerrinAccumulationHorizon initial) :=
  ⟨elapsedTime initial index, by
    constructor
    · exact GeneratedWholeRestartCurrent.elapsedTime_nonneg initial index
    · have beforeAccumulation :=
        elapsedTime_lt_wholeRestartVelocityAccumulationTime
          initial elapsedBounded index
      unfold completeSerrinAccumulationHorizon
      linarith⟩

private def completeSerrinAccumulationPoint
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Icc (0 : Real) (completeSerrinAccumulationHorizon initial) :=
  ⟨wholeRestartVelocityAccumulationTime initial, by
    constructor
    · simpa only [elapsedTime_zero] using
        (elapsedTime_lt_wholeRestartVelocityAccumulationTime
          initial elapsedBounded 0).le
    · unfold completeSerrinAccumulationHorizon
      linarith⟩

private theorem run_initialState_eq_completeSerrinReceipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (receipt : WholeContinuousMildSerrinReceipt nu initial.initialState
      (completeSerrinAccumulationHorizon initial)) :
    ∀ index : Nat,
      (run initial index).initialState =
        receipt.wholePath
          (completeSerrinElapsedPoint initial elapsedBounded index) := by
  intro index
  induction index with
  | zero =>
      simpa [completeSerrinElapsedPoint] using receipt.wholePath_initial.symm
  | succ index inductionHypothesis =>
      have startNonneg : 0 ≤ elapsedTime initial index :=
        GeneratedWholeRestartCurrent.elapsedTime_nonneg initial index
      have startBeforeAccumulation :
          elapsedTime initial index <
            wholeRestartVelocityAccumulationTime initial :=
        elapsedTime_lt_wholeRestartVelocityAccumulationTime
          initial elapsedBounded index
      have startBeforeHorizon :
          elapsedTime initial index <
            completeSerrinAccumulationHorizon initial := by
        unfold completeSerrinAccumulationHorizon
        linarith
      let suffix :=
        positiveTimeSuffixWholeContinuousMildSerrinReceipt
          receipt (elapsedTime initial index) startNonneg startBeforeHorizon
      have initialEq :
          (run initial index).initialState =
            receipt.wholePath
              (wholeContinuousMildSerrinSuffixStartTime
                receipt (elapsedTime initial index)
                  startNonneg startBeforeHorizon) := by
        rw [inductionHypothesis]
        apply congrArg receipt.wholePath
        apply Subtype.ext
        rfl
      have contactFits :
          (run initial index).contact.time.1 ≤
            completeSerrinAccumulationHorizon initial -
              elapsedTime initial index := by
        have nextBeforeAccumulation :=
          elapsedTime_lt_wholeRestartVelocityAccumulationTime
            initial elapsedBounded (index + 1)
        rw [elapsedTime_succ] at nextBeforeAccumulation
        unfold completeSerrinAccumulationHorizon
        linarith
      have pathEq :=
        wholeContinuousMildSerrin_overlap_of_initial_eq
          initialEq (run initial index).contact.prefixReceipt
          suffix contactFits
      let terminal :
          Icc (0 : Real) (run initial index).contact.time.1 :=
        ⟨(run initial index).contact.time.1,
          ⟨(run initial index).contact.time_pos.le, le_rfl⟩⟩
      have atTerminal := congrArg (fun path => path terminal) pathEq
      rw [(run initial index).contact.prefixReceipt_terminal] at atTerminal
      calc
        (run initial (index + 1)).initialState =
            (run initial index).contact.physicalState :=
          run_succ_initialState initial index
        _ = receipt.wholePath
            (commonTimeShift startNonneg startBeforeHorizon.le
              (commonTimeInclusion contactFits terminal)) := by
          simpa only [suffix,
            positiveTimeSuffixWholeContinuousMildSerrinReceipt_wholePath,
            BoundedContinuousFunction.compContinuous_apply] using atTerminal
        _ = receipt.wholePath
            (completeSerrinElapsedPoint
              initial elapsedBounded (index + 1)) := by
          apply congrArg receipt.wholePath
          apply Subtype.ext
          simp [terminal, commonTimeShift_apply,
            commonTimeInclusion_apply, completeSerrinElapsedPoint,
            elapsedTime_succ]

private theorem run_contact_eq_completeSerrinReceipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (receipt : WholeContinuousMildSerrinReceipt nu initial.initialState
      (completeSerrinAccumulationHorizon initial))
    (index : Nat) :
    (run initial index).contact.physicalState =
      receipt.wholePath
        (completeSerrinElapsedPoint initial elapsedBounded (index + 1)) := by
  calc
    (run initial index).contact.physicalState =
        (run initial (index + 1)).initialState :=
      (run_succ_initialState initial index).symm
    _ = receipt.wholePath
        (completeSerrinElapsedPoint
          initial elapsedBounded (index + 1)) :=
      run_initialState_eq_completeSerrinReceipt
        initial elapsedBounded receipt (index + 1)

private theorem completeSerrinElapsedPoint_succ_tendsto
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (fun index =>
        completeSerrinElapsedPoint initial elapsedBounded (index + 1))
      atTop
      (nhds (completeSerrinAccumulationPoint initial elapsedBounded)) := by
  rw [tendsto_subtype_rng]
  change
    Tendsto (fun index => elapsedTime initial (index + 1)) atTop
      (nhds (wholeRestartVelocityAccumulationTime initial))
  exact
    (generatedNativeAccumulationEvent initial elapsedBounded).elapsed_tendsto.comp
      (Filter.tendsto_add_atTop_nat 1)

/-- A complete standard receipt through the canonical post-accumulation
horizon generates the exact forbidden strong landing.  The endpoint and all
contact/path identifications are conclusions. -/
def completeSerrinReceipt_generates_nativeAccumulationWholeVorticityStrongLandingAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (receipt : WholeContinuousMildSerrinReceipt nu initial.initialState
      (completeSerrinAccumulationHorizon initial)) :
    NativeAccumulationWholeVorticityStrongLandingAt
      initial elapsedBounded := by
  let endpoint : ComplexVorticityHilbertState :=
    receipt.wholePath
      (completeSerrinAccumulationPoint initial elapsedBounded)
  have pathTendsto :
      Tendsto
        (fun index => receipt.wholePath
          (completeSerrinElapsedPoint initial elapsedBounded (index + 1)))
        atTop (nhds endpoint) :=
    receipt.wholePath.continuous.continuousAt.tendsto.comp
      (completeSerrinElapsedPoint_succ_tendsto initial elapsedBounded)
  have contactTendsto :
      Tendsto
        (fun index => (run initial index).contact.physicalState)
        atTop (nhds endpoint) := by
    apply pathTendsto.congr'
    filter_upwards [] with index
    exact
      (run_contact_eq_completeSerrinReceipt
        initial elapsedBounded receipt index).symm
  exact
    { boundaryOccurrence :=
        generatedNativeAccumulationConditionalOccurrence
          initial elapsedBounded
      boundaryOccurrence_eq := rfl
      endpoint := endpoint
      contact_tendsto := contactTendsto }

/-- Bounded native time excludes a complete Serrin receipt already at the
canonical horizon `T + 1`. -/
theorem completeSerrinAccumulationHorizon_receipt_isEmpty
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    IsEmpty
      (WholeContinuousMildSerrinReceipt nu initial.initialState
        (completeSerrinAccumulationHorizon initial)) := by
  refine ⟨fun receipt => ?_⟩
  exact
    (nativeAccumulationWholeVorticityStrongLandingAt_isEmpty
      initial elapsedBounded).false
        (completeSerrinReceipt_generates_nativeAccumulationWholeVorticityStrongLandingAt
          initial elapsedBounded receipt)

/-- A bounded native clock is incompatible with a complete family of
standard whole mild/Serrin receipts from the original initial state. -/
theorem elapsedTime_bddAbove_excludes_completeSerrinReceiptFamily
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ (∀ requestedTime : Real, 0 < requestedTime →
      Nonempty
        (WholeContinuousMildSerrinReceipt
          nu initial.initialState requestedTime)) := by
  intro complete
  rcases complete
      (completeSerrinAccumulationHorizon initial)
      (completeSerrinAccumulationHorizon_pos initial elapsedBounded) with
    ⟨receipt⟩
  exact
    (completeSerrinAccumulationHorizon_receipt_isEmpty
      initial elapsedBounded).false receipt

/-! ## Standard global solution mouth -/

/-- A standard global whole mild/Serrin solution from one initial state,
presented by its receipt on every positive finite horizon.  Same-initial-data
uniqueness already makes the horizon family coherent, so no independent
overlap or transport field is accepted from the caller. -/
structure StandardGlobalWholeMildSerrinSolutionAt
    (nu : Viscosity)
    (initialState : ComplexVorticityHilbertState) : Type 1 where
  receiptAt : ∀ requestedTime : Real, 0 < requestedTime →
    WholeContinuousMildSerrinReceipt nu initialState requestedTime

/-- Bounded native time excludes the standard global solution object by
evaluating it only at the source-generated canonical horizon. -/
theorem elapsedTime_bddAbove_standardGlobalWholeMildSerrinSolutionAt_isEmpty
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    IsEmpty (StandardGlobalWholeMildSerrinSolutionAt
      nu initial.initialState) := by
  refine ⟨fun solution => ?_⟩
  let horizon := completeSerrinAccumulationHorizon initial
  have horizonPos := completeSerrinAccumulationHorizon_pos
    initial elapsedBounded
  exact
    (completeSerrinAccumulationHorizon_receipt_isEmpty
      initial elapsedBounded).false
        (solution.receiptAt horizon horizonPos)

/-! ## Direct consumers of a paid native clock -/

/-- Summability of the actual occurrence times bounds the complete native
clock.  The bound is the total of that same time row; no scheduler or
replacement clock is introduced. -/
theorem contactTime_summable_forces_elapsedTime_bddAbove
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (contactSummable :
      Summable fun index => (run initial index).contact.time.1) :
    BddAbove (Set.range (elapsedTime initial)) := by
  refine
    ⟨∑' index : Nat, (run initial index).contact.time.1, ?_⟩
  intro elapsed elapsedMem
  rcases elapsedMem with ⟨length, rfl⟩
  rw [elapsedTime_eq_sum_contactTime]
  exact
    contactSummable.sum_le_tsum (Finset.range length)
      (fun index _ => (run initial index).contact.time_pos.le)

/-- A globally paid contact-time row immediately consumes the existing
Serrin-action exhaustion theorem on the same native run. -/
theorem contactTime_summable_forces_accumulatedSerrinAction_unbounded
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (contactSummable :
      Summable fun index => (run initial index).contact.time.1) :
    ¬ BddAbove
      (Set.range (wholeRestartAccumulatedSerrinAction initial)) :=
  elapsedTime_bddAbove_forces_accumulatedSerrinAction_unbounded
    initial
    (contactTime_summable_forces_elapsedTime_bddAbove
      initial contactSummable)

/-- A globally paid contact-time row excludes the standard complete Serrin
receipt family, with the forbidden landing generated internally. -/
theorem contactTime_summable_excludes_completeSerrinReceiptFamily
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (contactSummable :
      Summable fun index => (run initial index).contact.time.1) :
    ¬ (∀ requestedTime : Real, 0 < requestedTime →
      Nonempty
        (WholeContinuousMildSerrinReceipt
          nu initial.initialState requestedTime)) :=
  elapsedTime_bddAbove_excludes_completeSerrinReceiptFamily
    initial
    (contactTime_summable_forces_elapsedTime_bddAbove
      initial contactSummable)

/-- Standard initial/solution-shaped consumer of a globally paid native
clock.  The elapsed bound, canonical horizon and forbidden landing remain
internal conclusions. -/
theorem contactTime_summable_standardGlobalWholeMildSerrinSolutionAt_isEmpty
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (contactSummable :
      Summable fun index => (run initial index).contact.time.1) :
    IsEmpty (StandardGlobalWholeMildSerrinSolutionAt
      nu initial.initialState) :=
  elapsedTime_bddAbove_standardGlobalWholeMildSerrinSolutionAt_isEmpty
    initial
    (contactTime_summable_forces_elapsedTime_bddAbove
      initial contactSummable)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCompleteSerrinLanding
end NavierStokes
end SaturationMonoid
