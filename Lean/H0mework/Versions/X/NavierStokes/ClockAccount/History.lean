import H0mework.Versions.X.NavierStokes.NativeWorkButterfly.StandingActionKineticClock

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticAmbientBound
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientInstantaneousWholeNetPowerCapture
open ThreeDimensionalVorticityCoefficientFiniteSupportWholeActionTube
open ThreeDimensionalVorticityCoefficientFullReceiptNormalizedWorkEulerEscrow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCompleteSerrinLanding
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSerrinActionExhaustion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMovingInventoryScaleRelativeClockFold
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientStandingValuedKineticPayment
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedExpansionMaterial
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator.ButterflyStackedKineticAdvance

noncomputable section

/-! ## Framework recursion of the dependent face transition -/

/-- The unique total disposition generated at this actual run occurrence. -/
private abbrev ButterflyActualClockDispositionAt (stage : Nat) :=
  SourceGeneratedStandingActionRunClockDispositionAt
    stackedInitialActionMaterialInstruction stage
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage))

/-- The only source-owned mouth left after the total face compiler runs.
It is indexed by the exact current face, disposition, and generated
shortfall; returning it settles this current edge and generates the next
face.  The mouth contains no future instruction or recurrence table. -/
def ButterflyCreditClockFaceResidualResolutionAt
    (stage : Nat)
    (face : ButterflyCreditClockFaceAt (source.stateAfter stage))
    (_shortfall : ButterflyCreditClockFaceResidualAt
      stage face (sourceGeneratedStandingActionRunClockDisposition
        stackedInitialActionMaterialInstruction stage)) : Type :=
  Σ nextFace : ButterflyCreditClockFaceAt
      (source.stateAfter (stage + 1)),
    SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage) face.clockState nextFace.clockState
        (nativeFluidMediumRootOperationalOutcomeAt source
          (source.stateAfter stage))

/-- Rebuild only the clock instruction on the same physical successor.  Its
predecessor is the current canonical disposition and every unused unit is
added to the existing bank. -/
private noncomputable def butterflyCapitalizedNextFace
    (stage : Nat)
    (nextFace : ButterflyCreditClockFaceAt (source.stateAfter (stage + 1)))
    (credit : Real) (creditNonneg : 0 ≤ credit) :
    ButterflyCreditClockFaceAt (source.stateAfter (stage + 1)) :=
  let disposition := sourceGeneratedStandingActionRunClockDisposition
    stackedInitialActionMaterialInstruction stage
  match nextFace with
  | .rich instruction => .rich (butterflyCompleteCreditNextInstruction
      stage disposition ⟨instruction.bank + credit,
        add_nonneg instruction.bank_nonneg creditNonneg⟩)
  | .complete instruction => .complete (butterflyCompleteCreditNextInstruction
      stage disposition ⟨instruction.bank + credit,
        add_nonneg instruction.bank_nonneg creditNonneg⟩)
  | .capped instruction => .capped (butterflyCompleteCreditNextInstruction
      stage disposition ⟨instruction.bank + credit,
        add_nonneg instruction.bank_nonneg creditNonneg⟩)

private theorem butterflyCapitalizedNextFace_potential
    (stage : Nat)
    (nextFace : ButterflyCreditClockFaceAt (source.stateAfter (stage + 1)))
    (credit : Real) (creditNonneg : 0 ≤ credit) :
    (butterflyCapitalizedNextFace stage nextFace credit creditNonneg
      ).clockState.potential = nextFace.clockState.potential + credit := by
  cases nextFace <;>
    simp only [butterflyCapitalizedNextFace, ButterflyCreditClockFaceAt.clockState,
      butterflyCreditBearingClockState, butterflyCompleteCreditClockState,
      butterflyCappedCreditClockState, butterflyCompleteCreditNextInstruction] <;>
    ring

noncomputable def butterflyRetainFaceSettlement
    (stage : Nat)
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    {nextFace : ButterflyCreditClockFaceAt (source.stateAfter (stage + 1))}
    (settlement : SourceGeneratedRootClockSettlementAt source
      (source.stateAfter stage) face.clockState nextFace.clockState
      (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage))) :
    Σ retainedFace : ButterflyCreditClockFaceAt
        (source.stateAfter (stage + 1)),
      { retained : SourceGeneratedRootClockSettlementAt source
          (source.stateAfter stage) face.clockState retainedFace.clockState
          (nativeFluidMediumRootOperationalOutcomeAt source
            (source.stateAfter stage)) //
        retained.resolved.waste = 0 } := by
  let advance := settlement.resolved
  let retainedFace := butterflyCapitalizedNextFace stage nextFace
    advance.waste advance.waste_nonneg
  let retainedAdvance : SourceGeneratedRootClockAdvanceAt source
      (source.stateAfter stage) face.clockState retainedFace.clockState :=
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by
        have paid := advance.settlement
        change face.clockState.potential =
          source.clockAt (source.stateAfter stage) +
            retainedFace.clockState.potential + 0
        rw [show retainedFace.clockState.potential =
          nextFace.clockState.potential + advance.waste from
            butterflyCapitalizedNextFace_potential stage nextFace
              advance.waste advance.waste_nonneg]
        simpa only [add_zero, add_assoc] using paid }
  have install : ∀ outcome : NativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage),
      { retained : SourceGeneratedRootClockSettlementAt source
          (source.stateAfter stage) face.clockState retainedFace.clockState
          outcome // retained.resolved.waste = 0 } := by
    intro outcome
    cases outcome with
    | exactPayment => exact ⟨.exactPayment retainedAdvance, rfl⟩
    | generatedResidual => exact ⟨.generatedResidual retainedAdvance, rfl⟩
    | obstruction => exact ⟨.obstructionAlternative retainedAdvance, rfl⟩
  exact ⟨retainedFace, install _⟩

/-- Finite lineage of faces actually generated by the root clock compiler.
Every step retains all settlement waste and writes the canonical predecessor;
an arbitrary bank or discarded-credit face is not a reachable instruction. -/
inductive ButterflyCreditClockFaceReachableAt :
    (stage : Nat) →
      ButterflyCreditClockFaceAt (source.stateAfter stage) → Type
  | initial : ButterflyCreditClockFaceReachableAt 0
      (.capped butterflyZeroBankInitialInstruction)
  | next
      {stage : Nat}
      {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
      {nextFace : ButterflyCreditClockFaceAt
        (source.stateAfter (stage + 1))}
      (current : ButterflyCreditClockFaceReachableAt stage face)
      (settlement : SourceGeneratedRootClockSettlementAt source
        (source.stateAfter stage) face.clockState nextFace.clockState
          (nativeFluidMediumRootOperationalOutcomeAt source
            (source.stateAfter stage))) :
      ButterflyCreditClockFaceReachableAt (stage + 1)
        (butterflyRetainFaceSettlement stage settlement).1

/-- Every paid unit or unused credit remains on the finite generated
history.  The current resolver therefore receives the exact unspent source
account, not an arbitrary smaller balance. -/
theorem
    ButterflyCreditClockFaceReachableAt.prefix_add_potential_eq_initial
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face) :
    (∑ prior ∈ Finset.range stage,
        source.clockAt (source.stateAfter prior)) + face.clockState.potential =
      (butterflyCappedCreditClockState
        butterflyZeroBankInitialInstruction).potential := by
  induction reachable with
  | initial => simp [ButterflyCreditClockFaceAt.clockState]
  | @next stage face nextFace current settlement inductionHypothesis =>
      let retained := butterflyRetainFaceSettlement stage settlement
      let advance := retained.2.1.resolved
      have settled := advance.settlement
      have wasteZero : advance.waste = 0 := retained.2.2
      change
        face.clockState.potential =
          source.clockAt (source.stateAfter stage) +
            retained.1.clockState.potential + advance.waste at settled
      rw [wasteZero, add_zero] at settled
      rw [Finset.sum_range_succ]
      linarith

theorem
    ButterflyCreditClockFaceReachableAt.prefix_add_potential_le_initial
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face) :
    (∑ prior ∈ Finset.range stage,
        source.clockAt (source.stateAfter prior)) + face.clockState.potential ≤
      (butterflyCappedCreditClockState
        butterflyZeroBankInitialInstruction).potential :=
  reachable.prefix_add_potential_eq_initial.le

theorem
    ButterflyCreditClockFaceReachableAt.prefix_le_initial
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face) :
    (∑ prior ∈ Finset.range stage,
        source.clockAt (source.stateAfter prior)) ≤
      (butterflyCappedCreditClockState
        butterflyZeroBankInitialInstruction).potential := by
  have folded := reachable.prefix_add_potential_le_initial
  exact le_trans (le_add_of_nonneg_right face.clockState.potential_nonneg)
    folded

private theorem butterflySourceClockAt_stateAfter_eq_contact_succ
    (stage : Nat) :
    source.clockAt (source.stateAfter stage) =
      (run concreteCounterexampleInitial (stage + 1)).contact.time.1 := by
  have currentEq :=
    standingActionWholeRestartMediumSource_stateAfter_current
      stackedInitialActionMaterialInstruction stage
  have physicalEq : (source.stateAfter stage).1.physical =
      run stackedShortCurrent stage :=
    congrArg (fun current => current.physical) currentEq
  change (source.stateAfter stage).1.physical.nextContact.time.1 =
    (run stackedShortCurrent (stage + 1)).contact.time.1
  rw [physicalEq, run_succ, next_contact]

def butterflyInitialTotalClockBank : Real :=
  concreteCounterexampleInitial.contact.time.1 +
    (butterflyCappedCreditClockState
      butterflyZeroBankInitialInstruction).potential

/-- The physical-time ledger and the completely retained clock account have
the same exact finite-prefix fold. -/
theorem
    butterflyReachable_elapsedTime_succ_add_potential_eq_initial
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face) :
    elapsedTime concreteCounterexampleInitial (stage + 1) +
        face.clockState.potential =
      butterflyInitialTotalClockBank := by
  have prefixBound :
      (∑ prior ∈ Finset.range stage,
          source.clockAt (source.stateAfter prior)) + face.clockState.potential =
        (butterflyCappedCreditClockState
          butterflyZeroBankInitialInstruction).potential :=
    reachable.prefix_add_potential_eq_initial
  have shifted :
      (∑ prior ∈ Finset.range stage,
          source.clockAt (source.stateAfter prior)) =
        ∑ prior ∈ Finset.range stage,
          (run concreteCounterexampleInitial (prior + 1)).contact.time.1 := by
    apply Finset.sum_congr rfl
    intro prior _priorMem
    exact butterflySourceClockAt_stateAfter_eq_contact_succ prior
  rw [shifted] at prefixBound
  have elapsedEq :
      elapsedTime concreteCounterexampleInitial (stage + 1) =
        concreteCounterexampleInitial.contact.time.1 +
          ∑ prior ∈ Finset.range stage,
            (run concreteCounterexampleInitial
              (prior + 1)).contact.time.1 := by
    rw [elapsedTime_eq_sum_contactTime]
    simpa only [run_zero, add_comm] using
      (Finset.sum_range_succ'
        (fun prior : Nat =>
          (run concreteCounterexampleInitial prior).contact.time.1) stage)
  rw [elapsedEq]
  unfold butterflyInitialTotalClockBank
  linarith [prefixBound]

/-- Every fixed Fourier row at a reachable residual remains inside the
finite ball paid by the actual root prefix.  This transports the exact
clock fold into the existing Duhamel row estimate; it does not assume the
current residual is payable. -/
theorem
    ButterflyCreditClockFaceReachableAt.fixedRow_displacement_le_initial
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    ‖(run concreteCounterexampleInitial stage).contact.physicalState output -
        concreteCounterexampleInitial.contact.physicalState output‖ ≤
      fixedRowKineticSpeed concreteCounterexampleViscosity
          (puncturedWholeVorticityKineticMass
            concreteCounterexampleInitial.contact.physicalState) output *
        (butterflyCappedCreditClockState
          butterflyZeroBankInitialInstruction).potential := by
  have displacement := run_fixedRow_displacement_le_clockPrefix
    concreteCounterexampleInitial output outputNe stage
  have prefixBound := reachable.prefix_le_initial
  have clockSumEq :
      (∑ prior ∈ Finset.range stage,
          (run concreteCounterexampleInitial prior).nextContact.time.1) =
        ∑ prior ∈ Finset.range stage,
          source.clockAt (source.stateAfter prior) := by
    apply Finset.sum_congr rfl
    intro prior _priorMem
    rw [butterflySourceClockAt_stateAfter_eq_contact_succ,
      run_succ, next_contact]
  rw [clockSumEq] at displacement
  exact displacement.trans
    (mul_le_mul_of_nonneg_left prefixBound
      (fixedRowKineticSpeed_nonneg concreteCounterexampleViscosity
        (puncturedWholeVorticityKineticMass
          concreteCounterexampleInitial.contact.physicalState)
        (puncturedWholeVorticityKineticMass_nonneg _)
        output))


end
end SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
