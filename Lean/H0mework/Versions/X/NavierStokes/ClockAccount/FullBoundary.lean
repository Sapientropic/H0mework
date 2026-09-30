import H0mework.Versions.X.NavierStokes.NativeWork.StandingPaidActionMaterialInstruction
import H0mework.NavierStokes.Accumulation.NativeTurbulenceLaw
import H0mework.NavierStokes.Restart.CompleteSerrinLanding

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.FullBoundary

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCompleteSerrinLanding
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent

noncomputable section

abbrev source := stackedStandingActionMediumSource

private def horizon
    (inquiry : SourceGeneratedBoundaryRevisedInquiryAt concreteCounterexampleInitial) : Real :=
  Classical.choose inquiry.elapsedBounded

private theorem elapsed_le_horizon
    (inquiry : SourceGeneratedBoundaryRevisedInquiryAt concreteCounterexampleInitial)
    (stage : Nat) : elapsedTime concreteCounterexampleInitial stage ≤ horizon inquiry :=
  (Classical.choose_spec inquiry.elapsedBounded) (mem_range_self stage)

/-- The instruction records the actual finite past, with no future face table. -/
private structure InstructionAt (state : source.State) where
  stage : Nat
  state_eq : state = source.stateAfter stage

private def clockState
    (inquiry : SourceGeneratedBoundaryRevisedInquiryAt concreteCounterexampleInitial)
    {state : source.State} (instruction : InstructionAt state) :
    SourceGeneratedRootClockStateAt source state where
  potential := horizon inquiry - elapsedTime concreteCounterexampleInitial (instruction.stage + 1)
  potential_nonneg := sub_nonneg.mpr (elapsed_le_horizon inquiry (instruction.stage + 1))

private theorem clock_eq_contact_succ (stage : Nat) :
    source.clockAt (source.stateAfter stage) =
      (run concreteCounterexampleInitial (stage + 1)).contact.time.1 := by
  have currentEq := standingActionWholeRestartMediumSource_stateAfter_current
    stackedInitialActionMaterialInstruction stage
  have physicalEq : (source.stateAfter stage).1.physical = run stackedShortCurrent stage :=
    congrArg (fun current => current.physical) currentEq
  change (source.stateAfter stage).1.physical.nextContact.time.1 =
    (run stackedShortCurrent (stage + 1)).contact.time.1
  rw [physicalEq, run_succ, next_contact]

/-- The sealed native boundary branch has already generated a finite horizon.
Its clock readout spends only the original finite past and writes the original
medium outcome and successor. -/
def rootClockOfRevised
    (inquiry : SourceGeneratedBoundaryRevisedInquiryAt concreteCounterexampleInitial) :
    SourceGeneratedRootClockLaw source where
  ClockInstructionAt := InstructionAt
  clockState := clockState inquiry
  initialInstruction := ⟨0, rfl⟩
  transitionAt := by
    intro state instruction
    rcases instruction with ⟨stage, rfl⟩
    let currentInstruction : InstructionAt (source.stateAfter stage) := ⟨stage, rfl⟩
    let nextInstruction : InstructionAt (source.successor (source.stateAfter stage)) :=
      ⟨stage + 1, (NativeFluidMediumSource.stateAfter_succ source stage).symm⟩
    have advance : SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
        (clockState inquiry currentInstruction) (clockState inquiry nextInstruction) :=
      { waste := 0
        waste_nonneg := le_rfl
        settlement := by
          change horizon inquiry - elapsedTime concreteCounterexampleInitial (stage + 1) =
            source.clockAt (source.stateAfter stage) +
              (horizon inquiry - elapsedTime concreteCounterexampleInitial (stage + 1 + 1)) + 0
          rw [clock_eq_contact_succ,
            elapsedTime_succ concreteCounterexampleInitial (stage + 1)]
          ring }
    refine ⟨nextInstruction, ?_⟩
    cases nativeFluidMediumRootOperationalOutcomeAt source (source.stateAfter stage) with
    | exactPayment => exact .exactPayment advance
    | generatedResidual => exact .generatedResidual advance
    | obstruction => exact .obstructionAlternative advance

def standingClockOfRevised
    (inquiry : SourceGeneratedBoundaryRevisedInquiryAt concreteCounterexampleInitial) :
    SourceGeneratedStandingActionClockLaw concreteCounterexampleInitial where
  initialActionMaterial := stackedInitialActionMaterialInstruction
  clockLaw := rootClockOfRevised inquiry

/-- Consume the total native answer through the original full clock grammar. -/
theorem fixedNativeAnswer :
    Nonempty (GeneratedWholeGlobalPhysicalTrajectory concreteCounterexampleInitial) ∨
      Nonempty (SourceGeneratedStandingActionClockLaw concreteCounterexampleInitial) :=
  (sourceGeneratedNativeBoundaryReachabilityAnswer concreteCounterexampleInitial).fold
    (fun _ trajectory => Or.inl ⟨trajectory⟩)
    (fun inquiry _ _ => Or.inr ⟨standingClockOfRevised inquiry⟩)

theorem standingClockOfRevised_standardConsumer
    (inquiry : SourceGeneratedBoundaryRevisedInquiryAt concreteCounterexampleInitial) :
    IsEmpty (StandardGlobalWholeMildSerrinSolutionAt concreteCounterexampleViscosity
      concreteCounterexampleInitial.initialState) :=
  contactTime_summable_standardGlobalWholeMildSerrinSolutionAt_isEmpty
    concreteCounterexampleInitial (standingClockOfRevised inquiry).contactTime_summable

end
end SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.FullBoundary
