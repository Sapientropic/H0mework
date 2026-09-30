import H0mework.Versions.X.NavierStokes.ClockAccount.DensityAccount

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.FullSource

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.DensityAccount
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator

noncomputable section

def richInitialPotential : Real :=
  (butterflyCreditBearingClockState butterflyCreditBearingInitialInstruction).potential

def cappedInitialPotential : Real :=
  (butterflyCappedCreditClockState butterflyZeroBankInitialInstruction).potential

/-- Exact current-source asset discarded by the zero-bank capped start. -/
def initialCreditDifference : Real :=
  standingActionBarrierTail butterflyGainViscosity source.initial.1.standing.anchorLevel +
    butterflyInitialCreditBank + butterflyRichCurrentPrepaidCredit 0 - 2

theorem initialPotential_difference :
    richInitialPotential - cappedInitialPotential = initialCreditDifference := by
  have high : 2 ≤ wholeVorticityEuclideanMass
      source.initial.1.physical.contact.physicalState :=
    stackedShortCurrent_contact_wholeMass_gt_two.le
  unfold richInitialPotential cappedInitialPotential
  have richEq := butterflyCreditBearingClockState_eq_complete_add_prepaid 0
    butterflyCreditBearingInitialInstruction
  change (butterflyCreditBearingClockState
    butterflyCreditBearingInitialInstruction).potential = _ at richEq
  rw [richEq]
  change kineticBarrierPotential source.initial +
    (butterflyInitialCreditBank + butterflyRichCurrentPrepaidCredit 0) -
      (cappedMassKineticClockPotential source.initial + 0) = initialCreditDifference
  unfold kineticBarrierPotential cappedMassKineticClockPotential initialCreditDifference
  rw [min_eq_right high]
  ring

theorem initialCreditDifference_pos : 0 < initialCreditDifference := by
  have high : 2 < wholeVorticityEuclideanMass
      source.initial.1.physical.contact.physicalState :=
    stackedShortCurrent_contact_wholeMass_gt_two
  have standing := source.initial.1.standing.remainingCellDeficit_nonneg
  have tail := standingActionBarrierTail_nonneg
    butterflyGainViscosity source.initial.1.standing.anchorLevel
  have prepaid := butterflyRichCurrentPrepaidCredit_nonneg 0
  unfold initialCreditDifference butterflyInitialCreditBank
  linarith

theorem originalBank_eq_eightySeven : butterflyInitialCreditBank = 87 := by
  have standing := source.initial.1.standing.remainingCellDeficit_eq_anchorLevel_sub_physicalMass
  have anchor : source.initial.1.standing.anchorLevel = 88 := by
    change (runCellStanding stackedShortCurrent 0).anchorLevel = 88
    exact stackedShortCurrent_level_eq_eighty_eight
  unfold butterflyInitialCreditBank
  rw [standing, anchor]
  norm_num

theorem restoredCredit_ge_eightyFive : 85 ≤ initialCreditDifference := by
  have tail := standingActionBarrierTail_nonneg
    butterflyGainViscosity source.initial.1.standing.anchorLevel
  have prepaid := butterflyRichCurrentPrepaidCredit_nonneg 0
  unfold initialCreditDifference
  rw [originalBank_eq_eightySeven]
  linarith

theorem cappedInitialPotential_lt_richInitialPotential :
    cappedInitialPotential < richInitialPotential := by
  linarith [initialPotential_difference, initialCreditDifference_pos]

/-- Material keeps its original bank and predecessor data. Only `clock`
is spendable here; the material bank is not added a second time. -/
structure InstructionAt (state : source.State) : Type where
  material : ButterflyCreditBearingClockInstructionAt state
  clock : SourceGeneratedRootClockStateAt source state

def initialInstruction : InstructionAt source.initial where
  material := butterflyCreditBearingInitialInstruction
  clock := butterflyCreditBearingClockState butterflyCreditBearingInitialInstruction

def faceInstruction {state : source.State}
    (face : ButterflyCreditClockFaceAt state) : InstructionAt state where
  material := match face with
    | .rich instruction => instruction
    | .complete instruction => instruction
    | .capped instruction => instruction
  clock := face.clockState

/-- The existing rich first transition starts the restored source account.
Its existing waste-capitalization preserves the complete emitted face. -/
def initialTransition :
    Σ nextInstruction : InstructionAt (source.successor source.initial),
      SourceGeneratedRootClockSettlementAt source source.initial
        initialInstruction.clock nextInstruction.clock
        (nativeFluidMediumRootOperationalOutcomeAt source source.initial) := by
  let paid := butterflyRichInitialRootTransition
  let retained := butterflyRetainFaceSettlement 0
    (face := .rich butterflyCreditBearingInitialInstruction) paid.2
  exact ⟨faceInstruction retained.1, retained.2.1⟩

theorem initialTransition_exact_remaining :
    richInitialPotential = source.clockAt source.initial +
      initialTransition.1.clock.potential := by
  let paid := butterflyRichInitialRootTransition
  let retained := butterflyRetainFaceSettlement 0
    (face := .rich butterflyCreditBearingInitialInstruction) paid.2
  have settled := retained.2.1.resolved.settlement
  rw [retained.2.2, add_zero] at settled
  exact settled

/-- A fresh material instruction comes from the canonical complete
disposition. All clock credit stays in `clock`; no second reserved bank is
minted, and no future instruction is accepted. -/
def advance (stage : Nat)
    (instruction : InstructionAt (source.stateAfter stage))
    (solvent : source.clockAt (source.stateAfter stage) ≤ instruction.clock.potential) :
    Σ nextInstruction : InstructionAt (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
        instruction.clock nextInstruction.clock
        (nativeFluidMediumRootOperationalOutcomeAt source (source.stateAfter stage)) := by
  let disposition := sourceGeneratedStandingActionRunClockDisposition
    stackedInitialActionMaterialInstruction stage
  let nextInstruction : InstructionAt (source.stateAfter (stage + 1)) :=
    { material := butterflyCompleteCreditNextInstruction stage disposition ⟨0, le_rfl⟩
      clock := ⟨instruction.clock.potential - source.clockAt (source.stateAfter stage),
        sub_nonneg.mpr solvent⟩ }
  let paid : SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      instruction.clock nextInstruction.clock :=
    { waste := 0
      waste_nonneg := le_rfl
      settlement := by dsimp [nextInstruction]; ring }
  refine ⟨nextInstruction, ?_⟩
  generalize nativeFluidMediumRootOperationalOutcomeAt source
    (source.stateAfter stage) = outcome
  cases outcome with
  | exactPayment => exact .exactPayment paid
  | generatedResidual => exact .generatedResidual paid
  | obstruction => exact .obstructionAlternative paid

theorem advance_predecessor (stage : Nat)
    (instruction : InstructionAt (source.stateAfter stage))
    (solvent : source.clockAt (source.stateAfter stage) ≤ instruction.clock.potential) :
    (advance stage instruction solvent).1.material.predecessor? =
      some ⟨stage, nativeFluidMediumRootOperationalOutcomeAt source (source.stateAfter stage),
        ⟨sourceGeneratedStandingActionRunClockDisposition
          stackedInitialActionMaterialInstruction stage, rfl⟩⟩ := by
  rfl

/-- The old three-face residual can continue through the full instruction
whenever its total physical account is solvent. This is one actual edge. -/
def advanceResidual
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face)
    (_shortfall : ButterflyCreditClockFaceResidualAt stage face
      (sourceGeneratedStandingActionRunClockDisposition
        stackedInitialActionMaterialInstruction stage))
    (solvent : 0 ≤ physicalKineticAccount (stage + 1) +
      physicalDensityReserve (stage + 1)) :
    Σ nextInstruction : InstructionAt (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
        face.clockState nextInstruction.clock
        (nativeFluidMediumRootOperationalOutcomeAt source (source.stateAfter stage)) := by
  apply advance stage (faceInstruction face)
  change source.clockAt (source.stateAfter stage) ≤ face.clockState.potential
  rw [reachable_potential_eq_kinetic_add_densityReserve reachable]
  have kinetic := physicalKineticAccount_step stage
  have density := physicalDensityReserve_step stage
  linarith

end
end SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.FullSource
