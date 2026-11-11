import H0mework.Foundation.Runtime.Activation
import H0mework.Arithmetic.PrimeShadow.LivingLawRootAnswerNextHistoryRegression

/-!
# Regression: canonical activation and dormant-authority rejection

The fixture begins at a compiler-generated local terminal, enters its fixed
handoff root, and then unfolds ordinary native writes.  Runtime activation
adds no branch or successor choice.  A Boolean payload which resembles an
installed result but disagrees with the fixed source projection cannot obtain
active-authority coverage.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalActivationRuntimeRegression

open RootAnswerNextRegression
open RootAnswerNextHistoryRegression
open SourceNativeRootAuthorityRegression

abbrev N := SourceNativeLedgerCompilerRegression.N

/-- The only seed constructor starts at the source process's own initial
state. -/
def terminalRuntimeState : LivingRuntimeState process :=
  .initial process

/-- Later runtime states are generated only by canonical `next`. -/
def writeRuntimeState : LivingRuntimeState process :=
  terminalRuntimeState.tick.next

def secondWriteRuntimeState : LivingRuntimeState process :=
  writeRuntimeState.tick.next

/-- The local terminal still advances through the source-fixed handoff. -/
theorem terminal_tick_next_is_first_write :
    terminalRuntimeState.tick.next.state = some 0 :=
  rfl

/-- An ordinary write advances to the next exact temporal visit. -/
theorem write_tick_next_is_second_write :
    writeRuntimeState.tick.next.state = some 1 :=
  rfl

/-- Re-evaluating one state returns the same activation occurrence. -/
theorem fixed_state_has_one_tick
    (left right : ExactActivatedRootOccurrenceAt writeRuntimeState) :
    left = right := by
  exact left.eq_tick.trans right.eq_tick.symm

/-- Zero fuel is observation exhaustion, not a terminal branch. -/
theorem zero_fuel_retains_current :
    writeRuntimeState.run 0 =
      @SourceNativeLivingRootHistoryAt.exhausted
        N process writeRuntimeState.state :=
  rfl

theorem terminal_tick_kind :
    terminalRuntimeState.tick.structuralKind = .faithfulTerminal :=
  rfl

theorem write_tick_kind :
    writeRuntimeState.tick.structuralKind = .nativeWrite :=
  rfl

/-- The runtime reuses the existing finite history and unfolds three actual
successors without a caller selecting their branches. -/
theorem three_ticks_reach_fourth_write_visit :
    historyTarget (writeRuntimeState.run 3) = some 3 :=
  rfl

/-- A receipt indexed by another current cannot be replayed as this state's
activation token. -/
theorem sibling_current_activation_cannot_replay : True := by
  fail_if_success
    exact (terminalRuntimeState.tick :
      ExactActivatedRootOccurrenceAt writeRuntimeState)
  trivial

/- The runtime-state constructor is private: arbitrary process states cannot
be activated without an `initial`/`next` reachability derivation. -/
/-- error: Unknown constant `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingRuntimeState.mk` -/
#guard_msgs in
#check LivingRuntimeState.mk

/- An installed projection alone no longer mints active authority. -/
/-- error: Unknown identifier `SourceNativeActivatedAuthorityCoverageAt.ofInstalled` -/
#guard_msgs in
#check SourceNativeActivatedAuthorityCoverageAt.ofInstalled

/- Generated material histories cannot carry a caller-supplied completed
trace or output through their private constructor. -/
/-- error: Unknown constant `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRuntimeMaterialHistoryAt.mk` -/
#guard_msgs in
#check SourceGeneratedRuntimeMaterialHistoryAt.mk

/- No generic evaluator program exists in the authority core. -/
/-- error: Unknown identifier `SourceNativeRuntimeCalculationProgramAt.mk` -/
#guard_msgs in
#check SourceNativeRuntimeCalculationProgramAt.mk

/- Domain payloads cannot mint a generated authority token directly. -/
/-- error: Unknown identifier `SourceGeneratedRuntimeAuthorityAt.mk` -/
#guard_msgs in
#check SourceGeneratedRuntimeAuthorityAt.mk

/- An installed face has a readout but no generic calculation-program
promotion mouth. -/
/-- error: Unknown identifier `SourceNativeRuntimeCalculationProgramAt.ofInstalledProjection` -/
#guard_msgs in
#check SourceNativeRuntimeCalculationProgramAt.ofInstalledProjection

/- A strike cannot choose a material carrier or seed function. -/
/-- error: Unknown identifier `SourceNativeRuntimeCalculationCandidateAt` -/
#guard_msgs in
#check SourceNativeRuntimeCalculationCandidateAt

/-- Reachability proof paths are not runtime identity. -/
theorem same_process_state_is_same_runtime
    (left right : LivingRuntimeState process)
    (state_eq : left.state = right.state) : left = right :=
  LivingRuntimeState.ext state_eq

def writeProjectionInstallation :
    SourceNativeProjectionLaw.InstallationAt
      (boolProjectionLaw false)
      writeRuntimeState.current.root.toAuthoritativeRoot.source.projectionLaw :=
  .ofEq rfl

abbrev WriteProjectionOutcome :=
  SourceNativeProjectionFiberAt (boolProjectionLaw false) ()
    writeRuntimeState.emittedOccurrence

def installedFalseOutcome : WriteProjectionOutcome :=
  .inl ⟨(), false⟩

def dormantTrueOutcome : WriteProjectionOutcome :=
  .inl ⟨(), true⟩

/-- Installed payloads remain exact readouts.  They are intentionally not
calculation programs. -/
def installedFalseRead : SourceNativeInstalledProjectionReadAt
    writeRuntimeState (boolProjectionLaw false) writeProjectionInstallation () :=
  .generate writeRuntimeState (boolProjectionLaw false)
    writeProjectionInstallation ()

theorem installedFalseRead_eq : installedFalseRead.output = installedFalseOutcome :=
  rfl

/-- Positive generative calculation is the fixed nonempty history itself. -/
def generatedTargetHistory :
    SourceGeneratedRuntimeMaterialHistoryAt writeRuntimeState 1 :=
  .generate writeRuntimeState 1

theorem generatedTargetHistory_eq_successor :
    generatedTargetHistory.target.state =
      process.successor writeRuntimeState.state :=
  rfl

/-- A same-carrier value is not a generated history. -/
theorem dormant_true_is_readout_only : True := by
  fail_if_success
    exact (dormantTrueOutcome :
      SourceGeneratedRuntimeMaterialHistoryAt writeRuntimeState 1)
  trivial

/-! A named facade closes the installed readout inventory.  It does not
inspect theorem names, synthesize a component after activation, or promote
the readout to calculation authority. -/

def cofinalFacade : SourceNativeLivingRuntimeFacade N where
  process := cofinalProcess
  FaceAt := fun _runtime => PUnit
  componentAt := fun _runtime _face => boolProjectionLaw false
  installationAt := fun _runtime _face => .ofEq rfl
  projectionAt := fun _runtime _face => ()

def cofinalFacadeSeed : LivingRuntimeState cofinalFacade.process :=
  cofinalFacade.seed

abbrev CofinalFacadeOutcome :=
  SourceNativeProjectionFiberAt (boolProjectionLaw false) ()
    cofinalFacadeSeed.emittedOccurrence

def cofinalFacadeFalseOutcome : CofinalFacadeOutcome :=
  cofinalFacade.readoutAt cofinalFacadeSeed PUnit.unit

def cofinalFacadeDormantTrueOutcome : CofinalFacadeOutcome :=
  .inl ⟨(), true⟩

set_option linter.defProp false in
def named_facade_readout_factorizes :=
  cofinalFacade.readoutAt_factorizes cofinalFacadeSeed PUnit.unit

/-- The same typed payload cannot be replayed as a generated history. -/
theorem named_facade_rejects_dormant_true : True := by
  fail_if_success
    exact (cofinalFacadeDormantTrueOutcome :
      SourceGeneratedRuntimeMaterialHistoryAt cofinalFacadeSeed 1)
  trivial

/-! The source fixes the obstruction, local Prop-valued law, stage count and
target coordinate.  Realization can only prove those laws; it cannot submit
material data or an answer. -/

def localCalculationFrontier : SourceNativeRuntimeCalculationFrontierAt
    cofinalFacade cofinalFacadeSeed PUnit.unit :=
  .ofActive () rfl 2 (fun _stage _obstruction generatedStage =>
    generatedStage.next.current = generatedStage.activated.nextCurrent)

theorem localCalculationRealization :
    SourceNativeRuntimeCalculationRealizationAt localCalculationFrontier where
  operationAt := fun _stage => rfl

def localCalculationNormalForm :
    SourceGeneratedRuntimeCalculationNormalFormAt
      localCalculationRealization :=
  .generate localCalculationRealization

theorem localCalculationTarget_is_generated :
    localCalculationNormalForm.targetRuntime =
      cofinalFacadeSeed.advance 3 :=
  rfl

set_option linter.defProp false in
def localCalculationTarget_factorizes :=
  localCalculationNormalForm.target_factorizes

/- The normal-form constructor is private; source-fixed realization is the
only positive generator. -/
/-- error: Unknown constant `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRuntimeCalculationNormalFormAt.mk` -/
#guard_msgs in
#check SourceGeneratedRuntimeCalculationNormalFormAt.mk

/- A completed installed face cannot be used as a proof-only realization. -/
theorem installed_face_cannot_become_calculation_realization : True := by
  fail_if_success
    exact (cofinalFacadeFalseOutcome :
      SourceNativeRuntimeCalculationRealizationAt localCalculationFrontier)
  trivial

#print axioms LivingRuntimeState.tick_nextState_eq
#print axioms LivingRuntimeState.tick_occurrence_eq
#print axioms ExactActivatedRootOccurrenceAt.eq_tick
#print axioms LivingRuntimeState.run_zero
#print axioms ExactActivatedRootOccurrenceAt.structuralKind
#print axioms dormant_true_is_readout_only
#print axioms LivingRuntimeState.ext
#print axioms SourceNativeInstalledProjectionReadAt.output
#print axioms SourceGeneratedRuntimeMaterialStageAt.factorizes
#print axioms SourceGeneratedRuntimeMaterialHistoryAt.eq
#print axioms SourceGeneratedRuntimeMaterialHistoryAt.target_factorizes
#print axioms generatedTargetHistory_eq_successor
#print axioms SourceNativeLivingRuntimeFacade.readoutAt_factorizes
#print axioms named_facade_rejects_dormant_true
#print axioms SourceGeneratedRuntimeCalculationNormalFormAt.unique
#print axioms SourceGeneratedRuntimeCalculationNormalFormAt.unique_over_frontier
#print axioms SourceGeneratedRuntimeCalculationNormalFormAt.target_factorizes
#print axioms localCalculationRealization
#print axioms localCalculationTarget_factorizes

end CanonicalActivationRuntimeRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
