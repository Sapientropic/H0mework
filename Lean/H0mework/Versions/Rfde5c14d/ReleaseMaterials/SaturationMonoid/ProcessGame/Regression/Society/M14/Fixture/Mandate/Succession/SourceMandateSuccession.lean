import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.SourceMandateRenewal

/-!
# Source-native mandate succession

The existing exit history receives one genuinely later continuing event.  Its
office seed is transported from the exit current, while its controller seed
is the successor of the controller-maximum fold over the existing occurrence.
The existing election lineage compiler generates the successor controller,
persistent office relation, renewed phase/role, restored power and live
obligation from that event.

No compiler, root, ledger, participant registry, election schedule or
completed future is added.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceMandateSuccession

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Election Relations Power Renewal
open M8ActualElectionMandateRenewalRegression
open M14SourceMandateRenewal

/-! ## Actual successor occurrence -/

/-- Source fold selecting the maximum controller seed in one exact election
occurrence.  Branch maxima are compiled before the current root. -/
def sourceMandateControllerMaximumAlgebra
    (event : ActualEvent) (branchMaxima : List Nat) : Nat :=
  branchMaxima.foldl Nat.max event.controllerSeed

/-- Closed controller maximum of the existing exit occurrence. -/
def sourceMandateExitControllerMaximum : Nat :=
  sourceMandateExitHistory.occurrence.fold
    sourceMandateControllerMaximumAlgebra

@[simp] theorem sourceMandateExitControllerMaximum_exact :
    sourceMandateExitControllerMaximum = 13 :=
  rfl

/-- The successor seed is generated from the closed source fold, rather than
written into the successor event. -/
def sourceMandateSuccessorControllerSeed : Nat :=
  sourceMandateExitControllerMaximum + 1

def sourceMandateSuccessorPeriod : Nat :=
  sourceMandateExitHistory.current.period + 1

def sourceMandateSuccessorOfficeSeed : Nat :=
  sourceMandateExitHistory.current.officeSeed

@[simp] theorem sourceMandateSuccessorControllerSeed_exact :
    sourceMandateSuccessorControllerSeed = 14 := by
  rw [sourceMandateSuccessorControllerSeed,
    sourceMandateExitControllerMaximum_exact]

theorem sourceMandateSuccessorControllerSeed_ne_standing :
    sourceMandateSuccessorControllerSeed ≠
      sourceMandateHistory.current.controllerSeed := by
  rw [sourceMandateSuccessorControllerSeed_exact]
  change (14 : Nat) ≠ 11
  decide

theorem sourceMandateSuccessorControllerSeed_ne_exit :
    sourceMandateSuccessorControllerSeed ≠
      sourceMandateExitHistory.current.controllerSeed := by
  rw [sourceMandateSuccessorControllerSeed_exact]
  change (14 : Nat) ≠ 13
  decide

/-- Every evaluator commuting with the sole occurrence constructor agrees
with the controller-maximum fold on this source occurrence. -/
theorem sourceMandateExitControllerMaximum_fold_unique
    (candidate : RootedAccountedUnfolding ActualEvent → Nat)
    (commutes : ∀ (origin : ActualEvent)
        (branches : AccountedBranches ActualEvent),
      candidate (.occur origin branches) =
        sourceMandateControllerMaximumAlgebra origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate sourceMandateExitHistory.occurrence =
      sourceMandateExitControllerMaximum :=
  RootedAccountedUnfolding.fold_unique
    sourceMandateControllerMaximumAlgebra candidate commutes
      sourceMandateExitHistory.occurrence

/-- A real next mandate event.  Period, office and controller are all read
from the existing exit occurrence and its fold. -/
def sourceMandateSuccessorEvent : ActualEvent :=
  { period := sourceMandateSuccessorPeriod
    officeSeed := sourceMandateSuccessorOfficeSeed
    controllerSeed := sourceMandateSuccessorControllerSeed
    disposition := .continue }

def sourceMandateSuccessorHistory : ActualHistory :=
  .next sourceMandateExitHistory sourceMandateSuccessorEvent

abbrev SourceMandateSuccessorGame :=
  SourceMandateGameFor sourceMandateSuccessorHistory

abbrev SourceMandateSuccessorSeed :=
  SourceMandateSeedFor sourceMandateSuccessorHistory

abbrev SourceMandateSuccessorSeedAt :=
  SourceMandateSeedAtFor sourceMandateSuccessorHistory

abbrev SourceMandateSuccessorConsumerAt :=
  SourceMandateConsumerAtFor sourceMandateSuccessorHistory

abbrev SourceMandateSuccessorDispositionAt :=
  SourceMandateDispositionAtFor sourceMandateSuccessorHistory

abbrev SourceMandateSuccessorRenewalFace :=
  SourceMandateRenewalFaceFor sourceMandateSuccessorHistory

def sourceMandateSuccessorFace : SourceMandateSuccessorRenewalFace :=
  sourceMandateRenewalFaceFor sourceMandateSuccessorHistory

abbrev sourceMandateSuccessorSeed :=
  sourceMandateSeedFor sourceMandateSuccessorHistory

def sourceMandateSuccessorConsumer :
    SourceMandateSuccessorConsumerAt sourceMandateSuccessorSeed :=
  sourceMandateConsumerFor sourceMandateSuccessorHistory

def sourceMandateSuccessorDisposition :
    SourceMandateSuccessorDispositionAt sourceMandateSuccessorSeed :=
  sourceMandateDispositionFor sourceMandateSuccessorHistory

theorem sourceMandateSuccessor_retains_exit_current :
    sourceMandateExitHistory.current ∈
      sourceMandateSuccessorHistory.occurrence.trace :=
  MandateHistory.prior_current_mem_next_trace sourceMandateExitHistory
    sourceMandateSuccessorEvent

@[simp] theorem sourceMandateSuccessor_current_exact :
    sourceMandateSuccessorHistory.current = sourceMandateSuccessorEvent :=
  rfl

@[simp] theorem sourceMandateSuccessor_face_event_exact :
    sourceMandateSuccessorFace.event = sourceMandateSuccessorHistory.current :=
  rfl

/-! ## Fresh controller and persistent office relation -/

@[simp] theorem sourceMandateSuccessor_controller_lineage_exact :
    sourceMandateSuccessorFace.actor.1 =
      sourceMandateSuccessorControllerSeed :=
  rfl

theorem sourceMandateSuccessor_controller_is_fresh :
    sourceMandateSuccessorFace.actor.1 ≠
        sourceMandateHistory.current.controllerSeed ∧
      sourceMandateSuccessorFace.actor.1 ≠
        sourceMandateExitHistory.current.controllerSeed := by
  rw [sourceMandateSuccessor_controller_lineage_exact]
  exact ⟨sourceMandateSuccessorControllerSeed_ne_standing,
    sourceMandateSuccessorControllerSeed_ne_exit⟩

theorem sourceMandateSuccessor_office_relation_has_exact_trace :
    OfficeRelationTraceAt sourceMandateSuccessorHistory :=
  electionRenewal_relation_exact_trace_provenance
    sourceMandateSuccessorHistory lineageCompiler

theorem sourceMandateSuccessor_office_and_relation_exact :
    (mandateOffice sourceMandateSuccessorHistory lineageCompiler).1 =
        lineageCompiler.officeOf
          sourceMandateSuccessorHistory.current.officeSeed ∧
      (mandateOffice sourceMandateSuccessorHistory lineageCompiler).1 =
        (mandateOffice sourceMandateExitHistory lineageCompiler).1 ∧
      (generatedOfficeControllerRelation sourceMandateSuccessorHistory
          lineageCompiler).1.office = 7 ∧
      (generatedOfficeControllerRelation sourceMandateSuccessorHistory
          lineageCompiler).1.controller =
        sourceMandateSuccessorControllerSeed :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The office/controller group relation is generated by the existing exact
relation seed and compiler transport. -/
theorem sourceMandateSuccessor_group_relation_generated :
    (officeControllerRelationCompiler sourceMandateSuccessorHistory
      lineageCompiler).GeneratedInterestAt
        (mandateOffice sourceMandateSuccessorHistory lineageCompiler)
        (generatedOfficeControllerRelation sourceMandateSuccessorHistory
          lineageCompiler) :=
  (mandateActionPower sourceMandateSuccessorHistory
    lineageCompiler).constraint.interest

/-! ## Renewed standing, power and responsibility -/

/-- Succession starts with a new admission edge into an empty local state.
It is not a reopening of the terminal archive produced by the prior exit. -/
def sourceMandateSuccessorAdmissionEdge :
    (mandateProcess lineageCompiler).Edge
      (ResponsibilityState.empty (mandateVocabulary lineageCompiler)) :=
  mandateAdmissionEdge lineageCompiler sourceMandateSuccessorHistory.current

@[simp] theorem sourceMandateSuccessorAdmissionEdge_kind :
    sourceMandateSuccessorAdmissionEdge.lifecycleEvent.kind =
      LifecycleKind.admitted :=
  rfl

theorem sourceMandateSuccessor_has_no_terminal_reopen
    (archive : TerminalArchive (mandateVocabulary lineageCompiler)) :
    IsEmpty ((mandateProcess lineageCompiler).ReopenEvent archive) :=
  ⟨fun reopen => nomatch reopen⟩

@[simp] theorem sourceMandateSuccessor_relation_phase_is_renew :
    (officeControllerRelationCompiler sourceMandateSuccessorHistory
      lineageCompiler).phaseStep
        (generatedOfficeControllerRelation sourceMandateSuccessorHistory
          lineageCompiler) = MandatePhase.renew :=
  rfl

@[simp] theorem sourceMandateSuccessor_target_role_is_held :
    (officeControllerRelationCompiler sourceMandateSuccessorHistory
      lineageCompiler).roleAt
        (generatedOfficeControllerRelation sourceMandateSuccessorHistory
          lineageCompiler) .target = MandateRole.held :=
  rfl

@[simp] theorem sourceMandateSuccessor_power_consumer_exact :
    sourceMandateSuccessorConsumer.1.1 =
      mandateActionPower sourceMandateSuccessorHistory lineageCompiler :=
  rfl

@[simp] theorem sourceMandateSuccessor_power_is_restored :
    sourceMandateSuccessorConsumer.1.1.freedomChange.kind =
      FreedomChangeKind.restored :=
  rfl

def sourceMandateSuccessor_M1_consumer :
    SourceOwnsResponsibilityIncidence
      (mandateVocabulary lineageCompiler)
      sourceMandateSuccessorHistory.current
      (mandateObligation lineageCompiler
        sourceMandateSuccessorHistory.current) :=
  sourceMandateSuccessorConsumer.2

theorem sourceMandateSuccessor_obligation_is_live :
    sourceMandateSuccessorDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateSuccessorHistory.current).val]? =
      some (.live
        (mandateObligation lineageCompiler
          sourceMandateSuccessorHistory.current)) :=
  electionRenewal_continues_live sourceMandateSuccessorHistory
    lineageCompiler rfl

/-- Exit and succession occupy the same ordinal in their respective one-slot
representations, but their dependent obligations are distinct because the
new admission has a fresh controller bearer. -/
@[simp] theorem sourceMandate_exit_successor_slotOrdinal_same :
    (mandateSlot lineageCompiler sourceMandateExitHistory.current).val =
      (mandateSlot lineageCompiler
        sourceMandateSuccessorHistory.current).val :=
  rfl

theorem sourceMandate_exit_successor_obligations_distinct :
    mandateObligation lineageCompiler sourceMandateExitHistory.current ≠
      mandateObligation lineageCompiler
        sourceMandateSuccessorHistory.current := by
  intro obligationEquality
  have bearerEquality := congrArg
    (fun obligation => obligation.bearer) obligationEquality
  change (13 : Nat) = 14 at bearerEquality
  omega

/-! ## Current-action exclusion -/

/-- The previous exit event remains in the successor trace but cannot be
retyped as the successor source's admitted current action. -/
theorem sourceMandateSuccessor_rejects_old_exit_as_current :
    ¬ ((electionActionController sourceMandateSuccessorHistory
      lineageCompiler).actionAdmittedAt sourceMandateExitHistory.current) := by
  intro admitted
  have controllerEq := congrArg MandateEvent.controllerSeed admitted
  exact sourceMandateSuccessorControllerSeed_ne_exit controllerEq.symm

/-! ## Direct fixture certificate -/

structure SourceMandateSuccessionCertificate : Prop where
  priorExitInTrace : sourceMandateExitHistory.current ∈
    sourceMandateSuccessorHistory.occurrence.trace
  currentExact : sourceMandateSuccessorHistory.current =
    sourceMandateSuccessorEvent
  controllerSeedFromFold : sourceMandateSuccessorControllerSeed =
    sourceMandateExitControllerMaximum + 1
  freshController : sourceMandateSuccessorFace.actor.1 =
      sourceMandateSuccessorControllerSeed ∧
    sourceMandateSuccessorFace.actor.1 ≠
      sourceMandateHistory.current.controllerSeed ∧
    sourceMandateSuccessorFace.actor.1 ≠
      sourceMandateExitHistory.current.controllerSeed
  officeRelationTrace : OfficeRelationTraceAt sourceMandateSuccessorHistory
  officePersists :
    (mandateOffice sourceMandateSuccessorHistory lineageCompiler).1 =
      (mandateOffice sourceMandateExitHistory lineageCompiler).1
  phaseRenew :
    (officeControllerRelationCompiler sourceMandateSuccessorHistory
      lineageCompiler).phaseStep
        (generatedOfficeControllerRelation sourceMandateSuccessorHistory
          lineageCompiler) = MandatePhase.renew
  roleHeld :
    (officeControllerRelationCompiler sourceMandateSuccessorHistory
      lineageCompiler).roleAt
        (generatedOfficeControllerRelation sourceMandateSuccessorHistory
          lineageCompiler) .target = MandateRole.held
  powerRestored :
    sourceMandateSuccessorConsumer.1.1.freedomChange.kind =
      FreedomChangeKind.restored
  admissionKind : sourceMandateSuccessorAdmissionEdge.lifecycleEvent.kind =
    LifecycleKind.admitted
  noTerminalReopen : ∀ archive :
      TerminalArchive (mandateVocabulary lineageCompiler),
    IsEmpty ((mandateProcess lineageCompiler).ReopenEvent archive)
  obligationLive :
    sourceMandateSuccessorDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateSuccessorHistory.current).val]? =
      some (.live
        (mandateObligation lineageCompiler
          sourceMandateSuccessorHistory.current))
  sameSlotOrdinal :
    (mandateSlot lineageCompiler sourceMandateExitHistory.current).val =
      (mandateSlot lineageCompiler
        sourceMandateSuccessorHistory.current).val
  distinctObligation :
    mandateObligation lineageCompiler sourceMandateExitHistory.current ≠
      mandateObligation lineageCompiler
        sourceMandateSuccessorHistory.current
  oldExitRejected :
    ¬ ((electionActionController sourceMandateSuccessorHistory
      lineageCompiler).actionAdmittedAt sourceMandateExitHistory.current)

theorem sourceMandateSuccessionDirectConsumer :
    SourceMandateSuccessionCertificate where
  priorExitInTrace := sourceMandateSuccessor_retains_exit_current
  currentExact := sourceMandateSuccessor_current_exact
  controllerSeedFromFold := rfl
  freshController :=
    ⟨sourceMandateSuccessor_controller_lineage_exact,
      sourceMandateSuccessor_controller_is_fresh.1,
      sourceMandateSuccessor_controller_is_fresh.2⟩
  officeRelationTrace :=
    sourceMandateSuccessor_office_relation_has_exact_trace
  officePersists := sourceMandateSuccessor_office_and_relation_exact.2.1
  phaseRenew := sourceMandateSuccessor_relation_phase_is_renew
  roleHeld := sourceMandateSuccessor_target_role_is_held
  powerRestored := sourceMandateSuccessor_power_is_restored
  admissionKind := sourceMandateSuccessorAdmissionEdge_kind
  noTerminalReopen := sourceMandateSuccessor_has_no_terminal_reopen
  obligationLive := sourceMandateSuccessor_obligation_is_live
  sameSlotOrdinal := sourceMandate_exit_successor_slotOrdinal_same
  distinctObligation := sourceMandate_exit_successor_obligations_distinct
  oldExitRejected := sourceMandateSuccessor_rejects_old_exit_as_current

theorem sourceMandateSuccession_hasNoCompletedFuture : True := by
  fail_if_success exact sourceMandateSuccessorFace.nextElection
  fail_if_success exact sourceMandateSuccessorFace.periodicTable
  fail_if_success exact sourceMandateSuccessorFace.registry
  fail_if_success exact sourceMandateSuccessorFace.completedFuture
  trivial

end
end M14SourceMandateSuccession
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceMandateSuccession.sourceMandateSuccessorFace
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceMandateSuccession.sourceMandateExitControllerMaximum_fold_unique
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceMandateSuccession.sourceMandateSuccessor_office_relation_has_exact_trace
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceMandateSuccession.sourceMandateSuccessorAdmissionEdge
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceMandateSuccession.sourceMandateSuccessor_obligation_is_live
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceMandateSuccession.sourceMandateSuccessionDirectConsumer
