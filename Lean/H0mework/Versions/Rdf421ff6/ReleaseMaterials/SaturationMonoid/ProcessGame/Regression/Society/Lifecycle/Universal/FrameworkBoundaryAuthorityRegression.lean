import H0mework.Foundation.Agency.OriginExit
import H0mework.Foundation.Agency.Succession
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.AcceptedResponsibilityTransfer

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace Society
namespace Lifecycle
namespace Universal
namespace FrameworkBoundaryAuthorityRegression

open ResponsibilityLifecycle
open _root_.SaturationMonoid.ProcessGame.Society.Lifecycle
open _root_.SaturationMonoid.ProcessGame.Society.Lifecycle.Universal

abbrev V := LifecycleVocabulary

local instance : DecidableEq V.Bearer := by
  change DecidableEq ActorBearer
  infer_instance

inductive BoundaryEvent (obligation : AdmittedObligation V) where
  | maintain
  | transfer
      (nextBearer : V.Bearer)
      (receipt : V.TransferAcceptedAt .after obligation.bearer
        nextBearer obligation.scope)
  | final

def boundaryDisposition {obligation : AdmittedObligation V} :
    BoundaryEvent obligation →
      BoundaryDisposition V obligation EventState.after
  | .maintain => .carry (.maintained ())
  | .transfer nextBearer receipt =>
      .carry (.transferred nextBearer receipt)
  | .final => .terminal (.final (.fulfilled ()))

structure ReopenLineageAt (archive : TerminalArchive V) : Type where
  sameLineage : sourceObligationPayload.lineage = archive.obligation.lineage

def reopenPayload (archive : TerminalArchive V)
    (event : ReopenLineageAt archive) :
    NativeReopenPayload V archive where
  sourceEvent := .before
  admission := sourceObligationPayload
  source_eq := rfl
  incidence := ()
  lineage_eq := event.sameLineage
  anchorTransport := SourceAnchorTransport.refl _

def process : NativeResponsibilityProcess V where
  AdmissionEvent := Unit
  admissionPayload := fun _ => sourceObligationPayload
  BoundaryEvent := BoundaryEvent
  boundarySource := fun _ => .after
  boundary_anchor_eq := fun _ => rfl
  boundary_incidence_eq := fun _ => rfl
  boundaryDisposition := boundaryDisposition
  ReopenEvent := ReopenLineageAt
  reopenPayload := fun {_} event => reopenPayload _ event

abbrev P := process

def emptyState : ResponsibilityState V := ResponsibilityState.empty V

def admitEdge : P.Edge emptyState := .admit ()

def admittedState : ResponsibilityState V := admitEdge.target

def admittedSlot : Fin admittedState.slots.length :=
  ⟨0, by simp [admittedState, admitEdge, emptyState,
    NativeResponsibilityProcess.Edge.target]⟩

theorem admittedPresent :
    admittedState.slots.get admittedSlot = .live sourceObligation :=
  rfl

def maintainEdge : P.Edge admittedState :=
  .cross admittedSlot sourceObligation admittedPresent .maintain

def transferEdge : P.Edge admittedState :=
  .cross admittedSlot sourceObligation admittedPresent
    (.transfer (.target .t4) exactAcceptedTransferReceipt)

def finalEdge : P.Edge admittedState :=
  .cross admittedSlot sourceObligation admittedPresent .final

def terminalArchive : TerminalArchive V :=
  ⟨sourceObligation, .after, .fulfilled ()⟩

def terminalState : ResponsibilityState V := finalEdge.target

def terminalSlot : Fin terminalState.slots.length :=
  ⟨0, by simp [terminalState, finalEdge, admittedState, admitEdge, emptyState,
    NativeResponsibilityProcess.Edge.target]⟩

theorem terminalPresent :
    terminalState.slots.get terminalSlot = .terminal terminalArchive :=
  rfl

def reopenEdge : P.Edge terminalState :=
  .reopen terminalSlot terminalArchive terminalPresent ⟨rfl⟩

theorem admit_compile_hits :
    (FreshAdmissionEdge.compile P admitEdge).isSome = true :=
  rfl

def admissionAuthority : FreshAdmissionEdge P admitEdge :=
  (FreshAdmissionEdge.compile P admitEdge).get admit_compile_hits

theorem admission_target_slot :
    admitEdge.target.slots[admissionAuthority.slot P]? =
      some (.live (admissionAuthority.targetObligation P)) :=
  admissionAuthority.target_slot P

theorem admission_is_freshly_allocated :
    ResponsibilityState.FreshlyAllocatedAt emptyState admitEdge.target
      (admissionAuthority.slot P) :=
  admissionAuthority.freshlyAllocated P

theorem reopen_compile_hits :
    (ReopenEdge.compile P reopenEdge).isSome = true :=
  rfl

def reopenAuthority : ReopenEdge P reopenEdge :=
  (ReopenEdge.compile P reopenEdge).get reopen_compile_hits

theorem reopen_target_slot :
    reopenEdge.target.slots[reopenAuthority.slot P]? =
      some (.live (reopenAuthority.targetObligation P)) :=
  reopenAuthority.target_slot P

theorem reopen_preserves_same_debt_lineage :
    SameDebtLineage reopenAuthority.archive.obligation
      (reopenAuthority.targetObligation P) :=
  reopenAuthority.sameDebtLineage P

def reopenAnchorTransport :
    SourceAnchorTransport reopenAuthority.archive.obligation.sourceAnchor
      (reopenAuthority.targetObligation P).sourceAnchor :=
  reopenAuthority.anchorTransport P

theorem final_compile_hits :
    (FinalExitEdge.compile P finalEdge).isSome = true :=
  rfl

def finalExitAuthority : FinalExitEdge P finalEdge :=
  (FinalExitEdge.compile P finalEdge).get final_compile_hits

theorem final_exit_target_slot :
    finalEdge.target.slots[finalExitAuthority.slot P]? =
      some (.terminal (finalExitAuthority.targetArchive P)) :=
  finalExitAuthority.target_slot P

theorem final_exit_disappears :
    ResponsibilityState.DisappearsAt admittedState finalEdge.target
      (finalExitAuthority.slot P) :=
  finalExitAuthority.disappears P

theorem framework_succession_compile_hits :
    (FrameworkSuccessionEdge.compile transferEdge).isSome = true :=
  rfl

def frameworkSuccession : FrameworkSuccessionEdge P transferEdge :=
  (FrameworkSuccessionEdge.compile transferEdge).get
    framework_succession_compile_hits

theorem framework_succession_compile_eq :
    FrameworkSuccessionEdge.compile transferEdge = some frameworkSuccession :=
  (Option.some_get framework_succession_compile_hits).symm

theorem concrete_transfer_bearers_differ :
    sourceObligation.bearer ≠
      (ActiveCarryDisposition.transferred (ActorBearer.target .t4)
        exactAcceptedTransferReceipt).target.bearer := by
  decide

theorem framework_succession_bearers_differ :
    frameworkSuccession.oldObligation.bearer ≠
      frameworkSuccession.nextObligation.bearer := by
  change sourceObligation.bearer ≠
    (ActiveCarryDisposition.transferred (ActorBearer.target .t4)
      exactAcceptedTransferReceipt).target.bearer
  exact concrete_transfer_bearers_differ

theorem exact_succession_compile_hits :
    (ExactSuccessionAt.compile transferEdge).isSome = true :=
  by
    unfold ExactSuccessionAt.compile
    rw [framework_succession_compile_eq]
    simp [framework_succession_bearers_differ]
    split <;> rfl

def exactSuccession : ExactSuccessionAt P transferEdge :=
  (ExactSuccessionAt.compile transferEdge).get exact_succession_compile_hits

theorem succession_source_event :
    exactSuccession.sourceEvent = EventState.after :=
  rfl

def successionOldNext : AdmittedObligation V × AdmittedObligation V :=
  (exactSuccession.oldObligation, exactSuccession.nextObligation)

theorem succession_target_slot :
    transferEdge.target.slots[frameworkSuccession.sourceSlot.val]? =
      some (.live frameworkSuccession.nextObligation) :=
  frameworkSuccession.targetSlot_contains_next

theorem succession_same_debt_and_bearer_changed :
    SameDebtLineage exactSuccession.oldObligation
        exactSuccession.nextObligation ∧
      exactSuccession.authority.BearerChanged :=
  ⟨exactSuccession.sameDebtLineage, exactSuccession.bearerChanged⟩

theorem maintain_and_transfer_do_not_forge_reopen :
    ReopenEdge.compile P maintainEdge = none ∧
      ReopenEdge.compile P transferEdge = none :=
  ⟨rfl, rfl⟩

theorem maintain_and_transfer_do_not_forge_final_exit :
    FinalExitEdge.compile P maintainEdge = none ∧
      FinalExitEdge.compile P transferEdge = none :=
  ⟨rfl, rfl⟩

def sameBearerVocabulary : Vocabulary :=
  { actorLifecycleVocabulary with
    TransferAcceptedAt := fun _ _ _ _ => Unit }

abbrev SameV := sameBearerVocabulary

local instance : DecidableEq SameV.Bearer := by
  change DecidableEq ActorBearer
  infer_instance

def sameBearerPayload : NativeAdmissionPayload SameV where
  sourceEvent := .before
  content := ()
  residual := ()
  bearer := .source .s5
  beneficiary := ()
  scope := ()
  lineage := .debt
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

inductive SameBoundary (_ : AdmittedObligation SameV) | transfer

def sameBearerProcess : NativeResponsibilityProcess SameV where
  AdmissionEvent := PEmpty
  admissionPayload := fun event => nomatch event
  BoundaryEvent := SameBoundary
  boundarySource := fun _ => .after
  boundary_anchor_eq := fun _ => rfl
  boundary_incidence_eq := fun _ => rfl
  boundaryDisposition := fun {obligation} _ =>
    .carry (.transferred obligation.bearer ())
  ReopenEvent := fun _ => PEmpty
  reopenPayload := fun {_} event => nomatch event

abbrev SameP := sameBearerProcess

def sameBearerState : ResponsibilityState SameV :=
  ⟨[.live sameBearerPayload.toObligation], []⟩

def sameBearerSlot : Fin sameBearerState.slots.length := ⟨0, by simp [sameBearerState]⟩

theorem sameBearerPresent :
    sameBearerState.slots.get sameBearerSlot =
      .live sameBearerPayload.toObligation := rfl

def sameBearerTransfer : SameP.Edge sameBearerState :=
  .cross sameBearerSlot sameBearerPayload.toObligation sameBearerPresent
    .transfer

theorem same_bearer_raw_succession_hits :
    (FrameworkSuccessionEdge.compile sameBearerTransfer).isSome = true := rfl

theorem same_bearer_exact_succession_rejected :
    ExactSuccessionAt.compile sameBearerTransfer = none := rfl

end FrameworkBoundaryAuthorityRegression
end Universal
end Lifecycle
end Society
end Regression
end ProcessGame
end SaturationMonoid
