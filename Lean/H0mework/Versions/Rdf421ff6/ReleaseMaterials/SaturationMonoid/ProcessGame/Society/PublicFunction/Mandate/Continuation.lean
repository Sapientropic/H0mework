import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.Disposition
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Response.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Continuation

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (input : BoundSource base scope)

abbrev source := Response.source input
abbrev bound := Response.bound input
abbrev current (depth : Nat) := (source input).currentAt (depth + 2)

/-- Admitted inputs remain actual authorization events after service
completion. Refused responses retain the original-member obstruction. -/
inductive AuthorityDisposition (depth : Nat) where
  | private received (event : (source input).ReceivedEvent (depth + 1))
  | private service (pending : (source input).pendingSlots ((source input).frameAt (depth + 2)).payments ≠ [])
  | private inactive (complete : (source input).pendingSlots ((source input).frameAt (depth + 2)).payments = [])
      (inactive : ¬ Response.Active (current input depth))
      (word : ((source input).actualExecution (depth + 1)).submitted = [])
  | private revoked (complete : (source input).pendingSlots ((source input).frameAt (depth + 2)).payments = [])
      (actor : {actor // actor ∈ Delegation.members scope.task})
      (accepted : (law base scope).Valid (current input depth) (request scope (current input depth) actor.val .revoke))
      (word : ((source input).actualExecution (depth + 1)).submitted =
        [request scope (current input depth) actor.val .revoke])
      (effect : ((source input).actualExecution (depth + 1)).after.technology.holder = none)
      (claims : ((source input).actualExecution (depth + 1)).after.claims = (current input depth).claims)
  | private blocked (complete : (source input).pendingSlots ((source input).frameAt (depth + 2)).payments = [])
      (actor : {actor // actor ∈ Delegation.members scope.task})
      (active : Response.Active (current input depth))
      (refused : ∀ candidate ∈ Delegation.members scope.task,
        ¬ (law base scope).Valid (current input depth) (request scope (current input depth) candidate .revoke))
      (word : ((source input).actualExecution (depth + 1)).submitted =
        [request scope (current input depth) actor.val .revoke])
      (unchanged : (law base scope).step (current input depth)
        (request scope (current input depth) actor.val .revoke) = current input depth)

def authorityDisposition (depth : Nat) : AuthorityDisposition input depth := by
  cases admitted : (source input).incoming? (current input depth) with
  | some incoming =>
      have present : ((source input).receivedAt (depth + 1)).isSome = true := by
        obtain ⟨event, found⟩ := (source input).admitted_input_is_received
          (depth + 1) (by omega) incoming admitted
        rw [found]
        rfl
      exact .received (((source input).receivedAt (depth + 1)).get present)
  | none =>
      by_cases complete : (source input).pendingSlots ((source input).frameAt (depth + 2)).payments = []
      · have emitted := (source input).actual_continuation_word depth
        unfold OutstandingSource.decideAt at emitted
        rw [admitted, dif_pos complete] at emitted
        change ((source input).actualExecution (depth + 1)).submitted =
          (Response.produce base scope (current input depth)).word at emitted
        generalize produced : Response.produce base scope (current input depth) = outcome at emitted
        rcases outcome with ⟨inactive⟩ | ⟨actor, active, accepted⟩ | ⟨actor, active, refused⟩
        · exact .inactive complete inactive emitted
        ·
            have effect := paid_command_effect base scope (current input depth) actor.val .revoke accepted
            have after : ((source input).actualExecution (depth + 1)).after =
                (law base scope).next (current input depth) [request scope (current input depth) actor.val .revoke] := by
              change (source input).seed.law.next (current input depth)
                ((source input).actualExecution (depth + 1)).submitted = _
              rw [emitted]
              exact congrArg (fun original => original.next (current input depth)
                [request scope (current input depth) actor.val .revoke]) (bound input).law_exact
            refine .revoked complete actor accepted emitted ?_ ?_
            · rw [after]
              exact congrArg State.holder effect.1
            · rw [after]
              exact effect.2
        ·
            exact .blocked complete actor active refused emitted
              ((law base scope).rejected_preserves_current _ _ (refused actor.val actor.property))
      · exact .service complete

inductive AuthorityKind where
  | received | service | inactive | revoked | blocked
  deriving DecidableEq, Repr

def AuthorityDisposition.kind {input : BoundSource base scope} {depth : Nat} : AuthorityDisposition input depth → AuthorityKind
  | .received .. => .received
  | .service .. => .service
  | .inactive .. => .inactive
  | .revoked .. => .revoked
  | .blocked .. => .blocked

/-- These are restrictions of one actual visit. Original native histories
are generated from their real admissions, never supplied as target states. -/
structure PublicContinuationDisposition (depth : Nat) where
  private mk ::
  service : (source input).PublicContinuationDisposition depth
  slots : (index : (source input).Slot) → (source input).SlotDisposition (depth + 1) index
  authority : AuthorityDisposition input depth
  mandates : List (Sigma fun birth : Fin (depth + 2) =>
    Lifecycle.Runtime.TracedGrant (bound input) birth.val (depth + 1))
  mandates_exact : mandates = Lifecycle.Runtime.recordsAt (bound input) (depth + 1)

def generate (depth : Nat) : PublicContinuationDisposition input depth :=
  ⟨(source input).publicDisposition depth, (source input).slotDisposition (depth + 1),
    authorityDisposition input depth, Lifecycle.Runtime.recordsAt (bound input) (depth + 1), rfl⟩

theorem every_original_mandate_is_retained (depth : Nat) (birth : Fin (depth + 2))
    (grant : Grant base scope (Lifecycle.Runtime.currentAt (bound input) birth.val)
      (Lifecycle.Runtime.wordAt (bound input) birth.val))
    (actual : grant ∈ NativeRuntime.actualGrants (bound input) birth.val) :
    (⟨birth, Lifecycle.Runtime.traceGrant (bound input) birth.val (depth + 1) grant⟩ :
      Sigma fun birth : Fin (depth + 2) => Lifecycle.Runtime.TracedGrant (bound input) birth.val (depth + 1)) ∈
        (generate input depth).mandates := by
  exact Lifecycle.Runtime.grant_is_in_payload (bound input) (depth + 1) birth grant actual

theorem original_mandate_crosses_this_actual_visit (depth birth : Nat)
    (grant : Grant base scope (Lifecycle.Runtime.currentAt (bound input) birth)
      (Lifecycle.Runtime.wordAt (bound input) birth)) :
    ((Lifecycle.Runtime.traceGrant (bound input) birth depth grant).continuation.visit (depth + 1)) =
      (Lifecycle.Runtime.traceGrant (bound input) birth (depth + 1) grant).continuation :=
  Lifecycle.through_succ depth

theorem original_mandate_never_settles_from_service_completion (depth : Nat)
    (record : Sigma fun birth : Fin (depth + 2) => Lifecycle.Runtime.TracedGrant (bound input) birth.val (depth + 1)) :
    record.2.continuation.state.LiveAt 0 :=
  record.2.continuation.responsibility_remains_live

theorem original_admission_is_not_replaced (depth : Nat)
    (record : Sigma fun birth : Fin (depth + 2) => Lifecycle.Runtime.TracedGrant (bound input) birth.val (depth + 1)) :
    HEq record.2.continuation.obligation.admission
      (Lifecycle.original base scope (Lifecycle.Runtime.currentAt (bound input))
        (Lifecycle.Runtime.wordAt (bound input)) record.1.val record.2.admission.grant).admission :=
  record.2.continuation.original_admission

def ServiceMandateClosedAt (depth : Nat) : Prop :=
  (∀ index, (OutstandingSource.NativeService.historyAt (source input) index (depth + 2)).state.TerminalAt 0) ∧
  ∀ record ∈ (generate input depth).mandates, record.2.continuation.state.TerminalAt 0

theorem registered_mandate_prevents_service_only_closure (depth : Nat) (birth : Fin (depth + 2))
    (grant : Grant base scope (Lifecycle.Runtime.currentAt (bound input) birth.val)
      (Lifecycle.Runtime.wordAt (bound input) birth.val))
    (actual : grant ∈ NativeRuntime.actualGrants (bound input) birth.val) :
    ¬ ServiceMandateClosedAt input depth := by
  intro closed
  let record : Sigma fun birth : Fin (depth + 2) =>
      Lifecycle.Runtime.TracedGrant (bound input) birth.val (depth + 1) :=
    ⟨birth, Lifecycle.Runtime.traceGrant (bound input) birth.val (depth + 1) grant⟩
  have terminal := closed.2 record (every_original_mandate_is_retained input depth birth grant actual)
  obtain ⟨archive, terminal⟩ := terminal
  rw [record.2.continuation.slots] at terminal
  cases terminal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Continuation
