import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.ScopeBoundary

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace
open ResponsibilityLifecycle ComplementObservation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type}
  (bound : ProgrammeFamily base scope Index)
  (inputs : Index)

inductive Event
  | birth (claim : Claim bound inputs)
  | reaffirm (claim : Claim bound inputs) (previous : Target bound inputs claim)
      (receipt : Reconfirmation bound inputs claim)
  | attempt (claim : Claim bound inputs) (target : Target bound inputs claim)
      (receipt : Attempt bound inputs (target.claim bound inputs))
  | remoteReaffirm (claim : Claim bound inputs)
      (actualInputs : Index)
      (previous : Cross.Target bound claim actualInputs) (receipt : Cross.Reconfirmation bound previous)
  | remoteAttempt (claim : Claim bound inputs)
      (actualInputs : Index)
      (target : Cross.Target bound claim actualInputs) (receipt : Attempt bound actualInputs target.claim)
  | scopeBoundary (claim : Claim bound inputs) (source : ScopeBoundary.Source base)
      (laterWindow : scope.task.deadline < source.scope.task.earliest) (receipt : ScopeBoundary.Receipt source)

def Event.claim : Event bound inputs → Claim bound inputs
  | .birth claim | .reaffirm claim .. | .attempt claim .. | .remoteReaffirm claim .. | .remoteAttempt claim .. | .scopeBoundary claim .. => claim

def Event.AdmissionAt : Event bound inputs → Claim bound inputs → Type
  | .birth original, claim => PLift (original = claim)
  | _, _ => Empty

def Event.ProgressAt : Event bound inputs → Claim bound inputs → State Party Technology → State Party Technology → Type
  | .reaffirm original previous receipt, claim, before, after => PLift (original = claim ∧
      before = (previous.claim bound inputs).snapshot bound inputs ∧ after = receipt.target.snapshot bound inputs ∧
      Later bound inputs (previous.claim bound inputs).position receipt.target.position)
  | .remoteReaffirm original _ previous receipt, claim, before, after => PLift (original = claim ∧
      before = previous.snapshot bound ∧ after = receipt.target.snapshot bound)
  | _, _, _, _ => Empty

def Event.ResolvedAt : Event bound inputs → Claim bound inputs → Financial.InstructionOrigin (I bound inputs) → Type
  | .attempt original _ receipt, claim, origin => PLift (original = claim ∧ origin = claim.origin bound inputs ∧
      (law base scope).Valid (receipt.position.item bound inputs).before (receipt.position.item bound inputs).request)
  | _, _, _ => Empty

def Event.RefusedAt : Event bound inputs → Claim bound inputs → Financial.InstructionOrigin (I bound inputs) → Type
  | .attempt original _ receipt, claim, origin => PLift (original = claim ∧ origin = claim.origin bound inputs ∧
      ¬ (law base scope).Valid (receipt.position.item bound inputs).before (receipt.position.item bound inputs).request)
  | _, _, _ => Empty

def Event.RemoteResolvedAt : Event bound inputs → Claim bound inputs → Financial.InstructionOrigin (I bound inputs) → Type
  | .remoteAttempt original actualInputs _ receipt, claim, origin => PLift (original = claim ∧ origin = claim.origin bound inputs ∧
      (law base scope).Valid (receipt.position.item bound actualInputs).before (receipt.position.item bound actualInputs).request)
  | _, _, _ => Empty

def Event.RemoteRefusedAt : Event bound inputs → Claim bound inputs → Financial.InstructionOrigin (I bound inputs) → Type
  | .remoteAttempt original actualInputs _ receipt, claim, origin => PLift (original = claim ∧ origin = claim.origin bound inputs ∧
      ¬ (law base scope).Valid (receipt.position.item bound actualInputs).before (receipt.position.item bound actualInputs).request)
  | .scopeBoundary original source _ receipt, claim, origin => PLift (original = claim ∧ origin = claim.origin bound inputs ∧
      receipt.accepted source = false)
  | _, _, _ => Empty

def Event.MaintainedAt : Event bound inputs → Claim bound inputs → Financial.InstructionOrigin (I bound inputs) → Type
  | .scopeBoundary original source _ receipt, claim, origin => PLift (original = claim ∧ origin = claim.origin bound inputs ∧
      receipt.accepted source = true)
  | _, _, _ => Empty

def vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event bound inputs
  Content := Claim bound inputs
  Residual := State Party Technology
  Bearer := ActualBirth.Actor (I bound inputs)
  ProtectedInterest := PublicTaskSpec Party Good
  Scope := Financial.InstructionOrigin (I bound inputs)
  Lineage := Financial.InstructionOrigin (I bound inputs)
  Incidence := Financial.InstructionOrigin (I bound inputs)
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical
    (event.claim bound inputs).origin (event.claim bound inputs).origin
  sourceIncidence := fun event => (event.claim bound inputs).origin
  ObstructionAt := fun _ => Empty
  demandContent := fun impossible => nomatch impossible
  demandResidual := fun impossible => nomatch impossible
  CommitmentAt := fun _ _ => Empty
  MandateOriginAt := fun _ _ => Empty
  AcceptedTaskAt := Event.AdmissionAt bound inputs
  ActiveDependencyAt := fun _ _ => Empty
  ProtectedRiskAt := fun _ _ => Empty
  AdmissionAuthorityAt := fun event origin => PLift (origin = (event.claim bound inputs).origin bound inputs)
  AcceptedAt := fun bearer event origin => PLift (bearer = (event.claim bound inputs).actor bound inputs ∧
    origin = (event.claim bound inputs).origin bound inputs)
  StandingMandateAt := fun _ _ _ => Empty
  DischargeJurisdiction := fun claim origin => PLift (origin = claim.origin bound inputs)
  ProgressAt := Event.ProgressAt bound inputs
  MaintenanceAt := Event.MaintainedAt bound inputs
  TypedDeferAt := fun event claim origin => Sum (Event.RefusedAt bound inputs event claim origin)
    (Event.RemoteRefusedAt bound inputs event claim origin)
  ScopeNarrowingAt := fun _ _ _ => Empty
  TransferAcceptedAt := fun _ _ _ _ => Empty
  FulfilledAt := fun event claim origin => Sum (Event.ResolvedAt bound inputs event claim origin)
    (Event.RemoteResolvedAt bound inputs event claim origin)
  WaivedAt := fun _ _ _ => Empty
  InvalidatedAt := fun _ _ _ => Empty
  AbandonedAt := fun _ _ _ => Empty
  ImpossibleResidueAcceptedAt := fun _ _ _ => Empty
  SupersessionAt := fun _ _ _ _ _ _ _ => Empty
  ReopenAt := fun _ _ _ _ _ _ _ => Empty
  JurisdictionEndedAt := fun _ _ _ => Empty
  ConsentRevokedAt := fun _ _ _ => Empty
  CapacityReleasedAt := fun _ _ _ => Empty
  UpperRouteAt := fun _ _ _ => Empty
  NextActorSignal := Empty
  AgeSignal := Empty
  TransferOfferSignal := Empty

abbrev V := vocabulary bound inputs

def admission (claim : Claim bound inputs) : NativeAdmissionPayload (V bound inputs) where
  sourceEvent := .birth claim
  content := claim
  residual := claim.snapshot bound inputs
  bearer := claim.actor bound inputs
  beneficiary := scope.task
  scope := claim.origin bound inputs
  lineage := claim.origin bound inputs
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .acceptedTask ⟨rfl⟩
  authority := ⟨rfl⟩
  assumption := .accepted ⟨rfl, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

def obligation (claim : Claim bound inputs) := (admission bound inputs claim).toObligation

def tracked (original : Claim bound inputs) (target : Target bound inputs original) : AdmittedObligation (V bound inputs) :=
  { obligation bound inputs original with residual := (target.claim bound inputs).snapshot bound inputs }

inductive Boundary (original : Claim bound inputs) (obligation : AdmittedObligation (V bound inputs))
  | reaffirm (previous : Target bound inputs original) (receipt : Reconfirmation bound inputs original)
      (later : Later bound inputs (previous.claim bound inputs).position receipt.target.position)
      (exact : obligation = tracked bound inputs original previous)
  | attempt (target : Target bound inputs original) (receipt : Attempt bound inputs (target.claim bound inputs))
      (exact : obligation = tracked bound inputs original target)

def Boundary.source {original : Claim bound inputs} {obligation : AdmittedObligation (V bound inputs)} :
    Boundary bound inputs original obligation → Event bound inputs
  | .reaffirm previous receipt _ _ => .reaffirm original previous receipt
  | .attempt target receipt _ => .attempt original target receipt

def disposition (original : Claim bound inputs) {obligation : AdmittedObligation (V bound inputs)}
    (event : Boundary bound inputs original obligation) : BoundaryDisposition (V bound inputs) obligation event.source := by
  cases event with
  | reaffirm previous receipt later exact =>
      subst obligation
      exact .carry (.progressed (receipt.target.snapshot bound inputs) ⟨rfl, rfl, rfl, later⟩)
  | attempt target receipt exact =>
      subst obligation
      if accepted : (law base scope).Valid (receipt.position.item bound inputs).before (receipt.position.item bound inputs).request then
        exact .terminal (.final (.fulfilled (.inl ⟨rfl, rfl, accepted⟩)))
      else exact .carry (.deferred (.inl ⟨rfl, rfl, accepted⟩))

def process (original : Claim bound inputs) : NativeResponsibilityProcess (V bound inputs) where
  AdmissionEvent := Unit
  admissionPayload := fun _ => admission bound inputs original
  BoundaryEvent := Boundary bound inputs original
  boundarySource := Boundary.source bound inputs
  boundary_anchor_eq := fun event => by cases event <;> subst_vars <;> rfl
  boundary_incidence_eq := fun event => by cases event <;> subst_vars <;> rfl
  boundaryDisposition := disposition bound inputs original
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

inductive History (original : Claim bound inputs)
  | pending (target : Target bound inputs original) (state : (process bound inputs original).GeneratedState)
      (slots : state.current.slots = [.live (tracked bound inputs original target)])
  | closed (state : (process bound inputs original).GeneratedState) (archive : TerminalArchive (V bound inputs))
      (slots : state.current.slots = [.terminal archive])

def History.state {original : Claim bound inputs} : History bound inputs original → (process bound inputs original).GeneratedState
  | .pending _ state _ | .closed state _ _ => state

def History.isPending {original : Claim bound inputs} : History bound inputs original → Bool
  | .pending .. => true | .closed .. => false

def History.initial (original : Claim bound inputs) : History bound inputs original :=
  .pending .initial
    ((NativeResponsibilityProcess.GeneratedState.initial (process bound inputs original)).step (process bound inputs original) (.admit ())) rfl

def History.receive {original : Claim bound inputs} (history : History bound inputs original) (position : Position bound inputs) :
    History bound inputs original := by
  cases history with
  | closed state archive slots => exact .closed state archive slots
  | pending target state slots =>
    let address : Fin state.current.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
    have present : state.current.slots.get address = .live (tracked bound inputs original target) := by simp [slots, address]
    match readReconfirmation bound inputs original position with
    | some receipt =>
      if later : Later bound inputs (target.claim bound inputs).position receipt.target.position then
        let event : Boundary bound inputs original (tracked bound inputs original target) := .reaffirm target receipt later rfl
        let edge : (process bound inputs original).Edge state.current := .cross address _ present event
        exact .pending (.renewed receipt) (state.step (process bound inputs original) edge) (by
          simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
            process, disposition, slots, event, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target, tracked, Target.claim])
      else exact .pending target state slots
    | none =>
      match readAttempt bound inputs (target.claim bound inputs) position with
      | none => exact .pending target state slots
      | some receipt =>
        let event : Boundary bound inputs original (tracked bound inputs original target) := .attempt target receipt rfl
        let edge : (process bound inputs original).Edge state.current := .cross address _ present event
        if accepted : (law base scope).Valid (receipt.position.item bound inputs).before (receipt.position.item bound inputs).request then
          exact .closed (state.step (process bound inputs original) edge)
            ⟨tracked bound inputs original target, .attempt original target receipt, .fulfilled (.inl ⟨rfl, rfl, accepted⟩)⟩ (by
              simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
                process, disposition, accepted, slots, event, address, BoundaryDisposition.targetSlot, Boundary.source])
        else
          exact .pending target (state.step (process bound inputs original) edge) (by
            simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
              process, disposition, accepted, slots, event, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target])

def through (original : Claim bound inputs) : Nat → History bound inputs original
  | 0 => History.initial bound inputs original
  | ordinal + 1 => (positionsAt bound inputs ordinal).foldl (History.receive bound inputs) (through original ordinal)

def recordsAt (count : Nat) : List (Sigma fun claim : Claim bound inputs => History bound inputs claim) :=
  (List.range count).flatMap fun ordinal => (claimsAt bound inputs ordinal).map fun claim => ⟨claim, through bound inputs claim count⟩

-- Export the shared receive equations from their defining module.
attribute [local simp] History.receive.eq_1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge
