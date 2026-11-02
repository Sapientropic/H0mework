import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle ComplementObservation
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable (fuel : ℚ) (inputs : List (List Action))

inductive Event
  | birth (claim : Claim fuel inputs)
  | attempt (claim : Claim fuel inputs) (receipt : Attempt fuel inputs claim)
  | reaffirmed (claim : Claim fuel inputs) (previous : Followup.Target fuel inputs claim)
      (receipt : Followup.Reconfirmation fuel inputs claim)
  | trackedAttempt (claim : Claim fuel inputs) (target : Followup.Target fuel inputs claim)
      (receipt : Attempt fuel inputs (target.claim fuel inputs))
  | crossReaffirm (claim : Claim fuel inputs) (actualInputs : List (List Action))
      (previous : Followup.Cross.Target claim actualInputs) (receipt : Followup.Cross.Reconfirmation previous)
  | crossAttempt (claim : Claim fuel inputs) (actualInputs : List (List Action))
      (target : Followup.Cross.Target claim actualInputs) (receipt : Attempt fuel actualInputs target.claim)

def Event.claim : Event fuel inputs → Claim fuel inputs
  | .birth claim | .attempt claim _ | .reaffirmed claim .. | .trackedAttempt claim .. |
      .crossReaffirm claim .. | .crossAttempt claim .. => claim

def Event.AdmissionAt : Event fuel inputs → Claim fuel inputs → Type
  | .birth original, claim => PLift (original = claim)
  | .attempt .., _ | .reaffirmed .., _ | .trackedAttempt .., _ | .crossReaffirm .., _ | .crossAttempt .., _ => Empty

def Event.ResolvedAt : Event fuel inputs → Claim fuel inputs → Financial.InstructionOrigin (I fuel inputs) → Type
  | .birth _, _, _ => Empty
  | .attempt original receipt, claim, scope => PLift (original = claim ∧ scope = claim.origin fuel inputs ∧
      law.Valid (receipt.position.item fuel inputs).before (receipt.position.item fuel inputs).request)
  | .reaffirmed .., _, _ | .trackedAttempt .., _, _ | .crossReaffirm .., _, _ | .crossAttempt .., _, _ => Empty

def Event.RefusedAt : Event fuel inputs → Claim fuel inputs → Financial.InstructionOrigin (I fuel inputs) → Type
  | .birth _, _, _ => Empty
  | .attempt original receipt, claim, scope => PLift (original = claim ∧ scope = claim.origin fuel inputs ∧
      ¬ law.Valid (receipt.position.item fuel inputs).before (receipt.position.item fuel inputs).request)
  | .reaffirmed .., _, _ | .trackedAttempt .., _, _ | .crossReaffirm .., _, _ | .crossAttempt .., _, _ => Empty

def Event.ProgressAt : Event fuel inputs → Claim fuel inputs → State Bool Unit → State Bool Unit → Type
  | .reaffirmed original previous receipt, claim, before, after =>
      PLift (original = claim ∧ before = (previous.claim fuel inputs).snapshot fuel inputs ∧
        after = receipt.target.snapshot fuel inputs ∧
        Followup.Later fuel inputs (previous.claim fuel inputs).position receipt.target.position)
  | .crossReaffirm original _ previous receipt, claim, before, after =>
      PLift (original = claim ∧ before = previous.snapshot ∧ after = receipt.target.snapshot)
  | _, _, _, _ => Empty

def Event.TrackedResolvedAt : Event fuel inputs → Claim fuel inputs → Financial.InstructionOrigin (I fuel inputs) → Type
  | .trackedAttempt original _ receipt, claim, scope => PLift (original = claim ∧ scope = claim.origin fuel inputs ∧
      law.Valid (receipt.position.item fuel inputs).before (receipt.position.item fuel inputs).request)
  | _, _, _ => Empty

def Event.TrackedRefusedAt : Event fuel inputs → Claim fuel inputs → Financial.InstructionOrigin (I fuel inputs) → Type
  | .trackedAttempt original _ receipt, claim, scope => PLift (original = claim ∧ scope = claim.origin fuel inputs ∧
      ¬ law.Valid (receipt.position.item fuel inputs).before (receipt.position.item fuel inputs).request)
  | _, _, _ => Empty

def Event.CrossResolvedAt : Event fuel inputs → Claim fuel inputs → Financial.InstructionOrigin (I fuel inputs) → Type
  | .crossAttempt original actualInputs _ receipt, claim, scope => PLift (original = claim ∧ scope = claim.origin fuel inputs ∧
      law.Valid (receipt.position.item fuel actualInputs).before (receipt.position.item fuel actualInputs).request)
  | _, _, _ => Empty

def Event.CrossRefusedAt : Event fuel inputs → Claim fuel inputs → Financial.InstructionOrigin (I fuel inputs) → Type
  | .crossAttempt original actualInputs _ receipt, claim, scope => PLift (original = claim ∧ scope = claim.origin fuel inputs ∧
      ¬ law.Valid (receipt.position.item fuel actualInputs).before (receipt.position.item fuel actualInputs).request)
  | _, _, _ => Empty

def vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event fuel inputs
  Content := Claim fuel inputs
  Residual := State Bool Unit
  Bearer := ActualBirth.Actor (I fuel inputs)
  ProtectedInterest := PublicTaskSpec Bool Good
  Scope := Financial.InstructionOrigin (I fuel inputs)
  Lineage := Financial.InstructionOrigin (I fuel inputs)
  Incidence := Financial.InstructionOrigin (I fuel inputs)
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical
    (event.claim fuel inputs).origin (event.claim fuel inputs).origin
  sourceIncidence := fun event => (event.claim fuel inputs).origin
  ObstructionAt := fun _ => Empty
  demandContent := fun impossible => nomatch impossible
  demandResidual := fun impossible => nomatch impossible
  CommitmentAt := fun _ _ => Empty
  MandateOriginAt := fun _ _ => Empty
  AcceptedTaskAt := Event.AdmissionAt fuel inputs
  ActiveDependencyAt := fun _ _ => Empty
  ProtectedRiskAt := fun _ _ => Empty
  AdmissionAuthorityAt := fun event scope => PLift (scope = (event.claim fuel inputs).origin fuel inputs)
  AcceptedAt := fun bearer event scope => PLift (bearer = (event.claim fuel inputs).actor fuel inputs ∧
    scope = (event.claim fuel inputs).origin fuel inputs)
  StandingMandateAt := fun _ _ _ => Empty
  DischargeJurisdiction := fun claim scope => PLift (scope = claim.origin fuel inputs)
  ProgressAt := Event.ProgressAt fuel inputs
  MaintenanceAt := fun _ _ _ => Empty
  TypedDeferAt := fun event claim scope => Sum (Event.RefusedAt fuel inputs event claim scope)
    (Sum (Event.TrackedRefusedAt fuel inputs event claim scope) (Event.CrossRefusedAt fuel inputs event claim scope))
  ScopeNarrowingAt := fun _ _ _ => Empty
  TransferAcceptedAt := fun _ _ _ _ => Empty
  FulfilledAt := fun event claim scope => Sum (Event.ResolvedAt fuel inputs event claim scope)
    (Sum (Event.TrackedResolvedAt fuel inputs event claim scope) (Event.CrossResolvedAt fuel inputs event claim scope))
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

abbrev V := vocabulary fuel inputs

def admission (claim : Claim fuel inputs) : NativeAdmissionPayload (V fuel inputs) where
  sourceEvent := .birth claim
  content := claim
  residual := claim.snapshot fuel inputs
  bearer := claim.actor fuel inputs
  beneficiary := task
  scope := claim.origin fuel inputs
  lineage := claim.origin fuel inputs
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .acceptedTask ⟨rfl⟩
  authority := ⟨rfl⟩
  assumption := .accepted ⟨rfl, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

def obligation (claim : Claim fuel inputs) := (admission fuel inputs claim).toObligation

structure Boundary (claim : Claim fuel inputs) (original : AdmittedObligation (V fuel inputs)) where
  attempt : Attempt fuel inputs claim
  original_eq : original = obligation fuel inputs claim

def disposition (claim : Claim fuel inputs) {original : AdmittedObligation (V fuel inputs)}
    (event : Boundary fuel inputs claim original) :
    BoundaryDisposition (V fuel inputs) original (.attempt claim event.attempt) := by
  rcases event with ⟨attempt, rfl⟩
  if accepted : law.Valid (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request then
    exact .terminal (.final (.fulfilled (.inl ⟨rfl, rfl, accepted⟩)))
  else exact .carry (.deferred (.inl ⟨rfl, rfl, accepted⟩))

def process (claim : Claim fuel inputs) : NativeResponsibilityProcess (V fuel inputs) where
  AdmissionEvent := Unit
  admissionPayload := fun _ => admission fuel inputs claim
  BoundaryEvent := Boundary fuel inputs claim
  boundarySource := fun event => .attempt claim event.attempt
  boundary_anchor_eq := fun event => by rcases event with ⟨attempt, rfl⟩; rfl
  boundary_incidence_eq := fun event => by rcases event with ⟨attempt, rfl⟩; rfl
  boundaryDisposition := disposition fuel inputs claim
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

inductive History (claim : Claim fuel inputs)
  | pending (state : (process fuel inputs claim).GeneratedState)
      (slots : state.current.slots = [.live (obligation fuel inputs claim)])
  | closed (state : (process fuel inputs claim).GeneratedState)
      (archive : TerminalArchive (V fuel inputs)) (slots : state.current.slots = [.terminal archive])

def History.state {claim : Claim fuel inputs} : History fuel inputs claim → (process fuel inputs claim).GeneratedState
  | .pending state _ | .closed state _ _ => state

def History.isPending {claim : Claim fuel inputs} : History fuel inputs claim → Bool
  | .pending .. => true
  | .closed .. => false

theorem History.live_of_pending {claim : Claim fuel inputs} (history : History fuel inputs claim)
    (pending : history.isPending fuel inputs = true) : (history.state fuel inputs).current.LiveAt 0 := by
  cases history with
  | pending state slots =>
      exact ⟨obligation fuel inputs claim, by simp [History.state, slots]⟩
  | closed state archive slots => cases pending

def History.initial (claim : Claim fuel inputs) : History fuel inputs claim :=
  .pending ((NativeResponsibilityProcess.GeneratedState.initial (process fuel inputs claim)).step (process fuel inputs claim) (.admit ())) rfl

def History.receive {claim : Claim fuel inputs} (history : History fuel inputs claim) (position : Position fuel inputs) :
    History fuel inputs claim := by
  cases history with
  | closed state archive slots => exact .closed state archive slots
  | pending state slots =>
    match readAttempt fuel inputs claim position with
    | none => exact .pending state slots
    | some attempt =>
      let address : Fin state.current.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
      have present : state.current.slots.get address = .live (obligation fuel inputs claim) := by simp [slots, address]
      let event : Boundary fuel inputs claim (obligation fuel inputs claim) := ⟨attempt, rfl⟩
      let edge : (process fuel inputs claim).Edge state.current := .cross address _ present event
      if accepted : law.Valid (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request then
        exact .closed (state.step (process fuel inputs claim) edge)
          ⟨obligation fuel inputs claim, .attempt claim attempt, .fulfilled (.inl ⟨rfl, rfl, accepted⟩)⟩ (by
            simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
              process, disposition, accepted, slots, event, address, BoundaryDisposition.targetSlot])
      else
        exact .pending (state.step (process fuel inputs claim) edge) (by
          simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
            process, disposition, accepted, slots, event, address, BoundaryDisposition.targetSlot,
            ActiveCarryDisposition.target])

def through (claim : Claim fuel inputs) : Nat → History fuel inputs claim
  | 0 => History.initial fuel inputs claim
  | ordinal + 1 => (positionsAt fuel inputs ordinal).foldl (History.receive fuel inputs) (through claim ordinal)

def recordsAt (count : Nat) : List (Sigma fun claim : Claim fuel inputs => History fuel inputs claim) :=
  (List.range count).flatMap fun ordinal => (claimsAt fuel inputs ordinal).map fun claim =>
    ⟨claim, through fuel inputs claim count⟩

theorem native_admission_allocates_live (claim : Claim fuel inputs) :
    (History.initial fuel inputs claim).state.current.LiveAt 0 := by
  exact ⟨obligation fuel inputs claim, rfl⟩

theorem original_source_is_retained (claim : Claim fuel inputs) :
    (admission fuel inputs claim).toObligation.admission.sourceEvent = .birth claim ∧
    (admission fuel inputs claim).toObligation.residual = claim.snapshot fuel inputs := ⟨rfl, rfl⟩

theorem every_decoded_claim_is_consumed (position : Position fuel inputs) (claim : Claim fuel inputs)
    (decoded : read fuel inputs position = some claim) (count : Nat) (inside : position.ordinal < count) :
    (⟨claim, through fuel inputs claim count⟩ : Sigma fun original : Claim fuel inputs => History fuel inputs original) ∈
      recordsAt fuel inputs count := by
  apply List.mem_flatMap.mpr
  refine ⟨position.ordinal, List.mem_range.mpr inside, List.mem_map.mpr ⟨claim, ?_, rfl⟩⟩
  apply List.mem_filterMap.mpr
  refine ⟨position, ?_, decoded⟩
  apply List.mem_map.mpr
  exact ⟨position.index, List.mem_finRange _, by cases position; rfl⟩

theorem fulfilled_receipt_has_actual_withdrawal (event : Event fuel inputs) (claim : Claim fuel inputs)
    (origin : Financial.InstructionOrigin (I fuel inputs)) (receipt : Event.ResolvedAt fuel inputs event claim origin) :
    ∃ attempt : Attempt fuel inputs claim, event = .attempt claim attempt ∧
      law.Valid (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request ∧
      (law.step (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request).technology.holder = none ∧
      (law.step (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request).technology.offered = none ∧
      (law.step (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request).technology.version =
        (claim.snapshot fuel inputs).version + 1 := by
  cases event with
  | birth original => exact nomatch receipt
  | reaffirmed original previous next => exact nomatch receipt
  | trackedAttempt original target attempt => exact nomatch receipt
  | crossReaffirm original actualInputs previous next => exact nomatch receipt
  | crossAttempt original actualInputs target attempt => exact nomatch receipt
  | attempt original attempt =>
    rcases receipt with ⟨rfl, scope_eq, accepted⟩
    exact ⟨attempt, rfl, accepted, attempt.actual_withdrawal fuel inputs original accepted⟩

theorem actual_native_history (claim : Claim fuel inputs) (count : Nat) :
    (through fuel inputs claim count).state.current.history =
      (through fuel inputs claim count).state.generated.events :=
  (through fuel inputs claim count).state.history_eq

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection
