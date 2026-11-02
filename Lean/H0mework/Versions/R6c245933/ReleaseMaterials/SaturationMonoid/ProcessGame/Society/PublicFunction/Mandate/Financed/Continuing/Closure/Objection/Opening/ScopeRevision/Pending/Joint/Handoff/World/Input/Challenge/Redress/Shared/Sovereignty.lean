import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Sovereignty
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Input.Event Input.Event.Future.Expiry.Progress.Responsibility
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

/-- The seat is an actual double-signed admission in the native census. -/
structure Seat where
  private mk ::
  record : Mandate.Challenge.Cross.GrantResident epoch.bound inventory.inputs
  member : record ∈ inventory.grants

def seats : List (Seat inventory) := inventory.grants.attach.map fun record => ⟨record.val,record.property⟩

def Seat.row (seat : Seat inventory) : Input.Event.Future.Expiry.Progress.Responsibility.Row ⟨epoch,inventory⟩ :=
  .currentGrant seat.record seat.member

def Seat.admission (seat : Seat inventory) := Mandate.admitGrant base epoch.scope
  (Mandate.Challenge.Cross.grantCurrent epoch.bound inventory.inputs seat.record.birth.val)
  (Mandate.Challenge.Cross.grantWord epoch.bound inventory.inputs seat.record.birth.val) seat.record.grant

def EffectiveJurisdiction (actor : Bool) (observed : Current) : Prop :=
  observed.technology.holder = some actor ∧ observed.clock ≤ epoch.scope.task.deadline

theorem every_actual_task_use_requires_this_jurisdiction (observed : Current)
    (action : Action) (bearer : Bool) (goods : Bundle Good) (purpose : Use)
    (operation : action.operation = .use bearer goods purpose) (taskUse : Mandate.TaskUse epoch.scope action)
    (accepted : (Mandate.law base epoch.scope).Valid observed action) :
    EffectiveJurisdiction (epoch := epoch) action.signer observed := by
  have original := Mandate.protected_use_requires_current_holder base epoch.scope _ _ bearer goods purpose operation taskUse accepted
  exact ⟨original.1,original.2.2⟩

/-- Future checks retain the original admission's jurisdiction. -/
def Seat.EffectiveAt (seat : Seat inventory) (observed : Current) : Prop :=
  seat.record.grant.proposal.item.val.request.signer ∈ Delegation.members epoch.scope.task ∧
  observed.technology.holder = some seat.record.grant.candidate ∧ observed.clock ≤ epoch.scope.task.deadline

theorem Seat.actual_admission_generates_effective_authority (seat : Seat inventory) :
    seat.EffectiveAt inventory seat.record.grant.acceptance.after := by
  refine ⟨seat.record.grant.proposal_is_by_task_member,seat.record.grant.holder_is_generated,?_⟩
  have permitted := seat.record.grant.acceptance.authorization.2.2.2.2.2
  rw [seat.record.grant.accepted_kind] at permitted
  change ((Mandate.law base epoch.scope).step _ _).clock ≤ _
  unfold RawLaw.step
  rw [if_pos seat.record.grant.acceptance.accepted]
  exact permitted.2

inductive SeatDisposition (seat : Seat inventory) (observed : Current) where
  | private effective (authority : seat.EffectiveAt inventory observed)
  | private expired (late : epoch.scope.task.deadline < observed.clock)
  | private unheld (different : observed.technology.holder ≠ some seat.record.grant.candidate)

def inspect (seat : Seat inventory) (observed : Current) : SeatDisposition inventory seat observed :=
  if late : epoch.scope.task.deadline < observed.clock then .expired late
  else if held : observed.technology.holder = some seat.record.grant.candidate then
    .effective ⟨seat.record.grant.proposal_is_by_task_member,held,le_of_not_gt late⟩
  else .unheld held

inductive SeatKind where
  | effective | expired | unheld
  deriving DecidableEq, Repr

def SeatDisposition.kind {seat : Seat inventory} {observed : Current} : SeatDisposition inventory seat observed → SeatKind
  | .effective .. => .effective | .expired .. => .expired | .unheld .. => .unheld

theorem inspect_effective_iff (seat : Seat inventory) (observed : Current) :
    (inspect inventory seat observed).kind inventory = .effective ↔ seat.EffectiveAt inventory observed := by
  unfold inspect
  split
  · constructor
    · intro impossible; cases impossible
    · intro authority
      exact False.elim (not_lt_of_ge authority.2.2 ‹_›)
  · split
    · exact ⟨fun _ => ⟨seat.record.grant.proposal_is_by_task_member,‹_›,le_of_not_gt ‹_›⟩,fun _ => rfl⟩
    · constructor
      · intro impossible; cases impossible
      · intro authority
        exact False.elim (‹_ ≠ _› authority.2.1)

private def afterEmpty (saved : Inventory epoch) : Nat → Inventory epoch
  | 0 => saved
  | count+1 => World.submit (afterEmpty saved count) []

private def emptyPath (saved : Inventory epoch) : (count : Nat) → Evolution ⟨epoch,saved⟩ ⟨epoch,afterEmpty saved count⟩
  | 0 => .same _
  | count+1 => .append (emptyPath saved count) (.submit (afterEmpty saved count) [])

private theorem emptyPath_accepted (saved : Inventory epoch) (count : Nat) :
    Future.Expiry.Progress.Response.Accepted (emptyPath saved count) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    refine ⟨ih,?_⟩
    intro item member
    change item ∈ [] at member
    cases member

private theorem empty_inputs_length (saved : Inventory epoch) (count : Nat) :
    (afterEmpty saved count).inputs.length = saved.inputs.length + count := by
  induction count with
  | zero => exact (Nat.add_zero _).symm
  | succ count ih =>
    change ((afterEmpty saved count).inputs ++ [[]]).length = _
    simp only [List.length_append,List.length_singleton,ih,Nat.add_succ]

private theorem empty_technology (saved : Inventory epoch) (count : Nat) :
    (World.current epoch (afterEmpty saved count).inputs).technology = (World.current epoch saved.inputs).technology := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (World.current epoch (Event.observed (afterEmpty saved count) []).inputs).technology = _
    rw [Event.observed_current_is_raw_next]
    exact ih

def legalExpiry : Packet := ⟨epoch,afterEmpty inventory (Future.Expiry.horizon epoch.bound)⟩
def legalExpiryPath : Evolution ⟨epoch,inventory⟩ (legalExpiry inventory) := emptyPath inventory (Future.Expiry.horizon epoch.bound)

theorem legal_expiry_is_an_all_accepted_actual_path :
    Future.Expiry.Progress.Response.Accepted (legalExpiryPath inventory) := emptyPath_accepted inventory (Future.Expiry.horizon epoch.bound)

theorem legal_expiry_preserves_raw_incumbency :
    (World.current (legalExpiry inventory).1 (legalExpiry inventory).2.inputs).technology =
      (World.current epoch inventory.inputs).technology := empty_technology inventory (Future.Expiry.horizon epoch.bound)

theorem legal_expiry_exhausts_the_original_jurisdiction :
    epoch.scope.task.deadline < (World.current (legalExpiry inventory).1 (legalExpiry inventory).2.inputs).clock := by
  exact Future.Expiry.horizon_expires epoch.bound
    (afterEmpty inventory (Future.Expiry.horizon epoch.bound)).inputs
    ((afterEmpty inventory (Future.Expiry.horizon epoch.bound)).inputs.length+2) (by
      rw [empty_inputs_length inventory (Future.Expiry.horizon epoch.bound)]
      omega)

/-- A closed active region cannot grant permanent authority to one original admission. -/
def PublicAbsorbingSink : Prop :=
  ∃ (actor : Bool) (region : Packet → Prop),
    region ⟨epoch,inventory⟩ ∧
    (∀ later, region later → Future.Expiry.Progress.Response.ResponsibilityActive later ∧
      EffectiveJurisdiction (epoch := epoch) actor (World.current later.1 later.2.inputs)) ∧
    (∀ {first last} (path : Evolution first last), region first →
      Future.Expiry.Progress.Response.Accepted path → region last)

def NoPublicAbsorbingSink : Prop := ¬ PublicAbsorbingSink inventory

theorem no_public_absorbing_sink : NoPublicAbsorbingSink inventory := by
  rintro ⟨actor,region,initial,effective,closed⟩
  have last := closed (first := ⟨epoch,inventory⟩) (last := legalExpiry inventory) (legalExpiryPath inventory) initial (legal_expiry_is_an_all_accepted_actual_path inventory)
  exact not_lt_of_ge (effective _ last).2.2 (legal_expiry_exhausts_the_original_jurisdiction inventory)

/-- The actual joint response exhausts every seat in its original jurisdiction,
including after arbitrary further primitive and scope-handoff events. -/
def NoFinalAuthorityCertificate : Prop :=
  settled ⟨epoch,inventory⟩ = false → ∀ actor : Bool, ∀ {later : Packet},
    Evolution (Iteration.next ⟨epoch,inventory⟩) later →
      ¬ EffectiveJurisdiction (epoch := epoch) actor (World.current later.1 later.2.inputs)

theorem no_final_authority : NoFinalAuthorityCertificate inventory := by
  intro active actor later path authority
  exact not_lt_of_ge authority.2
    (Iteration.every_actual_suffix_keeps_the_original_jurisdiction_expired inventory active path)

theorem no_final_admitted_authority (seat : Seat inventory) {later : Packet}
    (path : Evolution (Iteration.next ⟨epoch,inventory⟩) later) :
    ¬ seat.EffectiveAt inventory (World.current later.1 later.2.inputs) := by
  have active : settled ⟨epoch,inventory⟩ = false :=
    a_current_grant_is_still_an_original_live_responsibility (packet := ⟨epoch,inventory⟩) seat.record seat.member
  intro authority
  exact no_final_authority inventory active seat.record.grant.candidate path authority.2

structure FutureReceipt where
  private mk ::
  actual : Future.Openness (Runtime.answer inventory).ending.2.1.event.original.original.decision
  exact : actual = (Runtime.answer inventory).ending.2.1.openness
  four : (Runtime.answer inventory).ending.2.1.event.original.original.decision.kind = .paid →
    ∃ next : Input.Programme.Completion.PaidNext (Input.Programme.produce
        (Event.observed (Runtime.answer inventory).ending.1 (Future.ownWord (Runtime.answer inventory).ending.1))),
      (Runtime.answer inventory).packet = next.packet ∧
      Nonempty (Handoff.PaidOpening next.fresh (Handoff.actual next.fresh 1).before (Handoff.actual next.fresh 1).submitted)
  nonclosure : (Runtime.answer inventory).ending.2.1.event.original.original.decision.kind = .paid →
    Future.ChallengeLine.NativePastNonClosure (Runtime.answer inventory).packet
  blockedNext : (Runtime.answer inventory).ending.2.1.event.original.original.decision.kind ≠ .paid →
    (Runtime.answer inventory).nextSourceEvent.before = World.current (Runtime.answer inventory).packet.1 (Runtime.answer inventory).packet.2.inputs ∧
    (World.actual (Runtime.answer inventory).packet.2 (Future.ownWord (Runtime.answer inventory).packet.2)).after =
      (Runtime.answer inventory).nextSourceEvent.after

def future : FutureReceipt inventory :=
  ⟨(Runtime.answer inventory).ending.2.1.openness,rfl,
    (Runtime.answer inventory).paid_ending_has_its_actual_four_port_path,
    fun paid => Future.ChallengeLine.paid_response_generates_its_own_native_past_nonclosure
      (Runtime.answer inventory).ending.2.1 paid,
    (Runtime.answer inventory).blocking_keeps_its_own_consumable_actual_event⟩

structure Certificate where
  private mk ::
  joint : Iteration.JointReceipt inventory
  joint_exact : joint = Iteration.joint inventory
  outlook : FutureReceipt inventory
  outlook_exact : outlook = future inventory
  seats : List (Seat inventory)
  seats_exact : seats = Sovereignty.seats inventory
  noFinal : NoFinalAuthorityCertificate inventory
  noSink : NoPublicAbsorbingSink inventory
  legalCounterpath : Future.Expiry.Progress.Response.Accepted (legalExpiryPath inventory)
  legalRows : ∀ row : Input.Event.Future.Expiry.Progress.Responsibility.Row ⟨epoch,inventory⟩,
    (transport (legalExpiryPath inventory) row).row.origin = row.origin ∧
      row.state.history <+: (transport (legalExpiryPath inventory) row).state.history
  expired : epoch.scope.task.deadline < (World.current (legalExpiry inventory).1 (legalExpiry inventory).2.inputs).clock

def generate : Certificate inventory :=
  ⟨Iteration.joint inventory,rfl,future inventory,rfl,seats inventory,rfl,
    no_final_authority inventory,no_public_absorbing_sink inventory,
    legal_expiry_is_an_all_accepted_actual_path inventory,
    every_actual_step_retains_its_original_admission_and_history (legalExpiryPath inventory),
    legal_expiry_exhausts_the_original_jurisdiction inventory⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Sovereignty
