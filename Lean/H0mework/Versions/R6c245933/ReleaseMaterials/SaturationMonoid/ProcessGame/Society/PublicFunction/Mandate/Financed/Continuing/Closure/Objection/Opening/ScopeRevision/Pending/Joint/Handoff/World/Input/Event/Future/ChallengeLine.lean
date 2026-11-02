import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Runtime

/-! One original Claim vocabulary follows the actual current-to-past transition.
The active source emits its real challenge and transports the newborn full Run. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.ChallengeLine
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

structure Origin where
  scope : World.Scope
  bound : BoundSource base scope
  inputs : List (List Action)
  claim : Mandate.Challenge.Claim (Mandate.Challenge.fromHistory bound) inputs

def Origin.V (origin : Origin) := Mandate.Challenge.V (Mandate.Challenge.fromHistory origin.bound) origin.inputs

inductive Row (packet : Packet) where
  | current (record : Mandate.Challenge.Cross.Resident packet.1.bound packet.2.inputs)
      (member : record ∈ packet.2.objections)
  | past (entry : World.ChallengeCohort packet.1.scope) (member : entry ∈ packet.2.pastChallenges)

def Row.origin {packet : Packet} : Row packet → Origin
  | .current record _ => ⟨packet.1.scope,packet.1.bound,record.originInputs,record.original⟩
  | .past entry _ => ⟨entry.origin.1.originalScope,entry.origin.1.original,entry.origin.2.originInputs,entry.origin.2.original⟩

def Row.native {packet : Packet} (row : Row packet) : NativeResponsibilityProcess row.origin.V :=
  match row with
  | .current record _ => Mandate.Challenge.Cross.process (Mandate.Challenge.fromHistory packet.1.bound) record.original
  | .past entry _ => entry.saved.native

def Row.state {packet : Packet} (row : Row packet) : row.native.GeneratedState :=
  match row with
  | .current record _ => record.history.state
  | .past entry _ => entry.saved.state

structure Located (origin : Origin) (packet : Packet) where
  row : Row packet
  same : row.origin = origin

def Located.native {origin : Origin} {packet : Packet} (position : Located origin packet) :
    NativeResponsibilityProcess origin.V := position.same ▸ position.row.native

def Located.state {origin : Origin} {packet : Packet} (position : Located origin packet) : position.native.GeneratedState := by
  rcases position with ⟨row,same⟩
  cases same
  exact row.state

variable {origin : Origin} {epoch : Epoch} {inventory : Inventory epoch}

def Located.submit (position : Located origin ⟨epoch,inventory⟩) (word : List Action) :
    Located origin ⟨epoch,World.submit inventory word⟩ := by
  rcases position with ⟨row,same⟩
  cases row with
  | current record member =>
    exact ⟨.current (record.advance epoch.bound word)
      (Mandate.Challenge.Cross.every_old_resident_is_actually_consumed epoch.bound inventory.objections word record member),same⟩
  | past entry member =>
    refine ⟨.past (entry.advance (World.boundarySource epoch (inventory.inputs ++ [word])) (le_refl _) (World.receipts inventory word)) ?_,same⟩
    exact List.mem_map.mpr ⟨entry,member,rfl⟩

def Located.handoff (position : Located origin ⟨epoch,inventory⟩) (fresh : Handoff.Ready epoch.bound inventory.inputs) :
    Located origin ⟨Epoch.ofFresh fresh,World.handoff inventory fresh⟩ := by
  rcases position with ⟨row,same⟩
  cases row with
  | current record member =>
    refine ⟨.past (World.currentChallenge inventory fresh record) ?_,same⟩
    exact every_current_challenge_becomes_the_actual_full_saved_row inventory fresh record member
  | past entry member =>
    refine ⟨.past (entry.advance (Handoff.Challenge.occurrence fresh) (World.window_follows inventory fresh) (World.nextReceipts inventory fresh)) ?_,same⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)

def Located.handoffAt (position : Located origin ⟨epoch,inventory⟩)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
    Located origin ⟨Epoch.ofFresh fresh,World.handoffAt inventory fresh actualInputs⟩ := by
  rcases position with ⟨row,same⟩
  cases row with
  | current record member =>
    refine ⟨.past (World.openingCurrentChallenge inventory fresh actualInputs record) ?_,same⟩
    exact List.mem_append_right _ (List.mem_map.mpr ⟨record,member,rfl⟩)
  | past entry member =>
    refine ⟨.past (entry.advance (World.openingBoundary inventory fresh actualInputs)
      (World.window_follows inventory fresh) (World.openingReceipts inventory fresh actualInputs)) ?_,same⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)

inductive Extension (origin : Origin) : {first : Packet} → Located origin first → {last : Packet} → Located origin last → Type where
  | same {packet : Packet} (position : Located origin packet) : Extension origin position position
  | submit {epoch : Epoch} {inventory : Inventory epoch} (position : Located origin ⟨epoch,inventory⟩) (word : List Action) :
      Extension origin position (position.submit word)
  | handoff {epoch : Epoch} {inventory : Inventory epoch} (position : Located origin ⟨epoch,inventory⟩)
      (fresh : Handoff.Ready epoch.bound inventory.inputs) : Extension origin position (position.handoff fresh)
  | handoffAt {epoch : Epoch} {inventory : Inventory epoch} (position : Located origin ⟨epoch,inventory⟩)
      (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
      Extension origin position (position.handoffAt fresh actualInputs)
  | append {first middle last : Packet} {before : Located origin first} {between : Located origin middle} {after : Located origin last} :
      Extension origin before between → Extension origin between after → Extension origin before after

variable {first last : Packet} {before : Located origin first} {after : Located origin last}

def Extension.inherit (trace : Extension origin before after)
    {start finish : ResponsibilityState origin.V} (path : before.native.Run start finish) : after.native.Run start finish := by
  induction trace with
  | same position => exact path
  | @submit epoch inventory position word =>
    rcases position with ⟨row,same⟩
    cases row with
    | current record member => cases same; exact path
    | past entry member =>
      cases same
      exact (Event.Challenge.Extension.consume entry.saved (World.boundarySource epoch (inventory.inputs ++ [word])) entry.later (World.receipts inventory word)).inherit path
  | @handoff epoch inventory position fresh =>
    rcases position with ⟨row,same⟩
    cases row with
    | current record member =>
      cases same
      exact Mandate.Challenge.ScopeProcess.inheritRun _ _ (Handoff.Challenge.occurrence fresh)
        (Handoff.Challenge.laterWindow fresh) _ _ path
    | past entry member =>
      cases same
      exact (Event.Challenge.Extension.consume entry.saved (Handoff.Challenge.occurrence fresh)
        (lt_of_lt_of_le entry.later (World.window_follows inventory fresh)) (World.nextReceipts inventory fresh)).inherit path
  | @handoffAt epoch inventory position fresh actualInputs =>
    rcases position with ⟨row,same⟩
    cases row with
    | current record member =>
      cases same
      exact (Event.Challenge.Extension.consume (origin := ⟨Epoch.ofFresh fresh,record⟩)
        (Continuation.Challenge.beginAt (Handoff.Challenge.entry fresh record 0))
        (World.openingBoundary inventory fresh actualInputs) (Handoff.Challenge.laterWindow fresh)
        (World.openingReceipts inventory fresh actualInputs)).inherit
          (Mandate.Challenge.ScopeProcess.inheritRun _ _ (Handoff.Challenge.occurrence fresh)
            (Handoff.Challenge.laterWindow fresh) _ _ path)
    | past entry member =>
      cases same
      exact (Event.Challenge.Extension.consume entry.saved (World.openingBoundary inventory fresh actualInputs)
        (lt_of_lt_of_le entry.later (World.window_follows inventory fresh))
        (World.openingReceipts inventory fresh actualInputs)).inherit path
  | append earlier later first second => exact second (first path)

def Extension.crossing (trace : Extension origin before after) :
    after.native.Run before.state.current after.state.current := by
  induction trace with
  | same position => exact .nil
  | @submit epoch inventory position word =>
    rcases position with ⟨row,same⟩
    cases row with
    | current record member => cases same; exact record.responseRun epoch.bound word
    | past entry member =>
      cases same
      exact (Event.Challenge.Extension.consume entry.saved (World.boundarySource epoch (inventory.inputs ++ [word])) entry.later (World.receipts inventory word)).crossing
  | @handoff epoch inventory position fresh =>
    rcases position with ⟨row,same⟩
    cases row with
    | current record member =>
      cases same
      exact (Handoff.Challenge.continued fresh record 4).crossing
    | past entry member =>
      cases same
      exact (Event.Challenge.Extension.consume entry.saved (Handoff.Challenge.occurrence fresh)
        (lt_of_lt_of_le entry.later (World.window_follows inventory fresh)) (World.nextReceipts inventory fresh)).crossing
  | @handoffAt epoch inventory position fresh actualInputs =>
    rcases position with ⟨row,same⟩
    cases row with
    | current record member =>
      cases same
      exact (Event.Challenge.Extension.consume (origin := ⟨Epoch.ofFresh fresh,record⟩)
        (Continuation.Challenge.beginAt (Handoff.Challenge.entry fresh record 0))
        (World.openingBoundary inventory fresh actualInputs) (Handoff.Challenge.laterWindow fresh)
        (World.openingReceipts inventory fresh actualInputs)).crossing
    | past entry member =>
      cases same
      exact (Event.Challenge.Extension.consume entry.saved (World.openingBoundary inventory fresh actualInputs)
        (lt_of_lt_of_le entry.later (World.window_follows inventory fresh))
        (World.openingReceipts inventory fresh actualInputs)).crossing
  | append earlier later first second => exact (later.inherit first).concatRuns _ second

def Extension.complete (trace : Extension origin before after) :
    after.native.Run (ResponsibilityState.empty origin.V) after.state.current :=
  (trace.inherit before.state.generated).concatRuns _ trace.crossing

theorem Extension.complete_is_the_whole_saved_event_sequence (trace : Extension origin before after) :
    trace.complete.events = after.state.generated.events :=
  List.append_cancel_left (trace.complete.history_eq.symm.trans after.state.generated.history_eq)

def follow {first last : Packet} (path : Evolution first last) :
    (position : Located origin first) → Sigma fun next : Located origin last => Extension origin position next := by
  induction path with
  | same packet => intro position; exact ⟨position,.same position⟩
  | submit inventory word => intro position; exact ⟨position.submit word,.submit position word⟩
  | handoff inventory fresh => intro position; exact ⟨position.handoff fresh,.handoff position fresh⟩
  | handoffAt inventory fresh actualInputs => intro position; exact ⟨position.handoffAt fresh actualInputs,.handoffAt position fresh actualInputs⟩
  | append earlier later before after =>
    intro position
    let middle := before position
    let final := after middle.1
    exact ⟨final.1,.append middle.2 final.2⟩

variable (inventory : Inventory epoch)

def word : List Action :=
  if Mandate.Response.Active (current epoch inventory.inputs) then Input.emit inventory .challenge else Future.ownWord inventory

theorem active_word_is_the_actual_challenge (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    word inventory = Input.emit inventory .challenge := if_pos active

def birthOrigin (active : Mandate.Response.Active (current epoch inventory.inputs)) : Origin :=
  ⟨epoch.scope,epoch.bound,(Input.staged inventory .challenge).inputs,Input.challengeClaim inventory active⟩

def birthLocation (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    Located (birthOrigin inventory active) ⟨epoch,Input.staged inventory .challenge⟩ :=
  ⟨.current (Input.challengeResident inventory active) (Input.challenge_resident_is_in_the_saved_next_inventory inventory active),rfl⟩

def afterIncoming (submitted : List Action) :
    Evolution ⟨epoch,Event.observed inventory submitted⟩ (Future.produce inventory submitted).packet :=
  completionEvolution (Event.response inventory submitted).original.decision

def Born (active : Mandate.Response.Active (current epoch inventory.inputs)) (packet : Packet) :=
  Sigma fun position : Located (birthOrigin inventory active) packet => Extension (birthOrigin inventory active) (birthLocation inventory active) position

def born (active : Mandate.Response.Active (current epoch inventory.inputs)) (depth : Nat) :
    Born inventory active (Future.Runtime.fromRoot inventory (Input.emit inventory .challenge) depth).continuation.packet :=
  follow (.append (afterIncoming inventory (Input.emit inventory .challenge))
    (Future.Runtime.fromRoot inventory (Input.emit inventory .challenge) depth).continuation.native) (birthLocation inventory active)

structure Disposition (inventory : Inventory epoch) (depth : Nat) where
  private mk ::
  answer : Future.Response inventory (word inventory) depth
  answer_exact : answer = Future.Runtime.fromRoot inventory (word inventory) depth
  newborn : (active : Mandate.Response.Active (current epoch inventory.inputs)) → Born inventory active answer.continuation.packet

def produce (depth : Nat) : Disposition inventory depth := by
  refine ⟨Future.Runtime.fromRoot inventory (word inventory) depth,rfl,?_⟩
  intro active
  rw [active_word_is_the_actual_challenge inventory active]
  exact born inventory active depth

variable {inventory}

def Disposition.packet {depth : Nat} (result : Disposition inventory depth) := result.answer.continuation.packet

def Disposition.native {depth : Nat} (result : Disposition inventory depth) : Evolution ⟨epoch,inventory⟩ result.packet := result.answer.native

def Disposition.finance {depth : Nat} (result : Disposition inventory depth) := result.answer.finance

def Disposition.afterEvents {depth : Nat} (result : Disposition inventory depth) (history : List (List Action)) (laterDepth : Nat) :=
  Future.afterEvents result.packet.2 history laterDepth

def Disposition.newbornAfterEvents {depth : Nat} (result : Disposition inventory depth)
    (active : Mandate.Response.Active (current epoch inventory.inputs)) (history : List (List Action)) (laterDepth : Nat) :
    Born inventory active (result.afterEvents history laterDepth).packet :=
  let previous := result.newborn active
  let advanced := follow (.append (Event.Iteration.native result.packet.2 history)
    (result.afterEvents history laterDepth).native) previous.1
  ⟨advanced.1,.append previous.2 advanced.2⟩

def Disposition.completeNewbornRun {depth : Nat} (result : Disposition inventory depth)
    (active : Mandate.Response.Active (current epoch inventory.inputs)) := (result.newborn active).2.complete

def Disposition.completeNewbornRunAfterEvents {depth : Nat} (result : Disposition inventory depth)
    (active : Mandate.Response.Active (current epoch inventory.inputs)) (history : List (List Action)) (laterDepth : Nat) :=
  (result.newbornAfterEvents active history laterDepth).2.complete

theorem Disposition.the_complete_newborn_run_is_the_actual_full_saved_sequence {depth : Nat}
    (result : Disposition inventory depth) (active : Mandate.Response.Active (current epoch inventory.inputs))
    (history : List (List Action)) (laterDepth : Nat) :
    (result.newbornAfterEvents active history laterDepth).2.complete.events =
      (result.newbornAfterEvents active history laterDepth).1.state.generated.events :=
  (result.newbornAfterEvents active history laterDepth).2.complete_is_the_whole_saved_event_sequence

variable (inventory)

theorem birth_claim_position_is_the_actual_new_signature
    (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    (Input.challengeClaim inventory active).position = Input.challengePosition inventory active :=
  Mandate.Challenge.read_position _ _ _ _ (Option.some_get _).symm

theorem birth_keeps_the_actual_snapshot_and_counterparty
    (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    (Input.challengeClaim inventory active).snapshot _ _ = (current epoch inventory.inputs).technology ∧
    (Input.challengeClaim inventory active).signer _ _ = Input.challenger inventory active := by
  dsimp only [Mandate.Challenge.Claim.snapshot,Mandate.Challenge.Claim.signer]
  rw [birth_claim_position_is_the_actual_new_signature,Input.challenge_position_item]
  exact ⟨rfl,rfl⟩

/-- Sealing an incumbent forbids any independently signed, accepted native claim
with that same active snapshot in a legal primitive extension. -/
def NativeChallengeSeal (holder : Bool) : Prop :=
  ∀ submitted : List Action,
    (∀ item ∈ (Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) submitted,
      (Mandate.law base epoch.scope).Valid item.before item.request) →
    ∀ claim ∈ Mandate.Challenge.claimsAt (Mandate.Challenge.fromHistory epoch.bound)
      (World.submit inventory submitted).inputs (inventory.inputs.length+2),
      claim.snapshot _ _ = (current epoch inventory.inputs).technology → claim.signer _ _ = holder

theorem a_seal_would_identify_the_actual_accepted_newborn_with_the_holder
    (active : Mandate.Response.Active (current epoch inventory.inputs)) (holder : Bool)
    (sealed : NativeChallengeSeal inventory holder) : Input.challenger inventory active = holder := by
  have same := sealed (Input.emit inventory .challenge) (by
    rw [Input.challenge_word_is_one_original_signature inventory active]
    intro item member
    change item ∈ [⟨0,current epoch inventory.inputs,Input.signature epoch (Input.challenger inventory active)⟩] at member
    cases List.mem_singleton.mp member
    exact Input.signature_valid epoch _ _ (Input.every_challenge_choice_is_a_real_member epoch _ _ (Input.challengePayment inventory active).listed))
    (Input.challengeClaim inventory active) (Input.challenge_claim_is_in_the_actual_newborn_census inventory active)
    (birth_keeps_the_actual_snapshot_and_counterparty inventory active).1
  change (Input.challengeClaim inventory active).signer (Mandate.Challenge.fromHistory epoch.bound)
    (Input.staged inventory .challenge).inputs = holder at same
  rw [(birth_keeps_the_actual_snapshot_and_counterparty inventory active).2] at same
  exact same

theorem no_active_holder_can_seal_the_actual_native_challenge
    (members : Handoff.BothMembers epoch.scope) (holder : Bool)
    (held : (current epoch inventory.inputs).technology.holder = some holder) :
    ¬ NativeChallengeSeal inventory holder := by
  have active : Mandate.Response.Active (current epoch inventory.inputs) := by
    unfold Mandate.Response.Active
    exact Or.inl (by rw [held]; rfl)
  intro sealed
  exact (Input.the_actual_challenger_is_independent_of_the_holder inventory active members holder held).2
    (a_seal_would_identify_the_actual_accepted_newborn_with_the_holder inventory active holder sealed)

theorem no_active_offer_can_seal_the_actual_native_challenge
    (members : Handoff.BothMembers epoch.scope) (holder : Bool)
    (unheld : (current epoch inventory.inputs).technology.holder = none)
    (offered : (current epoch inventory.inputs).technology.offered = some holder) :
    ¬ NativeChallengeSeal inventory holder := by
  have active : Mandate.Response.Active (current epoch inventory.inputs) := by
    unfold Mandate.Response.Active
    exact Or.inr (by rw [offered]; rfl)
  intro sealed
  exact (Input.the_actual_challenger_is_independent_of_the_offer inventory active members holder unheld offered).2
    (a_seal_would_identify_the_actual_accepted_newborn_with_the_holder inventory active holder sealed)

def ControllerAt (holder : Bool) : Prop :=
  (current epoch inventory.inputs).technology.holder = some holder ∨
    ((current epoch inventory.inputs).technology.holder = none ∧ (current epoch inventory.inputs).technology.offered = some holder)

def NativePastNonClosure (initial : Packet) : Prop :=
  ∀ {later : Packet}, Evolution initial later → ∀ holder : Bool,
    ControllerAt later.2 holder → ¬ NativeChallengeSeal later.2 holder

theorem standing_transports_into_native_past_nonclosure (initial : Packet)
    (members : Handoff.BothMembers initial.1.scope) : NativePastNonClosure initial := by
  intro later path holder controller
  have retained : Handoff.BothMembers later.1.scope := fun actor => Future.standing_transport path actor (members actor)
  rcases controller with held | ⟨unheld,offered⟩
  · exact no_active_holder_can_seal_the_actual_native_challenge later.2 retained holder held
  · exact no_active_offer_can_seal_the_actual_native_challenge later.2 retained holder unheld offered

variable {inventory}

theorem paid_response_generates_its_own_native_past_nonclosure {submitted : List Action}
    (result : Future.Result inventory submitted)
    (paid : result.event.original.original.decision.kind = .paid) : NativePastNonClosure result.packet := by
  apply standing_transports_into_native_past_nonclosure
  cases result.openness
  next next kind packet facts =>
    change Handoff.BothMembers result.event.original.original.decision.packet.1.scope
    rw [packet]
    exact facts.standing
  next kind absent reason packet => cases kind.symm.trans paid
  next kind fresh chosen absent actual methods packet => cases kind.symm.trans paid

theorem Disposition.every_finite_future_after_actual_paid_birth_excludes_the_native_seal {depth : Nat}
    (result : Disposition inventory depth)
    (paid : result.answer.result.event.original.original.decision.kind = .paid)
    {later : Packet} (path : Evolution result.packet later) (holder : Bool)
    (controller : ControllerAt later.2 holder) : ¬ NativeChallengeSeal later.2 holder :=
  paid_response_generates_its_own_native_past_nonclosure result.answer.result paid
    (.append result.answer.continuation.native path) holder controller

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.ChallengeLine
