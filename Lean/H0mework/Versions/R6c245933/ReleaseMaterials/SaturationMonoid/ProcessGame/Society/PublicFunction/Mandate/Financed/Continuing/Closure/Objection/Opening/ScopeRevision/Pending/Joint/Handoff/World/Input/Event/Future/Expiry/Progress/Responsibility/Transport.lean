import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility

/-! All current and past native rows retain their source identity through the
actual inventory operations. The financial row retains its full Family process. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {packet : Packet}

structure GrantOccurrence where
  scope : World.Scope
  source : BoundSource base scope
  inputPrefix : List (List Action)
  visit : Nat
  birthWord : List Action
  proposal : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  acceptance : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  candidate : Bool

structure Origin where
  V : Vocabulary
  initial : ResponsibilityState V
  obligations : List (AdmittedObligation V)
  grantOccurrence : Option GrantOccurrence

def Row.initial (row : Row packet) : ResponsibilityState row.V :=
  match row with
  | .currentGrant entry _ => Mandate.Lifecycle.Observed.initialState base packet.1.scope
      (Mandate.Challenge.Cross.grantCurrent packet.1.bound packet.2.inputs)
      (Mandate.Challenge.Cross.grantWord packet.1.bound packet.2.inputs) entry.birth.val entry.grant
  | .pastGrant entry _ => Continuation.Grant.origin entry.origin.2
  | .currentChallenge .. | .pastChallenge .. | .currentService .. | .pastService .. | .finance => .empty _

def Row.originals (row : Row packet) : List (AdmittedObligation row.V) :=
  match row with
  | .currentGrant entry member =>
      (Row.initial (.currentGrant entry member)).slots.map
        (fun slot => match slot with | .live obligation => obligation | .terminal archive => archive.obligation)
  | .pastGrant entry _ =>
      (Continuation.Grant.origin entry.origin.2).slots.map
        (fun slot => match slot with | .live obligation => obligation | .terminal archive => archive.obligation)
  | .finance => []
  | .currentChallenge entry _ => [Mandate.Challenge.obligation (Mandate.Challenge.fromHistory packet.1.bound) entry.originInputs entry.original]
  | .pastChallenge entry _ => [Mandate.Challenge.obligation (Mandate.Challenge.fromHistory entry.origin.1.original) entry.origin.2.originInputs entry.origin.2.original]
  | .currentService index => [OutstandingSource.History.NativeService.obligation packet.1.source (epochInputs packet.1.fresh) index]
  | .pastService entry _ => [OutstandingSource.History.NativeService.obligation entry.origin.source entry.origin.originInputs entry.origin.index]

def Row.grantOccurrence : Row packet → Option GrantOccurrence
  | .currentGrant entry _ => some ⟨packet.1.scope,packet.1.bound,
      packet.2.inputs.take entry.birth.val,entry.birth.val,
      Mandate.Challenge.Cross.grantWord packet.1.bound packet.2.inputs entry.birth.val,
      entry.grant.proposal.item.val,entry.grant.acceptance.item.val,entry.grant.candidate⟩
  | .pastGrant entry _ => some ⟨entry.origin.1.originalScope,entry.origin.1.original,
      entry.origin.1.history.take entry.origin.2.birth.val,entry.origin.2.birth.val,
      Mandate.Challenge.Cross.grantWord entry.origin.1.original entry.origin.1.history entry.origin.2.birth.val,
      entry.origin.2.grant.proposal.item.val,entry.origin.2.grant.acceptance.item.val,entry.origin.2.grant.candidate⟩
  | _ => none

def Row.origin (row : Row packet) : Origin := ⟨row.V,row.initial,row.originals,row.grantOccurrence⟩

def Row.native (row : Row packet) : NativeResponsibilityProcess row.V :=
  match row with
  | .currentGrant entry _ => Mandate.Lifecycle.Observed.process (base := base) (scope := packet.1.scope)
      (currentAt := Mandate.Challenge.Cross.grantCurrent packet.1.bound packet.2.inputs)
      (wordAt := Mandate.Challenge.Cross.grantWord packet.1.bound packet.2.inputs)
      (birth := entry.birth.val) (grant := entry.grant)
  | .pastGrant entry _ => entry.saved.native
  | .currentChallenge entry _ => Mandate.Challenge.Cross.process (Mandate.Challenge.fromHistory packet.1.bound) entry.original
  | .pastChallenge entry _ => entry.saved.native
  | .currentService _ => OutstandingSource.History.NativeService.threadProcess packet.1.source (epochInputs packet.1.fresh)
  | .pastService entry _ => OutstandingSource.History.NativeService.Expired.process entry.origin.source entry.origin.originInputs
  | .finance => Financial.Family.process sources

def Row.complete (row : Row packet) : row.native.Run row.initial row.state :=
  match row with
  | .currentGrant entry _ => entry.history.generated
  | .pastGrant entry _ => entry.saved.entire
  | .currentChallenge entry _ => entry.history.state.generated
  | .pastChallenge entry _ => entry.saved.state.generated
  | .currentService index => (packet.2.services index).state.generated
  | .pastService entry _ => entry.saved.state.generated
  | .finance => packet.2.finance.generated

variable {epoch : Epoch} {inventory : Inventory epoch}

def Row.submit (row : Row ⟨epoch,inventory⟩) (word : List Action) : Row ⟨epoch,World.submit inventory word⟩ :=
  match row with
  | .currentGrant entry member => .currentGrant (entry.advance epoch.bound word)
      (Mandate.Challenge.Cross.every_original_grant_is_preserved epoch.bound inventory.grants word entry member)
  | .pastGrant entry member => .pastGrant (entry.advance (boundarySource epoch (inventory.inputs ++ [word])) (World.receipts inventory word))
      (List.mem_map.mpr ⟨entry,member,rfl⟩)
  | .currentChallenge entry member => .currentChallenge (entry.advance epoch.bound word)
      (Mandate.Challenge.Cross.every_old_resident_is_actually_consumed epoch.bound inventory.objections word entry member)
  | .pastChallenge entry member => .pastChallenge
      (entry.advance (boundarySource epoch (inventory.inputs ++ [word])) (le_refl _) (World.receipts inventory word))
      (List.mem_map.mpr ⟨entry,member,rfl⟩)
  | .currentService index => .currentService index
  | .pastService entry member => .pastService
      (entry.advance (boundarySource epoch (inventory.inputs ++ [word])) (le_refl _) (inventory.inputs.length+1) 1)
      (List.mem_map.mpr ⟨entry,member,rfl⟩)
  | .finance => .finance

def Row.handoff (row : Row ⟨epoch,inventory⟩) (fresh : Handoff.Ready epoch.bound inventory.inputs) :
    Row ⟨Epoch.ofFresh fresh,World.handoff inventory fresh⟩ :=
  match row with
  | .currentGrant entry member => .pastGrant (World.currentGrant inventory fresh entry)
      (every_current_grant_becomes_the_actual_full_saved_row inventory fresh entry member)
  | .pastGrant entry member => .pastGrant
      (entry.advance (Handoff.Challenge.occurrence fresh) (World.nextReceipts inventory fresh))
      (List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩))
  | .currentChallenge entry member => .pastChallenge (World.currentChallenge inventory fresh entry)
      (every_current_challenge_becomes_the_actual_full_saved_row inventory fresh entry member)
  | .pastChallenge entry member => .pastChallenge
      (entry.advance (Handoff.Challenge.occurrence fresh) (World.window_follows inventory fresh) (World.nextReceipts inventory fresh))
      (List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩))
  | .currentService index => .pastService (World.currentService inventory fresh index)
      (every_current_service_becomes_the_actual_full_saved_row inventory fresh index)
  | .pastService entry member => .pastService
      (entry.advance (Handoff.Challenge.occurrence fresh) (World.initial_clock_follows inventory fresh) 0 3)
      (List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩))
  | .finance => .finance

theorem Row.submit_origin (row : Row ⟨epoch,inventory⟩) (word : List Action) : (row.submit word).origin = row.origin := by
  cases row with
  | currentGrant entry member =>
    apply congrArg₂ (fun (state : ResponsibilityState Continuation.Grant.V) (occurrence : Option GrantOccurrence) =>
      (⟨Continuation.Grant.V,state,
        state.slots.map (fun slot => match slot with | .live obligation => obligation | .terminal archive => archive.obligation),occurrence⟩ : Origin))
    · exact entry.original_native_admission_is_preserved epoch.bound word
    · change some (GrantOccurrence.mk epoch.scope epoch.bound ((inventory.inputs ++ [word]).take entry.birth.val)
        entry.birth.val (Mandate.Challenge.Cross.grantWord epoch.bound (inventory.inputs ++ [word]) entry.birth.val)
        (Mandate.Challenge.Cross.transportGrant epoch.bound inventory.inputs word entry.birth entry.grant).proposal.item.val
        (Mandate.Challenge.Cross.transportGrant epoch.bound inventory.inputs word entry.birth entry.grant).acceptance.item.val
        (Mandate.Challenge.Cross.transportGrant epoch.bound inventory.inputs word entry.birth entry.grant).candidate) = _
      have items := Mandate.Challenge.Cross.transportGrant_actual_birth_items epoch.bound inventory.inputs word entry.birth entry.grant
      rw [items.1,items.2.1,items.2.2]
      have birthWord : Mandate.Challenge.Cross.grantWord epoch.bound (inventory.inputs ++ [word]) entry.birth.val =
          Mandate.Challenge.Cross.grantWord epoch.bound inventory.inputs entry.birth.val :=
        Mandate.Challenge.Cross.common_word epoch.bound inventory.inputs word entry.birth.val entry.birth.isLt
      rw [birthWord]
      have inside : entry.birth.val ≤ inventory.inputs.length := by
        have bound := entry.birth.isLt
        change entry.birth.val < inventory.inputs.length + 1 at bound
        omega
      simp only [List.take_append,Nat.sub_eq_zero_of_le inside,List.take_zero,List.append_nil]
      rfl
  | pastGrant entry member => rfl
  | currentChallenge entry member => rfl
  | pastChallenge entry member => rfl
  | currentService index => rfl
  | pastService entry member => rfl
  | finance => rfl

theorem Row.handoff_origin (row : Row ⟨epoch,inventory⟩) (fresh : Handoff.Ready epoch.bound inventory.inputs) :
    (row.handoff fresh).origin = row.origin := by cases row <;> rfl

theorem Row.submit_V (row : Row ⟨epoch,inventory⟩) (word : List Action) : (row.submit word).V = row.V := by cases row <;> rfl

theorem Row.handoff_V (row : Row ⟨epoch,inventory⟩) (fresh : Handoff.Ready epoch.bound inventory.inputs) :
    (row.handoff fresh).V = row.V := by cases row <;> rfl

def Row.submitRun (row : Row ⟨epoch,inventory⟩) (word : List Action) :
    (row.submit word).native.Run ((row.submit_V word).symm ▸ row.state) (row.submit word).state := by
  cases row with
  | currentGrant entry member => exact entry.actualRun epoch.bound word
  | pastGrant entry member => exact Event.Grant.consumeRun entry.saved _ _
  | currentChallenge entry member => exact entry.responseRun epoch.bound word
  | pastChallenge entry member => exact (Event.Challenge.Extension.consume entry.saved _ entry.later _).crossing
  | currentService index => exact OutstandingSource.History.NativeService.Thread.actualRun epoch.source (inventory.services index) word
  | pastService entry member => exact Event.Service.consumeRun entry.saved _
  | finance => exact World.financialRun inventory word

def Row.handoffRun (row : Row ⟨epoch,inventory⟩) (fresh : Handoff.Ready epoch.bound inventory.inputs) :
    (row.handoff fresh).native.Run ((row.handoff_V fresh).symm ▸ row.state) (row.handoff fresh).state := by
  cases row with
  | currentGrant entry member => exact (Handoff.Grant.continued fresh entry 4).crossing
  | pastGrant entry member => exact Event.Grant.consumeRun entry.saved _ _
  | currentChallenge entry member => exact (Handoff.Challenge.continued fresh entry 4).crossing
  | pastChallenge entry member => exact (Event.Challenge.Extension.consume entry.saved _ _ _).crossing
  | currentService index => exact (Handoff.Service.continued fresh (inventory.services index) 3).crossing
  | pastService entry member => exact Event.Service.consumeRun entry.saved _
  | finance => exact World.handoffFinancialRun inventory fresh

structure Located (origin : Origin) (packet : Packet) where
  row : Row packet
  same : row.origin = origin

def Located.native {origin : Origin} (position : Located origin packet) : NativeResponsibilityProcess origin.V :=
  (congrArg Origin.V position.same) ▸ position.row.native

def Located.state {origin : Origin} (position : Located origin packet) : ResponsibilityState origin.V :=
  (congrArg Origin.V position.same) ▸ position.row.state

def Located.complete {origin : Origin} (position : Located origin packet) : position.native.Run origin.initial position.state := by
  rcases position with ⟨row,same⟩
  cases same
  exact row.complete

def Located.submit {origin : Origin} (position : Located origin ⟨epoch,inventory⟩) (word : List Action) :
    Located origin ⟨epoch,World.submit inventory word⟩ := ⟨position.row.submit word,(position.row.submit_origin word).trans position.same⟩

def Located.handoff {origin : Origin} (position : Located origin ⟨epoch,inventory⟩)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) : Located origin ⟨Epoch.ofFresh fresh,World.handoff inventory fresh⟩ :=
  ⟨position.row.handoff fresh,(position.row.handoff_origin fresh).trans position.same⟩

def Located.submitRun {origin : Origin} (position : Located origin ⟨epoch,inventory⟩) (word : List Action) :
    (position.submit word).native.Run position.state (position.submit word).state := by
  rcases position with ⟨row,same⟩
  cases same
  cases row with
  | currentGrant entry member => exact Row.submitRun (.currentGrant entry member) word
  | pastGrant entry member => exact Row.submitRun (.pastGrant entry member) word
  | currentChallenge entry member => exact Row.submitRun (.currentChallenge entry member) word
  | pastChallenge entry member => exact Row.submitRun (.pastChallenge entry member) word
  | currentService index => exact Row.submitRun (.currentService index) word
  | pastService entry member => exact Row.submitRun (.pastService entry member) word
  | finance => exact Row.submitRun (Row.finance (packet := ⟨epoch,inventory⟩)) word

def Located.handoffRun {origin : Origin} (position : Located origin ⟨epoch,inventory⟩)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) :
    (position.handoff fresh).native.Run position.state (position.handoff fresh).state := by
  rcases position with ⟨row,same⟩
  cases same
  cases row with
  | currentGrant entry member => exact Row.handoffRun (.currentGrant entry member) fresh
  | pastGrant entry member => exact Row.handoffRun (.pastGrant entry member) fresh
  | currentChallenge entry member => exact Row.handoffRun (.currentChallenge entry member) fresh
  | pastChallenge entry member => exact Row.handoffRun (.pastChallenge entry member) fresh
  | currentService index => exact Row.handoffRun (.currentService index) fresh
  | pastService entry member => exact Row.handoffRun (.pastService entry member) fresh
  | finance => exact Row.handoffRun (Row.finance (packet := ⟨epoch,inventory⟩)) fresh

def Row.handoffAt (row : Row ⟨epoch,inventory⟩) (fresh : Handoff.Ready epoch.bound inventory.inputs)
    (actualInputs : List (List Action)) : Row ⟨Epoch.ofFresh fresh,World.handoffAt inventory fresh actualInputs⟩ :=
  match row with
  | .currentGrant entry member => .pastGrant (World.openingCurrentGrant inventory fresh actualInputs entry)
      (List.mem_append_right _ (List.mem_map.mpr ⟨entry,member,rfl⟩))
  | .pastGrant entry member => .pastGrant
      (entry.advance (World.openingBoundary inventory fresh actualInputs) (World.openingReceipts inventory fresh actualInputs))
      (List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩))
  | .currentChallenge entry member => .pastChallenge (World.openingCurrentChallenge inventory fresh actualInputs entry)
      (List.mem_append_right _ (List.mem_map.mpr ⟨entry,member,rfl⟩))
  | .pastChallenge entry member => .pastChallenge
      (entry.advance (World.openingBoundary inventory fresh actualInputs) (World.window_follows inventory fresh)
        (World.openingReceipts inventory fresh actualInputs))
      (List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩))
  | .currentService index => .pastService (World.openingCurrentService inventory fresh actualInputs index)
      (List.mem_append_right _ (List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩))
  | .pastService entry member => .pastService
      (entry.advance (World.openingBoundary inventory fresh actualInputs) (World.initial_clock_follows inventory fresh) 0 (actualInputs.length+1))
      (List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩))
  | .finance => .finance

theorem Row.handoffAt_origin (row : Row ⟨epoch,inventory⟩)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
    (row.handoffAt fresh actualInputs).origin = row.origin := by cases row <;> rfl

theorem Row.handoffAt_V (row : Row ⟨epoch,inventory⟩)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
    (row.handoffAt fresh actualInputs).V = row.V := by cases row <;> rfl

def Row.handoffAtRun (row : Row ⟨epoch,inventory⟩)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
    (row.handoffAt fresh actualInputs).native.Run
      ((row.handoffAt_V fresh actualInputs).symm ▸ row.state) (row.handoffAt fresh actualInputs).state := by
  cases row with
  | currentGrant entry member =>
    exact Event.Grant.consumeRun (origin := ⟨Epoch.ofFresh fresh,entry⟩)
      (Continuation.Grant.beginAt (Handoff.Grant.entry fresh entry 0)) _ _
  | pastGrant entry member => exact Event.Grant.consumeRun entry.saved _ _
  | currentChallenge entry member =>
    exact (Event.Challenge.Extension.consume (origin := ⟨Epoch.ofFresh fresh,entry⟩)
      (Continuation.Challenge.beginAt (Handoff.Challenge.entry fresh entry 0)) _ _ _).crossing
  | pastChallenge entry member => exact (Event.Challenge.Extension.consume entry.saved _ _ _).crossing
  | currentService index =>
    exact Event.Service.consumeRun
      (origin := ⟨epoch.source,epochInputs epoch.fresh,inventory.inputs,index,inventory.services index⟩)
      (OutstandingSource.History.NativeService.Expired.begin epoch.source (inventory.services index)) _
  | pastService entry member => exact Event.Service.consumeRun entry.saved _
  | finance => exact World.handoffAtFinancialRun inventory fresh actualInputs

def Located.handoffAt {origin : Origin} (position : Located origin ⟨epoch,inventory⟩)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
    Located origin ⟨Epoch.ofFresh fresh,World.handoffAt inventory fresh actualInputs⟩ :=
  ⟨position.row.handoffAt fresh actualInputs,(position.row.handoffAt_origin fresh actualInputs).trans position.same⟩

def Located.handoffAtRun {origin : Origin} (position : Located origin ⟨epoch,inventory⟩)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
    (position.handoffAt fresh actualInputs).native.Run position.state (position.handoffAt fresh actualInputs).state := by
  rcases position with ⟨row,same⟩
  cases same
  cases row with
  | currentGrant entry member => exact Row.handoffAtRun (.currentGrant entry member) fresh actualInputs
  | pastGrant entry member => exact Row.handoffAtRun (.pastGrant entry member) fresh actualInputs
  | currentChallenge entry member => exact Row.handoffAtRun (.currentChallenge entry member) fresh actualInputs
  | pastChallenge entry member => exact Row.handoffAtRun (.pastChallenge entry member) fresh actualInputs
  | currentService index => exact Row.handoffAtRun (.currentService index) fresh actualInputs
  | pastService entry member => exact Row.handoffAtRun (.pastService entry member) fresh actualInputs
  | finance => exact Row.handoffAtRun (Row.finance (packet := ⟨epoch,inventory⟩)) fresh actualInputs

theorem Located.handoffAt_history {origin : Origin} (position : Located origin ⟨epoch,inventory⟩)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
    position.state.history <+: (position.handoffAt fresh actualInputs).state.history :=
  ⟨(position.handoffAtRun fresh actualInputs).events,(position.handoffAtRun fresh actualInputs).history_eq.symm⟩


def follow {first last : Packet} (path : Evolution first last) {origin : Origin}
    (position : Located origin first) : Located origin last :=
  match path with
  | .same _ => position
  | .submit _ word => position.submit word
  | .handoff _ fresh => position.handoff fresh
  | .handoffAt _ fresh actualInputs => position.handoffAt fresh actualInputs
  | .append earlier later => follow later (follow earlier position)

def transport {first last : Packet} (path : Evolution first last) (row : Row first) : Located row.origin last :=
  follow path ⟨row,rfl⟩


theorem follow_retains_the_complete_original_history {first last : Packet} (path : Evolution first last) :
    ∀ {origin : Origin} (position : Located origin first), position.state.history <+: (follow path position).state.history := by
  induction path with
  | same packet => intro origin position; exact List.prefix_rfl
  | submit inventory word =>
    intro origin position
    exact ⟨(position.submitRun word).events,(position.submitRun word).history_eq.symm⟩
  | handoff inventory fresh =>
    intro origin position
    exact ⟨(position.handoffRun fresh).events,(position.handoffRun fresh).history_eq.symm⟩
  | handoffAt inventory fresh actualInputs =>
    intro origin position
    exact ⟨(position.handoffAtRun fresh actualInputs).events,(position.handoffAtRun fresh actualInputs).history_eq.symm⟩
  | append earlier later before after =>
    intro origin position
    exact (before position).trans (after (follow earlier position))

def completeOriginal {first last : Packet} (path : Evolution first last) (row : Row first) :=
  (transport path row).complete

theorem every_actual_step_retains_its_original_admission_and_history {first last : Packet}
    (path : Evolution first last) (row : Row first) :
    (transport path row).row.origin = row.origin ∧
    row.state.history <+: (transport path row).state.history :=
  ⟨(transport path row).same,follow_retains_the_complete_original_history path ⟨row,rfl⟩⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility
