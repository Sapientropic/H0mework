import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

/-- The operations of the existing inventory producer, with their full dependent endpoints. -/
inductive Evolution : Packet → Packet → Type where
  | same (packet : Packet) : Evolution packet packet
  | submit {epoch : Epoch} (inventory : Inventory epoch) (word : List Action) :
      Evolution ⟨epoch,inventory⟩ ⟨epoch,World.submit inventory word⟩
  | handoff {epoch : Epoch} (inventory : Inventory epoch)
      (fresh : Handoff.Ready epoch.bound inventory.inputs) :
      Evolution ⟨epoch,inventory⟩ ⟨Epoch.ofFresh fresh,World.handoff inventory fresh⟩
  | handoffAt {epoch : Epoch} (inventory : Inventory epoch)
      (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
      Evolution ⟨epoch,inventory⟩ ⟨Epoch.ofFresh fresh,World.handoffAt inventory fresh actualInputs⟩
  | append {first middle last : Packet} (earlier : Evolution first middle) (later : Evolution middle last) :
      Evolution first last

variable {epoch : Epoch} (inventory : Inventory epoch) (intent : Intent)

def inputEvolution : Evolution ⟨epoch,inventory⟩ ⟨epoch,Input.advance inventory intent⟩ :=
  .append (.submit inventory (Input.emit inventory intent))
    (.submit (Input.staged inventory intent) (Input.repayment inventory intent))

def cutEvolution : Evolution ⟨epoch,inventory⟩ ⟨epoch,Programme.cut inventory intent⟩ := by
  unfold Programme.cut
  split
  · exact inputEvolution inventory intent
  · exact .same _

def programmeEvolution {inventory : Inventory epoch} (execution : Programme.Execution inventory) :
    Evolution ⟨epoch,inventory⟩ ⟨epoch,execution.finalInventory⟩ :=
  Programme.Execution.fold (fun saved actual => Evolution ⟨epoch,saved⟩ ⟨epoch,actual.finalInventory⟩)
    (fun saved intent _ => .append (cutEvolution saved intent) (inputEvolution (Programme.cut saved intent) intent))
    (fun saved _ _ => .append (cutEvolution saved .revision) (inputEvolution (Programme.cut saved .revision) .revision))
    (fun saved intent _ _ _ later =>
      .append (.append (cutEvolution saved intent) (inputEvolution (Programme.cut saved intent) intent)) later)
    execution

def completionEvolution {inventory : Inventory epoch} {execution : Programme.Execution inventory}
    (decision : Programme.Completion.Decision execution) :
    Evolution ⟨epoch,inventory⟩ decision.packet := by
  cases decision
  next next => exact .append (programmeEvolution execution) (.handoff execution.finalInventory next.fresh)
  next absent reason => exact programmeEvolution execution
  next fresh chosen absent actual methods => exact .append (programmeEvolution execution) (.handoff execution.finalInventory fresh)

namespace Grant
abbrev Saved (origin : GrantOrigin) := Continuation.Grant.Saved origin.1.fresh origin.2
inductive Extension (origin : GrantOrigin) : Saved origin → Saved origin → Type where
  | same (saved : Saved origin) : Extension origin saved saved
  | consume (saved : Saved origin) (source : Mandate.Challenge.ScopeBoundary.Source base)
      (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) :
      Extension origin saved (saved.consume source receipts)
  | append {first middle last : Saved origin} : Extension origin first middle →
      Extension origin middle last → Extension origin first last

variable {origin : GrantOrigin}
def inheritConsume (saved : Saved origin) (source : Mandate.Challenge.ScopeBoundary.Source base)
    (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source))
    {first last : ResponsibilityState Continuation.Grant.V} (path : saved.native.Run first last) :
    (saved.consume source receipts).native.Run first last := by
  induction receipts generalizing saved with
  | nil => exact path
  | cons receipt tail ih =>
      exact ih (saved.step source receipt) (Continuation.Grant.inheritRun source saved.native path)

def Extension.inherit {before after : Saved origin} (trace : Extension origin before after)
    {first last : ResponsibilityState Continuation.Grant.V} (path : before.native.Run first last) :
    after.native.Run first last := by
  induction trace with
  | same saved => exact path
  | consume saved source receipts => exact inheritConsume saved source receipts path
  | append earlier later first second => exact second (first path)

def stepRun {origin : GrantOrigin} (saved : Saved origin)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (receipt : Mandate.Challenge.ScopeBoundary.Receipt source) :
    (saved.step source receipt).native.Run saved.state (saved.step source receipt).state := by
  change (Continuation.Grant.process source saved.native).Run saved.state (saved.step source receipt).state
  let address : Fin saved.state.slots.length := ⟨0,by rw [saved.slots]; exact Nat.zero_lt_succ 0⟩
  let edge : (Continuation.Grant.process source saved.native).Edge saved.state :=
    .cross address origin.2.history.obligation (by simp [address,saved.slots]) (.actual receipt)
  exact .step .nil edge

def consumeRun {origin : GrantOrigin} (saved : Saved origin)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) :
    (saved.consume source receipts).native.Run saved.state (saved.consume source receipts).state := by
  induction receipts generalizing saved with
  | nil => exact .nil
  | cons receipt tail ih =>
    exact (inheritConsume (saved.step source receipt) source tail (stepRun saved source receipt)).concatRuns _ (ih (saved.step source receipt))

def Extension.crossing {origin : GrantOrigin} {before after : Saved origin} (trace : Extension origin before after) :
    after.native.Run before.state after.state := by
  induction trace with
  | same saved => exact .nil
  | consume saved source receipts => exact consumeRun saved source receipts
  | append earlier later first second => exact (later.inherit first).concatRuns _ second

def Extension.complete {origin : GrantOrigin} {before after : Saved origin} (trace : Extension origin before after) :
    after.native.Run (Continuation.Grant.origin origin.2) after.state :=
  (trace.inherit before.entire).concatRuns _ trace.crossing

theorem Extension.complete_is_the_full_saved_event_sequence {origin : GrantOrigin} {before after : Saved origin}
    (trace : Extension origin before after) : trace.complete.events = after.entire.events :=
  List.append_cancel_left (trace.complete.history_eq.symm.trans after.entire.history_eq)
end Grant

namespace Challenge
abbrev Saved (origin : ChallengeOrigin) := Continuation.Challenge.Saved origin.1.fresh origin.2
inductive Extension (origin : ChallengeOrigin) : Saved origin → Saved origin → Type where
  | same (saved : Saved origin) : Extension origin saved saved
  | consume (saved : Saved origin) (source : Mandate.Challenge.ScopeBoundary.Source base)
      (later : origin.1.originalScope.task.deadline < source.scope.task.earliest)
      (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) :
      Extension origin saved (saved.consume source later receipts)
  | append {first middle last : Saved origin} : Extension origin first middle →
      Extension origin middle last → Extension origin first last

variable {origin : ChallengeOrigin}
def Extension.inherit {before after : Saved origin} (trace : Extension origin before after)
    {first last : ResponsibilityState (Mandate.Challenge.V (Mandate.Challenge.fromHistory origin.1.original) origin.2.originInputs)}
    (path : before.native.Run first last) : after.native.Run first last := by
  induction trace with
  | same saved => exact path
  | consume saved source later receipts =>
      exact Mandate.Challenge.ScopeProcess.inheritRun _ _ source later saved.native _ path
  | append earlier later first second => exact second (first path)

def Extension.crossing {origin : ChallengeOrigin} {before after : Saved origin} (trace : Extension origin before after) :
    after.native.Run before.state.current after.state.current := by
  induction trace with
  | same saved => exact .nil
  | consume saved source later receipts => exact (saved.thread source later receipts).crossing
  | append earlier later first second => exact (later.inherit first).concatRuns _ second

def Extension.complete {origin : ChallengeOrigin} {before after : Saved origin} (trace : Extension origin before after) :
    after.native.Run (ResponsibilityState.empty _) after.state.current :=
  (trace.inherit before.state.generated).concatRuns _ trace.crossing

theorem Extension.complete_is_the_full_saved_event_sequence {origin : ChallengeOrigin} {before after : Saved origin}
    (trace : Extension origin before after) : trace.complete.events = after.state.generated.events :=
  List.append_cancel_left (trace.complete.history_eq.symm.trans after.state.generated.history_eq)
end Challenge

namespace Service
abbrev Saved (origin : ServiceOrigin) := OutstandingSource.History.NativeService.Expired.Continuation origin.source origin.original
inductive Extension (origin : ServiceOrigin) : Saved origin → Saved origin → Type where
  | same (saved : Saved origin) : Extension origin saved saved
  | consume (saved : Saved origin) (observations : List (OutstandingSource.History.NativeService.ExpiredInput origin.source)) :
      Extension origin saved (saved.consume origin.source observations)
  | append {first middle last : Saved origin} : Extension origin first middle →
      Extension origin middle last → Extension origin first last

def stepRun {origin : ServiceOrigin} (saved : Saved origin)
    (input : OutstandingSource.History.NativeService.ExpiredInput origin.source) :
    (OutstandingSource.History.NativeService.Expired.process origin.source origin.originInputs).Run
      saved.state.current (saved.step origin.source input).state.current := by
  rcases origin with ⟨source,originInputs,inputs,index,original⟩
  rcases original with ⟨originalState,originalShape⟩
  cases originalShape with
  | live unpaid slots =>
    have live := saved.slots.trans slots
    let address : Fin saved.state.current.slots.length := ⟨0,by rw [live]; exact Nat.zero_lt_succ 0⟩
    let edge : (OutstandingSource.History.NativeService.Expired.process source originInputs).Edge saved.state.current :=
      .cross address (OutstandingSource.History.NativeService.obligation source originInputs index) (by simp [address,live]) (.observed index input rfl rfl rfl)
    exact .step .nil edge
  | terminal archive paid recorded original_eq slots => exact .nil

def consumeRun {origin : ServiceOrigin} (saved : Saved origin)
    (observations : List (OutstandingSource.History.NativeService.ExpiredInput origin.source)) :
    (OutstandingSource.History.NativeService.Expired.process origin.source origin.originInputs).Run
      saved.state.current (saved.consume origin.source observations).state.current := by
  induction observations generalizing saved with
  | nil => exact .nil
  | cons observation rest ih => exact (stepRun saved observation).concatRuns _ (ih (saved.step origin.source observation))

def Extension.crossing {origin : ServiceOrigin} {before after : Saved origin} (trace : Extension origin before after) :
    (OutstandingSource.History.NativeService.Expired.process origin.source origin.originInputs).Run
      before.state.current after.state.current := by
  induction trace with
  | same saved => exact .nil
  | consume saved observations => exact consumeRun saved observations
  | append earlier later first second => exact first.concatRuns _ second

def Extension.complete {origin : ServiceOrigin} {before after : Saved origin} (trace : Extension origin before after) :
    (OutstandingSource.History.NativeService.Expired.process origin.source origin.originInputs).Run (ResponsibilityState.empty _) after.state.current :=
  before.state.generated.concatRuns _ trace.crossing

theorem Extension.complete_is_the_full_saved_event_sequence {origin : ServiceOrigin} {before after : Saved origin}
    (trace : Extension origin before after) : trace.complete.events = after.state.generated.events :=
  List.append_cancel_left (trace.complete.history_eq.symm.trans after.state.generated.history_eq)
end Service

structure GrantTransport (entry : GrantCohort) (packet : Packet) where
  saved : Grant.Saved entry.origin
  member : (⟨entry.origin,saved⟩ : GrantCohort) ∈ packet.2.pastGrants
  extension : Grant.Extension entry.origin entry.saved saved

def GrantTransport.row {entry : GrantCohort} {packet : Packet} (result : GrantTransport entry packet) : GrantCohort :=
  ⟨entry.origin,result.saved⟩

structure ChallengeTransport {scope : Scope} (entry : ChallengeCohort scope) (packet : Packet) where
  saved : Challenge.Saved entry.origin
  later : entry.origin.1.originalScope.task.deadline < packet.1.scope.task.earliest
  member : (⟨entry.origin,saved,later⟩ : ChallengeCohort packet.1.scope) ∈ packet.2.pastChallenges
  extension : Challenge.Extension entry.origin entry.saved saved

def ChallengeTransport.row {scope : Scope} {entry : ChallengeCohort scope} {packet : Packet}
    (result : ChallengeTransport entry packet) : ChallengeCohort packet.1.scope := ⟨entry.origin,result.saved,result.later⟩

structure ServiceTransport {clock : ℚ} (entry : ServiceCohort clock) (packet : Packet) where
  saved : Service.Saved entry.origin
  expired : entry.origin.source.seed.task.deadline < packet.1.source.seed.initial.clock
  member : (⟨entry.origin,saved,expired⟩ : ServiceCohort packet.1.source.seed.initial.clock) ∈ packet.2.pastServices
  extension : Service.Extension entry.origin entry.saved saved

def ServiceTransport.row {clock : ℚ} {entry : ServiceCohort clock} {packet : Packet}
    (result : ServiceTransport entry packet) : ServiceCohort packet.1.source.seed.initial.clock := ⟨entry.origin,result.saved,result.expired⟩

variable {first last : Packet}

def Evolution.grant (trace : Evolution first last) (entry : GrantCohort)
    (member : entry ∈ first.2.pastGrants) : GrantTransport entry last := by
  induction trace generalizing entry with
  | same packet => exact ⟨entry.saved,member,.same entry.saved⟩
  | submit saved word =>
    refine ⟨entry.saved.consume (boundarySource _ (saved.inputs ++ [word])) (World.receipts saved word),?_,.consume ..⟩
    exact List.mem_map.mpr ⟨entry,member,rfl⟩
  | handoff saved fresh =>
    refine ⟨entry.saved.consume (Handoff.Challenge.occurrence fresh) (World.nextReceipts saved fresh),?_,.consume ..⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
  | handoffAt saved fresh actualInputs =>
    refine ⟨entry.saved.consume (World.openingBoundary saved fresh actualInputs)
      (World.openingReceipts saved fresh actualInputs),?_,.consume ..⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
  | append earlier later before after =>
    let middle := before entry member
    let final := after middle.row middle.member
    exact ⟨final.saved,final.member,.append middle.extension final.extension⟩

def Evolution.challenge (trace : Evolution first last) (entry : ChallengeCohort first.1.scope)
    (member : entry ∈ first.2.pastChallenges) : ChallengeTransport entry last := by
  induction trace with
  | same packet => exact ⟨entry.saved,entry.later,member,.same entry.saved⟩
  | submit saved word =>
    refine ⟨entry.saved.consume (boundarySource _ (saved.inputs ++ [word])) entry.later (World.receipts saved word),entry.later,?_,.consume ..⟩
    exact List.mem_map.mpr ⟨entry,member,rfl⟩
  | handoff saved fresh =>
    refine ⟨entry.saved.consume (Handoff.Challenge.occurrence fresh)
      (lt_of_lt_of_le entry.later (World.window_follows saved fresh)) (World.nextReceipts saved fresh),
      lt_of_lt_of_le entry.later (World.window_follows saved fresh),?_,.consume ..⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
  | handoffAt saved fresh actualInputs =>
    refine ⟨entry.saved.consume (World.openingBoundary saved fresh actualInputs)
      (lt_of_lt_of_le entry.later (World.window_follows saved fresh))
      (World.openingReceipts saved fresh actualInputs),
      lt_of_lt_of_le entry.later (World.window_follows saved fresh),?_,.consume ..⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
  | append earlier later before after =>
    let middle := before entry member
    let final := after middle.row middle.member
    exact ⟨final.saved,final.later,final.member,.append middle.extension final.extension⟩

def Evolution.service (trace : Evolution first last) (entry : ServiceCohort first.1.source.seed.initial.clock)
    (member : entry ∈ first.2.pastServices) : ServiceTransport entry last := by
  induction trace with
  | same packet => exact ⟨entry.saved,entry.expired,member,.same entry.saved⟩
  | @submit currentEpoch saved word =>
    refine ⟨entry.saved.consume entry.origin.source (entry.observations (boundarySource currentEpoch (saved.inputs ++ [word])) (saved.inputs.length+1) 1),entry.expired,?_,.consume ..⟩
    exact List.mem_map.mpr ⟨entry,member,rfl⟩
  | handoff saved fresh =>
    refine ⟨entry.saved.consume entry.origin.source (entry.observations (Handoff.Challenge.occurrence fresh) 0 3),
      lt_of_lt_of_le entry.expired (World.initial_clock_follows saved fresh),?_,.consume ..⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
  | handoffAt saved fresh actualInputs =>
    refine ⟨entry.saved.consume entry.origin.source
      (entry.observations (World.openingBoundary saved fresh actualInputs) 0 (actualInputs.length+1)),
      lt_of_lt_of_le entry.expired (World.initial_clock_follows saved fresh),?_,.consume ..⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
  | append earlier later before after =>
    let middle := before entry member
    let final := after middle.row middle.member
    exact ⟨final.saved,final.expired,final.member,.append middle.extension final.extension⟩


variable {epoch : Epoch}
theorem every_current_grant_becomes_the_actual_full_saved_row (saved : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound saved.inputs)
    (record : Mandate.Challenge.Cross.GrantResident epoch.bound saved.inputs) (member : record ∈ saved.grants) :
    World.currentGrant saved fresh record ∈ (World.handoff saved fresh).pastGrants :=
  List.mem_append_right _ (List.mem_map.mpr ⟨record,member,rfl⟩)

theorem every_current_challenge_becomes_the_actual_full_saved_row (saved : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound saved.inputs)
    (record : Mandate.Challenge.Cross.Resident epoch.bound saved.inputs) (member : record ∈ saved.objections) :
    World.currentChallenge saved fresh record ∈ (World.handoff saved fresh).pastChallenges :=
  List.mem_append_right _ (List.mem_map.mpr ⟨record,member,rfl⟩)

theorem every_current_service_becomes_the_actual_full_saved_row (saved : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound saved.inputs) (index : epoch.source.Slot) :
    World.currentService saved fresh index ∈ (World.handoff saved fresh).pastServices :=
  List.mem_append_right _ (List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event
