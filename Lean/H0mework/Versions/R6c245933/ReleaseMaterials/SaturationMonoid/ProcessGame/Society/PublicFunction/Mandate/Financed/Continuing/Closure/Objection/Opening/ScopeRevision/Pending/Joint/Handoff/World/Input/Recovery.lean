import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Distributed.Reaction.Native.Future.Recovery
noncomputable section

variable {epoch : Epoch} (inventory : Inventory epoch) (word : List Action)

def context : Search.Context (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨base,epoch.scope,epoch.source.seed.actionsAt (current epoch inventory.inputs),
    [.feedstock,.service],epoch.source.seed.budget⟩

structure Origin where
  private mk ::
  item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  actual : item ∈ (Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) word
  refused : ¬ (Mandate.law base epoch.scope).Valid item.before item.request

/-- Raw execution may continue past a refusal. Only its actually refused positions
enter recovery; previously valid issues, payments and commands are not retried. -/
def origins : List (Origin inventory word) :=
  ((Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) word).attach.filterMap fun item =>
    if refused : ¬ (Mandate.law base epoch.scope).Valid item.val.before item.val.request
    then some ⟨item.val,item.property,refused⟩ else none

def pending := (origins inventory word).map (fun entry => entry.item.request)

structure Cursor where
  private mk ::
  saved : Inventory epoch
  consumed : List Action
  residual : List Action
  split : consumed ++ residual = pending inventory word
  extension : ∃ suffix, saved.inputs = inventory.inputs ++ [word] ++ suffix
  native : Event.Evolution ⟨epoch,inventory⟩ ⟨epoch,saved⟩
  finance : (Financial.Family.process sources).Run inventory.finance.current saved.finance.current

def begin : Cursor inventory word :=
  ⟨World.submit inventory word,[],pending inventory word,rfl,⟨[],by simp [World.submit]⟩,
    .submit inventory word,World.financialRun inventory word⟩

namespace Cursor
variable {inventory word} (cursor : Cursor inventory word)
abbrev before := current epoch cursor.saved.inputs
abbrev model := context cursor.saved
abbrev proposal (actor : Bool) := Search.selected cursor.model cursor.before actor cursor.residual
abbrev retry (actor : Bool) := (cursor.proposal actor).retry cursor.model cursor.before cursor.residual
abbrev emitted (actor : Bool) := (cursor.proposal actor).word cursor.model cursor.before cursor.residual
abbrev quality (actor : Bool) := (cursor.proposal actor).quality cursor.model cursor.before cursor.residual

def advance (actor : Bool) : Cursor inventory word :=
  ⟨World.submit cursor.saved (cursor.emitted actor),cursor.consumed ++ (cursor.retry actor).consumed,
    (cursor.retry actor).residual,(by rw [List.append_assoc,(cursor.retry actor).original_split,cursor.split]),
    (by
      obtain ⟨suffix,same⟩ := cursor.extension
      exact ⟨suffix ++ [cursor.emitted actor],by simp only [World.submit,same,List.append_assoc]⟩),
    .append cursor.native (.submit cursor.saved (cursor.emitted actor)),
    cursor.finance.concatRuns _ (World.financialRun cursor.saved (cursor.emitted actor))⟩

/-- A bill is an actual submission and never an original-request completion. -/
def appendActual (emitted : List Action) : Recovery.Cursor inventory word :=
  ⟨World.submit cursor.saved emitted,cursor.consumed,cursor.residual,cursor.split,(by
      obtain ⟨suffix,same⟩ := cursor.extension
      exact ⟨suffix ++ [emitted],by simp only [World.submit,same,List.append_assoc]⟩),
    .append cursor.native (.submit cursor.saved emitted),
    cursor.finance.concatRuns _ (World.financialRun cursor.saved emitted)⟩

def replayPreparation (preparation : List Action) : Recovery.Cursor inventory word :=
  let proposal : Search.Proposal cursor.model := ⟨preparation⟩
  let retry := proposal.retry cursor.model cursor.before cursor.residual
  let emitted := proposal.word cursor.model cursor.before cursor.residual
  ⟨World.submit cursor.saved emitted,cursor.consumed ++ retry.consumed,retry.residual,
    (by rw [List.append_assoc,retry.original_split,cursor.split]),(by
      obtain ⟨suffix,same⟩ := cursor.extension
      exact ⟨suffix ++ [emitted],by simp only [World.submit,same,List.append_assoc]⟩),
    .append cursor.native (.submit cursor.saved emitted),
    cursor.finance.concatRuns _ (World.financialRun cursor.saved emitted)⟩

def remainingOrigins := (origins inventory word).drop cursor.consumed.length

theorem every_remaining_position_retains_its_original_failed_identity :
    cursor.remainingOrigins.map (fun entry => entry.item.request) = cursor.residual := by
  rw [remainingOrigins,List.map_drop]
  change (pending inventory word).drop cursor.consumed.length = _
  rw [←cursor.split,List.drop_left]

theorem preparation_is_personal_and_actually_legal (actor : Bool) :
    Mandate.Replay.Personal actor ((cursor.proposal actor).prepared cursor.model cursor.before).output ∧
    Mandate.Replay.Legal (base := base) epoch.scope cursor.before
      ((cursor.proposal actor).prepared cursor.model cursor.before).output :=
  ⟨Search.selected_preparation_is_personally_signed cursor.model cursor.before actor cursor.residual,
    ((cursor.proposal actor).prepared cursor.model cursor.before).successful_output_is_all_legal
      (Search.selected_preparation_is_legal cursor.model cursor.before actor cursor.residual)⟩

theorem actual_repair_and_cut (actor : Bool) :
    (World.actual cursor.saved (cursor.emitted actor)).submitted = cursor.emitted actor ∧
    (World.actual cursor.saved (cursor.emitted actor)).before = cursor.before :=
  World.actual_word_and_cut _ _

theorem positive_progress (actor : Bool) (positive : 0 < cursor.quality actor) :
    (cursor.advance actor).residual.length < cursor.residual.length := by
  have paid := Search.selected_preparation_is_legal cursor.model cursor.before actor cursor.residual
  have split : (cursor.retry actor).consumed.length + (cursor.retry actor).residual.length = cursor.residual.length := by
    simpa only [List.length_append] using congrArg List.length (cursor.retry actor).original_split
  have consumed : 0 < (cursor.retry actor).consumed.length := by
    change 0 < (cursor.proposal actor).quality cursor.model cursor.before cursor.residual at positive
    simpa only [Search.Proposal.quality,paid,if_true] using positive
  change (cursor.retry actor).residual.length < cursor.residual.length
  have arithmetic (a b c : Nat) (same : a+b=c) (positive : 0<a) : b<c := by omega
  exact arithmetic _ _ _ split consumed

theorem no_progress_is_complete_for_the_actual_generated_catalogue (actor : Bool)
    (stopped : ¬ 0 < cursor.quality actor) (candidate : Search.Proposal cursor.model)
    (listed : candidate ∈ Search.proposals cursor.model cursor.before actor cursor.residual) :
    candidate.quality cursor.model cursor.before cursor.residual = 0 := by
  have maximal := Search.selected_maximal cursor.model cursor.before actor cursor.residual candidate listed
  change candidate.quality cursor.model cursor.before cursor.residual ≤ cursor.quality actor at maximal
  omega
end Cursor

inductive Trace : Cursor inventory word → Type where
  | finished (cursor : Cursor inventory word) (empty : cursor.residual = []) : Trace cursor
  | blocked (cursor : Cursor inventory word) (head : Action) (tail : List Action)
      (remaining : cursor.residual = head::tail) (stopped : ¬ 0 < cursor.quality head.signer) : Trace cursor
  | advanced (cursor : Cursor inventory word) (head : Action) (tail : List Action)
      (remaining : cursor.residual = head::tail) (progress : 0 < cursor.quality head.signer)
      (later : Trace (cursor.advance head.signer)) : Trace cursor

def execute (cursor : Cursor inventory word) : Trace inventory word cursor :=
  match remaining : cursor.residual with
  | [] => .finished cursor remaining
  | head::tail => if progress : 0 < cursor.quality head.signer then
      .advanced cursor head tail remaining progress (execute (cursor.advance head.signer))
    else .blocked cursor head tail remaining progress
termination_by cursor.residual.length
decreasing_by exact cursor.positive_progress head.signer progress

def Trace.finish : {cursor : Cursor inventory word} → Trace inventory word cursor → Cursor inventory word
  | _,.finished cursor _ => cursor
  | _,.blocked cursor head _ _ _ => cursor.advance head.signer
  | _,.advanced _ _ _ _ _ later => later.finish

def produce := execute inventory word (begin inventory word)

def sourceRequest (intent : Intent) := produce inventory (Input.emit inventory intent)
def sourceRepayment := produce inventory
  (Repayment.Portfolio.word (Mandate.law base epoch.scope)
    (Handoff.debtPositions (current epoch inventory.inputs)) (current epoch inventory.inputs))

/-- The existing event root consumes the generated repair's saved full inventory. -/
def response := Event.produce (produce inventory word).finish.saved []
def packet := (response inventory word).packet
def evolution : Event.Evolution ⟨epoch,inventory⟩ (packet inventory word) :=
  .append (produce inventory word).finish.native (response inventory word).native
def financialRun : (Financial.Family.process sources).Run inventory.finance.current (packet inventory word).2.finance.current :=
  (produce inventory word).finish.finance.concatRuns _ (response inventory word).finance

theorem all_original_refused_positions_are_preserved :
    (produce inventory word).finish.consumed ++ (produce inventory word).finish.residual = pending inventory word :=
  (produce inventory word).finish.split

theorem all_old_and_new_actual_inputs_reach_the_original_response_source :
    ∃ suffix, (produce inventory word).finish.saved.inputs = inventory.inputs ++ [word] ++ suffix :=
  (produce inventory word).finish.extension

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery
