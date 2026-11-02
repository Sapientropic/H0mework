import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Runtime

import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.FullPlan
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Ancestry

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication
open Publication.Reservation.Feedback.Asynchronous

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- Operational payment and messages do not force the unused future-opponent table.
Restoring the delayed views returns the unchanged original cached transition. -/
structure Frame where
  shell : Owned.Cache task
  delayed : Unit → List (View (code := task.model.source.code))

namespace Frame
variable {task}
def pack (cache : Owned.Cache task) : Frame task := ⟨{cache with beliefs := []},fun _ => cache.beliefs⟩
abbrev past (frame : Frame task) := frame.shell.past
abbrev programme (frame : Frame task) := frame.shell.programme
abbrev within (frame : Frame task) := frame.shell.within
abbrev actualWithin (frame : Frame task) := frame.shell.actualWithin
abbrev retained (frame : Frame task) := frame.shell.retained
abbrev above (frame : Frame task) := frame.shell.above
abbrev views (frame : Frame task) := frame.delayed ()
abbrev current (frame : Frame task) := frame.shell.current

def restore (frame : Frame task) : Owned.Cache task := {frame.shell with beliefs := frame.views}

def advance (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (frame : Frame task) : Frame task :=
  let raw := Driving.Progress.next {frame.shell with beliefs := []}
  ⟨raw,fun _ => Reception.condition task.reader
    (Reception.fresh task.point task.rival task.reader task.vocabulary task.encoding task.law raw.past frame.past.length)
    (Window.Observed.Transcript.publicViews (Driving.Progress.rules frame.shell) frame.views)⟩

private theorem progressing_changed_beliefs (cache : Owned.Cache task)
    (beliefs : List (View (code := task.model.source.code))) :
    Driving.Progress.next {cache with beliefs := beliefs} =
      {Driving.Progress.next cache with beliefs := Window.Observed.Transcript.publicViews (Driving.Progress.rules cache) beliefs} := by
  unfold Driving.Progress.next
  by_cases live : Driving.Progress.Live cache
  · have modified : Driving.Progress.Live {cache with beliefs := beliefs} := live
    rw [dif_pos modified,dif_pos live]
    simp only [Driving.Progress.rules,if_pos live]
    rfl
  · have modified : ¬ Driving.Progress.Live {cache with beliefs := beliefs} := live
    rw [dif_neg modified,dif_neg live]
    simp only [Driving.Progress.rules,if_neg live]
    rfl

theorem restoring_keeps_the_exact_original_transition (frame : Frame task) :
    (advance task frame).restore = Owned.advance task frame.restore := by
  have erased := progressing_changed_beliefs frame.shell []
  have restored := progressing_changed_beliefs frame.shell frame.views
  unfold advance restore Owned.advance Reception.refresh
  rw [erased,restored]

theorem advance_past (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (frame : Frame task) :
    (advance task frame).past = frame.past ++ Driving.Progress.rules frame.shell := by
  exact Driving.Progress.the_next_cached_stage_is_paid_into_the_actual_past {frame.shell with beliefs := []}

theorem advance_knowledge (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (frame : Frame task)
    (covered : Knowledge.Contains frame.views (frame.current task.point task.rival)) :
    Knowledge.Contains (advance task frame).views ((advance task frame).current task.point task.rival) := by
  have original := Owned.advance_knowledge task frame.restore covered
  rw [←restoring_keeps_the_exact_original_transition frame] at original
  exact original
theorem advance_full (frame : Frame task) (full : Owned.FullPlan.Full task frame.restore) :
    Owned.FullPlan.Full task (advance task frame).restore := by
  rw [restoring_keeps_the_exact_original_transition]
  exact Owned.FullPlan.advance task frame.restore full

theorem advance_controls (frame : Frame task) (full : Owned.FullPlan.Full task frame.restore) :
    (advance task frame).programme.controls = frame.programme.controls := by
  change (Driving.Progress.next {frame.shell with beliefs := []}).programme.controls = _
  have width : frame.programme.controls.length = horizon task.domain := full
  unfold Driving.Progress.next
  split
  · change Prefix.Padding.controls task.original frame.programme = _
    simp only [Prefix.Padding.controls,width,Nat.sub_self,List.replicate_zero,List.append_nil]
  · rfl

theorem advance_ancestry (frame : Frame task) (initial : List (View (code := task.model.source.code)))
    (prior : Owned.Ancestry.Generated initial frame.past frame.views) :
    Owned.Ancestry.Generated initial (advance task frame).past (advance task frame).views := by
  have original := Owned.Ancestry.advancing_keeps_every_beliefs_actual_trace task frame.restore prior
  rw [←restoring_keeps_the_exact_original_transition] at original
  exact original
end Frame

def ruleDecidableEq : DecidableEq (Prefix.Rule task.model.source.code) := fun first second =>
  decidable_of_iff (∀ key : task.model.source.code.Key,
    first.work.val key (task.model.source.code.key_mem key) = second.work.val key (task.model.source.code.key_mem key) ∧
    (first.events key (task.model.source.code.key_mem key)).val = (second.events key (task.model.source.code.key_mem key)).val) (by
    constructor
    · intro same
      have work : first.work = second.work := Subtype.ext (funext fun key => funext fun _ => (same key).1)
      have events : first.events = second.events := funext fun key => funext fun _ => Subtype.ext (same key).2
      cases first;cases second;cases work;cases events;rfl
    · intro same;subst second;exact fun _ => ⟨rfl,rfl⟩)
local instance : DecidableEq (Prefix.Rule task.model.source.code) := ruleDecidableEq task

structure Leg (before : Frame task) where
  finish : Frame task
  word : List (Prefix.Rule task.model.source.code)
  literal : finish.past = before.past ++ word
  knowledge : Knowledge.Contains before.views (before.current task.point task.rival) →
    Knowledge.Contains finish.views (finish.current task.point task.rival)
  full : Owned.FullPlan.Full task before.restore → Owned.FullPlan.Full task finish.restore
  ancestry : ∀ initial : List (View (code := task.model.source.code)),
    Owned.Ancestry.Generated initial before.past before.views →
    Owned.Ancestry.Generated initial finish.past finish.views

namespace Leg
variable {task}
def stay (cache : Frame task) : Leg task cache :=
  ⟨cache,[],(List.append_nil _).symm,fun covered => covered,fun full => full,fun _ prior => prior⟩
def advance (cache : Frame task) : Leg task cache :=
  ⟨Frame.advance task cache,Driving.Progress.rules cache.shell,Frame.advance_past task cache,
    Frame.advance_knowledge task cache,Frame.advance_full cache,Frame.advance_ancestry cache⟩
def append {cache : Frame task} (first : Leg task cache) (later : Leg task first.finish) : Leg task cache :=
  ⟨later.finish,first.word ++ later.word,by rw [later.literal,first.literal,List.append_assoc],
    fun covered => later.knowledge (first.knowledge covered),fun full => later.full (first.full full),
    fun initial prior => later.ancestry initial (first.ancestry initial prior)⟩
end Leg

def clock (cache : Frame task) := task.point.point.cut + cache.past.length
abbrev senderTask (sender : Fin task.model.source.code.sites) := {task with reader := sender}
abbrev owns (sender : Fin task.model.source.code.sites) (cache : Frame task) :=
  Owned.Owns (senderTask task sender) cache.shell

structure Slot where
  signal : Fin task.model.source.code.signals
  body : StageBudget.Ballot (code := task.model.source.code)
  encoded : task.encoding signal = some body

def slots (sender : Fin task.model.source.code.sites) (cache : Frame task) : List (Slot task) :=
  (List.finRange task.model.source.code.signals).filterMap fun signal =>
    match found : task.encoding signal with
    | none => none
    | some body =>
        if body.key = sender ∧ body.actor = task.model.source.code.siteParty sender ∧
            body.position = 0 ∧ clock task cache ≤ body.cut then some ⟨signal,body,found⟩ else none

def slot (sender : Fin task.model.source.code.sites) (cache : Frame task) : Option (Slot task) :=
  (slots task sender cache).foldl (fun prior item => match prior with
    | none => some item
    | some earlier => if item.body.cut < earlier.body.cut then some item else prior) none

def move (cache : Frame task) (sender : Fin task.model.source.code.sites)
    (proposed : Prefix.Rule task.model.source.code) : Prefix.Rule task.model.source.code :=
  let signal := observation (cache.current task.point task.rival) sender
  let fallback := cache.programme.at task.original cache.past.length
  {work := ⟨fun key inside => if key = (sender,signal) then proposed.work.val key inside else fallback.work.val key inside,by
      apply task.model.source.code.every_local_policy_is_enumerated
      intro key inside;split
      · exact (List.mem_pi _ _).mp proposed.work.property key inside
      · exact (List.mem_pi _ _).mp fallback.work.property key inside⟩,
   events := fun key inside => if key = (sender,signal) then proposed.events key inside else fallback.events key inside}

theorem only_the_sender_local_key_changes (cache : Frame task) (sender : Fin task.model.source.code.sites)
    (proposed : Prefix.Rule task.model.source.code) (key : task.model.source.code.Key)
    (other : key ≠ (sender,observation (cache.current task.point task.rival) sender)) :
    (move task cache sender proposed).work.val key (task.model.source.code.key_mem key) =
      (cache.programme.at task.original cache.past.length).work.val key (task.model.source.code.key_mem key) ∧
    (move task cache sender proposed).events key (task.model.source.code.key_mem key) =
      (cache.programme.at task.original cache.past.length).events key (task.model.source.code.key_mem key) := by
  simp only [move,if_neg other];exact ⟨trivial,trivial⟩

abbrev proposal (cache : Frame task) (rule : Prefix.Rule task.model.source.code) :=
  Prefix.extension (horizon task.domain) cache.past
    (Splice.word (rule :: cache.programme.controls.drop (cache.past.length+1)))

inductive Judgement (cache : Frame task) (rule : Prefix.Rule task.model.source.code) where
  | admitted (accepted : Selection.acceptable task.model task.domain task.original cache.programme (proposal task cache rule))
  | refused (rejected : Selection.Rejection task.model task.domain task.original cache.programme (proposal task cache rule))

def inspect (cache : Frame task) (rule : Prefix.Rule task.model.source.code) : Judgement task cache rule :=
  if same : (proposal task cache rule).controls = cache.programme.controls then
    .admitted (by
      have exactProgramme : proposal task cache rule = cache.programme := by
        exact (Continuation.Whole.Program.mk.injEq ..).mpr same
      rw [exactProgramme]
      exact Prefix.Commitment.admissible_plan_is_its_own_valid_reference
        task.model task.domain task.original task.baseline cache.programme cache.above)
  else if accepted : Selection.acceptable task.model task.domain task.original cache.programme (proposal task cache rule) then
    .admitted accepted
  else match Distributed.inspect (Selection.holds task.model task.domain task.original cache.programme (proposal task cache rule))
      (Replanning.rows task.model task.domain) with
    | .accepted all => False.elim (accepted all)
    | .rejected row original broken => .refused ⟨row,original,broken⟩

def commit (cache : Frame task) (rule : Prefix.Rule task.model.source.code)
    (accepted : Selection.acceptable task.model task.domain task.original cache.programme (proposal task cache rule)) : Frame task :=
  {cache with
    shell := {cache.shell with
      programme := proposal task cache rule
      retained := Prefix.every_completion_preserves_the_committed_control_prefix _ _ _ cache.within
      above := Selection.acceptable_trans _ _ _ _ _ _ accepted cache.above}}

theorem committed_next (cache : Frame task) (rule : Prefix.Rule task.model.source.code)
    (accepted : Selection.acceptable task.model task.domain task.original cache.programme (proposal task cache rule))
    (live : Driving.Progress.Live cache.shell) :
    Driving.Progress.rule (commit task cache rule accepted).shell = rule := by
  change (proposal task cache rule).at task.original cache.past.length = _
  change ((cache.past ++ (rule :: cache.programme.controls.drop (cache.past.length+1))).take
    (horizon task.domain))[cache.past.length]?.getD _ = _
  rw [List.getElem?_take_of_lt live.2,List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]

def execute (cache : Frame task) (rule : Prefix.Rule task.model.source.code)
    (accepted : Selection.acceptable task.model task.domain task.original cache.programme (proposal task cache rule))
    (live : Driving.Progress.Live cache.shell) : Leg task cache :=
  {finish := Frame.advance task (commit task cache rule accepted)
   word := [rule]
   literal := by
      rw [Frame.advance_past]
      rw [Driving.Progress.rules,if_pos (show Driving.Progress.Live (commit task cache rule accepted).shell from live),
        committed_next task cache rule accepted live]
      rfl
   knowledge := fun covered => Frame.advance_knowledge task _ covered
   full := by
      intro full
      apply Frame.advance_full
      change (proposal task cache rule).controls.length = horizon task.domain
      have width : cache.programme.controls.length = horizon task.domain := full
      simp only [proposal,Prefix.extension,Continuation.Whole.Complete.clip,Splice.word,
        List.length_take,List.length_append,List.length_cons,List.length_drop,width]
      have within := cache.within
      omega
   ancestry := fun initial prior => Frame.advance_ancestry (commit task cache rule accepted) initial prior}

def waitAt (cut : Nat) : Nat → (cache : Frame task) → Leg task cache
  | 0,cache => Leg.stay cache
  | fuel+1,cache =>
      if Driving.Progress.Live cache.shell ∧ clock task cache < cut then
        let step := Leg.advance cache
        step.append (waitAt cut fuel step.finish)
      else Leg.stay cache

def waitOwn (sender : Fin task.model.source.code.sites) : Nat → (cache : Frame task) → Leg task cache
  | 0,cache => Leg.stay cache
  | fuel+1,cache =>
      if Driving.Progress.Live cache.shell ∧ ¬ owns task sender cache then
        let step := Leg.advance cache
        step.append (waitOwn sender fuel step.finish)
      else Leg.stay cache

abbrev RawRequest := Institutions.Capitalism.Universal.Source.Program.Request Party Good Port (Mandate.State Party Technology) Instrument

def eligible (sender : Fin task.model.source.code.sites) (planned : Slot task) (request : RawRequest (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Bool :=
  RequestAttestation.protocolSyntax request && decide (request.signer = task.model.source.code.siteParty sender ∧
    task.vocabulary.decode request.purpose = some (planned.body.scope,planned.body.choice))

def request (sender : Fin task.model.source.code.sites) (planned : Slot task) :=
  task.model.source.code.actions.find? (eligible task sender planned)

abbrev rows (cache : Frame task) := StageTrace.records task.point.point (Reception.stages task.rival cache.past)

def attestedAt (cache : Frame task) (index : Nat) :=
  (rows task cache)[index]?.bind (fun row => RequestAttestation.issued task.vocabulary row 0)

abbrev wireAt (cache : Frame task) (index : Nat) :=
  StageTransport.issuedAt task.vocabulary task.encoding task.point.point (Reception.stages task.rival cache.past) index

abbrev fresh (cache : Frame task) (previous : Nat) :=
  Reception.fresh task.point task.rival task.reader task.vocabulary task.encoding task.law cache.past previous

inductive Failure (cache : Frame task) where
  | noEncoding (sender : Fin task.model.source.code.sites) (missing : slot task sender cache = none)
  | windowEnded (ended : ¬ Driving.Progress.Live cache.shell)
  | missedOwnCut (sender : Fin task.model.source.code.sites) (cut : Nat)
      (missed : ¬ (clock task cache = cut ∧ owns task sender cache))
  | notOwnTurn (sender : Fin task.model.source.code.sites) (foreign : ¬ owns task sender cache)
  | unsupportedActivation (sender : Fin task.model.source.code.sites)
      (outside : .activate sender ∉ task.model.source.code.eventAlphabet)
  | noRequest (sender : Fin task.model.source.code.sites) (planned : Slot task)
      (missing : request task sender planned = none)
  | unsupportedWord (raw : RawRequest (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
      (outside : [raw] ∉ words task.model.source.code.actions task.model.source.code.actionLimit)
  | originalRefusal (rule : Prefix.Rule task.model.source.code)
      (row : Selection.Rejection task.model task.domain task.original cache.programme (proposal task cache rule))
  | noStatement (index : Nat) (missing : attestedAt task cache index = none)
  | differentBallot (expected actual : StageBudget.Ballot (code := task.model.source.code)) (different : actual ≠ expected)
  | unsupportedSend (sender : Fin task.model.source.code.sites)
      (missing : Publication.Plan.sendRule (code := task.model.source.code) sender task.reader = none)
  | noWire (index : Nat) (missing : wireAt task cache index = none)
  | pending (statement : RequestAttestation.Statement (code := task.model.source.code))
      (wire : StageTransport.Wire (code := task.model.source.code))
      (previous : Nat) (missing : (fresh task cache previous).find? (fun receipt =>
        decide (receipt.statement = statement ∧ receipt.confirmation.wire = wire)) = none)

structure Result (before : Frame task) (Output : Frame task → Type) where
  path : Leg task before
  value : Sum (Failure task path.finish) (Output path.finish)

namespace Result
variable {task} {Output : Frame task → Type}
def fail (cache : Frame task) (reason : Failure task cache) : Result task cache Output :=
  ⟨Leg.stay cache,.inl reason⟩
def prepend {cache : Frame task} (first : Leg task cache)
    (later : Result task first.finish Output) : Result task cache Output :=
  ⟨first.append later.path,later.value⟩
end Result

structure Activation (cache : Frame task) where
  statement : RequestAttestation.Statement (code := task.model.source.code)
  index : Nat
  newStage : index + 1 = cache.past.length
  generated : attestedAt task cache index = some statement

private theorem executed_length (cache : Frame task) (rule : Prefix.Rule task.model.source.code)
    (accepted : Selection.acceptable task.model task.domain task.original cache.programme (proposal task cache rule))
    (live : Driving.Progress.Live cache.shell) :
    cache.past.length + 1 = (execute task cache rule accepted live).finish.past.length := by
  rw [(execute task cache rule accepted live).literal,List.length_append]
  rfl

def activate (sender : Fin task.model.source.code.sites) (planned : Slot task)
    (cache : Frame task) : Result task cache (Activation task) :=
  if live : Driving.Progress.Live cache.shell then
    if atCut : clock task cache = planned.body.cut ∧ owns task sender cache then
      if supported : .activate sender ∈ task.model.source.code.eventAlphabet then
        match chosen : request task sender planned with
        | none => Result.fail cache (.noRequest sender planned chosen)
        | some raw =>
          if work : [raw] ∈ words task.model.source.code.actions task.model.source.code.actionLimit then
            let rule := move task cache sender (Replay.protocol sender [raw] work)
            match inspect task cache rule with
            | .refused row => Result.fail cache (.originalRefusal rule row)
            | .admitted accepted =>
                let actual := execute task cache rule accepted live
                match emitted : attestedAt task actual.finish cache.past.length with
                | none => ⟨actual,.inl (.noStatement cache.past.length emitted)⟩
                | some body =>
                    if same : body.ballot = planned.body then
                      ⟨actual,.inr ⟨body,cache.past.length,executed_length task cache rule accepted live,emitted⟩⟩
                    else ⟨actual,.inl (.differentBallot planned.body body.ballot same)⟩
          else Result.fail cache (.unsupportedWord raw work)
      else Result.fail cache (.unsupportedActivation sender supported)
    else Result.fail cache (.missedOwnCut sender planned.body.cut atCut)
  else Result.fail cache (.windowEnded live)

structure Dispatch (cache : Frame task) where
  statement : RequestAttestation.Statement (code := task.model.source.code)
  wire : StageTransport.Wire (code := task.model.source.code)
  index : Nat
  newStage : index + 1 = cache.past.length
  generated : wireAt task cache index = some wire
  source : wire.ballot = statement.ballot

def dispatch (sender : Fin task.model.source.code.sites)
    (statement : RequestAttestation.Statement (code := task.model.source.code))
    (cache : Frame task) : Result task cache (Dispatch task) :=
  if live : Driving.Progress.Live cache.shell then
    if owned : owns task sender cache then
      match supported : Publication.Plan.sendRule (code := task.model.source.code) sender task.reader with
      | none => Result.fail cache (.unsupportedSend sender supported)
      | some sending =>
          let rule := move task cache sender sending
          match inspect task cache rule with
          | .refused row => Result.fail cache (.originalRefusal rule row)
          | .admitted accepted =>
              let actual := execute task cache rule accepted live
              match sent : wireAt task actual.finish cache.past.length with
              | none => ⟨actual,.inl (.noWire cache.past.length sent)⟩
              | some wire =>
                  if same : wire.ballot = statement.ballot then
                    ⟨actual,.inr ⟨statement,wire,cache.past.length,executed_length task cache rule accepted live,sent,same⟩⟩
                  else ⟨actual,.inl (.differentBallot statement.ballot wire.ballot same)⟩
    else Result.fail cache (.notOwnTurn sender owned)
  else Result.fail cache (.windowEnded live)

structure Receipt (cache : Frame task) where
  statement : RequestAttestation.Statement (code := task.model.source.code)
  wire : StageTransport.Wire (code := task.model.source.code)
  receipt : RequestReadback.Receipt (code := task.model.source.code)
  previous : Nat
  generated : receipt ∈ fresh task cache previous
  complete : receipt.statement = statement
  sameWire : receipt.confirmation.wire = wire

def receive (statement : RequestAttestation.Statement (code := task.model.source.code))
    (wire : StageTransport.Wire (code := task.model.source.code)) :
    Nat → (cache : Frame task) → Result task cache (Receipt task)
  | 0,cache =>
      match found : (fresh task cache cache.past.length).find? (fun receipt =>
          decide (receipt.statement = statement ∧ receipt.confirmation.wire = wire)) with
      | none => Result.fail cache (.pending statement wire cache.past.length found)
      | some receipt =>
          have inside := List.mem_of_find?_eq_some found
          have same : receipt.statement = statement ∧ receipt.confirmation.wire = wire :=
            of_decide_eq_true (List.find?_some (p := fun receipt : RequestReadback.Receipt (code := task.model.source.code) => decide (receipt.statement = statement ∧ receipt.confirmation.wire = wire)) found)
          ⟨Leg.stay cache,.inr ⟨statement,wire,receipt,cache.past.length,inside,same.1,same.2⟩⟩
  | fuel+1,cache =>
      if live : Driving.Progress.Live cache.shell then
        let step := Leg.advance cache
        match found : (fresh task step.finish cache.past.length).find? (fun receipt =>
            decide (receipt.statement = statement ∧ receipt.confirmation.wire = wire)) with
        | none => Result.prepend step (receive statement wire fuel step.finish)
        | some receipt =>
            have inside := List.mem_of_find?_eq_some found
            have same : receipt.statement = statement ∧ receipt.confirmation.wire = wire :=
            of_decide_eq_true (List.find?_some (p := fun receipt : RequestReadback.Receipt (code := task.model.source.code) => decide (receipt.statement = statement ∧ receipt.confirmation.wire = wire)) found)
            ⟨step,.inr ⟨statement,wire,receipt,cache.past.length,inside,same.1,same.2⟩⟩
      else Result.fail cache (.windowEnded live)

def round (sender : Fin task.model.source.code.sites) (cache : Frame task) : Result task cache (Receipt task) :=
  match found : slot task sender cache with
  | none => Result.fail cache (.noEncoding sender found)
  | some planned =>
      let waiting := waitAt task planned.body.cut (horizon task.domain+1) cache
      let activated := activate task sender planned waiting.finish
      Result.prepend waiting (match activated.value with
        | .inl reason => ⟨activated.path,.inl reason⟩
        | .inr body =>
            let sendingTurn := waitOwn task sender (horizon task.domain+1) activated.path.finish
            let sent := dispatch task sender body.statement sendingTurn.finish
            Result.prepend activated.path (Result.prepend sendingTurn (match sent.value with
              | .inl reason => ⟨sent.path,.inl reason⟩
              | .inr delivered => Result.prepend sent.path
                  (receive task delivered.statement delivered.wire (horizon task.domain+1) sent.path.finish))))

inductive Walk : Frame task → Type where
  | done {cache : Frame task} : Walk cache
  | stopped {cache : Frame task} (path : Leg task cache) (reason : Failure task path.finish) : Walk cache
  | learned {cache : Frame task} (path : Leg task cache) (receipt : Receipt task path.finish)
      (later : Walk path.finish) : Walk cache

def learn (sender : Fin task.model.source.code.sites) : Nat → (cache : Frame task) → Walk task cache
  | 0,_ => .done
  | count+1,cache =>
      let next := round task sender cache
      match next.value with
      | .inl reason => .stopped next.path reason
      | .inr receipt => .learned next.path receipt (learn sender count next.path.finish)

namespace Walk
variable {task}
def path : {cache : Frame task} → Walk task cache → Leg task cache
  | cache,.done => Leg.stay cache
  | _,.stopped path _ => path
  | _,.learned first _ later => first.append later.path

def statements : {cache : Frame task} → Walk task cache → List (RequestAttestation.Statement (code := task.model.source.code))
  | _,.done | _,.stopped .. => []
  | _,.learned _ receipt later => receipt.statement :: later.statements

def complete : {cache : Frame task} → Walk task cache → Bool
  | _,.done => true
  | _,.stopped .. => false
  | _,.learned _ _ later => later.complete

theorem every_successful_stage_is_an_actual_prefix {cache : Frame task} (walk : Walk task cache) :
    match walk with
    | .done | .stopped .. => True
    | .learned first _ _later => ∃ suffix, walk.path.finish.past = first.finish.past ++ suffix := by
  cases walk with
  | done | stopped => trivial
  | learned first receipt later => exact ⟨later.path.word,later.path.literal⟩
end Walk

abbrev Generated := Sum (Selection.Rejection task.model task.domain task.original task.baseline task.baseline)
  (Sigma fun cache : Frame task => Walk task cache)

def generate (sender : Fin task.model.source.code.sites) (count : Nat) : Generated task :=
  match Owned.Source.seed task with
  | .rejected reason => Sum.inl reason
  | .accepted cache _ _ _ => Sum.inr (Sigma.mk (Frame.pack (task := task) cache) (learn task sender count (Frame.pack (task := task) cache)))


namespace Receipt
variable {task} {cache : Frame task}
theorem paid_source_and_exact_local_readback (body : Receipt task cache) :
    body.statement ∈ RequestAttestation.ledger task.vocabulary task.point.point (Reception.stages task.rival cache.past) ∧
    body.statement.ballot = body.wire.ballot ∧
    observation (cache.current task.point task.rival) task.reader = body.receipt.reading := by
  have included := ((Reception.mem_fresh_iff _ _ _ _ _ _ _ _ _).mp body.generated).1
  have original := RequestReadback.recovered_requests_have_paid_communication_complete_source_and_local_readback
    task.vocabulary task.encoding task.law task.point.point (Reception.stages task.rival cache.past)
    task.reader cache.past.length body.receipt included
  refine ⟨?_,?_,Reception.a_new_receipt_reads_this_exact_actual_cut _ _ _ _ _ _ _ _ _ body.generated⟩
  · rw [←body.complete];exact original.2.1
  · rw [←body.complete,←body.sameWire];exact original.2.2.1

theorem the_same_delivery_cannot_be_learned_again (body : Receipt task cache)
    (later : List (Prefix.Rule task.model.source.code)) (laterStart : Nat)
    (ordered : cache.past.length ≤ laterStart) :
    body.receipt ∉ Reception.fresh task.point task.rival task.reader task.vocabulary task.encoding task.law later laterStart :=
  Reception.a_consumed_packet_cannot_reappear_in_a_later_stage _ _ _ _ _ _ _ _ later laterStart ordered _ body.generated
end Receipt

structure Occurrence (cache : Frame task) (sender : Fin task.model.source.code.sites) (count : Nat) where
  generated : Walk task cache
  exact_generation : generated = learn task sender count cache

def occurrence (cache : Frame task) (sender : Fin task.model.source.code.sites) (count : Nat) : Occurrence task cache sender count :=
  ⟨learn task sender count cache,rfl⟩

namespace Occurrence
variable {task} {cache : Frame task} {sender : Fin task.model.source.code.sites} {count : Nat}
abbrev controls (made : Occurrence task cache sender count) := made.generated.path.finish.past
end Occurrence



private theorem nondomination_survives {Policy Axis : Type} (axes : List Axis) (benefit : Policy → Axis → ℚ)
    (old next other : Policy) (maximal : ¬ Distributed.Improves axes benefit old other)
    (above : Distributed.NoWorse axes benefit next old) : ¬ Distributed.Improves axes benefit next other := by
  intro strict
  exact maximal ⟨Distributed.noWorse_trans strict.1 above,
    fun reverse => strict.2 (Distributed.noWorse_trans above reverse)⟩

namespace Public
variable (request : PublicTask.Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (point : Cursor request.model.source.code) (future : Opponent request.model.source.code)
  (localRounds : Nat) (sender : Fin request.model.source.code.sites) (rounds : Nat)

abbrev Prior := Local.Output request quotas point future localRounds

def Follow (prior : Prior request quotas point future localRounds) : Type := match prior with
  | .inherited _ => Unit
  | .installed fits _ _ choice _ actual _ =>
      Occurrence (PublicTask.Feedback.task request _ fits quotas point future choice)
        (Frame.pack actual.1) sender rounds

def follow (prior : Prior request quotas point future localRounds) : Follow request quotas point future localRounds sender rounds prior :=
  match prior with
  | .inherited _ => ()
  | .installed fits _ _ choice _ actual _ =>
      occurrence (PublicTask.Feedback.task request _ fits quotas point future choice) (Frame.pack actual.1) sender rounds

def produce :=
  let prior := Local.produce request quotas point future localRounds
  Sigma.mk prior (follow request quotas point future localRounds sender rounds prior)

def Sound (prior : Prior request quotas point future localRounds)
    (next : Follow request quotas point future localRounds sender rounds prior) : Prop :=
  prior.Sound ∧ match prior,next with
  | .inherited _,_ => True
  | .installed fits _ _ choice _ actual _,next =>
      let task := PublicTask.Feedback.task request _ fits quotas point future choice
      let final := next.generated.path.finish
      Selection.acceptable request.model (PublicTask.domain request (observation (currentView point) request.reader)) request.original
        (PaidSearch.reference request _ fits) final.programme ∧
      Knowledge.Contains final.views (final.current task.point task.rival) ∧
      (∃ suffix, final.past = actual.1.past ++ suffix) ∧
      ∀ other ∈ Prefix.candidates request.model (PublicTask.domain request (observation (currentView point) request.reader))
        request.original (PaidSearch.fees request quotas) (PaidSearch.reference request _ fits),
        ¬ Distributed.Improves
          (Selection.axes (fuel := horizon task.domain) task.model task.domain)
          (Selection.benefit task.model task.domain task.original) final.programme other.protocol

theorem follows_the_same_source (prior : Prior request quotas point future localRounds) (sound : prior.Sound) :
    Sound request quotas point future localRounds sender rounds prior
      (follow request quotas point future localRounds sender rounds prior) := by
  refine ⟨sound,?_⟩
  cases prior with
  | inherited => trivial
  | installed fits work released choice selected actual generated =>
      let task := PublicTask.Feedback.task request _ fits quotas point future choice
      let made := occurrence task (Frame.pack actual.1) sender rounds
      refine ⟨Selection.acceptable_trans _ _ _ _ _ _ made.generated.path.finish.above choice.policy.accepted,
        made.generated.path.knowledge sound.2.1,⟨_,made.generated.path.literal⟩,?_⟩
      intro other inside
      exact nondomination_survives (Selection.axes (fuel := horizon task.domain) task.model task.domain)
        (Selection.benefit task.model task.domain task.original) choice.policy.protocol
        made.generated.path.finish.programme other.protocol (choice.maximal other inside)
        (Selection.acceptance_bounds_every_benefit _ _ _ _ _ made.generated.path.finish.above)

theorem all_public_histories_generate_fresh_inquiry_or_a_typed_failure
    (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed) :
    let current := EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages
    Sound request quotas current future localRounds sender rounds
      (produce request quotas current future localRounds sender rounds).1
      (produce request quotas current future localRounds sender rounds).2 :=
  follows_the_same_source request quotas _ future localRounds sender rounds _
    (Local.all_public_histories_generate_actual_local_installation request quotas future localRounds origin stages installed)
end Public

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry
