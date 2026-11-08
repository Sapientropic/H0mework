import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CachedWorkDispatch
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CatalogueHandoffSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SuccessorSigningSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (parent : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (saved : Cursor parent.source.code)

-- Register future delivery addresses; existing packets and attempts remain actual history.
def catalogue : CatalogueHandoffSource.Catalogue parent.source.code :=
 ⟨[],0,[],0,(List.range (parent.source.code.sites*parent.source.code.sites)).map fun offset =>
  .deliver ((EventStep.seed saved).frame.sent.length+offset)⟩
abbrev code := CatalogueHandoffSource.code parent.source.code (catalogue parent saved)
def start := CatalogueHandoffSource.cursor parent.source.code (catalogue parent saved) saved

def model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument) :=
 ⟨parent.base,parent.scope,(start parent saved).source,parent.law_exact,parent.task_exact⟩

def vocabulary (previous : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) : OwnedAttestation.Vocabulary (Party := Party) (Good := Good)
 (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
 ⟨fun port => (previous.decode port).map fun label => ({label.1 with phase := saved.cut},label.2),
  previous.epoch,previous.feeUnit⟩

theorem start_keeps_the_entire_actual_state (original : saved.side = .original) :
 EventStep.seed (start parent saved) =
 Extension.state parent.source.code (CatalogueHandoffSource.supply parent.source.code (catalogue parent saved))
  (EventStep.seed saved) :=
 CatalogueHandoffSource.seed parent.source.code (catalogue parent saved) saved original

theorem every_future_run_preserves_the_original_financial_prefix
 (original : saved.side = .original)
 (stages : List (EventHistory.Stage (code := code parent saved))) (ordinal : Nat)
 (bounded : ordinal ≤ EventStep.boundary saved) :
 Native.Coupling.Match parent.source.code saved.source.input
  (EventHistory.execute (start parent saved) stages).source.input
  (Financial.accountAt saved.source.input ordinal)
  (Financial.accountAt (EventHistory.execute (start parent saved) stages).source.input ordinal) :=
 CatalogueHandoffSource.completeFinancialPrefix parent.source.code (catalogue parent saved) saved original stages ordinal bounded

variable (previous : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))

-- Rephasing applies only to future owned execution records, never to the old issuing segment.
theorem every_new_ballot_is_born_after_the_actual_successor
 (stages : List (EventHistory.Stage (code := code parent saved)))
 (body : StageBudget.Ballot (code := code parent saved))
 (inside : body ∈ StageBudget.ledger (vocabulary parent saved previous) (start parent saved) stages) :
 saved.cut ≤ body.cut ∧ body.scope.phase = saved.cut := by
 obtain ⟨row,member,position,made⟩ := StageBudget.ledger_origin _ _ _ body inside
 obtain ⟨site,item,_,_,_,_,decoded,_,_,cut,_⟩ := StageBudget.issued_has_an_owned_valid_paid_origin _ row position body made
 have clock : row.cursor.cut ∈ (StageTrace.records (start parent saved) stages).map (fun record => record.cursor.cut) :=
  List.mem_map.mpr ⟨row,member,rfl⟩
 rw [StageTrace.no_occurrence_is_lost_or_duplicated] at clock
 obtain ⟨index,_,same⟩ := List.mem_map.mp clock
 have phase : body.scope.phase = saved.cut := by
  change (previous.decode item.request.purpose).map (fun label => ({label.1 with phase := saved.cut},label.2)) = some (body.scope,body.choice) at decoded
  cases found : previous.decode item.request.purpose with
  | none => simp only [found,Option.map_none] at decoded; contradiction
  | some label =>
    simp only [found,Option.map_some,Option.some.injEq,Prod.mk.injEq] at decoded
    exact congrArg Scope.phase decoded.1.symm
 refine ⟨?_,phase⟩
 change saved.cut+index = row.cursor.cut at same
 omega

theorem an_old_ballot_cannot_be_reissued_by_relabelling
 (stages : List (EventHistory.Stage (code := code parent saved)))
 (body : StageBudget.Ballot (code := code parent saved)) (old : body.cut < saved.cut) :
 StageBudget.verify (vocabulary parent saved previous) (start parent saved) stages body = false := by
 apply Bool.eq_false_iff.mpr
 intro accepted
 have present := of_decide_eq_true accepted
 have born := (every_new_ballot_is_born_after_the_actual_successor parent saved previous stages body present).1
 omega
namespace Material
variable (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
abbrev Data := Cursor bound.source.code × Feedback.State bound.source.code × List (StageTrace.Record (code := bound.source.code))
def step (before : Data bound) (input : LocalCommandSource.Input) : Data bound :=
 let stage := CachedCommandRun.stageAt bound before.1 before.2.1 input
 let row := CachedCommandRun.materialAt bound before.1 before.2.1 stage.1 stage.2
 (before.1.after stage.1 stage.2,row.after,before.2.2++[row])
def fold (inputs : List LocalCommandSource.Input) (before : Data bound) : Data bound :=
 inputs.foldl (step bound) before

def row (before : Data bound) (input : LocalCommandSource.Input) :=
 let stage := CachedCommandRun.stageAt bound before.1 before.2.1 input
 CachedCommandRun.materialAt bound before.1 before.2.1 stage.1 stage.2

def progresses (baseline : Nat) (record : StageTrace.Record (code := bound.source.code)) : Bool :=
 match record.call with
 | .external move => match Distributed.Recall.Information.Agency.externalChoice bound.source.code move with
   | some event => decide (event ∈ CompletionEnvelope.available baseline record.before)
   | none => false
 | _ => false

def interference (baseline : Nat) (record : StageTrace.Record (code := bound.source.code)) : Bool :=
 match record.call with
 | .external move => (Distributed.Recall.Information.Agency.externalChoice bound.source.code move).isSome && !(progresses bound baseline record)
 | _ => false

def choices (baseline : Nat) (before : Data bound) : List (Move bound.source.code) :=
 let fresh := CompletionEnvelope.available baseline before.2.1
 let spent := (before.2.2.filter (fun record => interference bound baseline record)).length
 let extra := if spent < bound.source.code.eventLimit then
  (InterferenceEnvelope.externalEvents (code := bound.source.code)).filter fun event => decide (event ∉ fresh) else []
 if (CachedCommandRun.ownerAt bound before.1 before.2.1).isSome then [none]
 else match fresh with | [] => none::extra.map some | head::tail => (head::tail).map some

private def priority (candidates : List LocalCommandSource.Input)
 (delivery working sending : LocalCommandSource.Input → Bool) : LocalCommandSource.Input :=
 ((candidates.find? delivery).orElse fun _ =>
  (candidates.find? working).orElse fun _ =>
   (candidates.find? sending).orElse fun _ => candidates.head?).getD .idle

private theorem priority_keeps_an_actual_menu_input (candidates : List LocalCommandSource.Input)
 (delivery working sending : LocalCommandSource.Input → Bool) :
 priority candidates delivery working sending ∈ candidates ∨ priority candidates delivery working sending = .idle := by
 unfold priority
 cases first : candidates.find? delivery with
 | some input => simp only [Option.orElse_some,Option.getD_some]; exact Or.inl (List.mem_of_find?_eq_some first)
 | none =>
  cases second : candidates.find? working with
  | some input => simp only [Option.orElse_none,Option.orElse_some,Option.getD_some]; exact Or.inl (List.mem_of_find?_eq_some second)
  | none =>
   cases third : candidates.find? sending with
   | some input => simp only [Option.orElse_none,Option.orElse_some,Option.getD_some]; exact Or.inl (List.mem_of_find?_eq_some third)
   | none =>
    cases candidates with
    | nil => simp only [List.head?_nil,Option.orElse_none,Option.getD_none,or_true]
    | cons input rest => simp only [List.head?_cons,Option.orElse_none,Option.getD_some,List.mem_cons,true_or]

def choose (baseline : Nat)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) (before : Data bound) : LocalCommandSource.Input :=
 let seen := fun receiver => ((CachedWorkDispatch.run vocab law before.2.2 receiver before.2.2.length).receipts.map
  fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))
 let within := fun input =>
  let stage := CachedCommandRun.stageAt bound before.1 before.2.1 input
  let raw := if (CachedCommandRun.ownerAt bound before.1 before.2.1).isSome then none
    else stage.2 before.2.1.history before.2.1.past before.2.1.frame
  decide (Distributed.Recall.Information.Agency.externalChoice bound.source.code raw ∈ choices bound baseline before)
 let candidates := (CommandWindowSource.menu bound).filter within
 let delivery := fun input => if HeaderDispatch.isDelivery bound input then
   (CachedWorkDispatch.wires vocab before.2.2).any fun wire => decide
    (CachedWorkDispatch.check vocab law before.2.2 wire.recipient (row bound before input) (seen wire.recipient) wire = .accepted wire)
  else false
 let expected := work.find? fun request => !(before.2.2.any fun record => (StageTrace.items record).any fun item =>
  decide (item.request = request ∧ bound.source.code.law.Valid item.before item.request))
 let working := fun input => match input with
  | .command index => if bound.source.code.actions[index]? = expected then
    match expected with
    | none => false
    | some request => decide ((row bound before input).submitted = [request] ∧
      ∀ item ∈ StageTrace.items (row bound before input), bound.source.code.law.Valid item.before item.request)
    else false
  | _ => false
 let sending := fun input => if HeaderDispatch.isSend bound input then
   match HeaderTransport.issue vocab before.2.2 (row bound before input) with
   | none => false
   | some wire => decide ((wire.ballot.cut,wire.ballot.position) ∉ seen wire.recipient)
  else false
 priority candidates delivery working sending

theorem every_selected_input_is_in_the_original_source_interface
 (baseline : Nat)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) (before : Data bound) :
 choose bound baseline vocab law work before ∈ CommandWindowSource.menu bound := by
 unfold choose
 dsimp only
 rcases priority_keeps_an_actual_menu_input _ _ _ _ with member | idle
 · exact (List.mem_filter.mp member).1
 · rw [idle]
   exact List.mem_cons_self

def generate (baseline : Nat)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) :
 Nat → Data bound → Data bound × List LocalCommandSource.Input :=
 Nat.rec (fun before => (before,[])) fun _ recurse before =>
   let input := choose bound baseline vocab law work before
   let after := recurse (step bound before input)
   (after.1,input::after.2)

theorem generated_command_count
 (baseline : Nat)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) (count : Nat) (before : Data bound) :
 (generate bound baseline vocab law work count before).2.length=count := by
 induction count generalizing before with
 | zero => rfl
 | succ count ih =>
   change (generate bound baseline vocab law work count
    (step bound before (choose bound baseline vocab law work before))).2.length+1=count+1
   exact congrArg (fun size => size+1) (ih _)

theorem every_generated_input_has_an_actual_registered_interface_origin
 (baseline : Nat)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) (count : Nat)
 (before : Data bound) (input : LocalCommandSource.Input)
 (inside : input ∈ (generate bound baseline vocab law work count before).2) :
 input ∈ CommandWindowSource.menu bound := by
 induction count generalizing before with
 | zero => cases inside
 | succ count ih =>
  change input ∈ choose bound baseline vocab law work before :: _ at inside
  rcases List.mem_cons.mp inside with same | later
  · rw [same]
    exact every_selected_input_is_in_the_original_source_interface bound baseline vocab law work before
  · exact ih _ later

theorem generated_material_is_exactly_its_emitted_command_execution
 (baseline : Nat)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument))
 (count : Nat) (before : Data bound) :
 (generate bound baseline vocab law work count before).1 =
 fold bound (generate bound baseline vocab law work count before).2 before := by
 induction count generalizing before with
 | zero => rfl
 | succ count ih =>
   exact ih (step bound before (choose bound baseline vocab law work before))

theorem fold_is_the_same_cached_execution
 (origin : Cursor bound.source.code) (inputs : List LocalCommandSource.Input)
 {state : LocalCommandRun.State bound origin} (cache : CachedCommandRun.Cache bound origin state) :
 fold bound inputs (cache.cursor,cache.before,cache.rows) =
 ( (CachedCommandRun.run.fold bound origin inputs cache).cursor,
   (CachedCommandRun.run.fold bound origin inputs cache).before,
   (CachedCommandRun.run.fold bound origin inputs cache).rows ) := by
 induction inputs generalizing state with
 | nil => rfl
 | cons input tail ih =>
   exact ih (CachedCommandRun.step bound origin cache input)

theorem rows_are_the_actual_source_records
 (origin : Cursor bound.source.code) (before : Feedback.State bound.source.code)
 (correct : before = EventStep.seed origin) (inputs : List LocalCommandSource.Input) :
 (fold bound inputs (origin,before,[])).2.2 =
 StageTrace.records origin (LocalCommandRun.run bound origin inputs).stages := by
 let cache : CachedCommandRun.Cache bound origin (LocalCommandRun.initial bound origin) :=
  ⟨origin,before,[],rfl,correct,rfl⟩
 exact (congrArg (fun data : Data bound => data.2.2)
  (fold_is_the_same_cached_execution bound origin inputs cache)).trans
   (CachedCommandRun.run.fold bound origin inputs cache).rows_eq
theorem generated_rows_are_the_actual_source_records
 (origin : Cursor bound.source.code) (before : Feedback.State bound.source.code)
 (correct : before = EventStep.seed origin) (baseline : Nat)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) (count : Nat) :
 (generate bound baseline vocab law work count (origin,before,[])).1.2.2 =
 StageTrace.records origin (LocalCommandRun.run bound origin
  (generate bound baseline vocab law work count (origin,before,[])).2).stages := by
 rw [generated_material_is_exactly_its_emitted_command_execution]
 exact rows_are_the_actual_source_records bound origin before correct _

theorem generated_cursor_is_the_actual_source_endpoint
 (origin : Cursor bound.source.code) (before : Feedback.State bound.source.code)
 (correct : before = EventStep.seed origin) (baseline : Nat)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) (count : Nat) :
 (generate bound baseline vocab law work count (origin,before,[])).1.1 =
 (LocalCommandRun.run bound origin (generate bound baseline vocab law work count (origin,before,[])).2).current bound origin := by
 let cache : CachedCommandRun.Cache bound origin (LocalCommandRun.initial bound origin) :=
  ⟨origin,before,[],rfl,correct,rfl⟩
 rw [generated_material_is_exactly_its_emitted_command_execution]
 exact (congrArg (fun data : Data bound => data.1)
  (fold_is_the_same_cached_execution bound origin _ cache)).trans
   (CachedCommandRun.run.fold bound origin _ cache).cursor_eq

theorem generated_seed_is_the_same_actual_seed
 (origin : Cursor bound.source.code) (before : Feedback.State bound.source.code)
 (correct : before = EventStep.seed origin) (baseline : Nat)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) (count : Nat) :
 (generate bound baseline vocab law work count (origin,before,[])).1.2.1 =
 EventStep.seed (generate bound baseline vocab law work count (origin,before,[])).1.1 := by
 let cache : CachedCommandRun.Cache bound origin (LocalCommandRun.initial bound origin) :=
  ⟨origin,before,[],rfl,correct,rfl⟩
 rw [generated_material_is_exactly_its_emitted_command_execution]
 rw [fold_is_the_same_cached_execution bound origin _ cache]
 exact (CachedCommandRun.run.fold bound origin _ cache).before_eq

theorem generated_remaining_is_the_same_actual_budget
 (origin : Cursor bound.source.code) (before : Feedback.State bound.source.code)
 (correct : before = EventStep.seed origin) (baseline : Nat)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) (count : Nat) :
 (generate bound baseline vocab law work count (origin,before,[])).1.2.1.remaining =
 (EventStep.seed (generate bound baseline vocab law work count (origin,before,[])).1.1).remaining :=
 congrArg (fun state : Feedback.State bound.source.code => state.remaining)
  (generated_seed_is_the_same_actual_seed bound origin before correct baseline vocab law work count)

end Material
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SuccessorSigningSource
