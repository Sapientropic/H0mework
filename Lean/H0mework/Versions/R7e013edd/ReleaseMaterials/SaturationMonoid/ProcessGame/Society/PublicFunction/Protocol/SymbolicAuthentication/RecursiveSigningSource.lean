import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SuccessorSigningSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecursiveSigningSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

structure Segment where
 private mk ::
 origin : Cursor bound.source.code
 actual : LocalCommandRun.State bound origin

abbrev Segment.stages (segment : Segment bound) := segment.actual.stages
abbrev Segment.rows (segment : Segment bound) := StageTrace.records segment.origin segment.stages
abbrev Segment.final (segment : Segment bound) := segment.actual.current bound segment.origin
abbrev Segment.vocabulary (segment : Segment bound)
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) :=
 SuccessorSigningSource.vocabulary bound segment.origin base
abbrev Segment.wires (segment : Segment bound) (base : OwnedAttestation.Vocabulary (Party := Party)
 (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :=
 HeaderTransport.wires (segment.vocabulary bound base) segment.origin segment.stages

def Segment.law (segment : Segment bound) (base : StageReception.Law bound.source.code) :
 StageReception.Law bound.source.code :=
 ⟨fun receiver current => {base.scope receiver current with phase := segment.origin.cut},base.maxDelay⟩

variable (genesis : Cursor bound.source.code)

structure State where
 private mk ::
 stages : List (EventHistory.Stage (code := bound.source.code))
 archive : List (Segment bound)
 coverage : archive.flatMap (Segment.stages bound) = stages
 origins : ∀ segment ∈ archive, ∃ before after,
   stages = before ++ segment.stages ++ after ∧ segment.origin = EventHistory.execute genesis before

abbrev State.current (state : State bound genesis) := EventHistory.execute genesis state.stages
abbrev State.rows (state : State bound genesis) := StageTrace.records genesis state.stages

def initial : State bound genesis := ⟨[],[],rfl,by simp⟩

-- A controller supplies raw source inputs. Ownership, signatures, resources and
-- external admission are still decided by LocalCommandSource on each actual beat.
def segment (state : State bound genesis) (inputs : List LocalCommandSource.Input) : Segment bound :=
 ⟨state.current bound genesis,LocalCommandRun.run bound (state.current bound genesis) inputs⟩

def next (state : State bound genesis) (inputs : List LocalCommandSource.Input) : State bound genesis :=
 let fresh := segment bound genesis state inputs
 ⟨state.stages ++ fresh.stages,state.archive ++ [fresh],by
   simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,state.coverage],by
   intro prior member
   rcases List.mem_append.mp member with old | new
   · obtain ⟨before,after,shape,origin⟩ := state.origins prior old
     exact ⟨before,after ++ fresh.stages,by rw [shape,List.append_assoc,List.append_assoc],origin⟩
   · cases List.mem_singleton.mp new
     exact ⟨state.stages,[],by simp only [List.append_nil],rfl⟩⟩

abbrev Controller := (state : State bound genesis) → List LocalCommandSource.Input
def run (state : State bound genesis) (controller : Controller bound genesis) : Nat → State bound genesis :=
 Nat.rec state fun _ current => next bound genesis current (controller current)

abbrev Policy := (origin : Cursor bound.source.code) → LocalCommandRun.State bound origin → LocalCommandSource.Input

def dynamic (origin : Cursor bound.source.code) (policy : Policy bound) : Nat → LocalCommandRun.State bound origin :=
 Nat.rec (LocalCommandRun.initial bound origin) fun _ actual =>
  LocalCommandRun.step bound origin actual (policy origin actual)

theorem dynamic_inputs_replay_the_same_actual_execution
 (origin : Cursor bound.source.code) (policy : Policy bound) (count : Nat) :
 LocalCommandRun.run bound origin (dynamic bound origin policy count).inputs = dynamic bound origin policy count := by
 induction count with
 | zero => rfl
 | succ count ih =>
   change LocalCommandRun.run bound origin
    (LocalCommandRun.step bound origin (dynamic bound origin policy count)
     (policy origin (dynamic bound origin policy count))).inputs = _
   rw [(LocalCommandRun.every_step_retains_the_literal_attempt_and_its_actual_stage _ _ _ _).1]
   simp only [LocalCommandRun.run,List.foldl_append,List.foldl_cons,List.foldl_nil] at ih ⊢
   rw [ih]
   rfl

theorem dynamic_control_retains_exactly_its_requested_attempts
 (origin : Cursor bound.source.code) (policy : Policy bound) (count : Nat) :
 (dynamic bound origin policy count).inputs.length=count := by
 induction count with
 | zero => rfl
 | succ count ih =>
   change (LocalCommandRun.step bound origin (dynamic bound origin policy count)
    (policy origin (dynamic bound origin policy count))).inputs.length = count+1
   rw [(LocalCommandRun.every_step_retains_the_literal_attempt_and_its_actual_stage _ _ _ _).1]
   simp only [List.length_append,List.length_singleton,ih]

def runDynamic (state : State bound genesis)
 (control : State bound genesis → Nat × Policy bound) : Nat → State bound genesis :=
 run bound genesis state fun current =>
  (dynamic bound (current.current bound genesis) (control current).2 (control current).1).inputs

def normalPolicy (baseline : Nat)
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) : Policy bound :=
 fun origin actual => SuccessorSigningSource.Material.choose bound baseline
  (SuccessorSigningSource.vocabulary bound origin base)
  ⟨fun receiver current => {law.scope receiver current with phase := origin.cut},law.maxDelay⟩ work
  (actual.current bound origin,EventStep.seed (actual.current bound origin),StageTrace.records origin actual.stages)

theorem normal_policy_uses_the_original_registered_interface
 (baseline : Nat)
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument))
 (origin : Cursor bound.source.code) (actual : LocalCommandRun.State bound origin) :
 normalPolicy bound baseline base law work origin actual ∈ CommandWindowSource.menu bound :=
 SuccessorSigningSource.Material.every_selected_input_is_in_the_original_source_interface _ _ _ _ _ _

theorem every_round_starts_at_its_actual_predecessor
 (state : State bound genesis) (inputs : List LocalCommandSource.Input) :
 (segment bound genesis state inputs).origin = state.current bound genesis ∧
 (next bound genesis state inputs).current bound genesis = (segment bound genesis state inputs).final bound := by
 refine ⟨rfl,?_⟩
 change EventHistory.execute genesis (state.stages ++ _) = _
 exact StageQueue.execute_append genesis state.stages _

theorem first_round_is_the_same_native_execution (inputs : List LocalCommandSource.Input) :
 (next bound genesis (initial bound genesis) inputs).current bound genesis =
  (LocalCommandRun.run bound genesis inputs).current bound genesis ∧
 (next bound genesis (initial bound genesis) inputs).stages = (LocalCommandRun.run bound genesis inputs).stages ∧
 (next bound genesis (initial bound genesis) inputs).archive = [segment bound genesis (initial bound genesis) inputs] :=
 ⟨rfl,rfl,rfl⟩

theorem every_round_keeps_the_entire_actual_prefix
 (state : State bound genesis) (inputs : List LocalCommandSource.Input) :
 state.stages <+: (next bound genesis state inputs).stages ∧
 state.archive <+: (next bound genesis state inputs).archive :=
 ⟨List.prefix_append _ _,List.prefix_append _ _⟩

theorem arbitrary_later_control_keeps_all_prior_issuing_contexts
 (state : State bound genesis) (controller : Controller bound genesis) (count : Nat) :
 state.stages <+: (run bound genesis state controller count).stages ∧
 state.archive <+: (run bound genesis state controller count).archive := by
 induction count with
 | zero => exact ⟨List.prefix_refl _,List.prefix_refl _⟩
 | succ count ih =>
   have step := every_round_keeps_the_entire_actual_prefix bound genesis
    (run bound genesis state controller count) (controller (run bound genesis state controller count))
   exact ⟨ih.1.trans step.1,ih.2.trans step.2⟩

theorem an_archived_row_is_in_the_actual_cumulative_history
 (state : State bound genesis) (origin : Segment bound) (member : origin ∈ state.archive)
 (row : StageTrace.Record (code := bound.source.code)) (inside : row ∈ origin.rows bound) :
 row ∈ state.rows bound genesis := by
 obtain ⟨before,after,shape,whereFrom⟩ := state.origins origin member
 change row ∈ StageTrace.records genesis state.stages
 rw [shape,StageQueue.records_append,StageQueue.records_append]
 apply List.mem_append_left
 apply List.mem_append_right
 rw [← whereFrom]
 exact inside

theorem each_new_ballot_is_born_in_its_own_actual_phase
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (origin : Segment bound) (body : StageBudget.Ballot (code := bound.source.code))
 (member : body ∈ StageBudget.ledger (origin.vocabulary bound base) origin.origin origin.stages) :
 origin.origin.cut ≤ body.cut ∧ body.scope.phase = origin.origin.cut := by
 obtain ⟨row,inside,position,made⟩ := StageBudget.ledger_origin _ _ _ body member
 obtain ⟨site,item,_,_,_,_,decoded,_,_,cut,_⟩ := StageBudget.issued_has_an_owned_valid_paid_origin _ row position body made
 have clock : row.cursor.cut ∈ (origin.rows bound).map (fun record => record.cursor.cut) :=
  List.mem_map.mpr ⟨row,inside,rfl⟩
 rw [StageTrace.no_occurrence_is_lost_or_duplicated] at clock
 obtain ⟨index,_,same⟩ := List.mem_map.mp clock
 have phase : body.scope.phase = origin.origin.cut := by
  change (base.decode item.request.purpose).map (fun label => ({label.1 with phase := origin.origin.cut},label.2)) = some (body.scope,body.choice) at decoded
  cases found : base.decode item.request.purpose with
  | none => simp only [found,Option.map_none] at decoded; contradiction
  | some label =>
    simp only [found,Option.map_some,Option.some.injEq,Prod.mk.injEq] at decoded
    exact congrArg Scope.phase decoded.1.symm
 refine ⟨?_,phase⟩
 change origin.origin.cut+index = row.cursor.cut at same
 omega

private theorem earlier_body
 (cursor : Cursor bound.source.code) (stages : List (EventHistory.Stage (code := bound.source.code)))
 (location : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
 (early : location.round-bound.source.code.initial.round-1 < cursor.history.length+1+cursor.cut) :
 (EventHistory.execute cursor stages).source.body location = cursor.source.body location := by
 induction stages generalizing cursor with
 | nil => rfl
 | cons stage tail ih =>
   have nextEarly : location.round-bound.source.code.initial.round-1 <
    (cursor.after stage.1 stage.2).history.length+1+(cursor.after stage.1 stage.2).cut := by
     change location.round-bound.source.code.initial.round-1 < cursor.history.length+1+(cursor.cut+1)
     omega
   exact (ih (cursor.after stage.1 stage.2) nextEarly).trans
    (Future.earlier_body cursor.source cursor.entry cursor.cut (Cursor.controller cursor stage.1 stage.2)
     (term cursor.source cursor.entry cursor.cut stage.1).val rfl location early)

theorem every_archived_origin_keeps_the_complete_financial_prefix
 (state : State bound genesis) (ordinal : Nat) (bounded : ordinal ≤ EventStep.boundary genesis) :
 Native.Coupling.Match bound.source.code genesis.source.input (state.current bound genesis).source.input
  (Financial.accountAt genesis.source.input ordinal)
  (Financial.accountAt (state.current bound genesis).source.input ordinal) := by
 have words : ∀ n, n < EventStep.boundary genesis →
  ProgrammeSource.rawEvent (state.current bound genesis).source.input
   (ProgrammeHistory.visitAt genesis.source.input n).current =
  ProgrammeSource.rawEvent genesis.source.input (ProgrammeHistory.visitAt genesis.source.input n).current := by
   intro n small
   cases view : (ProgrammeHistory.visitAt genesis.source.input n).current with
   | bootstrap => rfl
   | running location past =>
     change (state.current bound genesis).source.body location = genesis.source.body location
     have rounds := ProgrammeHistory.visit_round genesis.source.input n
     rw [view] at rounds
     change location.round = bound.source.code.initial.round+n at rounds
     apply earlier_body bound genesis state.stages location
     change n < genesis.history.length+2+genesis.cut at small
     omega
 exact Native.Coupling.History.complete_accounts bound.source.code genesis.source.input
  (state.current bound genesis).source.input rfl rfl (EventStep.boundary genesis)
  words genesis.source.body (state.current bound genesis).source.body
  rfl rfl ordinal bounded

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecursiveSigningSource
