import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredWindowConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceContinuationTrace
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))

structure Trace where
 cursor : Cursor model.source.code
 before : Feedback.State model.source.code
 rows : List (StageTrace.Record (code := model.source.code))
 inputs : List LocalCommandSource.Input
 stages : List (EventHistory.Stage (code := model.source.code))

def initial (origin : Cursor model.source.code) (retained : Feedback.State model.source.code) : Trace model :=
 ⟨origin,retained,[],[],[]⟩

def step (trace : Trace model) (input : LocalCommandSource.Input) : Trace model :=
 let stage := CachedCommandRun.stageAt model trace.cursor trace.before input
 let row := CachedCommandRun.materialAt model trace.cursor trace.before stage.1 stage.2
 ⟨trace.cursor.after stage.1 stage.2,row.after,trace.rows++[row],trace.inputs++[input],trace.stages++[stage]⟩

def fixed (origin : Cursor model.source.code) (retained : Feedback.State model.source.code)
 (inputs : List LocalCommandSource.Input) : Trace model := inputs.foldl (step model) (initial model origin retained)

variable (origin : Cursor model.source.code) (baseline : Nat)
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law model.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument))

def choose (trace : Trace model) :=
 SuccessorSigningSource.Material.choose model baseline (SuccessorSigningSource.vocabulary model origin base)
  ⟨fun receiver current => {law.scope receiver current with phase := origin.cut},law.maxDelay⟩ work
  (trace.cursor,trace.before,trace.rows)

def dynamic (retained : Feedback.State model.source.code) : Nat → Trace model :=
 Nat.rec (initial model origin retained) fun _ trace =>
  step model trace (choose model origin baseline base law work trace)

def Sound (trace : Trace model) (state : LocalCommandRun.State model origin) : Prop :=
 trace.cursor=state.current model origin ∧ trace.before=EventStep.seed trace.cursor ∧
 trace.rows=StageTrace.records origin state.stages ∧ trace.inputs=state.inputs ∧ trace.stages=state.stages

theorem step_is_the_same_actual_source_step (trace : Trace model) (state : LocalCommandRun.State model origin)
 (sound : Sound model origin trace state) (input : LocalCommandSource.Input) :
 Sound model origin (step model trace input) (LocalCommandRun.step model origin state input) := by
 let cache : CachedCommandRun.Cache model origin state :=
  ⟨trace.cursor,trace.before,trace.rows,sound.1,sound.2.1,sound.2.2.1⟩
 let next := CachedCommandRun.step model origin cache input
 refine ⟨next.cursor_eq,next.before_eq,next.rows_eq,?_,?_⟩
 · change trace.inputs++[input]=(LocalCommandRun.step model origin state input).inputs
   rw [sound.2.2.2.1]
   exact (LocalCommandRun.every_step_retains_the_literal_attempt_and_its_actual_stage model origin state input).1.symm
 · change trace.stages++[CachedCommandRun.stageAt model trace.cursor trace.before input]=_
   rw [sound.2.2.2.2]
   rw [(LocalCommandRun.every_step_retains_the_literal_attempt_and_its_actual_stage model origin state input).2]
   exact congrArg (fun stage => state.stages++[stage]) (cache.stage_eq input)

theorem every_fixed_prefix_is_the_same_actual_execution
 (retained : Feedback.State model.source.code) (same : retained=EventStep.seed origin)
 (inputs : List LocalCommandSource.Input) :
 Sound model origin (fixed model origin retained inputs) (LocalCommandRun.run model origin inputs) := by
 have foldSound (rest : List LocalCommandSource.Input) (trace : Trace model)
  (state : LocalCommandRun.State model origin) (sound : Sound model origin trace state) :
  Sound model origin (rest.foldl (step model) trace) (rest.foldl (LocalCommandRun.step model origin) state) := by
  induction rest generalizing trace state with
  | nil => exact sound
  | cons input tail ih => exact ih _ _ (step_is_the_same_actual_source_step model origin trace state sound input)
 exact foldSound inputs _ _ ⟨rfl,same,rfl,rfl,rfl⟩

theorem every_dynamic_prefix_is_the_original_normal_policy_execution
 (retained : Feedback.State model.source.code) (same : retained=EventStep.seed origin) (count : Nat) :
 Sound model origin (dynamic model origin baseline base law work retained count)
  (SourceDynamicCache.actual model origin baseline base law work count) := by
 induction count with
 | zero => exact ⟨rfl,same,rfl,rfl,rfl⟩
 | succ count ih =>
  let prior := dynamic model origin baseline base law work retained count
  let cache : CachedCommandRun.Cache model origin (SourceDynamicCache.actual model origin baseline base law work count) :=
   ⟨prior.cursor,prior.before,prior.rows,ih.1,ih.2.1,ih.2.2.1⟩
  have chosen : choose model origin baseline base law work prior=
   SourceDynamicCache.policy model baseline base law work origin (SourceDynamicCache.actual model origin baseline base law work count) :=
   SourceDynamicCache.input_is_the_actual_source_choice model origin baseline base law work cache
  have next := step_is_the_same_actual_source_step model origin prior _ ih (choose model origin baseline base law work prior)
  have actual : LocalCommandRun.step model origin (SourceDynamicCache.actual model origin baseline base law work count)
    (choose model origin baseline base law work prior)=SourceDynamicCache.actual model origin baseline base law work (count+1) := by
   rw [chosen]
   rfl
  rw [actual] at next
  exact next

theorem fixed_execution_keeps_the_entire_actual_model_and_cursor
 (state : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (retained : Feedback.State model.source.code)
 (physical : FreshSigningReplay.physical state=⟨model,origin⟩)
 (same : retained=EventStep.seed origin) (inputs : List LocalCommandSource.Input) :
 FreshSigningReplay.physical (RenewableArchiveSource.execute state inputs)=
 ⟨model,(fixed model origin retained inputs).cursor⟩ := by
 have own (state : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (retained : Feedback.State state.model.source.code)
  (same : retained=EventStep.seed state.point) :
  FreshSigningReplay.physical (RenewableArchiveSource.execute state inputs)=
   ⟨state.model,(fixed state.model state.point retained inputs).cursor⟩ := by
  have actual := (every_fixed_prefix_is_the_same_actual_execution state.model state.point retained same inputs).1
  exact congrArg (fun cursor => (⟨state.model,cursor⟩ : FreshSigningReplay.Physical
   (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) actual.symm
 cases state
 cases physical
 exact own _ retained same

theorem fixed_keeps_the_source_side (retained : Feedback.State model.source.code)
 (inputs : List LocalCommandSource.Input) :
 (fixed model origin retained inputs).cursor.side=origin.side := by
 have foldSide (rest : List LocalCommandSource.Input) (trace : Trace model) :
  (rest.foldl (step model) trace).cursor.side=trace.cursor.side := by
  induction rest generalizing trace with
  | nil => rfl
  | cons input tail ih => exact ih (step model trace input)
 exact foldSide inputs _

section Fresh
variable {root : RenewableCodeLineage.Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}
 (terms : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (laws : (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) → StageReception.Law model.source.code)
 (state : JointReceptionSource.State root)
 (retained : Feedback.State model.source.code)
 (physical : FreshSigningReplay.physical state.actual=⟨model,origin⟩)
 (same : retained=EventStep.seed origin)
 (request : FreshSigningSource.Request (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
include physical same

theorem fresh_next_keeps_the_entire_actual_model_and_cached_cursor (zero : request.depth=0) :
 FreshSigningReplay.physical (FreshSigningSource.next terms base laws state request).actual=
 ⟨model,(dynamic model origin retained.frame.sent.length base (laws model) request.work retained request.beats).cursor⟩ := by
 have own (state : JointReceptionSource.State root) (retained : Feedback.State state.actual.model.source.code)
  (same : retained=EventStep.seed state.actual.point) :
  FreshSigningReplay.physical (FreshSigningSource.next terms base laws state request).actual=
  ⟨state.actual.model,(dynamic state.actual.model state.actual.point retained.frame.sent.length
    base (laws state.actual.model) request.work retained request.beats).cursor⟩ := by
  subst retained
  have old := SourceDynamicCache.Fresh.zero_repair_keeps_the_entire_original_model_and_cached_cursor
   base laws state request terms zero
  have previous := (SourceDynamicCache.the_executable_stream_has_the_same_complete_source_execution
   state.actual.model state.actual.point (EventStep.seed state.actual.point).frame.sent.length
   base (laws state.actual.model) request.work request.beats).1
  have current := (every_dynamic_prefix_is_the_original_normal_policy_execution
   state.actual.model state.actual.point (EventStep.seed state.actual.point).frame.sent.length
   base (laws state.actual.model) request.work (EventStep.seed state.actual.point) rfl request.beats).1
  exact old.trans (congrArg (fun cursor => (⟨state.actual.model,cursor⟩ : FreshSigningReplay.Physical
   (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
   (previous.trans current.symm))
 cases state
 rename_i actual lineage rows
 cases actual
 cases physical
 exact own _ retained same

end Fresh

theorem every_generated_ballot_keeps_the_new_actual_phase
 (retained : Feedback.State model.source.code) (same : retained=EventStep.seed origin) (count : Nat)
 (ballot : StageBudget.Ballot (code := model.source.code))
 (issued : ballot∈StageBudget.ledger (SuccessorSigningSource.vocabulary model origin base) origin
  (dynamic model origin baseline base law work retained count).stages) :
 origin.cut≤ballot.cut ∧ ballot.scope.phase=origin.cut := by
 let segment := RecursiveSigningSource.segment model origin (RecursiveSigningSource.initial model origin)
  (SourceDynamicCache.actual model origin baseline base law work count).inputs
 have stages := (every_dynamic_prefix_is_the_original_normal_policy_execution
  model origin baseline base law work retained same count).2.2.2.2
 rw [stages] at issued
 have replays : segment.stages=(SourceDynamicCache.actual model origin baseline base law work count).stages :=
  congrArg (fun state => state.stages) (RecursiveSigningSource.dynamic_inputs_replay_the_same_actual_execution
   model origin (SourceDynamicCache.policy model baseline base law work) count)
 rw [← replays] at issued
 exact RecursiveSigningSource.each_new_ballot_is_born_in_its_own_actual_phase model base segment ballot issued

theorem taking_records_is_the_same_actual_source_prefix
 (stages : List (EventHistory.Stage (code := model.source.code))) (count : Nat) :
 (StageTrace.records origin stages).take count=StageTrace.records origin (stages.take count) := by
 induction stages generalizing origin count with
 | nil => simp [StageTrace.records]
 | cons stage tail ih =>
  cases count with
  | zero => rfl
  | succ count =>
   rcases stage with ⟨protocol,rival⟩
   simp only [StageTrace.records,List.take_succ_cons,ih]

theorem receiver_from_the_same_complete_actual_trace
 (trace : Trace model) (state : LocalCommandRun.State model origin)
 (sound : Sound model origin trace state)
 (vocab : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (law : StageReception.Law model.source.code)
 (recipient : Fin model.source.code.sites) :
 CachedWorkDispatch.run vocab law trace.rows recipient trace.rows.length=
 HeaderReception.run vocab law origin trace.stages recipient trace.stages.length := by
 have rows := sound.2.2.1.trans (congrArg (StageTrace.records origin) sound.2.2.2.2.symm)
 rw [rows,StageTrace.record_count]
 exact CachedWorkDispatch.run_eq _ _ _ _ _ _

theorem current_from_the_same_complete_occurrence
 (state : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (retained : Feedback.State model.source.code)
 (physical : FreshSigningReplay.physical state=⟨model,origin⟩)
 (same : retained=EventStep.seed origin) : (EventStep.seed state.point).current=retained.current := by
 have face := congrArg (fun endpoint : FreshSigningReplay.Physical
  (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) =>
   (EventStep.seed endpoint.2).current) physical
 exact face.trans (congrArg (fun before : Feedback.State model.source.code => before.current) same).symm

theorem earlier_signatures_are_not_in_the_new_actual_issuing_context
 (retained : Feedback.State model.source.code) (same : retained=EventStep.seed origin) (count : Nat)
 (wire : HeaderTransport.Wire (code := model.source.code)) (earlier : wire.ballot.cut<origin.cut) :
 HeaderTransport.verify (SuccessorSigningSource.vocabulary model origin base) origin
  (dynamic model origin baseline base law work retained count).stages wire=false := by
 apply Bool.eq_false_iff.mpr
 intro verified
 obtain ⟨_,_,_,_,_,_,_,signature,_⟩ := HeaderTransport.authenticated_wire_has_actual_send_and_paid_ballot
  (SuccessorSigningSource.vocabulary model origin base) origin _ wire verified
 have fresh := every_generated_ballot_keeps_the_new_actual_phase
  model origin baseline base law work retained same count wire.ballot signature
 omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceContinuationTrace
