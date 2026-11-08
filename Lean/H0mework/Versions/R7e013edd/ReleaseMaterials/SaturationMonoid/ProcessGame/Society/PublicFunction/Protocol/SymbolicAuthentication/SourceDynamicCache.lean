import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceDynamicCache
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (origin : Cursor model.source.code) (baseline : Nat)
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law model.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument))

abbrev policy := RecursiveSigningSource.normalPolicy model baseline base law work
abbrev actual (count : Nat) := RecursiveSigningSource.dynamic model origin (policy model baseline base law work) count

def input {state : LocalCommandRun.State model origin} (cache : CachedCommandRun.Cache model origin state) :=
 SuccessorSigningSource.Material.choose model baseline
  (SuccessorSigningSource.vocabulary model origin base)
  ⟨fun receiver current => {law.scope receiver current with phase := origin.cut},law.maxDelay⟩ work
  (cache.cursor,cache.before,cache.rows)

theorem input_is_the_actual_source_choice {state : LocalCommandRun.State model origin}
 (cache : CachedCommandRun.Cache model origin state) :
 input model origin baseline base law work cache=policy model baseline base law work origin state := by
 simp only [input,policy,RecursiveSigningSource.normalPolicy,
  cache.before_eq,cache.cursor_eq,cache.rows_eq]
 rw [cache.cursor_eq]

-- Keep the executable fold free of the uncached State used only by its proof.
structure Stream where
 cursor : Cursor model.source.code
 before : Feedback.State model.source.code
 rows : List (StageTrace.Record (code := model.source.code))
 inputs : List LocalCommandSource.Input

def choose (state : Stream model) :=
 SuccessorSigningSource.Material.choose model baseline
  (SuccessorSigningSource.vocabulary model origin base)
  ⟨fun receiver current => {law.scope receiver current with phase := origin.cut},law.maxDelay⟩ work
  (state.cursor,state.before,state.rows)

def beat (state : Stream model) : Stream model :=
 let selected := choose model origin baseline base law work state
 let stage := CachedCommandRun.stageAt model state.cursor state.before selected
 let row := CachedCommandRun.materialAt model state.cursor state.before stage.1 stage.2
 ⟨state.cursor.after stage.1 stage.2,row.after,state.rows++[row],state.inputs++[selected]⟩

def stream : Nat → Stream model :=
 Nat.rec ⟨origin,EventStep.seed origin,[],[]⟩ fun _ state => beat model origin baseline base law work state

theorem the_executable_stream_has_the_same_complete_source_execution (count : Nat) :
 let output := stream model origin baseline base law work count
 output.cursor=(actual model origin baseline base law work count).current model origin ∧
 output.before=EventStep.seed output.cursor ∧
 output.rows=StageTrace.records origin (actual model origin baseline base law work count).stages ∧
 output.inputs=(actual model origin baseline base law work count).inputs := by
 induction count with
 | zero => exact ⟨rfl,rfl,rfl,rfl⟩
 | succ count ih =>
  let prior := stream model origin baseline base law work count
  let cache : CachedCommandRun.Cache model origin (actual model origin baseline base law work count) :=
   ⟨prior.cursor,prior.before,prior.rows,ih.1,ih.2.1,ih.2.2.1⟩
  let selected := choose model origin baseline base law work prior
  have same : selected=policy model baseline base law work origin (actual model origin baseline base law work count) :=
   input_is_the_actual_source_choice model origin baseline base law work cache
  let next := CachedCommandRun.step model origin cache selected
  refine ⟨?_,next.before_eq,?_,?_⟩
  · change next.cursor=(actual model origin baseline base law work (count+1)).current model origin
    calc
     _=(LocalCommandRun.step model origin (actual model origin baseline base law work count) selected).current model origin := next.cursor_eq
     _=_ := by rw [same];rfl
  · change next.rows=StageTrace.records origin (actual model origin baseline base law work (count+1)).stages
    calc
     _=StageTrace.records origin (LocalCommandRun.step model origin (actual model origin baseline base law work count) selected).stages := next.rows_eq
     _=_ := by rw [same];rfl
  · change prior.inputs++[selected]=(actual model origin baseline base law work (count+1)).inputs
    rw [ih.2.2.2,same]
    exact (LocalCommandRun.every_step_retains_the_literal_attempt_and_its_actual_stage _ _ _ _).1.symm

namespace Fresh
variable {root : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}
 (shared : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (laws : (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) → StageReception.Law model.source.code)
 {old : RenewableCodeLineage.Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}
 (before : JointReceptionSource.State old)
 (request : FreshSigningSource.Request (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))

abbrev generated := stream before.actual.model before.actual.point (EventStep.seed before.actual.point).frame.sent.length
 shared (laws before.actual.model) request.work request.beats

theorem generated_inputs_are_the_original_dynamic_inputs :
 (generated shared laws before request).inputs=FreshSigningSource.inputs shared laws before request :=
 (the_executable_stream_has_the_same_complete_source_execution _ _ _ _ _ _ _).2.2.2

variable (terms : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))

theorem zero_repair_generates_no_extra_commands (zero : request.depth=0) :
 (FreshSigningSource.result terms shared laws before request).commands=[] := by
 let context := FreshSigningSource.origin shared laws before request
 let vocab := context.vocabulary before.actual.model shared
 let law := context.law before.actual.model (laws before.actual.model)
 let start := FreshSigningReplay.localStart before (FreshSigningSource.inputs shared laws before request)
 have bounded := (SourceRepairRun.every_report_replays_only_its_selected_actual_source_commands terms
  vocab law context.origin context.stages (FreshSigningReplay.currentScope before request.scope) request.value request.depth
  (SourceRepairSearch.debt vocab law context.origin context.stages (FreshSigningReplay.currentScope before request.scope)
   request.value start+1) start).2.2
 change (FreshSigningSource.result terms shared laws before request).commands.length≤_ at bounded
 rw [zero,Nat.mul_zero] at bounded
 exact List.eq_nil_of_length_eq_zero (by omega)

theorem zero_repair_keeps_the_same_complete_global_occurrence (zero : request.depth=0) :
 FreshSigningSource.next terms shared laws before request=
 FreshSigningReplay.globalStart terms before (generated shared laws before request).inputs := by
 change SourceRepairSearch.execute terms
  (FreshSigningReplay.globalStart terms before (FreshSigningSource.inputs shared laws before request))
  (FreshSigningSource.result terms shared laws before request).commands=_
 rw [zero_repair_generates_no_extra_commands shared laws before request terms zero]
 rw [generated_inputs_are_the_original_dynamic_inputs shared laws before request]
 rfl

theorem zero_repair_keeps_the_entire_original_model_and_cached_cursor (zero : request.depth=0) :
 FreshSigningReplay.physical (FreshSigningSource.next terms shared laws before request).actual=
  ⟨before.actual.model,(generated shared laws before request).cursor⟩ := by
 rw [zero_repair_keeps_the_same_complete_global_occurrence shared laws before request terms zero]
 have inputs := generated_inputs_are_the_original_dynamic_inputs shared laws before request
 have actual := (FreshSigningSource.generated_inputs_are_exactly_the_actual_dynamic_execution shared laws before request).1
 have cached := (the_executable_stream_has_the_same_complete_source_execution before.actual.model before.actual.point
  (EventStep.seed before.actual.point).frame.sent.length shared (laws before.actual.model) request.work request.beats).1
 change (⟨before.actual.model,(LocalCommandRun.run before.actual.model before.actual.point
  (generated shared laws before request).inputs).current before.actual.model before.actual.point⟩ : Sigma fun model => Cursor model.source.code)=_
 rw [inputs,actual,cached]

end Fresh
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceDynamicCache
