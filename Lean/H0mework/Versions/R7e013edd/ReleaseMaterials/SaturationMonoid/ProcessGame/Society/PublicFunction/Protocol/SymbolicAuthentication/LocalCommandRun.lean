import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalCommandSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalCommandRun
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program
open LocalCommandSource

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

structure State where
  private mk ::
  entries : List (LocalCommandSource.Entry model)
  stages : List (EventHistory.Stage (code := model.source.code))
  stage_exact : entries.map (LocalCommandSource.Entry.stage model) = stages
  row_exact : entries.map (LocalCommandSource.Entry.row model) = StageTrace.records start stages

abbrev State.inputs (state : LocalCommandRun.State model start) := state.entries.map LocalCommandSource.Entry.input
abbrev State.current (state : LocalCommandRun.State model start) := EventHistory.execute start state.stages

def initial : LocalCommandRun.State model start := ⟨[],[],rfl,rfl⟩

def step (state : LocalCommandRun.State model start) (input : Input) : LocalCommandRun.State model start :=
  let entry := observe model (state.current model start) input
  ⟨state.entries ++ [entry],state.stages ++ [entry.stage model],by
    simp only [List.map_append,List.map_cons,List.map_nil,state.stage_exact],by
    rw [List.map_append,state.row_exact,OriginQueue.records_append]
    rfl⟩

def run (inputs : List Input) : LocalCommandRun.State model start := inputs.foldl (step model start) (initial model start)

theorem every_step_retains_the_literal_attempt_and_its_actual_stage
    (state : LocalCommandRun.State model start) (input : Input) :
    (step model start state input).inputs = state.inputs ++ [input] ∧
      (step model start state input).stages = state.stages ++
        [(observe model (state.current model start) input).stage model] := by
  exact ⟨by simp [State.inputs,step,observe],rfl⟩

theorem fold_keeps_all_inputs (inputs : List Input) (state : LocalCommandRun.State model start) :
    (inputs.foldl (step model start) state).inputs = state.inputs ++ inputs := by
  induction inputs generalizing state with
  | nil => simp
  | cons input tail ih =>
    rw [List.foldl_cons,ih,(every_step_retains_the_literal_attempt_and_its_actual_stage model start state input).1]
    simp only [List.append_assoc,List.singleton_append]

theorem the_source_keeps_every_input_in_order (inputs : List Input) :
    (run model start inputs).inputs = inputs := by
  simpa only [run,initial,State.inputs,List.map_nil,List.nil_append] using
    fold_keeps_all_inputs model start inputs (initial model start)

theorem each_attempt_row_is_an_original_execution_record
    (state : LocalCommandRun.State model start) (entry : LocalCommandSource.Entry model) (inside : entry ∈ state.entries) :
    entry.row model ∈ StageTrace.records start state.stages := by
  rw [← state.row_exact]
  exact List.mem_map.mpr ⟨entry,inside,rfl⟩

theorem actual_extension_preserves_all_attempts_and_stages
    (inputs : List Input) (state : LocalCommandRun.State model start) :
    state.entries <+: (inputs.foldl (step model start) state).entries ∧
      state.stages <+: (inputs.foldl (step model start) state).stages := by
  induction inputs generalizing state with
  | nil => exact ⟨List.prefix_refl _,List.prefix_refl _⟩
  | cons input tail ih =>
    have later := ih (step model start state input)
    exact ⟨(List.prefix_append _ _).trans later.1,(List.prefix_append _ _).trans later.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalCommandRun
