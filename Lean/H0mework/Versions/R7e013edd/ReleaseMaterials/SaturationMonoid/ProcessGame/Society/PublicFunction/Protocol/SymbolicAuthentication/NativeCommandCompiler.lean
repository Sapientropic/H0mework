import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveDynamicCommandDomain

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeCommandCompiler
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (state : LocalCommandRun.State model start)
  (ready : NativeReview.Ready model start state.stages)

def index := model.source.code.actions.idxOf (NativeReview.action model start state.stages ready.receiver)
def input : LocalCommandSource.Input := .command (index model start state ready)
abbrev after := LocalCommandRun.step model start state (input model start state ready)
abbrev full := NativeReviewHistory.full model start state.stages ready (EventStep.fixed none)

theorem source_lookup : LocalCommandSource.request model (index model start state ready) =
    some (NativeReview.action model start state.stages ready.receiver) := by
  exact List.getElem?_idxOf ready.supported

theorem input_is_in_the_original_source_menu : input model start state ready ∈ CommandWindowSource.menu model :=
  CommandWindowSource.the_source_menu_contains_every_original_command model _ (List.idxOf_lt_length_of_mem ready.supported)

theorem the_compiled_stage_is_the_original_native_action :
    (LocalCommandSource.observe model (state.current model start) (input model start state ready)).stage model =
      (NativeReview.protocol model start state.stages ready,EventStep.fixed none) := by
  have live := Nat.ne_of_gt ready.fuel
  have owner : LocalCommandSource.owner model (state.current model start) = some ready.receiver := ready.owner
  change ((LocalCommandSource.select model (state.current model start) (.command (index model start state ready))).protocol model,
    (LocalCommandSource.select model (state.current model start) (.command (index model start state ready))).rival model) = _
  unfold LocalCommandSource.select
  dsimp only
  rw [dif_neg live]
  split
  next notOwned => rw [owner] at notOwned; contradiction
  next worker owned =>
    have same := Option.some.inj (owned.symm.trans ready.owner)
    subst worker
    split
    next absent => rw [source_lookup model start state ready] at absent; contradiction
    next value found =>
      have same := Option.some.inj (found.symm.trans (source_lookup model start state ready))
      subst value
      have signed : (NativeReview.action model start state.stages ready.receiver).signer = model.source.code.siteParty ready.receiver := rfl
      rw [dif_pos signed,dif_pos ready.capacity,dif_pos ready.memory,dif_pos ready.activation]
      rfl

theorem the_compiled_command_keeps_the_literal_native_history : (after model start state ready).stages = full model start state ready := by
  change state.stages ++ [_] = state.stages ++ [_]
  rw [the_compiled_stage_is_the_original_native_action model start state ready]

theorem the_compiled_command_submits_the_original_withdrawal :
    ((LocalCommandSource.observe model (state.current model start) (input model start state ready)).row model).submitted =
      [NativeReview.action model start state.stages ready.receiver] := by
  change (StageTrace.material (state.current model start)
    ((LocalCommandSource.observe model (state.current model start) (input model start state ready)).stage model).1
    ((LocalCommandSource.observe model (state.current model start) (input model start state ready)).stage model).2).submitted = _
  rw [the_compiled_stage_is_the_original_native_action model start state ready]
  exact (NativeReview.the_actual_owner_submits_the_original_member_request model start state.stages ready (EventStep.fixed none)).2

theorem the_native_command_is_within_every_source_communication_allowance (delay : Nat) :
    DynamicCommandSource.within model start delay state (input model start state ready) = true := by
  have actualOwner : LocalCommandSource.owner model (state.current model start) = some ready.receiver := ready.owner
  have owner : (LocalCommandSource.owner model (state.current model start)).isSome = true := by rw [actualOwner]; rfl
  unfold DynamicCommandSource.within
  apply decide_eq_true
  change InterferenceEnvelope.intake (state.current model start)
    ((LocalCommandSource.observe model (state.current model start) (input model start state ready)).stage model).2 ∈ _
  rw [the_compiled_stage_is_the_original_native_action model start state ready]
  simp [InterferenceEnvelope.choices,owner,CompletionEnvelope.intake,CompletionEnvelope.raw,
    Distributed.Recall.Information.Agency.externalChoice]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeCommandCompiler
