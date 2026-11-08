import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeCommandCompiler

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeCommandService
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (state : LocalCommandRun.State model start)

abbrev Original (ready : NativeReview.Ready model start state.stages) :=
  Native.Authority.Challenge (NativeReviewHistory.native model start state.stages ready (EventStep.fixed none))
def originals (ready : NativeReview.Ready model start state.stages) : List (Original model start state ready) :=
  (NativeReview.inventory model start (NativeCommandCompiler.full model start state ready)).map Sigma.fst
abbrev before (ready : NativeReview.Ready model start state.stages) (original : Original model start state ready) :=
  Mandate.Challenge.through (NativeReviewHistory.family model start state.stages ready (EventStep.fixed none))
    (NativeReviewHistory.sourceIndex model start state.stages ready (EventStep.fixed none)) original
    (NativeReviewHistory.position model start state.stages ready (EventStep.fixed none)).ordinal
def eligible (ready : NativeReview.Ready model start state.stages) (original : Original model start state ready) : Bool :=
  (before model start state ready original).isPending _ _ &&
    NativeReviewHistory.targetReady model start state.stages ready (EventStep.fixed none) original

structure Receipt where
  private mk ::
  ready : NativeReview.Ready model start state.stages
  accepted : model.source.code.law.Valid (EventStep.seed (state.current model start)).current
    (NativeReview.action model start state.stages ready.receiver)
  selected : NativeReview.produce model start state.stages = .paid ready accepted
  original : Original model start state ready
  member : original ∈ originals model start state ready
  pending : (before model start state ready original).isPending _ _ = true
  aligned : NativeReviewHistory.targetReady model start state.stages ready (EventStep.fixed none) original = true

inductive Result (delay : Nat) where
  | service (receipt : Receipt model start state)
  | paidWithoutTarget (ready : NativeReview.Ready model start state.stages)
      (accepted : model.source.code.law.Valid (EventStep.seed (state.current model start)).current
        (NativeReview.action model start state.stages ready.receiver))
      (selected : NativeReview.produce model start state.stages = .paid ready accepted)
      (absent : ∀ original ∈ originals model start state ready, eligible model start state ready original = false)
  | refused (ready : NativeReview.Ready model start state.stages)
      (denied : ¬ model.source.code.law.Valid (EventStep.seed (state.current model start)).current
        (NativeReview.action model start state.stages ready.receiver))
      (selected : NativeReview.produce model start state.stages = .refused ready denied)
  | complete (closed : NativeReview.complete model start state.stages = true)
  | blocked (reason : NativeReview.Obstruction) (selected : NativeReview.produce model start state.stages = .blocked reason)
  | exhausted (empty : (EventStep.seed (state.current model start)).remaining = 0)
  | communication (live : 0 < (EventStep.seed (state.current model start)).remaining)

-- A source scan distinguishes an actual old responsibility discharge from a merely paid request.
def produce (delay : Nat) : Result model start state delay :=
  match selected : NativeReview.produce model start state.stages with
  | .clear closed => .complete closed
  | .blocked reason => .blocked reason selected
  | .refused ready denied => .refused ready denied selected
  | .paid ready accepted =>
    match found : (originals model start state ready).find? (eligible model start state ready) with
    | none => .paidWithoutTarget ready accepted selected (by
        intro original member
        simpa only [Bool.not_eq_true] using (List.find?_eq_none.mp found) original member)
    | some original =>
      have observed : eligible model start state ready original = true := List.find?_some found
      have checked : (before model start state ready original).isPending _ _ = true ∧
          NativeReviewHistory.targetReady model start state.stages ready (EventStep.fixed none) original = true := by
        simpa only [eligible,Bool.and_eq_true] using observed
      .service ⟨ready,accepted,selected,original,List.mem_of_find?_eq_some found,checked.1,checked.2⟩
  | .environmentTurn =>
    if live : 0 < (EventStep.seed (state.current model start)).remaining then .communication live
    else .exhausted (by omega)

def Result.input {delay : Nat} : Result model start state delay → Option LocalCommandSource.Input
  | .service receipt => some (NativeCommandCompiler.input model start state receipt.ready)
  | .paidWithoutTarget ready .. | .refused ready .. => some (NativeCommandCompiler.input model start state ready)
  | .communication live => some (LiveDynamicCommandDomain.nextInput model start delay state live).val
  | _ => none
def Result.after {delay : Nat} (result : Result model start state delay) : LocalCommandRun.State model start :=
  match result.input model start state with
  | some input => LocalCommandRun.step model start state input
  | none => state

theorem every_generated_input_is_in_the_actual_dynamic_domain (delay : Nat)
    (result : Result model start state delay) (input : LocalCommandSource.Input)
    (actual : result.input model start state = some input) :
    input ∈ DynamicCommandSource.menu model start delay state := by
  cases result with
  | service receipt | paidWithoutTarget ready _ _ _ | refused ready _ _ =>
    all_goals
      cases Option.some.inj actual
      apply List.mem_filter.mpr
      exact ⟨NativeCommandCompiler.input_is_in_the_original_source_menu model start state _,
        NativeCommandCompiler.the_native_command_is_within_every_source_communication_allowance model start state _ delay⟩
  | communication live => cases Option.some.inj actual; exact (LiveDynamicCommandDomain.nextInput model start delay state live).property
  | complete | blocked | exhausted => contradiction

theorem every_result_preserves_its_actual_entries_and_stages (delay : Nat) (result : Result model start state delay) :
    state.entries <+: (result.after model start state).entries ∧ state.stages <+: (result.after model start state).stages := by
  unfold Result.after
  split
  · exact ⟨List.prefix_append _ _,List.prefix_append _ _⟩
  · exact ⟨List.prefix_refl _,List.prefix_refl _⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeCommandService
