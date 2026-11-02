import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Economic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input model.source.code) (cut : Nat) (active : model.source.feedback? = some input)

/-- The original complete evaluation, now reading an arbitrary raw programme. -/
def evaluate (rival : Opponent model.source.code) (raw : List (Option model.source.code.Policy)) : Evaluation model.source.code where
  legal := (Residual.run model.source.code (Residual.scheduleAt model.source cut raw) ⟨rival,input.budget⟩
    (Residual.seed model.source input cut) (Cut.horizon model.source input cut)).frame.localLegal
  complete := (List.finRange model.source.code.task.slots.length).all fun index =>
    (Identity.firstService (RawProfile.machine model.source input cut rival raw) (Cut.finish model.source input cut-1) index).isSome
  profile := RawProfile.profile model.source input cut rival raw
  native := RawAuthority.manifest model input cut rival raw active
  value := fun axis => match axis with
    | .material metric => RawProfile.material model.source input cut rival raw metric
    | .unpaid index holder => RawProfile.remaining model.source input cut rival raw index holder
    | .service index => RawProfile.serviceTime model.source input cut rival raw index

theorem the_raw_evaluator_keeps_the_original_full_evaluation (rival : Opponent model.source.code)
    (term : Cut.Term model.source input cut) :
    evaluate model input cut active rival term.val =
      Distributed.Recall.Information.Agency.Protocol.evaluate model input cut active rival term := by
  apply (Evaluation.mk.injEq ..).mpr
  exact ⟨rfl,rfl,rfl,RawAuthority.the_raw_manifest_preserves_the_original_complete_manifest model input cut rival active term,rfl⟩

variable (raw : List (Option model.source.code.Policy)) (party : Party) (good : Good)
  (floor : Gross.Floor model.source.code.law party good model.source.code.actions) (budget : ℚ)
  (rival : Opponent model.source.code)
  (paid : Source.Paid model.source input cut raw (Cut.horizon model.source input cut) party good budget rival)
  (empty : model.source.continuation = [])

include paid empty in
theorem normalization_preserves_the_original_complete_evaluation :
    evaluate model input cut active rival (NativeTransport.representative model input cut raw party good floor budget) =
      evaluate model input cut active rival raw := by
  apply (Evaluation.mk.injEq ..).mpr
  refine ⟨?_,?_,NativeTransport.profile_preserved model input cut raw party good floor budget rival paid active empty,
    NativeTransport.the_complete_raw_native_manifest_is_preserved model input cut raw party good floor budget rival paid active empty,?_⟩
  · have same := Source.one_public_normalization_preserves_each_rivals_actual_complete_prefix model.source input cut raw
      (Cut.horizon model.source input cut) party good floor budget rival paid
      (Cut.horizon model.source input cut) (Nat.le_refl _)
    rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state] at same
    exact congrArg (fun state : State model.source.code => state.frame.localLegal) same
  · apply List.all_congr rfl
    intro index
    exact congrArg Option.isSome (NativeTransport.first_service model input cut raw party good floor budget rival paid active empty
      (Cut.finish model.source input cut-1) (by dsimp only [Cut.finish,Cut.start,RawProfile.finish,RawProfile.start,RawProfile.horizon,Cut.horizon];omega) index)
  · funext axis
    cases axis with
    | material metric => exact NativeTransport.material_preserved model input cut raw party good floor budget rival paid active empty metric
    | unpaid index holder =>
      exact congrArg (fun matrix => (Settlement.holdingAt matrix index (model.source.code.parties.idxOf holder)).1)
        (NativeTransport.holdings_preserved model input cut raw party good floor budget rival paid active empty)
    | service index =>
      exact congrArg (fun first : Option Nat => (first.getD (Cut.finish model.source input cut) : ℚ))
        (NativeTransport.first_service model input cut raw party good floor budget rival paid active empty
          (Cut.finish model.source input cut-1) (by dsimp only [Cut.finish,Cut.start,RawProfile.finish,RawProfile.start,RawProfile.horizon,Cut.horizon];omega) index)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization
