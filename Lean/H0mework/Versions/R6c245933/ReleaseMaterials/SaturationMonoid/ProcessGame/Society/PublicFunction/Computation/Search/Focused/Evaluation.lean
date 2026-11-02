import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Programme
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Emission

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Distributed.Recall.Information.Agency.Protocol.Continuation.Whole
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}

variable (domain : List (Cursor code)) (point : Cursor code) (member : point ∈ domain)
  (original : Rule code) (programme : Program code fuel) (frozen : Nat) (rival : Opponent code)

include member in
theorem the_normalizer_emits_the_same_complete_actual_input :
    (Continuation.Whole.source point original (normalize domain original programme frozen) rival).input =
      (Continuation.Whole.source point original programme rival).input :=
  Emission.equal_actual_runs_generate_one_complete_input point
    (controller point original (normalize domain original programme frozen) rival) (controller point original programme rival)
    (schedule point original (normalize domain original programme frozen)) (schedule point original programme)
    (the_source_generated_projection_keeps_every_actual_state domain point member original programme frozen rival)

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (worlds : List (Cursor model.source.code)) (world : Cursor model.source.code) (inside : world ∈ worlds)
  (fallback : Rule model.source.code) (candidate : Program model.source.code fuel) (paid : Nat)
  (opponent : Opponent model.source.code)

include inside in
theorem the_normalizer_preserves_the_complete_responsibility_evaluation :
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.actualEvaluation model world fallback (normalize worlds fallback candidate paid) opponent =
      Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.actualEvaluation model world fallback candidate opponent := by
  have emitted := the_normalizer_emits_the_same_complete_actual_input worlds world inside fallback candidate paid opponent
  have states := the_source_generated_projection_keeps_every_actual_state worlds world inside fallback candidate paid opponent
  have compared := Acceptance.Generated.aligned_evaluation model world world (Aligned.refl world)
    (controller world fallback (normalize worlds fallback candidate paid) opponent) (controller world fallback candidate opponent)
    (schedule world fallback (normalize worlds fallback candidate paid)) (schedule world fallback candidate) emitted states
  have legal : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.rawLegal world (controller world fallback (normalize worlds fallback candidate paid) opponent) (schedule world fallback (normalize worlds fallback candidate paid)) =
      Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.rawLegal world (controller world fallback candidate opponent) (schedule world fallback candidate) := by
    unfold Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.rawLegal
    apply List.all_congr rfl
    intro ordinal
    dsimp only
    unfold Machine.actualExecution
    rw [emitted]
  apply (Evaluation.mk.injEq ..).mpr
  exact ⟨legal,congrArg Evaluation.complete compared,congrArg Evaluation.profile compared,
    congrArg Evaluation.native compared,congrArg Evaluation.value compared⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused
