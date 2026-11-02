import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Observation

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Commitment
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}

def padded (original : Prefix.Rule code) (programme : Program code fuel) : Program code fuel :=
  ⟨Padding.controls original programme,by rw [Padding.length]⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem stage (original : Prefix.Rule code) (programme : Program code fuel) (offset : Nat) :
    (padded original programme).at original offset = programme.at original offset :=
  Padding.every_stage_is_the_original_stage original programme offset

omit [DecidableEq Port] [DecidableEq Technology] in
theorem padded_length (original : Prefix.Rule code) (programme : Program code fuel) :
    (padded original programme).controls.length = fuel := Padding.length original programme

omit [DecidableEq Port] [DecidableEq Technology] in
theorem next_prefix (original : Prefix.Rule code) (programme : Program code fuel)
    (past : List (Prefix.Rule code)) (retained : programme.controls.take past.length = past)
    (inside : past.length < fuel) :
    (padded original programme).controls.take (past.length+1) = past ++ [programme.at original past.length] := by
  have within : past.length < (padded original programme).controls.length := by rw [padded_length];exact inside
  have old : (padded original programme).controls.take past.length = past := Padding.preserves_prefix original programme past retained
  rw [List.take_succ_eq_append_getElem within,old]
  have same := stage original programme past.length
  change ((padded original programme).controls[past.length]?).getD _ = _ at same
  rw [List.getElem?_eq_getElem within,Option.getD_some] at same
  rw [same]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem suffix_reconstructs_the_padded_plan (original : Prefix.Rule code) (programme : Program code fuel) (cut : Nat) :
    extension fuel ((padded original programme).controls.take cut)
      (Splice.word ((padded original programme).controls.drop cut)) = padded original programme := by
  exact (the_committed_plan_is_one_of_its_own_prefix_completions _ _ _).trans
    (Complete.clipping_a_bounded_program_is_itself _)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem retained_stages (original : Prefix.Rule code) (programme : Program code fuel)
    (past : List (Prefix.Rule code)) (retained : programme.controls.take past.length = past)
    (offset : Nat) (inside : offset < past.length) :
    (Splice.word past).at original offset = programme.at original offset := by
  have same := congrArg (fun controls : List (Prefix.Rule code) => controls[offset]?) retained
  rw [List.getElem?_take_of_lt inside] at same
  change (past[offset]?).getD _ = (programme.controls[offset]?).getD _
  rw [same,List.getElem?_eq_getElem inside,Option.getD_some]
  rfl

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)


theorem padded_evaluation (point : Cursor model.source.code) (programme : Program model.source.code fuel)
    (rival : Opponent model.source.code) :
    actualEvaluation model point original (padded original programme) rival = actualEvaluation model point original programme rival := by
  apply stages_generate_the_same_complete_evaluation
  intro offset _
  exact stage original programme offset

theorem admissible_plan_is_its_own_valid_reference
    (reference programme : Program model.source.code fuel)
    (accepted : Selection.acceptable model domain original reference programme) :
    Selection.acceptable model domain original programme programme := by
  apply (Selection.acceptable_iff_every_generated_cursor _ _ _ _ _).mpr
  intro world table
  have old := (Selection.acceptable_iff_every_generated_cursor _ _ _ _ _).mp accepted world table
  exact ⟨old.1,old.2.1,rfl,Authority.Trace.Lawful.refl _,fun _ _ => le_refl _⟩

theorem padded_acceptance (reference programme : Program model.source.code fuel)
    (accepted : Selection.acceptable model domain original reference programme) :
    Selection.acceptable model domain original reference (padded original programme) := by
  apply (Selection.acceptable_iff_every_common_external_opponent _ _ _ _ _).mpr
  intro world rival
  rw [padded_evaluation]
  exact (Selection.acceptable_iff_every_common_external_opponent _ _ _ _ _).mp accepted world rival


theorem every_paid_prefix_retains_the_previous_admitted_completion
    (reference programme : Program model.source.code (horizon domain))
    (accepted : Selection.acceptable model domain original reference programme) (cut : Nat) :
    ∃ choice, compile model domain original ((padded original programme).controls.take cut) programme = .selected choice := by
  cases result : compile model domain original ((padded original programme).controls.take cut) programme with
  | selected choice => exact ⟨choice,rfl⟩
  | blocked rejected =>
      let tail : Complete.FiniteProgram model.source.code :=
        ⟨((padded original programme).controls.drop cut).length,Splice.word ((padded original programme).controls.drop cut)⟩
      have same : extension (horizon domain) ((padded original programme).controls.take cut) tail.2 = padded original programme :=
        suffix_reconstructs_the_padded_plan original programme cut
      have own := padded_acceptance model domain original programme programme
        (admissible_plan_is_its_own_valid_reference model domain original reference programme accepted)
      rw [←same] at own
      exact False.elim ((rejected tail).broken (own _ (rejected tail).generated))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Commitment
