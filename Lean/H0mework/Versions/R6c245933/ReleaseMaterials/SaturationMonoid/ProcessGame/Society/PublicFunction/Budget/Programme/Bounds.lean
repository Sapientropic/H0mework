import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Normalize

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Bounds

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Program model.source.code)

private def maximum : List ℚ → ℚ
  | [] => 0
  | value :: rest => max value (maximum rest)

private theorem le_maximum (values : List ℚ) (value : ℚ) (inside : value ∈ values) : value ≤ maximum values := by
  induction values with
  | nil => simp only [List.not_mem_nil] at inside
  | cons first rest ih =>
    rcases List.mem_cons.mp inside with same | later
    · subst value;exact le_max_left _ _
    · exact (ih later).trans (le_max_right _ _)

/-- Each material coordinate keeps its own unit; no welfare scalar is formed. -/
def readings (axis : Party × Good) : List ℚ := domain.attach.flatMap fun world =>
  (Finite.tables world.val original [reference]).map fun table =>
    (Finite.tableEvaluation model world.val original [reference] reference table).value (.material (.debit axis.1 axis.2))

def upper (axis : Party × Good) : ℚ := maximum (readings model domain original reference axis)

def verifyUpper (axis : Party × Good) (proposed : ℚ) : Bool := decide
  (0 ≤ proposed ∧ ∀ amount ∈ readings model domain original reference axis,amount ≤ proposed)

theorem the_public_upper_bound_has_independent_review (axis : Party × Good) :
    verifyUpper model domain original reference axis (upper model domain original reference axis) = true := by
  simp only [verifyUpper,decide_eq_true_eq]
  have nonnegative (values : List ℚ) : 0 ≤ maximum values := by
    induction values with
    | nil => exact le_rfl
    | cons value rest ih => exact ih.trans (le_max_right _ _)
  exact ⟨nonnegative _,fun amount inside => le_maximum _ amount inside⟩

theorem every_material_debit_axis_is_original (world : Cursor model.source.code) (axis : Party × Good) :
    EconomicAxis.material (.debit axis.1 axis.2) ∈ economicAxes world.source world.cut := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨.debit axis.1 axis.2,?_,rfl⟩
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨axis.1,model.source.code.parties_cover axis.1,
    List.mem_flatMap.mpr ⟨axis.2,model.source.code.goods_cover axis.2,by simp⟩⟩

theorem the_public_upper_bound_covers_every_common_adaptive_opponent
    (world : Replanning.Point model domain) (rival : Opponent model.source.code) (axis : Party × Good) :
    (Finite.actualEvaluation model world.val original reference rival).value (.material (.debit axis.1 axis.2)) ≤
      upper model domain original reference axis := by
  rw [← Finite.one_external_restriction_preserves_the_complete_evaluation model world.val original [reference] reference List.mem_cons_self rival]
  apply le_maximum
  apply List.mem_flatMap.mpr
  refine ⟨world,List.mem_attach _ _,List.mem_map.mpr ⟨Finite.restrict world.val original [reference] rival,?_,rfl⟩⟩
  exact Residual.restriction_is_generated _ _ _ rival

theorem every_full_responsibility_accepted_evaluation_fits_the_generated_upper
    (world : Replanning.Point model domain) (rival : Opponent model.source.code)
    (new : Evaluation model.source.code)
    (accepted : Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
      new (Finite.actualEvaluation model world.val original reference rival)) (axis : Party × Good) :
    new.value (.material (.debit axis.1 axis.2)) ≤ upper model domain original reference axis :=
  (accepted.2.2.2.2 _ (every_material_debit_axis_is_original model world.val axis)).trans
    (the_public_upper_bound_covers_every_common_adaptive_opponent model domain original reference world rival axis)

def Accepted (program : Program model.source.code) : Prop :=
  ∀ (world : Replanning.Point model domain) (rival : Opponent model.source.code),
    Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
      (Finite.actualEvaluation model world.val original program rival)
      (Finite.actualEvaluation model world.val original reference rival)

variable (party : Party) (good : Good)
  (floor : Gross.Floor model.source.code.law party good model.source.code.actions)

abbrev cap := floor.cap (upper model domain original reference (party,good))
abbrev representative (program : Program model.source.code) :=
  normalized (cap model domain original reference party good floor) (Whole.Complete.horizon domain) original program
abbrev catalogue : List (Program model.source.code) :=
  programs model.source.code (cap model domain original reference party good floor) (Whole.Complete.horizon domain)

variable (program : Program model.source.code)
  (supported : ∀ n < Whole.Complete.horizon domain, (stage model.source.code original program n).supported)
  (accepted : Accepted model domain original reference program)

include supported accepted in
theorem every_accepted_raw_program_has_a_complete_representative
    (world : Replanning.Point model domain) (rival : Opponent model.source.code) :
    Finite.actualEvaluation model world.val original (representative model domain original reference party good floor program) rival =
      Finite.actualEvaluation model world.val original program rival := by
  have enough := Whole.Complete.each_remaining_horizon_is_generated domain world.val world.property
  have supportedSchedule := supported_schedule world.val original program
    (fun n inside => supported n (inside.trans_le enough))
  have paid := Normalization.full_acceptance_generates_the_original_paid_certificate
    (Replanning.native model world.val) world.val.entry world.val.cut rfl rfl
    (schedule world.val original program) (controller world.val original program rival) party good supportedSchedule
    (Finite.actualEvaluation model world.val original reference rival) (accepted world rival)
    (upper model domain original reference (party,good))
    (the_public_upper_bound_covers_every_common_adaptive_opponent model domain original reference world rival (party,good))
  exact normalized_program_preserves_the_complete_actual_evaluation model world.val original program party good floor
    (upper model domain original reference (party,good)) rival (Whole.Complete.horizon domain) enough paid

include supported in
theorem every_supported_representative_is_in_the_generated_catalogue :
    representative model domain original reference party good floor program ∈ catalogue model domain original reference party good floor :=
  every_supported_normalization_is_generated model.source.code original program
    (cap model domain original reference party good floor) (Whole.Complete.horizon domain) supported

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Bounds
