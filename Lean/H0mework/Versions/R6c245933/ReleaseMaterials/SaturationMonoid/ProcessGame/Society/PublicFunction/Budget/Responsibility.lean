import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Gross
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Whole.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Responsibility

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Whole.Program model.source.code fuel)

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
  (Cut.tables world.val.source world.val.entry world.val.cut).map fun table =>
    (Whole.tableEvaluation model world.val original reference table).value (.material (.debit axis.1 axis.2))

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
    (Whole.actualEvaluation model world.val original reference rival).value (.material (.debit axis.1 axis.2)) ≤
      upper model domain original reference axis := by
  rw [← Whole.one_common_external_table_preserves_the_entire_actual_evaluation model world.val original reference rival]
  apply le_maximum
  apply List.mem_flatMap.mpr
  refine ⟨world,List.mem_attach _ _,List.mem_map.mpr ⟨externalTable world.val rival,?_,rfl⟩⟩
  exact Residual.restriction_is_generated _ _ _ rival

theorem every_full_responsibility_accepted_evaluation_fits_the_generated_upper
    (world : Replanning.Point model domain) (rival : Opponent model.source.code)
    (new : Evaluation model.source.code)
    (accepted : Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
      new (Whole.actualEvaluation model world.val original reference rival)) (axis : Party × Good) :
    new.value (.material (.debit axis.1 axis.2)) ≤ upper model domain original reference axis :=
  (accepted.2.2.2.2 _ (every_material_debit_axis_is_original model world.val axis)).trans
    (the_public_upper_bound_covers_every_common_adaptive_opponent model domain original reference world rival axis)

def primitive (axis : Party × Good) := Gross.generate model.source.code.law axis.1 axis.2 model.source.code.actions

def WordContract (axis : Party × Good) : Gross.Outcome model.source.code.law axis.1 axis.2 model.source.code.actions → Prop
  | .positive result =>
      Gross.verify model.source.code.law axis.1 axis.2 model.source.code.actions result.epsilon = true ∧
      ∀ (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
        (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument),
        (∀ request ∈ word,request ∈ model.source.code.actions) →
        (∀ item ∈ model.source.code.law.rawItems current word,model.source.code.law.Valid item.before item.request) →
        Gross.debit model.source.code.law axis.1 axis.2 (model.source.code.law.rawItems current word) ≤
          upper model domain original reference axis →
        word ∈ words model.source.code.actions (result.cap (upper model domain original reference axis))
  | .unresolved request _ _ => request ∈ model.source.code.actions ∧
      ¬ Gross.Costly model.source.code.law axis.1 axis.2 request

theorem every_primitive_outcome_retains_its_exact_word_contract (axis : Party × Good)
    (outcome : Gross.Outcome model.source.code.law axis.1 axis.2 model.source.code.actions) :
    WordContract model domain original reference axis outcome := by
  cases outcome with
  | positive result =>
    exact ⟨Gross.every_generated_floor_has_independent_review _ _ _ _ result,result.every_cost_bounded_raw_word_is_enumerated _⟩
  | unresolved request original broken => exact ⟨original,broken⟩

def SelectedBound : Whole.Selection.Outcome model domain original reference → Prop
  | .selected choice => ∀ (world : Replanning.Point model domain) (rival : Opponent model.source.code) (axis : Party × Good),
      (Whole.actualEvaluation model world.val original choice.policy.protocol rival).value (.material (.debit axis.1 axis.2)) ≤
        upper model domain original reference axis
  | .blocked _ => True

theorem the_actual_selected_program_fits_the_public_material_bounds
    (outcome : Whole.Selection.Outcome model domain original reference) : SelectedBound model domain original reference outcome := by
  cases outcome with
  | blocked => trivial
  | selected choice =>
    intro world rival axis
    exact every_full_responsibility_accepted_evaluation_fits_the_generated_upper model domain original reference world rival _
      ((Whole.Selection.acceptable_iff_every_common_external_opponent model domain original reference choice.policy.protocol).mp
        choice.policy.accepted world rival) axis

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Responsibility
