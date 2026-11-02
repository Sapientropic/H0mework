import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Responsibility
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material.Flows

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

abbrev actualWord (world : Cursor model.source.code) (program : Whole.Program model.source.code fuel)
    (rival : Opponent model.source.code) (offset : Nat) :=
  (Whole.source world original program rival).actualExecution (Cut.start world.source world.cut-1+offset)

theorem each_actual_word_debit_is_in_its_complete_evaluation
    (world : Cursor model.source.code) (program : Whole.Program model.source.code fuel)
    (rival : Opponent model.source.code) (offset : Nat)
    (inside : offset < Cut.horizon world.source world.entry world.cut) (axis : Party × Good) :
    model.source.code.law.totalDebit (actualWord model original world program rival offset).interpreted.items axis.1 axis.2 ≤
      (Whole.actualEvaluation model world original program rival).value (.material (.debit axis.1 axis.2)) := by
  change _ ≤ ((List.range (Cut.horizon world.source world.entry world.cut)).map fun n =>
    model.source.code.law.totalDebit (actualWord model original world program rival n).interpreted.items axis.1 axis.2).sum
  apply List.single_le_sum
  · intro amount member
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp member
    exact Institutions.Capitalism.Universal.Source.Material.total_nonnegative _ _ (fun item _ =>
      Institutions.Capitalism.Universal.Source.Material.paid_nonnegative model.source.code.law item axis.1 axis.2)
  · exact List.mem_map.mpr ⟨offset,List.mem_range.mpr inside,rfl⟩

theorem every_accepted_actual_legal_work_word_is_in_the_generated_catalogue
    (program : Whole.Program model.source.code fuel)
    (accepted : Whole.Selection.acceptable model domain original reference program)
    (world : Replanning.Point model domain) (rival : Opponent model.source.code)
    (offset : Nat) (inside : offset < Cut.horizon world.val.source world.val.entry world.val.cut)
    (axis : Party × Good) (floor : Gross.Floor model.source.code.law axis.1 axis.2 model.source.code.actions)
    (supported : ∀ request ∈ (actualWord model original world.val program rival offset).submitted,request ∈ model.source.code.actions)
    (legal : ∀ item ∈ (actualWord model original world.val program rival offset).interpreted.items,
      model.source.code.law.Valid item.before item.request) :
    (actualWord model original world.val program rival offset).submitted ∈
      words model.source.code.actions (floor.cap (upper model domain original reference axis)) := by
  let actual := actualWord model original world.val program rival offset
  have interpreted : actual.interpreted = model.source.code.law.execute actual.before 0 actual.submitted := by
    exact actual.interpreted_exact
  have valid : ∀ item ∈ model.source.code.law.rawItems actual.before actual.submitted,
      model.source.code.law.Valid item.before item.request := by
    rw [RawLaw.rawItems,← interpreted]
    exact legal
  have all := (Whole.Selection.acceptable_iff_every_common_external_opponent model domain original reference program).mp accepted world rival
  have bound := (each_actual_word_debit_is_in_its_complete_evaluation model original world.val program rival offset inside axis).trans
    (every_full_responsibility_accepted_evaluation_fits_the_generated_upper model domain original reference world rival _ all axis)
  apply floor.every_cost_bounded_raw_word_is_enumerated _ actual.before actual.submitted supported valid
  change model.source.code.law.totalDebit (model.source.code.law.execute actual.before 0 actual.submitted).items axis.1 axis.2 ≤ _
  rw [← interpreted]
  exact bound

def ActualWordContract (outcome : Whole.Selection.Outcome model domain original reference)
    (primitive : (axis : Party × Good) → Gross.Outcome model.source.code.law axis.1 axis.2 model.source.code.actions) : Prop :=
  match outcome with
  | .selected choice => ∀ (axis : Party × Good)
      (floor : Gross.Floor model.source.code.law axis.1 axis.2 model.source.code.actions),
      primitive axis = .positive floor →
      ∀ (world : Replanning.Point model domain) (rival : Opponent model.source.code) (offset : Nat),
      offset < Cut.horizon world.val.source world.val.entry world.val.cut →
      (∀ request ∈ (actualWord model original world.val choice.policy.protocol rival offset).submitted,
        request ∈ model.source.code.actions) →
      (∀ item ∈ (actualWord model original world.val choice.policy.protocol rival offset).interpreted.items,
        model.source.code.law.Valid item.before item.request) →
      (actualWord model original world.val choice.policy.protocol rival offset).submitted ∈
        words model.source.code.actions (floor.cap (upper model domain original reference axis))
  | .blocked _ => True

theorem every_selected_outcome_has_its_own_actual_word_budget
    (outcome : Whole.Selection.Outcome model domain original reference)
    (primitive : (axis : Party × Good) → Gross.Outcome model.source.code.law axis.1 axis.2 model.source.code.actions) :
    ActualWordContract model domain original reference outcome primitive := by
  cases outcome with
  | blocked => trivial
  | selected choice =>
    intro axis floor _ world rival offset inside supported legal
    exact every_accepted_actual_legal_work_word_is_in_the_generated_catalogue model domain original reference
      choice.policy.protocol choice.policy.accepted world rival offset inside axis floor supported legal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Responsibility
