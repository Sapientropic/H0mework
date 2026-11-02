import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Evaluation
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Catalogue

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation Continuation.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (programme : Program model.source.code (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.horizon domain)) (paid : Nat)

theorem the_normalizer_keeps_each_complete_comparison_row
    (world : Replanning.Point model domain) (table : Replanning.TableAt model domain world) :
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.readTable model domain original world (normalize domain original programme paid) table =
      Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.readTable model domain original world programme table := by
  unfold Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.readTable
  exact the_normalizer_preserves_the_complete_responsibility_evaluation model domain world.val
    world.property original programme paid _

theorem the_normalizer_keeps_every_original_benefit :
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.benefit model domain original (normalize domain original programme paid) =
      Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.benefit model domain original programme := by
  funext axis
  cases axis with
  | economic world table axis =>
      simp only [Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.benefit,the_normalizer_keeps_each_complete_comparison_row]
  | native world table anchor =>
      simp only [Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.benefit,the_normalizer_keeps_each_complete_comparison_row]

theorem normalization_preserves_original_acceptance
    (reference : Program model.source.code (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.horizon domain)) :
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.acceptable model domain original reference (normalize domain original programme paid) ↔
      Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.acceptable model domain original reference programme := by
  rw [Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.acceptable_iff_every_common_external_opponent,
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.acceptable_iff_every_common_external_opponent]
  apply forall_congr'
  intro world
  apply forall_congr'
  intro rival
  rw [the_normalizer_preserves_the_complete_responsibility_evaluation model domain world.val
    world.property original programme paid rival]

theorem normalization_preserves_every_full_responsibility_dominator
    (other : Program model.source.code (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.horizon domain)) :
    Distributed.Improves (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.axes (fuel := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.horizon domain) model domain)
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.benefit model domain original) (normalize domain original programme paid) other ↔
    Distributed.Improves (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.axes (fuel := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.horizon domain) model domain)
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.benefit model domain original) programme other := by
  simp only [Distributed.Improves,Distributed.NoWorse,
    congrFun (the_normalizer_keeps_every_original_benefit model domain original programme paid)]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused
