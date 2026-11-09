import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Timing.Joint
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Source.Program (ExecutionItem)
open Quantities.Execution (endAt endAt_append the_actual_script_never_runs_the_clock_backwards)

noncomputable section

universe u v w

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

private def firstMaterialPosition {α : Type w} {items : List α} {item : α} (listed : item ∈ items) : Nat := by
  classical
  exact Nat.find (List.getElem?_of_mem listed)

private theorem firstMaterialPosition_reads_the_exact_item {α : Type w}
    {items : List α} {item : α} (listed : item ∈ items) :
    items[firstMaterialPosition listed]? = some item ∧
      ∀ index, items[index]? = some item → firstMaterialPosition listed ≤ index := by
  classical
  exact ⟨Nat.find_spec (List.getElem?_of_mem listed), fun _ => Nat.find_min' (List.getElem?_of_mem listed)⟩

namespace Game

variable {game : Game Party Good Port Technology Instrument Community CivilView OpponentView}
  {allowed : Position Party Good Port Technology Instrument CivilView OpponentView →
    Turn → Reparation.Actual.Input Party Good Port Technology Instrument → Prop}
  {plan : CivilPlan Party Good Port Technology Instrument CivilView}
  {opponent : List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument}
  {arbitrate : Nat → Root.Cut Party Good Port Technology Instrument → Turn} {tick : Nat}

/-- The exit is tested at the cut. A dispatch-level failure is placed
where the scheduler could still replace its original input. Standing,
deadline and shortage are read from that input's actual successor. -/
def JointIssue.address (issue : game.JointIssue allowed plan opponent arbitrate tick) : ℚ × Nat :=
  let window := (game.play plan.submit opponent arbitrate tick).window
  let input := game.inputAt plan.submit opponent arbitrate tick
  match issue with
  | .exit _ => (window.current.raw.clock, 0)
  | .material _ (.attack damage) => (window.current.raw.clock, damage.position.val + 1)
  | .material _ (.signature ..) => (window.current.raw.clock, 1)
  | .material _ (.material _ _ original _) => (window.current.raw.clock, firstMaterialPosition original + 1)
  | .material _ (.standing ..) | .material _ (.missedDeadline ..) | .material _ (.shortage ..) =>
      ((window.nextCut input).raw.clock, (Boundary.Actual.items window.current input).length + 1)

theorem JointIssue.an_authority_failure_keeps_the_first_actual_item
    (permit : game.VisitAllowed allowed plan opponent arbitrate tick)
    (own : (game.turnAt plan.submit opponent arbitrate tick).isCivil = true)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (listed : item ∈ Boundary.Actual.items (game.currentAt plan.submit opponent arbitrate tick)
      (game.inputAt plan.submit opponent arbitrate tick))
    (refused : ¬ Civil.Persistence.OwnMaterial (game.currentAt plan.submit opponent arbitrate tick) game.command item) :
    let issue : game.JointIssue allowed plan opponent arbitrate tick := .material permit (.material own item listed refused)
    let items := Boundary.Actual.items (game.currentAt plan.submit opponent arbitrate tick)
      (game.inputAt plan.submit opponent arbitrate tick)
    items[issue.address.2 - 1]? = some item ∧
      ∀ index, items[index]? = some item → issue.address.2 ≤ index + 1 := by
  obtain ⟨actual, earliest⟩ := firstMaterialPosition_reads_the_exact_item listed
  exact ⟨actual, fun index reads => Nat.succ_le_succ (earliest index reads)⟩

variable (breach : game.JointBreach allowed plan)

abbrev JointBreach.clock : ℚ := breach.issue.address.1
abbrev JointBreach.position : Nat := breach.issue.address.2
abbrev JointBreach.visit : Nat := (game.prefixAt plan breach.opponent breach.arbitrate breach.tick).length

theorem JointBreach.visit_is_its_original_prefix_length :
    breach.visit = game.past.length + breach.tick := by
  have length (n : Nat) : (game.scriptAt plan.submit breach.opponent breach.arbitrate n).length = n := by
    induction n with
    | zero => rfl
    | succ n earlier =>
      rw [game.play_succ_script, List.length_append, earlier]
      rfl
  change (game.past ++ game.scriptAt plan.submit breach.opponent breach.arbitrate breach.tick).length = _
  rw [List.length_append, length]

theorem JointBreach.clock_is_between_the_original_cuts :
    let window := (game.play plan.submit breach.opponent breach.arbitrate breach.tick).window
    let input := game.inputAt plan.submit breach.opponent breach.arbitrate breach.tick
    window.current.raw.clock ≤ breach.clock ∧ breach.clock ≤ (window.nextCut input).raw.clock := by
  rcases breach with ⟨opponent, arbitrate, tick, prior, issue⟩
  let window := (game.play plan.submit opponent arbitrate tick).window
  let input := game.inputAt plan.submit opponent arbitrate tick
  have grows : window.current.raw.clock ≤ (window.nextCut input).raw.clock :=
    the_actual_script_never_runs_the_clock_backwards window.current [input]
  cases issue with
  | exit => exact ⟨le_rfl, grows⟩
  | material permit failure => cases failure <;> first | exact ⟨le_rfl, grows⟩ | exact ⟨grows, le_rfl⟩

theorem JointBreach.clock_is_after_submission :
    (endAt game.seed game.past).raw.clock ≤ breach.clock := by
  have prior : (endAt game.seed game.past).raw.clock ≤
      (game.currentAt plan.submit breach.opponent breach.arbitrate breach.tick).raw.clock := by
    rw [game.play_is_the_original_current, endAt_append]
    exact the_actual_script_never_runs_the_clock_backwards _ _
  exact prior.trans breach.clock_is_between_the_original_cuts.1

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
