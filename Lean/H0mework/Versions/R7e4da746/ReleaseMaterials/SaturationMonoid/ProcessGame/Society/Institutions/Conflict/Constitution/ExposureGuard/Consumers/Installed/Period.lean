import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed.Root
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Deadline
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Period
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Reader

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed

open Capitalism.Universal.Source.Program Capitalism.Universal.Root Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Window)
open Quantities.Execution (endAt inventory)

noncomputable section

abbrev Item := ExecutionItem Bool Bool Port Tech Unit
abbrev Cell := Bool × Use × Bool × ℚ
abbrev Word := Reparation.Actual.Script Bool Bool Port Tech Unit

def life (person : Bool) : Req := ⟨person, [], .ordinary false, [], .use person [(true, 1)] .necessity⟩

def lifeWord : List Req := [life false, life true]

def service : Option (Compile.RawInput Bool Bool Port Tech Unit) := some (.execute lifeWord)

def exitWord : Word := [service]

abbrev window : Window Bool Bool Port Tech Unit := Window.at cut

abbrev material := Physical.Public.interpreter input

abbrev cellsOf (raw : Raw) (people : List Bool) :=
  Material.originalRequirements (Public.Scope.checkInput input) raw people

theorem native_cell (raw : Raw) (people : List Bool) (cell : Cell) (listed : cell ∈ cellsOf raw people) :
    ∃ person, cell = (person, .necessity, true, (1 : ℚ)) := by
  unfold cellsOf Material.originalRequirements at listed
  obtain ⟨person, _, actual⟩ := List.mem_flatMap.mp listed
  have food : (Public.Scope.checkInput input).law.necessities raw person = [(true, (1 : ℚ))] := rfl
  have maintenance : (Public.Scope.checkInput input).law.mandatoryMaintenance raw person = [] := rfl
  rw [food, maintenance] at actual
  have one : amount Bool [(true, 1)] true = 1 := by decide +kernel
  change cell ∈ [(person, .necessity, true, amount Bool [(true, 1)] true)] at actual
  rw [one] at actual
  exact ⟨person, List.mem_singleton.mp actual⟩

theorem requirements_are_native (cell : Cell) (listed : cell ∈ Quantities.Demand.requirements cut) :
    ∃ person, cell = (person, .necessity, true, (1 : ℚ)) := by
  unfold Quantities.Demand.requirements at listed
  rw [cut_input] at listed
  exact native_cell _ _ cell listed

private theorem check_law : (Public.Scope.checkInput cut.native.input).law = material := by
  rw [cut_input]
  rfl

theorem checked_period : Quantities.Execution.PeriodChecks cut lifeWord := by
  let n := cut.native
  let given := Public.Scope.checkInput n.input
  let members := Public.Scope.scope n.input n.depth n.count n.prefixLimit n.renewalLimit n.oldPast n.actual.snapshot lifeWord
  change Review.Guarded.Checks given (Actual.origin n.input n.depth n.count) cut.raw members lifeWord
  refine ⟨by decide +kernel, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro cell listed
    have native : cell ∈ cellsOf (Actual.origin input n.depth n.count) members := by
      change cell ∈ Material.originalRequirements (Public.Scope.checkInput cut.native.input)
        (Actual.origin cut.native.input n.depth n.count) members at listed
      rw [cut_input] at listed
      exact listed
    obtain ⟨person, rfl⟩ := native_cell _ _ cell native
    unfold Material.actualUse
    change (1 : ℚ) ≤ ((given.law.rawItems cut.raw lifeWord).map fun item =>
      match item.request.operation with
      | .use bearer _ kind =>
          if bearer = person ∧ kind = .necessity then flowAt (given.law.actualDebit item.before item.request) person true else 0
      | _ => 0).sum
    have law : given.law = material := check_law
    rw [law, cut_raw]
    cases person <;> decide +kernel
  · unfold Material.ActualAndIndependent
    change ∀ item ∈ (Public.Scope.checkInput cut.native.input).law.rawItems cut.raw lifeWord, _
    rw [check_law, cut_raw]
    decide +kernel
  · intro person _
    rw [check_law, cut_raw]
    cases person <;> decide +kernel
  · change Material.NoFreshControl (Public.Scope.checkInput cut.native.input) cut.raw lifeWord
    rw [cut_input, cut_raw]
    decide +kernel
  · intro person _
    rw [check_law, cut_raw]
    cases person <;> decide +kernel
  · change Material.PolicyExplained (Public.Scope.checkInput cut.native.input)
    rw [cut_input]
    trivial

theorem inventory_exact : Boundary.Actual.items cut service = material.rawItems cutRaw lifeWord := by
  change inventory cut [some (.execute lifeWord)] = _
  rw [Quantities.Execution.a_checked_period_has_the_original_paid_inventory cut lifeWord cut_ready cut_review checked_period,
    cut_input, cut_raw]
  rfl

theorem period_effect : (endAt cut exitWord).raw = material.next cutRaw lifeWord := by
  change (Quantities.Execution.next cut (some (.execute lifeWord))).raw = _
  rw [Quantities.Execution.a_checked_period_has_the_original_real_effect cut lifeWord cut_ready cut_review checked_period,
    cut_input, cut_raw]
  rfl

theorem successor_standing (person : Bool) : person ∈ (endAt cut exitWord).members := by
  let target := endAt cut exitWord
  obtain ⟨same, depth, count⟩ := Quantities.Execution.the_actual_script_keeps_the_original_reader_indices cut exitWord
  apply List.mem_dedup.mpr
  apply List.mem_append_left
  apply List.mem_dedup.mpr
  apply List.mem_append_left
  change person ∈ Actual.members target.native.input target.native.depth target.native.count
  rw [same, depth, count, cut_input, cut_parameters.1, cut_parameters.2.1]
  cases person <;> decide +kernel

theorem clock_advances : cut.raw.clock + 1 = (endAt cut exitWord).raw.clock := by
  rw [period_effect, cut_raw]
  decide +kernel

theorem deadline_exact : (window.nextCut service).raw.clock = window.deadline := by
  change (endAt cut exitWord).raw.clock =
    cut.raw.clock + max 0 ((Boundary.Actual.materialLaw cut).duration cut.raw)
  unfold Boundary.Actual.materialLaw
  rw [cut_input]
  change (endAt cut exitWord).raw.clock = cut.raw.clock + max 0 1
  rw [max_eq_right (by norm_num : (0 : ℚ) ≤ 1)]
  exact clock_advances.symm

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed
