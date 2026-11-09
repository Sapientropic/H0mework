import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities Evolving.Epoch Actual

noncomputable section

/-- This submission uses the same cut's food without the installed
production and provision. The original recipient has no opening food. -/
def withoutProvision : RawEvent Bool Bool Bool Unit Unit := [life true, life false]

variable (cut : C)

local notation "Owner" => cut.native.input
local notation "ScopeInput" => Public.Scope.checkInput Owner
local notation "Origin" => Abolition.Root.Actual.origin Owner cut.native.depth cut.native.count
local notation "Here" => cut.native.actual.snapshot
local notation "ScopeParties" => Public.Scope.scope Owner cut.native.depth cut.native.count
  cut.native.prefixLimit cut.native.renewalLimit cut.native.oldPast Here withoutProvision
abbrev MissingScope := Public.Scope.Failure Owner cut.native.depth cut.native.count
  cut.native.prefixLimit cut.native.renewalLimit cut.native.oldPast Here (Compile.RawInput.execute withoutProvision)

private theorem needy_person_is_in_the_actual_scope (owned : Owner = input)
    (raw : cut.raw = secondRaw) : false ∈ ScopeParties := by
  apply List.mem_dedup.mpr
  apply List.mem_append_right
  change false ∈ Source.ProgrammeFace.parties (Physical.Public.interpreter Owner) (cut.raw, withoutProvision)
  rw [show Physical.Public.interpreter Owner = publicLaw from congrArg Physical.Public.interpreter owned, raw]
  decide +kernel

private theorem the_original_food_lines (owned : Owner = input) (members : List Bool) :
    Material.originalRequirements ScopeInput Origin members =
      members.map (fun person => (person, .necessity, true, 1)) := by
  rw [show ScopeInput = checkInput from congrArg Public.Scope.checkInput owned]
  have one : amount Bool [(true,1)] true = 1 := by decide +kernel
  induction members with
  | nil => rfl
  | cons person rest prior =>
    change [(person, .necessity, true, amount Bool [(true,1)] true)] ++
      Material.originalRequirements checkInput Origin rest = _
    simp only [one, prior, List.singleton_append, List.map_cons]

private theorem original_food_line_is_due (owned : Owner = input) (raw : cut.raw = secondRaw) :
    (false, .necessity, true, (1 : ℚ)) ∈ Material.originalRequirements ScopeInput Origin ScopeParties := by
  rw [the_original_food_lines cut owned]
  exact List.mem_map.mpr ⟨false, needy_person_is_in_the_actual_scope cut owned raw, rfl⟩

private theorem the_only_possible_food_lines (owned : Owner = input) (cell : Bool × Use × Bool × ℚ)
    (due : cell ∈ Material.originalRequirements ScopeInput Origin ScopeParties) :
    cell = (false, .necessity, true, 1) ∨ cell = (true, .necessity, true, 1) := by
  rw [the_original_food_lines cut owned] at due
  obtain ⟨person, _, same⟩ := List.mem_map.mp due
  cases person
  · exact Or.inl same.symm
  · exact Or.inr same.symm

private theorem the_missing_food_is_exact (owned : Owner = input) (raw : cut.raw = secondRaw) (person : Bool) :
    Material.actualUse ScopeInput cut.raw withoutProvision person .necessity true =
      if person then 1 else 0 := by
  rw [show ScopeInput = checkInput from congrArg Public.Scope.checkInput owned, raw]
  cases person <;> decide +kernel

private theorem the_original_need_guard_returns_the_unfed_person (owned : Owner = input)
    (raw : cut.raw = secondRaw) :
    ∃ issue : Material.NeedFloorIssue ScopeInput Origin cut.raw ScopeParties withoutProvision,
      Abolition.Review.Guarded.inspect ScopeInput Origin cut.raw ScopeParties withoutProvision =
        .rejected (.originalNeed issue) ∧
      issue.cell = (false, .necessity, true, 1) := by
  have permitted : ∃ proof, Abolition.Root.Settlement.checkFinancial withoutProvision = .accepted proof :=
    ⟨by decide +kernel, rfl⟩
  obtain ⟨proof, permitted⟩ := permitted
  unfold Abolition.Review.Guarded.inspect
  rw [permitted]
  cases scan : Material.checkOriginalNeedFloor ScopeInput Origin cut.raw ScopeParties withoutProvision with
  | accepted paid =>
    have wrong := paid _ (original_food_line_is_due cut owned raw)
    change (1 : ℚ) ≤ Material.actualUse ScopeInput cut.raw withoutProvision false .necessity true at wrong
    rw [the_missing_food_is_exact cut owned raw] at wrong
    norm_num at wrong
  | rejected issue =>
    refine ⟨issue, rfl, ?_⟩
    rcases the_only_possible_food_lines cut owned issue.cell issue.original with missing | funded
    · exact missing
    · have wrong := issue.deficit
      rw [funded] at wrong
      change Material.actualUse ScopeInput cut.raw withoutProvision true .necessity true < (1 : ℚ) at wrong
      rw [the_missing_food_is_exact cut owned raw] at wrong
      norm_num at wrong

def shortage (failed : MissingScope cut) : Option (Bool × Use × Bool × ℚ) :=
  match failed.issue with
  | .originalNeed issue =>
    let (person, use, good, due) := issue.cell
    some (person, use, good, due - Material.actualUse ScopeInput cut.raw failed.word person use good)
  | _ => none

theorem the_actual_scope_refuses_for_the_original_need (owned : Owner = input)
    (raw : cut.raw = secondRaw) :
    ∃ failed : MissingScope cut,
      Public.Scope.inspect Owner cut.native.depth cut.native.count cut.native.prefixLimit
        cut.native.renewalLimit cut.native.oldPast Here (.execute withoutProvision) = .rejected failed ∧
      shortage cut failed = some (false, .necessity, true, 1) := by
  obtain ⟨issue, generated, cell⟩ := the_original_need_guard_returns_the_unfed_person cut owned raw
  unfold Public.Scope.inspect
  split
  · rename_i absent
    cases absent
  · rename_i word selected
    have same : word = withoutProvision := Option.some.inj selected.symm
    subst word
    have selectedIssue : Abolition.Review.Guarded.inspect ScopeInput Origin
        (Public.Scope.actualState Owner cut.native.depth cut.native.count cut.native.prefixLimit
          cut.native.renewalLimit cut.native.oldPast Here).raw ScopeParties withoutProvision =
          .rejected (.originalNeed issue) := generated
    rw [selectedIssue]
    refine ⟨_, rfl, ?_⟩
    change some (issue.cell.1, issue.cell.2.1, issue.cell.2.2.1, issue.cell.2.2.2 -
      Material.actualUse ScopeInput cut.raw withoutProvision issue.cell.1 issue.cell.2.1 issue.cell.2.2.1) = _
    rw [cell, show Material.actualUse ScopeInput cut.raw withoutProvision false .necessity true = 0
      from the_missing_food_is_exact cut owned raw false, sub_zero]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation
