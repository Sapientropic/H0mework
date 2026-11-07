import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Physics

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

def firstRawVariants : List Raw := Control.Scenario.seed ::
  Control.Scenario.commonWork.map (input.law.step Control.Scenario.seed)

theorem every_initial_repair_is_an_original_common_work_request
    (focus : Repair.Focus (Party := Party) (Good := Good) (Port := Bool))
    (attempt : Repair.AttemptAt input 0 count Control.Scenario.seed focus
      (Repair.alphabet input Control.Scenario.seed)) :
    attempt.request ∈ Control.Scenario.commonWork := by
  have original := attempt.original
  change attempt.request ∈ Control.Scenario.commonWork ++ Control.Scenario.commonWork at original
  exact (List.mem_append.mp original).elim id id

theorem every_initial_source_operation_has_one_of_its_original_physical_effects
    (operation : Actual.Operation input 0 count 0 0 (Actual.initial input 0 count)) :
    (operation.next input 0 count 0 0).raw ∈ firstRawVariants := by
  cases operation with
  | migration plan selected =>
      have original : Actual.origin input 0 count = Control.Scenario.seed :=
        the_original_physical_seed_is_the_actual_capital_successor
      rw [original, the_original_member_inventory_is_generated_before_the_trial] at plan
      exact ((a_zero_length_renewal_cannot_pay_the_original_members _).false plan).elim
  | renewal word phase checked => cases phase
  | repair cause attempt =>
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      have origin : (Actual.initial input 0 count).raw = Control.Scenario.seed :=
        the_original_physical_seed_is_the_actual_capital_successor
      have remaining : (Actual.initial input 0 count).remaining = Repair.alphabet input Control.Scenario.seed := by
        change Repair.alphabet input (Actual.origin input 0 count) = _
        exact congrArg (Repair.alphabet input) the_original_physical_seed_is_the_actual_capital_successor
      have original := Eq.mp (congrArg (fun xs => attempt.request ∈ xs) remaining) attempt.original
      change attempt.request ∈ Control.Scenario.commonWork ++ Control.Scenario.commonWork at original
      refine ⟨attempt.request, (List.mem_append.mp original).elim id id, ?_⟩
      exact (congrArg (fun raw => input.law.step raw attempt.request) origin).symm

theorem the_first_automatic_raw_is_in_its_actual_source_inventory :
    (Compile.next input 0 count 0 0 (Actual.initial input 0 count) .advance).raw ∈ firstRawVariants := by
  unfold Compile.next Compile.compile
  cases dispatch : Actual.dispatch input 0 count 0 0 (Actual.initial input 0 count) with
  | refusal obstruction source =>
      change Actual.origin input 0 count ∈ firstRawVariants
      rw [show Actual.origin input 0 count = Control.Scenario.seed from
        the_original_physical_seed_is_the_actual_capital_successor]
      exact List.mem_cons_self
  | automatic generated =>
      exact every_initial_source_operation_has_one_of_its_original_physical_effects generated.operation

theorem the_first_actual_raw_is_in_its_actual_source_inventory (nature : RequestAt) :
    (Physical.stateAt input 0 count 0 0 (firstRaw nature).germ.snapshot.past).raw ∈ firstRawVariants := by
  rw [(the_first_raw_cut_keeps_the_original_reader_and_physical_prefix nature).2.1]
  change (Compile.next input 0 count 0 0 (Actual.initial input 0 count)
    (Mandatory.executionRaw (review := none) input 0 count 0 0 Physical.initial
      (.primitive Control.Scenario.ownerPresent))).raw ∈ firstRawVariants
  rcases the_initial_opcode_is_an_advance_or_the_original_primitive with advance | primitive
  · rw [advance]
    exact the_first_automatic_raw_is_in_its_actual_source_inventory
  · rw [primitive]
    unfold Compile.next
    simp only [Compile.compile]
    cases verdict : Actual.inspectPrimitive input (Actual.initial input 0 count) Control.Scenario.ownerPresent <;>
      simp only [Compile.Result.next, Actual.Command.next, Actual.primitiveNext]
    · have same : input.law.step (Actual.initial input 0 count).raw Control.Scenario.ownerPresent = Control.Scenario.seed := by
        rw [show (Actual.initial input 0 count).raw = Control.Scenario.seed from
          the_original_physical_seed_is_the_actual_capital_successor]
        exact input.law.presentation_preserves_material_and_claims _ _ rfl
      rw [same]
      exact List.mem_cons_self
    · change Actual.origin input 0 count ∈ firstRawVariants
      rw [show Actual.origin input 0 count = Control.Scenario.seed from
        the_original_physical_seed_is_the_actual_capital_successor]
      exact List.mem_cons_self

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
