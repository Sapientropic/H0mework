import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Material
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Inventory
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Partition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape

open Source.Program Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Completion.Actual.Dividend
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

private theorem sum_nonpositive (values : List ℚ) (each : ∀ value ∈ values, value ≤ 0) : values.sum ≤ 0 := by
  induction values with
  | nil => exact le_rfl
  | cons value tail previous =>
      exact add_nonpos (each value List.mem_cons_self)
        (previous (fun next listed => each next (List.mem_cons_of_mem _ listed)))

theorem every_submitted_result_contains_only_original_accepted_items
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (result : Physical.Public.ResultAt input before raw) :
    ∀ item ∈ result.execution.items, (Physical.Public.interpreter input).Valid item.before item.request := by
  cases result with
  | accepted word selected checked => exact checked
  | refused => simp [Physical.Public.ResultAt.execution]
  | metadata => simp [Physical.Public.ResultAt.execution]

theorem every_programme_item_has_its_own_actual_source_acceptance
    (code : Optimality.Programme.Submission (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    ∀ item ∈ Optimality.Programme.items input before code,
      (Physical.Public.interpreter input).Valid item.before item.request := by
  induction code generalizing before with
  | nil => simp [Optimality.Programme.items]
  | cons raw tail later =>
      intro item member
      rcases List.mem_append.mp member with first | remaining
      · exact every_submitted_result_contains_only_original_accepted_items input before raw _ item first
      · exact later _ item remaining

theorem result_claims_have_the_original_financial_delta
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (result : Physical.Public.ResultAt input before raw) (instrument : Instrument) (debtor holder : Party) :
    result.next.raw.claims instrument debtor holder = before.raw.claims instrument debtor holder +
      Financial.inventoryClaims (Physical.Public.interpreter input) result.execution.items (instrument,debtor,holder) := by
  cases result with
  | accepted word selected checked =>
      have exactDelta := (Physical.Public.interpreter input).execute_financial_balance before.raw 0 word instrument debtor holder
      rw [← Financial.inventory_claims_are_the_original_financial_delta] at exactDelta
      cases raw <;> exact exactDelta
  | refused => simp [Physical.Public.ResultAt.next,Physical.Public.ResultAt.execution,Financial.inventoryClaims]
  | metadata => simp [Physical.Public.ResultAt.next,Physical.Public.ResultAt.execution,Financial.inventoryClaims]

theorem every_programme_preserves_the_entire_original_claim_matrix
    (code : Optimality.Programme.Submission (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (instrument : Instrument) (debtor holder : Party) :
    (Optimality.Programme.run input before code).raw.claims instrument debtor holder =
      before.raw.claims instrument debtor holder +
        Financial.inventoryClaims (Physical.Public.interpreter input)
          (Optimality.Programme.items input before code) (instrument,debtor,holder) := by
  induction code generalizing before with
  | nil => simp [Optimality.Programme.run,Optimality.Programme.items,Financial.inventoryClaims]
  | cons raw tail later =>
      have first := result_claims_have_the_original_financial_delta input before raw
        (Physical.Public.compile input before raw) instrument debtor holder
      rw [Optimality.Programme.run,later,first]
      simp only [Optimality.Programme.items,Financial.inventoryClaims,List.map_append,List.sum_append,Finsupp.add_apply]
      ring

/-- Even an alleged outside supplement must appear as a positive credit
of an accepted original item. Mere claims issuance is not material supply. -/
theorem every_real_resource_gain_has_an_original_credit_producer
    (code : Optimality.Programme.Submission (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (party : Party) (good : Good)
    (gain : before.raw.stock party good < (Optimality.Programme.run input before code).raw.stock party good) :
    ∃ item ∈ Optimality.Programme.items input before code,
      (Physical.Public.interpreter input).Valid item.before item.request ∧
      0 < flowAt ((Physical.Public.interpreter input).actualCredit item.before item.request) party good := by
  classical
  have balanced := Optimality.Programme.the_entire_programme_has_its_original_material_balance input before code party good
  have debit : 0 ≤ (Physical.Public.interpreter input).totalDebit
      (Optimality.Programme.items input before code) party good := by
    apply List.sum_nonneg
    intro value member
    obtain ⟨item,_,rfl⟩ := List.mem_map.mp member
    exact PublicFunction.Costs.actual_debit_nonnegative (Physical.Public.interpreter input) item party good
  have credit : 0 < (Physical.Public.interpreter input).totalCredit
      (Optimality.Programme.items input before code) party good := by linarith
  by_contra missing
  have nonpositive : (Physical.Public.interpreter input).totalCredit
      (Optimality.Programme.items input before code) party good ≤ 0 := by
    apply sum_nonpositive
    intro value member
    obtain ⟨item,original,rfl⟩ := List.mem_map.mp member
    apply le_of_not_gt
    intro positive
    exact missing ⟨item,original,
      every_programme_item_has_its_own_actual_source_acceptance input before code item original,positive⟩
  exact (not_lt_of_ge nonpositive) credit

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape
