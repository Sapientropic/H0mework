import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Valuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

def inventoryClaims (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    ClaimChange (Party := Party) (Instrument := Instrument) :=
  (items.map fun item => claimChange law item.before item.request).sum

def inventoryMaterial (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    MaterialChange (Party := Party) (Good := Good) :=
  (items.map fun item => materialChange law item.before item.request).sum

theorem inventory_claims_are_the_original_financial_delta
    (items : List (ExecutionItem Party Good Port Technology Instrument))
    (instrument : Instrument) (debtor creditor : Party) :
    inventoryClaims law items (instrument, debtor, creditor) =
      law.totalFinancialDelta items instrument debtor creditor := by
  induction items with
  | nil => rfl
  | cons item later inherited =>
      simp only [inventoryClaims, List.map_cons, List.sum_cons, Finsupp.add_apply] at *
      rw [claim_change_is_the_original_actual_matrix_delta, inherited]
      rfl

omit [DecidableEq Instrument] in
theorem inventory_material_is_the_original_net_flow
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (person : Party) (good : Good) :
    inventoryMaterial law items (person, good) = law.totalCredit items person good - law.totalDebit items person good := by
  induction items with
  | nil => simp [inventoryMaterial, RawLaw.totalCredit, RawLaw.totalDebit]
  | cons item later inherited =>
      simp only [inventoryMaterial, List.map_cons, List.sum_cons, Finsupp.add_apply] at *
      rw [material_change_is_the_original_net_flow, inherited]
      simp only [RawLaw.totalCredit, RawLaw.totalDebit, List.map_cons, List.sum_cons]
      ring

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)

local notation "C" => Root.Actual.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "R" => Compile.RawInput Party Good Port Technology Instrument

theorem an_actual_public_step_has_its_exact_original_claim_change
    (before : C) {raw : R} (result : Physical.Public.ResultAt input before raw)
    (instrument : Instrument) (debtor creditor : Party) :
    result.next.raw.claims instrument debtor creditor = before.raw.claims instrument debtor creditor +
      inventoryClaims (Physical.Public.interpreter input) result.execution.items (instrument, debtor, creditor) := by
  rw [inventory_claims_are_the_original_financial_delta]
  cases result with
  | accepted word selected checked =>
      cases raw <;> exact (Physical.Public.interpreter input).execute_financial_balance before.raw 0 word instrument debtor creditor
  | refused => simp [Physical.Public.ResultAt.next, Physical.Public.ResultAt.execution, RawLaw.totalFinancialDelta]
  | metadata => simp [Physical.Public.ResultAt.next, Physical.Public.ResultAt.execution, RawLaw.totalFinancialDelta]

theorem the_actual_public_prefix_has_its_exact_original_claim_change
    (before : C) (past : List R) (instrument : Instrument) (debtor creditor : Party) :
    (past.foldl (fun current raw => (Physical.Public.compile input current raw).next) before).raw.claims instrument debtor creditor =
      before.raw.claims instrument debtor creditor +
        inventoryClaims (Physical.Public.interpreter input) (traceItems input before past) (instrument, debtor, creditor) := by
  induction past generalizing before with
  | nil => simp only [List.foldl_nil, traceItems, inventoryClaims, List.map_nil, List.sum_nil, Finsupp.zero_apply, add_zero]
  | cons raw later inherited =>
      rw [List.foldl_cons, inherited, an_actual_public_step_has_its_exact_original_claim_change]
      simp only [traceItems, inventoryClaims, List.map_append, List.sum_append, Finsupp.add_apply]
      ring

def referenceItems (seed : RawCurrent Party Good Technology Instrument) : Nat → List (ExecutionItem Party Good Port Technology Instrument)
  | 0 => []
  | periods + 1 =>
      input.law.rawItems seed (ProgrammeSource.wordAt input seed) ++
        referenceItems (input.law.next seed (ProgrammeSource.wordAt input seed)) periods

theorem the_frozen_reference_has_its_exact_original_claim_change
    (seed : RawCurrent Party Good Technology Instrument) (periods : Nat)
    (instrument : Instrument) (debtor creditor : Party) :
    (baselineFinal input seed periods).claims instrument debtor creditor = seed.claims instrument debtor creditor +
      inventoryClaims input.law (referenceItems input seed periods) (instrument, debtor, creditor) := by
  induction periods generalizing seed with
  | zero => simp only [baselineFinal, baselineWords, Material.Dividend.final, referenceItems,
      inventoryClaims, List.map_nil, List.sum_nil, Finsupp.zero_apply, add_zero]
  | succ periods inherited =>
      change (baselineFinal input (input.law.next seed (ProgrammeSource.wordAt input seed)) periods).claims instrument debtor creditor = _
      rw [inherited]
      have first := input.law.execute_financial_balance seed 0 (ProgrammeSource.wordAt input seed) instrument debtor creditor
      change (input.law.next seed (ProgrammeSource.wordAt input seed)).claims instrument debtor creditor = _ at first
      rw [← inventory_claims_are_the_original_financial_delta input.law _ instrument debtor creditor] at first
      rw [first]
      simp only [referenceItems, inventoryClaims, RawLaw.rawItems, List.map_append, List.sum_append, Finsupp.add_apply]
      ring

theorem the_frozen_reference_counts_its_original_material_flows_once
    (seed : RawCurrent Party Good Technology Instrument) (periods : Nat) (person : Party) (good : Good) :
    inventoryMaterial input.law (referenceItems input seed periods) (person, good) =
      baselineNet input seed periods person good := by
  induction periods generalizing seed with
  | zero => rfl
  | succ periods inherited =>
      simp only [referenceItems, inventoryMaterial, List.map_append, List.sum_append, Finsupp.add_apply] at *
      rw [inherited]
      change inventoryMaterial input.law (input.law.rawItems seed (ProgrammeSource.wordAt input seed)) (person, good) + _ = _
      rw [inventory_material_is_the_original_net_flow]
      rfl

theorem the_actual_public_prefix_counts_its_original_material_flows_once
    (before : C) (past : List R) (person : Party) (good : Good) :
    inventoryMaterial (Physical.Public.interpreter input) (traceItems input before past) (person, good) =
      traceNet input before past person good := by
  rw [inventory_material_is_the_original_net_flow]
  exact (complete_net_flow_counts_each_original_debit_and_credit_once input before past person good).symm

#print axioms inventory_claims_are_the_original_financial_delta
#print axioms the_actual_public_prefix_has_its_exact_original_claim_change
#print axioms the_frozen_reference_has_its_exact_original_claim_change
#print axioms the_frozen_reference_counts_its_original_material_flows_once

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial
