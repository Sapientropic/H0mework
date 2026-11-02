import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

local notation "C" => Root.Actual.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "R" => Compile.RawInput Party Good Port Technology Instrument

theorem an_actual_material_step_cannot_reset_old_claims
    (before : C) {raw : R} (result : Physical.Public.ResultAt input before raw)
    (safe : ∀ item ∈ result.execution.items, Root.Settlement.NonFinancialRequest item.request) :
    result.next.raw.claims = before.raw.claims := by
  cases result with
  | accepted word selected checked =>
    have nonfinancial : Root.Settlement.NonFinancial word := by
      intro request present
      have listed : request ∈ ((Physical.Public.interpreter input).rawItems before.raw word).map ExecutionItem.request := by
        change request ∈ ((Physical.Public.interpreter input).execute before.raw 0 word).items.map ExecutionItem.request
        rw [(Physical.Public.interpreter input).inventory_requests_exact]
        exact present
      obtain ⟨item, original, same⟩ := List.mem_map.mp listed
      cases same
      exact safe item original
    cases raw <;> exact nonfinancial.execute_claims (Physical.Public.interpreter input) before.raw 0 word
  | refused => rfl
  | metadata => rfl

theorem an_actual_material_prefix_cannot_reset_old_claims
    (before : C) (past : List R)
    (safe : ∀ item ∈ traceItems input before past, Root.Settlement.NonFinancialRequest item.request) :
    (past.foldl (fun current raw => (Physical.Public.compile input current raw).next) before).raw.claims = before.raw.claims := by
  induction past generalizing before with
  | nil => rfl
  | cons raw later inherited =>
    have head : ∀ item ∈ (Physical.Public.compile input before raw).execution.items,
        Root.Settlement.NonFinancialRequest item.request := fun item member => safe item (List.mem_append_left _ member)
    have tail : ∀ item ∈ traceItems input (Physical.Public.compile input before raw).next later,
        Root.Settlement.NonFinancialRequest item.request := fun item member => safe item (List.mem_append_right _ member)
    rw [List.foldl_cons, inherited _ tail]
    exact an_actual_material_step_cannot_reset_old_claims input before _ head

variable [DecidableEq Port]

theorem a_strict_actual_material_dividend_keeps_all_original_raw_claims
    (depth count prefixLimit renewalLimit : Nat)
    (originalPast : List (Compile.RawInput Party Good Port Technology Instrument))
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (checked : Checks input depth count prefixLimit renewalLimit originalPast current) :
    (oldEndpoint input depth count prefixLimit renewalLimit originalPast current).claims =
        (seed input depth count prefixLimit renewalLimit originalPast).raw.claims ∧
      (publicCurrent input depth count prefixLimit renewalLimit originalPast current).raw.claims =
        (seed input depth count prefixLimit renewalLimit originalPast).raw.claims := by
  constructor
  · exact Material.Dividend.original_claims_are_retained input.law
      (seed input depth count prefixLimit renewalLimit originalPast).raw
      (baselineWords input (seed input depth count prefixLimit renewalLimit originalPast).raw
        (horizon input depth count prefixLimit renewalLimit originalPast current)) checked.1
  · exact an_actual_material_prefix_cannot_reset_old_claims input
      (seed input depth count prefixLimit renewalLimit originalPast) current.past checked.2.1

#print axioms an_actual_material_prefix_cannot_reset_old_claims
#print axioms a_strict_actual_material_dividend_keeps_all_original_raw_claims

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend
