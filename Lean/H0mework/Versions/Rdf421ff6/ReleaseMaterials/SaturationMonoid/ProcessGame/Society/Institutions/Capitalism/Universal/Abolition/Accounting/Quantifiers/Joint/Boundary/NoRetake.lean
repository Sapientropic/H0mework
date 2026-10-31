import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Reply

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed)) (current : Current seed claim)

theorem paid_original_rows_cannot_supply_another_renewal_permit
    (paid : Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current)
    (proposal : RawEvent Party Good Port Technology Instrument) (permit : Permit seed claim current proposal) : False := by
  have zero := (zero_budget_iff_both_original_rows_are_paid seed claim current).mpr paid
  have strict := permit.strictProgress
  omega

theorem a_paid_original_pair_cannot_mint_requested_renewal_authority
    (paid : Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current)
    (proposal : RawEvent Party Good Port Technology Instrument) :
    ¬ RequestedRenewalAuthorityAt seed claim current proposal (verdict seed claim current proposal) := by
  cases decision : verdict seed claim current proposal with
  | admitted permit => exact False.elim (paid_original_rows_cannot_supply_another_renewal_permit seed claim current paid proposal permit)
  | settled paid needs p g noStop => exact fun impossible => impossible
  | gate issue => exact fun impossible => impossible
  | needs issue => exact fun impossible => impossible
  | residual issue noProgress => exact fun impossible => impossible

variable [DecidableEq Technology]

theorem a_paid_pair_source_generates_only_current_needs_and_original_finite_settlements
    (paid : Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current) :
    Planning.chosen seed claim current = Planning.Menu.needsWord seed claim current ++ Planning.Menu.settlements seed := by
  have plans : Planning.Menu.plans seed claim current =
      [Planning.Menu.needsWord seed claim current ++ Planning.Menu.settlements seed] := if_pos paid
  unfold Planning.chosen
  cases choice : Planning.selection seed claim current with
  | ready word original resources =>
      rw [plans] at original
      exact List.mem_singleton.mp original
  | blocked issues =>
      change (Planning.Menu.plans seed claim current).headD
        (Planning.Menu.needsWord seed claim current ++ Planning.Menu.settlements seed) = _
      rw [plans]
      rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary
