import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.NoRetake

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
  (claim : Entitlement.Source.Claim (window seed))

def Admitted (current : Current seed claim) (proposal : RawEvent Party Good Port Technology Instrument) : Prop :=
  RequestedRenewalAuthorityAt seed claim current proposal (verdict seed claim current proposal)

theorem source_admitted_next_strictly_decreases_the_original_unpaid_count
    (current : Current seed claim) (proposal : RawEvent Party Good Port Technology Instrument)
    (admitted : Admitted seed claim current proposal) :
    budget seed claim (next seed claim current proposal) < budget seed claim current := by
  unfold Admitted at admitted
  cases decision : verdict seed claim current proposal with
  | admitted permit => exact permit.strictProgress
  | settled paid needs p g noStop => simp only [decision,RequestedRenewalAuthorityAt] at admitted
  | gate issue => simp only [decision,RequestedRenewalAuthorityAt] at admitted
  | needs issue => simp only [decision,RequestedRenewalAuthorityAt] at admitted
  | residual issue noProgress => simp only [decision,RequestedRenewalAuthorityAt] at admitted

def afterInputs (current : Current seed claim) : List (RawEvent Party Good Port Technology Instrument) → Current seed claim
  | [] => current
  | proposal :: rest => afterInputs (next seed claim current proposal) rest

def AllAdmitted (current : Current seed claim) : List (RawEvent Party Good Port Technology Instrument) → Prop
  | [] => True
  | proposal :: rest => Admitted seed claim current proposal ∧ AllAdmitted (next seed claim current proposal) rest

theorem the_actual_original_unpaid_count_bounds_every_admitted_continuation
    (current : Current seed claim) (inputs : List (RawEvent Party Good Port Technology Instrument))
    (admitted : AllAdmitted seed claim current inputs) :
    inputs.length + budget seed claim (afterInputs seed claim current inputs) ≤ budget seed claim current := by
  induction inputs generalizing current with
  | nil => simp only [List.length_nil,afterInputs,Nat.zero_add,Nat.le_refl]
  | cons proposal rest inherited =>
      have strict := source_admitted_next_strictly_decreases_the_original_unpaid_count seed claim current proposal admitted.1
      have later := inherited (next seed claim current proposal) admitted.2
      simp only [List.length_cons,afterInputs]
      omega

theorem only_the_original_number_of_unpaid_cells_can_buy_old_row_renewals
    (current : Current seed claim) (inputs : List (RawEvent Party Good Port Technology Instrument))
    (admitted : AllAdmitted seed claim current inputs) : inputs.length ≤ budget seed claim current := by
  have complete := the_actual_original_unpaid_count_bounds_every_admitted_continuation seed claim current inputs admitted
  omega

theorem exhausting_the_old_row_count_pays_both_original_rows
    (current : Current seed claim) (inputs : List (RawEvent Party Good Port Technology Instrument))
    (admitted : AllAdmitted seed claim current inputs) (exhausted : inputs.length = budget seed claim current) :
    Current.productivePaid seed claim (afterInputs seed claim current inputs) ∧
      Current.grossPaid seed claim (afterInputs seed claim current inputs) := by
  have complete := the_actual_original_unpaid_count_bounds_every_admitted_continuation seed claim current inputs admitted
  apply (zero_budget_iff_both_original_rows_are_paid seed claim _).mp
  omega

def AdmittedContinuation (after before : Current seed claim) : Prop :=
  ∃ proposal, after = next seed claim before proposal ∧ Admitted seed claim before proposal

theorem old_row_admitted_continuation_is_well_founded : WellFounded (AdmittedContinuation seed claim) := by
  apply (measure (budget seed claim)).wf.mono
  rintro after before ⟨proposal,rfl,admitted⟩
  exact source_admitted_next_strictly_decreases_the_original_unpaid_count seed claim before proposal admitted

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary
