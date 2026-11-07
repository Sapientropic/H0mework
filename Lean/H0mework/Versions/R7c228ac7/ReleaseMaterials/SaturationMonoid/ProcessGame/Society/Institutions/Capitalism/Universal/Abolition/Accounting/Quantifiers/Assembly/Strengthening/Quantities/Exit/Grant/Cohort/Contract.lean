import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Domain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction PublicFunction.Repayment
open Redemption (sourceLaw)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Proposal" => Plan Party Good Port Technology Instrument

/-- The vector records the actual gross tender credit of every member and
material unit. Issuance, unpaid offers and later allocations are separate. -/
def tenderAmounts (source : C) (plan : Proposal) (address : Party × Good) : EReal :=
  let origin := fundingStart source plan
  ((((sourceLaw origin).totalCredit (Execution.inventory origin (allTenders source plan))
    address.1 address.2 : ℚ) : ℝ) : EReal)

def checkPopulation (source : C) (task : PublicTaskSpec Party Good) (count : Nat) (_ : Unit) (plan : Proposal) :
    Option (Issue source task count plan) := inspect source task count plan

theorem exact_simultaneous_population_amounts
    (source : C) (task : PublicTaskSpec Party Good) (count : Nat) (profile : Party × Good → EReal) :
    profile ∈ Bounds.System.values source (compile source count) (checkPopulation source task count) (tenderAmounts source) ↔
      ∃ plan, Settled source (compile source count plan) ∧ Actionable source task count plan ∧
        tenderAmounts source plan = profile := by
  rw [Bounds.System.an_assignment_is_in_the_joint_domain_exactly_when_the_original_root_pays_it]
  have check (plan : Proposal) : Bounds.System.Passes (checkPopulation source task count) plan ↔
      Actionable source task count plan := by
    constructor
    · intro checked
      exact (inspection_is_exact_for_the_original_population source task count plan).mp (checked ())
    · intro actual _
      exact (inspection_is_exact_for_the_original_population source task count plan).mpr actual
  simp only [check]

/-- The selected population allocation or each exact obstruction belongs
to the same source and all original members. -/
def decidePopulation (source : C) (task : PublicTaskSpec Party Good) (count : Nat)
    (limit : Party × Good → EReal) :
    Bounds.System.BoxDecision source (compile source count) (checkPopulation source task count) (tenderAmounts source) limit :=
  Bounds.System.decideBox _ _ _ _ _

theorem the_paid_population_exit_uses_the_literal_original_successor
    (source : C) (count : Nat) (plan : Proposal) :
    Execution.endAt source (compile source count plan) =
      Execution.endAt (exitStart source count plan) plan.exit :=
  Execution.endAt_append _ _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort
