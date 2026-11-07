import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Contract

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction.Repayment
open Redemption (sourceLaw unit)
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Plan" => Proposal Party Good Port Technology Instrument

theorem the_paid_grant_preserves_every_other_material_unit
    (source : C) (position : Position Party Instrument) (plan : Plan)
    (actual : PaidAt (funded source plan) position plan.quantity)
    (bearer : Party) (good : Good) (other : good ≠ unit (sourceLaw (funded source plan)) position) :
    (redeemed source position plan).raw.stock bearer good = (funded source plan).raw.stock bearer good := by
  let front := funded source plan
  let law := sourceLaw front
  let issued := law.step front.raw (issue law position plan.quantity)
  have same := actual.actual.raw_is_the_complete_original_execution 0
  change (redeemed source position plan).raw = law.step issued (Redemption.request law position plan.quantity) at same
  have paid : law.Valid issued (Redemption.request law position plan.quantity) := actual.qualified.2.2.1
  rw [same, RawLaw.step, if_pos paid]
  change issued.stock bearer good -
      flowAt (law.debit issued (Redemption.request law position plan.quantity)) bearer good +
      flowAt (law.credit issued (Redemption.request law position plan.quantity)) bearer good = _
  have distinct : law.settlementUnit position.instrument ≠ good := Ne.symm other
  have debit : flowAt (law.debit issued (Redemption.request law position plan.quantity)) bearer good = 0 := by
    simp [RawLaw.debit, Redemption.request, locate, flowAt, amount, distinct]
  have credit : flowAt (law.credit issued (Redemption.request law position plan.quantity)) bearer good = 0 := by
    simp [RawLaw.credit, Redemption.request, locate, flowAt, amount, distinct]
  rw [debit, credit, sub_zero, add_zero]
  exact congrFun (congrFun (issue_keeps_all_real_stock law front.raw position plan.quantity) bearer) good

theorem the_issued_amount_is_the_same_real_debit_of_its_original_payer
    (source : C) (position : Position Party Instrument) (plan : Plan)
    (actual : PaidAt (funded source plan) position plan.quantity) :
    (redeemed source position plan).raw.stock position.debtor (unit (sourceLaw (funded source plan)) position) =
      (funded source plan).raw.stock position.debtor (unit (sourceLaw (funded source plan)) position) -
        actualMaterial source position plan := by
  let front := funded source plan
  let law := sourceLaw front
  let issued := law.step front.raw (issue law position plan.quantity)
  have sameRaw := actual.actual.raw_is_the_complete_original_execution 0
  change (redeemed source position plan).raw = law.step issued (Redemption.request law position plan.quantity) at sameRaw
  have receipt := (Redemption.paid_leg_moves_original_stock_and_claim law issued position plan.quantity
    actual.qualified.2.1 actual.qualified.2.2.1).2.1
  unfold Redemption.debtorStock at receipt
  rw [issue_keeps_all_real_stock law front.raw position plan.quantity] at receipt
  exact (congrArg (fun raw => raw.stock position.debtor (unit law position)) sameRaw).trans receipt

theorem the_paid_grant_microsteps_keep_the_real_clock
    (source : C) (position : Position Party Instrument) (plan : Plan)
    (actual : PaidAt (funded source plan) position plan.quantity) :
    (redeemed source position plan).raw.clock = (funded source plan).raw.clock := by
  change (Execution.endAt (funded source plan) (grantScript (funded source plan) position plan.quantity)).raw.clock = _
  rw [actual.actual.raw_is_the_complete_original_execution 0]
  exact (Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.a_whole_instruction_word_preserves_the_clock_until_the_period_boundary
    (sourceLaw (funded source plan)) (funded source plan).raw 0 _).1

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant
