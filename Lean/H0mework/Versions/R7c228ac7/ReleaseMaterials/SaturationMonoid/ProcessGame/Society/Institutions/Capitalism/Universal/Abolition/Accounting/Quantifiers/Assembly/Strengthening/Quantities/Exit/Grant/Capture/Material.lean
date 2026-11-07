import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Material

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Capture

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction.Repayment
open Redemption (sourceLaw sourceOrigin rate unit essentials)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Plan" => Proposal Party Good Port Technology Instrument
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- Charge and credit are measured only by the original execution inventory.
A quote or an unpaid bill never enters the debit side of this difference. -/
def netTaken (source : C) (script : Script) (bearer : Party) (good : Good) : ℚ :=
  let law := sourceLaw source
  let items := Execution.inventory source script
  law.totalDebit items bearer good - law.totalCredit items bearer good

def essentialUnit (source : C) (position : Position Party Instrument) : ℚ :=
  essentials (sourceLaw source) (sourceOrigin source) position.creditor (unit (sourceLaw source) position)

def survivalFloor (source : C) (position : Position Party Instrument) (plan : Plan) (charges : Script) : ℚ :=
  let front := funded source plan
  let good := unit (sourceLaw front) position
  max 0 (essentialUnit front position - front.raw.stock position.creditor good +
    netTaken (redeemed source position plan) charges position.creditor good) /
    rate (sourceLaw front) position

theorem after_original_charges_stock_is_the_real_net_receipt
    (source : C) (position : Position Party Instrument) (plan : Plan) (charges : Script)
    (paid : PaidAt (funded source plan) position plan.quantity) :
    let front := funded source plan
    let good := unit (sourceLaw front) position
    (Execution.endAt (redeemed source position plan) charges).raw.stock position.creditor good =
      front.raw.stock position.creditor good + actualMaterial source position plan -
        netTaken (redeemed source position plan) charges position.creditor good := by
  dsimp only
  let front := funded source plan
  let good := unit (sourceLaw front) position
  let received := redeemed source position plan
  have material := material_amount_is_literal_received_stock source position plan paid
  have cash := (record received charges).actualBalance position.creditor good
  change (Execution.endAt received charges).raw.stock position.creditor good +
    (sourceLaw received).totalDebit (Execution.inventory received charges) position.creditor good =
    received.raw.stock position.creditor good +
      (sourceLaw received).totalCredit (Execution.inventory received charges) position.creditor good at cash
  change received.raw.stock position.creditor good =
    front.raw.stock position.creditor good + actualMaterial source position plan at material
  rw [material] at cash
  unfold netTaken
  linarith only [cash]

/-- This is the exact same-unit condition at the chosen actual charge cut.
It includes positive production or new delivery in that prefix when present. -/
theorem the_charged_grant_covers_its_original_need_iff_the_actual_floor_is_met
    (source : C) (position : Position Party Instrument) (plan : Plan) (charges : Script)
    (paid : PaidAt (funded source plan) position plan.quantity) :
    let front := funded source plan
    essentialUnit front position ≤
      (Execution.endAt (redeemed source position plan) charges).raw.stock position.creditor
        (unit (sourceLaw front) position) ↔ survivalFloor source position plan charges ≤ plan.quantity := by
  dsimp only
  rw [after_original_charges_stock_is_the_real_net_receipt source position plan charges paid]
  let front := funded source plan
  have priced := (every_grant_is_exactly_checked_at_its_source_floor_and_stock_ceiling
    (sourceLaw front) (sourceOrigin front) front.raw position plan.quantity).mp paid.qualified
  have positive : 0 < rate (sourceLaw front) position := priced.2.2.1
  have quantity : 0 ≤ plan.quantity := paid.qualified.1.2.2.1
  unfold survivalFloor actualMaterial
  rw [div_le_iff₀ positive, max_le_iff]
  constructor
  · intro enough
    exact ⟨mul_nonneg quantity positive.le, by linarith only [enough]⟩
  · rintro ⟨_, enough⟩
    linarith only [enough]

theorem an_actual_charge_shortage_keeps_the_original_recipient_and_next_account
    (source : C) (position : Position Party Instrument) (plan : Plan) (charges : Script)
    (paid : PaidAt (funded source plan) position plan.quantity)
    (tooSmall : plan.quantity < survivalFloor source position plan charges) :
    let front := funded source plan
    (Execution.endAt (redeemed source position plan) charges).raw.stock position.creditor
      (unit (sourceLaw front) position) < essentialUnit front position ∧
      Recorded source (plan.preparation ++ grantScript front position plan.quantity ++ charges) := by
  dsimp only
  exact ⟨lt_of_not_ge (fun enough => (not_le_of_gt tooSmall)
    ((the_charged_grant_covers_its_original_need_iff_the_actual_floor_is_met source position plan charges paid).mp enough)),
    record source _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Capture
