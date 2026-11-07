import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Inspection
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Compiled
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction PublicFunction.Repayment
open Redemption (sourceLaw sourceOrigin rate unit)
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Plan" => Proposal Party Good Port Technology Instrument

def actualMaterial (source : C) (position : Position Party Instrument) (plan : Plan) : ℚ :=
  plan.quantity * rate (sourceLaw (funded source plan)) position

theorem material_amount_is_literal_received_stock
    (source : C) (position : Position Party Instrument) (plan : Plan)
    (actual : PaidAt (funded source plan) position plan.quantity) :
    (redeemed source position plan).raw.stock position.creditor (unit (sourceLaw (funded source plan)) position) =
      (funded source plan).raw.stock position.creditor (unit (sourceLaw (funded source plan)) position) +
        actualMaterial source position plan := by
  let front := funded source plan
  let law := sourceLaw front
  let issued := law.step front.raw (issue law position plan.quantity)
  have sameRaw := actual.actual.raw_is_the_complete_original_execution 0
  change (redeemed source position plan).raw = law.step issued (Redemption.request law position plan.quantity) at sameRaw
  rw [sameRaw]
  have receipt := Redemption.paid_leg_moves_original_stock_and_claim law issued position plan.quantity
    actual.qualified.2.1 actual.qualified.2.2.1
  unfold Redemption.creditorStock at receipt
  rw [issue_keeps_all_real_stock law front.raw position plan.quantity] at receipt
  exact receipt.1

structure Completed (source : C) (position : Position Party Instrument) (excluded : List Party)
    (task : PublicTaskSpec Party Good) (plan : Plan) : Prop where
  root : Settled source (compile source position plan)
  eligible : Eligible source position excluded task plan
  grant : PaidAt (funded source plan) position plan.quantity
  actualNext : Execution.endAt source (compile source position plan) =
    Execution.endAt (redeemed source position plan) plan.continuation

theorem complete_iff_original_paid_and_eligible
    (source : C) (position : Position Party Instrument) (excluded : List Party)
    (task : PublicTaskSpec Party Good) (plan : Plan) :
    Completed source position excluded task plan ↔
      Settled source (compile source position plan) ∧ inspectPlan source position excluded task plan = none := by
  constructor
  · intro paid
    exact ⟨paid.root, (inspect_passes_iff_funded_and_independently_served _ _ _ _ _).mpr paid.eligible⟩
  · rintro ⟨whole, passed⟩
    have eligible := (inspect_passes_iff_funded_and_independently_served _ _ _ _ _).mp passed
    exact ⟨whole, eligible,
      paid_grant_is_the_literal_original_issue_and_redemption _ _ _ eligible.native eligible.review eligible.grant,
      the_grant_and_its_continuation_share_the_actual_next source position plan⟩

def principal (plan : Plan) : EReal := ((plan.quantity : ℝ) : EReal)

theorem exact_joint_grant_domain (source : C) (position : Position Party Instrument) (excluded : List Party)
    (task : PublicTaskSpec Party Good) (amount : EReal) :
    amount ∈ Bounds.Compiled.values source (compile source position) (inspectPlan source position excluded task) principal ↔
      ∃ plan, Completed source position excluded task plan ∧ principal plan = amount := by
  constructor
  · rintro ⟨plan, root, passed, same⟩
    exact ⟨plan, (complete_iff_original_paid_and_eligible _ _ _ _ _).mpr ⟨root, passed⟩, same⟩
  · rintro ⟨plan, complete, same⟩
    obtain ⟨root, passed⟩ := (complete_iff_original_paid_and_eligible _ _ _ _ _).mp complete
    exact ⟨plan, root, passed, same⟩

theorem the_original_root_resolves_its_joint_grant_amounts
    (source : C) (position : Position Party Instrument) (excluded : List Party) (task : PublicTaskSpec Party Good) :
    Bounds.Compiled.Minimum source (compile source position) (inspectPlan source position excluded task) principal :=
  Bounds.Compiled.resolve _ _ _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant
