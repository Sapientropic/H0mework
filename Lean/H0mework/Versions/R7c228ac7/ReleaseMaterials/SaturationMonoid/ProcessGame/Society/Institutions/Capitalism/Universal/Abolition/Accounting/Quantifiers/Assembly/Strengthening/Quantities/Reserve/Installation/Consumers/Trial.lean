import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation.Consumers.Preparation

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation.Consumers

open Source.Program PublicFunction.Financing
open Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Innovation.Installation

noncomputable section

abbrev investment := quotedMechanism.investmentRequest
abbrev natureRevision (version : Nat) :=
  (Innovation.Control.Scenario.discovery version).resign
    (Innovation.Control.Scenario.discovery version).signer

private theorem actual_checks (raw : Raw) (original : raw ∈ firstRawVariants)
    (paid : Disbursement law (commonBefore raw).raw [issue, payout] terms)
    (read : some paid = receipt? raw) :
    floorShare paid [investment] = 0 ∧ law.Valid (retaining paid 1) investment ∧
      flowAt (law.actualDebit (retaining paid 1) investment) 0 .material = 3 ∧
      floorShare paid [investment, natureRevision 1] =
        max 0 (4 - (reserveBaseline paid).stock 0 .material) / 6 := by
  let check (raw : Raw) :=
    match receipt? raw with
    | none => false
    | some loan => decide (floorShare loan [investment] = 0 ∧ law.Valid (retaining loan 1) investment ∧
        flowAt (law.actualDebit (retaining loan 1) investment) 0 .material = 3 ∧
        floorShare loan [investment, natureRevision 1] =
          max 0 (4 - (reserveBaseline loan).stock 0 .material) / 6)
  have allOriginal : firstRawVariants.all check = true := by
    decide +kernel
  have applies := List.all_eq_true.mp allOriginal raw original
  have result : check raw = _ := applies
  unfold check at result
  rw [← read] at result
  exact of_decide_eq_true result

private theorem measured_on_the_original_cut (nature : RequestAt) :
    floorShare (originalReceipt nature) [investment] = 0 ∧
      law.Valid (retaining (originalReceipt nature) 1) investment ∧
      flowAt (law.actualDebit (retaining (originalReceipt nature) 1) investment) 0 .material = 3 ∧
      floorShare (originalReceipt nature) [investment, natureRevision 1] =
        max 0 (4 - (reserveBaseline (originalReceipt nature)).stock 0 .material) / 6 :=
  actual_checks (originalRaw nature) (originalRaw_mem nature) (originalReceipt nature)
    (Option.some_get _)

theorem the_original_preparation_has_distinct_paid_usage_and_tight_holdback (nature : RequestAt) :
    flowAt (law.actualDebit (actualCut nature 2) investment) 0 .material /
      funds (originalReceipt nature) = 1 / 2 ∧
    floorShare (originalReceipt nature) [investment] = 0 ∧
    floorShare (originalReceipt nature) [investment, natureRevision 1] =
      max 0 (4 - (reserveBaseline (originalReceipt nature)).stock 0 .material) / 6 := by
  obtain ⟨floor, legal, debit, nextFloor⟩ := measured_on_the_original_cut nature
  refine ⟨?_, floor, nextFloor⟩
  rw [the_full_retention_is_the_original_actual_payout_cut, debit,
    (the_signed_loan_preserves_its_original_principal_and_delivers_six nature).2.2]
  norm_num

theorem the_same_original_root_pays_the_installation_and_carries_the_financing
    (nature : RequestAt) :
    actualCut nature 3 = law.step (actualCut nature 2) investment ∧
      (actualPublicVisit nature 2).account.current.history <+:
        (actualPublicVisit nature 3).account.current.history ∧
      (actualPublicVisit nature 2).account.current.slots.map (Epoch.Finance.slotClaim input 0 count) <+:
        (actualPublicVisit nature 3).account.current.slots.map (Epoch.Finance.slotClaim input 0 count) := by
  have account := every_trial_visit_keeps_the_same_whole_native_history nature (actualAdmission nature) 2
  have accepted := (the_full_retention_is_the_original_actual_payout_cut nature).symm ▸
    (measured_on_the_original_cut nature).2.1
  refine ⟨?_, account.1, account.2⟩
  rw [actualCut_prefix nature 3 (by decide), actualCut_prefix nature 2 (by decide),
    the_pre_read_source_inventory_is_the_original_five_requests]
  rw [actualCut_prefix nature 2 (by decide), the_pre_read_source_inventory_is_the_original_five_requests] at accepted
  let before := Physical.Public.stateAt input 0 count 0 0 (oldPast nature)
    [.execute commonWork, .primitive issue, .primitive payout]
  change (Physical.Public.compile input before (.primitive investment)).next.raw = law.step before.raw investment
  exact a_checked_primitive_is_its_raw_step before investment rfl accepted

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation.Consumers
