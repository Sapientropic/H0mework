import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate.Readback
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate.Liability
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Consumers.UBI

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate.Consumers

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Instances.UBI (law)
open Redemption.Consumers (originalInput originalVisit redemptionCut position
  the_measured_leg_is_the_original_ubi_root_instruction the_actual_ubi_leg_attains_the_source_bounds)

noncomputable section

def measured := movement law position redemptionCut (law.step redemptionCut (request law position 1))

theorem the_actual_ubi_debit_and_credit_recover_the_same_original_rate :
    (law.rawItems (ProgrammeSource.rawCurrent originalInput originalVisit.current)
      (ProgrammeSource.rawEvent originalInput originalVisit.current))[2]? =
        some ⟨2, redemptionCut, request law position 1⟩ ∧
      measured.rate? = some 1 ∧ (∀ conversion, measured.reconciles conversion ↔ conversion = 1) := by
  have accepted := the_actual_ubi_leg_attains_the_source_bounds.2.2.1
  have identified := positive_paid_principal_identifies_one_rate_for_both_original_bearers
    law position redemptionCut 1 accepted.1 accepted.2.1 (by decide)
  exact ⟨the_measured_leg_is_the_original_ubi_root_instruction, identified⟩

theorem a_doubled_quote_does_not_reconcile_the_original_ubi_payment :
    ¬ measured.reconciles 2 := by
  intro quote
  have inconsistent := (the_actual_ubi_debit_and_credit_recover_the_same_original_rate.2.2 2).mp quote
  norm_num at inconsistent

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate.Consumers
