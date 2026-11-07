import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape.History
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape.Actual
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape.Discrepancy

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- A proof about the original evolving source, not a parallel ledger or
an extra registry of allowed escape routes. The source chooses every next. -/
structure AccountedActualHistoryAt : Prop where
  exactRootAndWholeLedger : ∀ n, Evolving.Epoch.Current.ClosedAt (Evolving.Epoch.History.currentAt source n)
  distinctOriginalClaims : ∀ n, Function.Injective (claimAlong source n)
  everyOldRow : ∀ original n,
    type_of% (every_actual_detour_carries_the_exact_original_claim source original n)
  noOriginalRefill : ∀ original n,
    type_of% (no_actual_detour_refills_an_original_responsibility source original n)
  everyRealMaterialFlow : ∀ n party good,
    type_of% (all_real_epoch_supplements_are_in_the_same_full_material_account source n party good)
  everyOriginalFinancialAddress : ∀ n instrument debtor holder,
    type_of% (every_new_epoch_claim_remains_in_the_original_full_financial_matrix source n instrument debtor holder)
  noUnbackedSupplement : ∀ n party good gain,
    type_of% (every_actual_epoch_material_gain_has_an_original_accepted_credit source n party good gain)
  activeNoCapital : ∀ n, Global.NoCapital (Evolving.Epoch.History.currentAt source n).native.handlerFace.rootRead
  regenerationChangesInterpretation : ∀ n claimed raw word capital,
    type_of% (every_regenerated_kernel_locates_its_exact_source_permission_change
      (Evolving.Epoch.History.currentAt source n).native claimed raw word capital)

theorem every_actual_source_route_has_its_complete_original_account : AccountedActualHistoryAt source where
  exactRootAndWholeLedger := all_actual_detours_are_the_original_answer_and_whole_ledger source
  distinctOriginalClaims := all_actual_detours_keep_original_claims_distinct source
  everyOldRow := every_actual_detour_carries_the_exact_original_claim source
  noOriginalRefill := no_actual_detour_refills_an_original_responsibility source
  everyRealMaterialFlow := all_real_epoch_supplements_are_in_the_same_full_material_account source
  everyOriginalFinancialAddress := every_new_epoch_claim_remains_in_the_original_full_financial_matrix source
  noUnbackedSupplement := every_actual_epoch_material_gain_has_an_original_accepted_credit source
  activeNoCapital := fun n => (Evolving.Epoch.History.currentAt source n).native.the_actual_root_interpreter_excludes_every_capital_relation
  regenerationChangesInterpretation := fun n => every_regenerated_kernel_locates_its_exact_source_permission_change
    (Evolving.Epoch.History.currentAt source n).native

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape
