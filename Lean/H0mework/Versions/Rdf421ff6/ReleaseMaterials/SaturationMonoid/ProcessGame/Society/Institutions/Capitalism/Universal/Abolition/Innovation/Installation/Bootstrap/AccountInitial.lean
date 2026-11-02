import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.AccountPrefix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Enactment

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

theorem the_first_actual_public_body_has_no_native_financial_mutation (nature : RequestAt) :
    Native.Payment.NonFinancialInput (firstPublic nature (actualAdmission nature)).start.incoming := by
  have start : (firstPublic nature (actualAdmission nature)).start =
      Physical.receive Physical.initial (.execute Control.Scenario.commonWork) :=
    every_first_admission_starts_the_actual_original_common_work nature (actualAdmission nature)
  have raw := congrArg Physical.Cursor.incoming start
  rw [raw]
  change ∀ request ∈ Control.Scenario.commonWork, Native.Payment.NonFinancial request.operation
  intro request original
  have safe := the_original_common_word_has_no_native_financial_mutation request original
  cases operation : request.operation <;>
    simp_all only [Native.Payment.NonFinancial, Settlement.NonFinancialRequest]

theorem the_first_actual_public_account_is_the_same_original_native_macro_base (nature : RequestAt) :
    (actualPublicVisit nature 0).account = Epoch.Finance.Future.Installed.initial input 0 count 0 count := by
  have drained := Native.Payment.the_actual_nonfinancial_body_keeps_its_entire_original_account
    (firstPublic nature (actualAdmission nature)) (the_first_actual_public_body_has_no_native_financial_mutation nature)
  have original : (firstPublic nature (actualAdmission nature)).account = (closedOriginal nature).account := rfl
  exact drained.trans (original.trans (the_closed_original_account_is_the_same_native_macro_base nature))

theorem the_first_actual_public_slots_are_the_original_pure_financial_cursor (nature : RequestAt) :
    (actualPublicVisit nature 0).account.current.slots =
      (Financial.Installation.Runtime.cursorAt input 0 count).account.current.slots.map
        (Epoch.Finance.Legacy.slot input 0 count) :=
  (congrArg (fun account => account.current.slots)
    (the_first_actual_public_account_is_the_same_original_native_macro_base nature)).trans
    the_original_macro_base_slots_are_the_same_pure_source_financial_cursor

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
