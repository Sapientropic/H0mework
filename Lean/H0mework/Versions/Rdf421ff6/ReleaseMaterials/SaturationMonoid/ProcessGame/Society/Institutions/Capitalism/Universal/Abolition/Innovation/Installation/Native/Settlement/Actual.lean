import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.AccountInitial

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

private theorem the_initial_source_prefix_preserves_the_original_base (nature : RequestAt) :
    Epoch.Finance.PublicPast.account input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
      (actualPublicVisit nature 0).snapshot.past
      (Epoch.Finance.Future.Installed.initial input 0 count 0 count) =
        Epoch.Finance.Future.Installed.initial input 0 count 0 count := by
  have sourcePast : (actualPublicVisit nature 0).snapshot.past = [.execute Control.Scenario.commonWork] :=
    congrArg Physical.Cursor.past (the_first_actual_public_visit_keeps_the_literal_source_body nature)
  have original := congrArg (fun past : List InputAt => Epoch.Finance.PublicPast.account input 0 count 0 0
    (firstOrigin nature).germ.snapshot.past past (Epoch.Finance.Future.Installed.initial input 0 count 0 count)) sourcePast
  refine original.trans ?_
  change Epoch.Finance.consumeVisit input 0 count
    (Macro.Public.Accounting.tag input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
      (Physical.receive Physical.initial (.execute Control.Scenario.commonWork)))
    (Macro.Public.Accounting.visit input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
      (Physical.receive Physical.initial (.execute Control.Scenario.commonWork)))
    (Epoch.Finance.Future.Installed.initial input 0 count 0 count) = _
  apply the_nonfinancial_public_event_keeps_the_same_original_account
  intro request original
  have safe := the_original_common_word_has_no_native_financial_mutation request original
  cases operation : request.operation <;>
    simp_all only [Payment.NonFinancial,Abolition.Root.Settlement.NonFinancialRequest]

theorem every_actual_public_visit_is_its_original_source_account (nature : RequestAt) (index : Nat) :
    (actualPublicVisit nature index).account =
      Epoch.Finance.PublicPast.account input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
        (actualPublicVisit nature index).snapshot.past
        (Epoch.Finance.Future.Installed.initial input 0 count 0 count) := by
  induction index with
  | zero =>
      exact (the_first_actual_public_account_is_the_same_original_native_macro_base nature).trans
        (the_initial_source_prefix_preserves_the_original_base nature).symm
  | succ index inherited =>
      let frame := actualPublicVisit nature index
      have step := a_real_public_step_has_its_same_original_prefix_and_account frame
        (every_public_visit_is_ready_at_its_original_raw_boundary nature (actualAdmission nature) index)
      have account := congrArg (fun before => Epoch.Finance.consumeVisit input 0 count
        (Epoch.Interface.Actors.PublicPast.eventTag input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
          frame.snapshot.past frame.next.start.incoming)
        (Epoch.Interface.Actors.PublicPast.eventVisit input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
          frame.snapshot.past frame.next.start.incoming) before) inherited
      have appended := the_original_public_account_appends_its_same_event
        (input := input) (depth := 0) (count := count) (prefixLimit := 0) (renewalLimit := 0)
        (firstOrigin nature).germ.snapshot.past frame.snapshot.past frame.next.start.incoming
        (Epoch.Finance.Future.Installed.initial input 0 count 0 count)
      have actualPast := congrArg (fun past : List InputAt => Epoch.Finance.PublicPast.account input 0 count 0 0
        (firstOrigin nature).germ.snapshot.past past
        (Epoch.Finance.Future.Installed.initial input 0 count 0 count)) step.1
      exact step.2.trans (account.trans (appended.symm.trans actualPast.symm))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement
