import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Society
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Consumers.Canonical

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Consumers

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Registered Source.Program Source.ProgrammeControl
open Source.ProgrammeControl.Kernel.AssetAuthority
open M14SourceGeneratedContributionMergeActionSource

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

def HasOriginalSocietyContract (input : ProgrammeSource.Input Party Good Port Technology Instrument) : Prop :=
  ∀ (oldVisit : OldVisit) (sourceIndex boundary sourceStart : Nat)
    (datum : Macro.Ingress.Datum input 1 sourceStart) (prefixLimit renewalLimit : Nat)
    (reader : Macro.Raw.Reader input 1 (Macro.Ingress.cut input 1 sourceStart)),
    ∃ registered, SocietyCapitalLawAt input registered oldVisit sourceIndex boundary sourceStart datum
      prefixLimit renewalLimit reader none

theorem original_unified_control_is_consumed_by_the_same_society_contract
    (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (visit : RootFace.Visit input) (nonempty : Structural.Consumers.Canonical.controls input visit ≠ []) :
    HasOriginalSocietyContract input := by
  intro oldVisit sourceIndex boundary sourceStart datum prefixLimit renewalLimit reader
  exact every_original_control_form_has_the_same_society_termination_contract
    oldVisit sourceIndex boundary sourceStart datum prefixLimit renewalLimit reader none visit
    ((Structural.Consumers.Canonical.controls input visit).head nonempty)

open Structural.Consumers.Canonical

theorem six_actual_capital_forms_enter_the_single_society_abolition_mouth :
    HasOriginalSocietyContract Industrial.input ∧ HasOriginalSocietyContract Care.input ∧
      HasOriginalSocietyContract Finance.input ∧ HasOriginalSocietyContract Platform.input ∧
      HasOriginalSocietyContract Automation.input ∧ HasOriginalSocietyContract StateCapital.input :=
  ⟨original_unified_control_is_consumed_by_the_same_society_contract
      Industrial.input Industrial.visit Industrial.actual_first_root_control,
    original_unified_control_is_consumed_by_the_same_society_contract Care.input Care.visit Care.actual_first_root_control,
    original_unified_control_is_consumed_by_the_same_society_contract Finance.input Finance.visit Finance.actual_first_root_control,
    original_unified_control_is_consumed_by_the_same_society_contract Platform.input Platform.visit Platform.actual_first_root_control,
    original_unified_control_is_consumed_by_the_same_society_contract Automation.input Automation.visit Automation.actual_first_root_control,
    original_unified_control_is_consumed_by_the_same_society_contract StateCapital.input StateCapital.visit StateCapital.actual_first_root_control⟩

theorem cooperation_redemption_and_self_supply_are_not_relabelled_as_capital :
    Structural.Consumers.Canonical.controls Common.input Common.visit = [] ∧
      Structural.Consumers.Canonical.controls UBI.input UBI.visit = [] ∧
      Structural.Consumers.Canonical.controls SelfSupply.input SelfSupply.visit = [] :=
  ⟨Common.actual_first_root_has_no_control, UBI.actual_first_root_has_no_control, SelfSupply.actual_first_root_has_no_control⟩

#print axioms original_unified_control_is_consumed_by_the_same_society_contract
#print axioms six_actual_capital_forms_enter_the_single_society_abolition_mouth
#print axioms cooperation_redemption_and_self_supply_are_not_relabelled_as_capital

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Consumers
