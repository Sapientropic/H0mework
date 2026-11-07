import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualMechanism

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening
noncomputable section

theorem source_parameters :
    source.native.depth = 0 ∧ source.native.count = 19 ∧
      source.native.prefixLimit = 0 ∧ source.native.renewalLimit = 0 ∧ source.native.oldPast = [] := by
  have first := (Root.Runtime.queued base Evolving.Epoch.Consumers.repair).advance_parameters
  have second := (Root.Runtime.afterBody base Evolving.Epoch.Consumers.repair).advance_parameters
  exact ⟨second.2.1.trans first.2.1,second.2.2.1.trans first.2.2.1,
    second.2.2.2.1.trans first.2.2.2.1,second.2.2.2.2.1.trans first.2.2.2.2.1,
    second.2.2.2.2.2.1.trans first.2.2.2.2.2.1⟩

theorem every_original_person_keeps_actual_standing (person : Bool) : person ∈ source.members := by
  have old : person ∈ Abolition.Root.Epoch.Interface.Actors.Census.parties source.native.input
      source.native.depth source.native.count source.native.prefixLimit source.native.renewalLimit
        (Physical.Prefix.cursor source.native.oldPast) := by
    rw [source_input_is_the_original_registered_input,source_parameters.1,source_parameters.2.1,
      source_parameters.2.2.1,source_parameters.2.2.2.1,source_parameters.2.2.2.2]
    cases person <;> decide +kernel
  exact Abolition.Root.Epoch.Interface.Actors.PublicCensus.every_old_member_keeps_current_standing
    _ _ _ _ _ _ _ person old

theorem the_quote_uses_the_original_public_physical_law :
    (Root.sourceInput source).law = PublicFunction.physicalLaw
      Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.law := by
  change (Public.Scope.checkInput source.native.input).law = _
  rw [source_input_is_the_original_registered_input]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
