import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (snapshot : Physical.Cursor Party Good Port Technology Instrument)
  (request : Request Party Good Port Technology Instrument)
  (noConsents : request.consents = [])
  (valid : (Physical.Public.interpreter input).Valid
    (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast snapshot.past).raw request)

include noConsents valid

theorem the_primitive_body_owns_exactly_its_original_one_item :
    (Public.Accounting.items input depth count prefixLimit renewalLimit oldPast
      (Physical.receive snapshot (.primitive request))).map (Epoch.Finance.ActualItem.instruction input depth count) =
      [⟨0,(Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast snapshot.past).raw,request⟩] :=
  (Public.Accounting.actual_items_are_the_same_public_execution input depth count prefixLimit renewalLimit oldPast _).trans
    (Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.one_checked_original_primitive_has_one_actual_material_step
      input (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast snapshot.past) request noConsents valid).2.1

theorem the_primitive_body_has_exactly_one_financial_position :
    (Public.Accounting.items input depth count prefixLimit renewalLimit oldPast
      (Physical.receive snapshot (.primitive request))).length = 1 := by
  have length := congrArg List.length
    (the_primitive_body_owns_exactly_its_original_one_item input depth count prefixLimit renewalLimit oldPast snapshot request noConsents valid)
  simpa only [List.length_map,List.length_cons,List.length_nil] using length

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing
