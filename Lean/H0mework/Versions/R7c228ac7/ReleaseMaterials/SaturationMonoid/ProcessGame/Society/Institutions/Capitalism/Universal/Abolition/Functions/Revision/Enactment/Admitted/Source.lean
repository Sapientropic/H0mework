import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Origin
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Frame.Ordinary
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Component
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.GeneratedRow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (context : Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (admission : InitialAdmissionAt context)

abbrev family := (context.data.familyAt context.visit.current context.germ.ready).val
abbrev oldPast := context.germ.snapshot.past
abbrev initial := Macro.Public.Accounting.initial input depth count (context.native.account context.visit.current)
abbrev bodyNext := Macro.Public.Accounting.bodyTarget input depth count (context.native.account context.visit.current)

def bareFrame :=
  let base := Macro.Public.Frame.ordinary input depth count prefixLimit renewalLimit (oldPast context)
    (InitialAdmission.start admission) (family context)
  base.withProjectionCoface (InitialAdmission.originalComponent context admission base.root)

def frame := Macro.Public.Inquiry.installedFrame (bareFrame context admission) (InitialAdmission.reader admission)
abbrev root := (frame context admission).root
abbrev firstVisit := (root context admission).toAuthoritativeRoot.toRoot.initialVisit

def firstSuccessor := (frame context admission).successor (initial context)

theorem first_successor_is_the_actual_public_body :
    (firstSuccessor context admission).targetCurrent = bodyNext context :=
  Macro.Public.Source.successor_current input depth count prefixLimit renewalLimit (oldPast context)
    (InitialAdmission.start admission) (family context) (initial context)

theorem initial_support_is_the_literal_original_current :
    (root context admission).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      ((root context admission).emitted (initial context)) = context.native.sourceSupport context.visit.current :=
  (context.data.familyAt context.visit.current context.germ.ready).property

theorem first_body_keeps_the_complete_original_account :
    (bodyNext context).account = context.native.account context.visit.current := rfl

#print axioms root
#print axioms first_successor_is_the_actual_public_body
#print axioms initial_support_is_the_literal_original_current

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted
