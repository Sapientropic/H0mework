import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.GeneratedRow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment

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
  (ready : Trigger.ReadyAt context)

abbrev family := (context.data.familyAt context.visit.current context.germ.ready).val
abbrev oldPast := context.germ.snapshot.past
abbrev publicStart := Physical.initial (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
abbrev initial := Macro.Public.Accounting.initial input depth count (context.native.account context.visit.current)
abbrev bodyNext := Macro.Public.Accounting.bodyTarget input depth count (context.native.account context.visit.current)

def baseRoot := Macro.Public.Source.livingRoot input depth count prefixLimit renewalLimit
  (oldPast context) publicStart (family context)


def root := (baseRoot context).withProjectionCoface (originalComponent context ready (baseRoot context))

abbrev firstVisit := (root context ready).toAuthoritativeRoot.toRoot.initialVisit

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    ((root context ready).emitted (initial context))
    ((root context ready).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (initial context)) :=
  Macro.Public.Source.successor input depth count prefixLimit renewalLimit (oldPast context) publicStart (family context)
    (initial context)

theorem first_successor_is_the_actual_public_body :
    (firstSuccessor context ready).targetCurrent = bodyNext context :=
  Macro.Public.Source.successor_current input depth count prefixLimit renewalLimit (oldPast context) publicStart
    (family context) (initial context)

theorem initial_support_is_the_literal_original_current :
    (root context ready).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      ((root context ready).emitted (initial context)) = context.native.sourceSupport context.visit.current :=
  (context.data.familyAt context.visit.current context.germ.ready).property

theorem first_body_keeps_the_complete_original_account :
    (bodyNext context).account = context.native.account context.visit.current := rfl

#print axioms root
#print axioms initial_support_is_the_literal_original_current
#print axioms first_successor_is_the_actual_public_body

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment
