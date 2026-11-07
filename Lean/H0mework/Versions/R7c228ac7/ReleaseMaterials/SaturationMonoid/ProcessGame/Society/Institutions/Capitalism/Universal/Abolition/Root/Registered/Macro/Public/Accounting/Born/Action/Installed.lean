import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.CanonicalEntry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private theorem cast_entry_key {N : WorldRelationNetwork} {left right : N.Support}
    (same : left = right) (entry : OpenResponsibilityAt N left) :
    (same ▸ entry : OpenResponsibilityAt N right).1 = entry.1 := by
  cases same
  rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (actual : Accounting.Current input depth count frame.anchor)
  (aligned : frame.cursor visit.current = some actual)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start actual)
  (reader : Macro.Raw.Reader input depth count)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))
  (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot visit)

local notation "targetFrame₀" => completeFrame frame visit actual registered reader
local notation "initial" => Source.initialVisit frame.family actual registered
def completeGenerated := SourceNativeDebtAdmissionActualActionProgramAt.generate
  (completeProgram frame visit actual aligned registered reader authority) event

local notation "selected" => completeGenerated frame visit actual aligned registered reader authority event

theorem complete_initial_row_is_the_same_installed_row :
    (selected).target.translatedSourceEntry = (targetFrame₀).entry (initial).current := by
  rw [event.eq_generated]
  apply Financial.Installation.entry_eq_of_key _ _
  · let chosen := completeGenerated frame visit actual aligned registered reader authority
      (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit)
    have key := cast_entry_key chosen.target.initialSupport_eq.symm
      (oldEntry (law := chosen.target.law) (state? := some chosen.target.sourceState)
        (frame.entry visit.current))
    exact key.trans (congrArg Sum.inl (frame.family.entry_key
      (frame.sourceSupport visit.current) (oldSupport frame.family actual)))
  · exact (family frame.family actual registered).open_fibres _

def completeInitialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (targetFrame₀).root initial ((targetFrame₀).entry (initial).current) := by
  exact complete_initial_row_is_the_same_installed_row frame visit actual aligned registered reader authority
      (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit) ▸
    ((completeProgram frame visit actual aligned registered reader authority).generate
      (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit)).target.initialAuthority

def completeNextVisit := Source.firstVisit frame.family actual registered

def completeNextAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (targetFrame₀).root (completeNextVisit frame actual registered)
      ((targetFrame₀).entry (completeNextVisit frame actual registered).current) :=
  nextAuthorityForInstalledEntry (targetFrame₀) initial
    (completeInitialAuthority frame visit actual aligned registered reader authority)

theorem the_complete_next_keeps_the_literal_consumed_head :
    (targetFrame₀).cursor (completeNextVisit frame actual registered).current = some registered.next :=
  Source.first_visit_is_the_literal_registered_next frame.family actual registered

#print axioms complete_initial_row_is_the_same_installed_row
#print axioms completeInitialAuthority
#print axioms completeNextAuthority

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action
