import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.NativeFrame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (entry : OpenResponsibilityAt frame.N (frame.sourceSupport visit.current))
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit entry)

def nextVisit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot :=
  visit.next (frame.successor visit.current).next_eq

def nextEntry : OpenResponsibilityAt frame.N (frame.sourceSupport (nextVisit frame visit).current) :=
  frame.root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
    (frame.successor visit.current).next_eq entry

/-- Keep the compiler-generated row and its sealed history together.
There is no target-side election of a replacement responsibility. -/
def nextAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root (nextVisit frame visit)
    (nextEntry frame visit entry) :=
  authority.next (frame.successor visit.current).next_eq

#print axioms nextEntry
#print axioms nextAuthority

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action
