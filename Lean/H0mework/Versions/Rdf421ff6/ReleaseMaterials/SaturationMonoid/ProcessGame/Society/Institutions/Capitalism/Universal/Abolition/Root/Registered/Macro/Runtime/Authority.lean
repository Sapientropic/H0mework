import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Package
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.Entry
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.AccountFold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  {review : Option (ReviewPhase.ContextAt input)}

variable {input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition}

def advanceAuthority (package : Inquiry.Package (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (visit : RootVisit package.frame.root.toAuthoritativeRoot.toRoot)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root (.finite visit) (package.frame.entry visit.current)) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root
      (.finite (visit.next (package.frame.successor visit.current).next_eq))
      (package.frame.entry (package.frame.next visit.current)) := by
  have moved := authority.next (package.frame.successor visit.current).next_eq
  have aligned := Continuation.canonical_successor_keeps_the_original_entry package.frame package.basis package.stableEntry visit.current
  change SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root
    ((SourceNativeTemporalVisitAt.finite visit).next (package.frame.successor visit.current).next_eq)
    (package.basis.entry (package.frame.sourceSupport (package.frame.next visit.current)))
  rw [← aligned]
  exact moved

theorem advanceFold (package : Inquiry.Package (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (current : package.frame.V.Current)
    (same : Continuation.AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition (package.frame.cursor current)) :
    Continuation.AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (package.frame.cursor (package.frame.next current)) :=
  Eq.mp (congrArg
    (Continuation.AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (package.frame.next_exact current).symm)
    (Continuation.next_preserves_the_original_source_account_fold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition _ same)


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
