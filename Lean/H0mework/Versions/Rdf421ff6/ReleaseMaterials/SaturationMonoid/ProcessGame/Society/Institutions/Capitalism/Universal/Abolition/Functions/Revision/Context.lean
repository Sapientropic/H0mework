import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.Action
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.Public

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  {review : Option (ReviewPhase.ContextAt input)}

/-- These are the existing raw inquiry's source objects. No target law,
future execution, replacement account or completion certificate is supplied. -/
structure Context where
  start : Physical.Cursor Party Good Port Technology Instrument
  proposal : Compile.RawInput Party Good Port Technology Instrument
  sourcePosition : Nat
  native : Macro.NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  data : Macro.Continuation.FinancialData native
  reader : Macro.Raw.Reader input depth count
  basis : Macro.Inquiry.Basis native.N
  visit : SourceNativeTemporalVisitAt (Macro.Raw.installCompleteFrame native data reader basis).root.toAuthoritativeRoot.toLedgerRoot
  germ : Macro.Raw.GermAt native data reader visit.current
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (Macro.Raw.installCompleteFrame native data reader basis).root visit
    (basis.entry (native.sourceSupport visit.current))

variable {depth count prefixLimit renewalLimit sourceDepth sourceCount}
  (context : Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount)

abbrev sourceFrame := Macro.Raw.installCompleteFrame context.native context.data context.reader context.basis
abbrev sourceRoot := (sourceFrame context).root
abbrev sourceVisit := context.visit
abbrev sourceEntry := context.basis.entry (context.native.sourceSupport context.visit.current)
abbrev sourceAuthority := context.authority
abbrev N := context.native.N

/-- This is the old installed snapshot payload, including both creator
restrictions and the complete original Epoch financial state. -/
def originalSnapshot : Macro.Raw.Snapshot (input := input) (depth := depth) (count := count)
    (prefixLimit := prefixLimit) (renewalLimit := renewalLimit) :=
  (Macro.Raw.component context.native context.data context.reader context.basis).project .snapshot
    (context.native.root.emitted context.visit.current) ⟨True.intro⟩

def originalAccount := (originalSnapshot context).account
def originalNative := (originalSnapshot context).native

theorem the_snapshot_keeps_the_literal_original_epoch_state :
    originalAccount context = context.native.account context.visit.current := rfl

theorem the_installed_snapshot_is_the_same_original_germ :
    (originalSnapshot context).physical = context.germ.snapshot := by
  change Macro.Raw.currentSnapshot context.native context.visit.current = context.germ.snapshot
  unfold Macro.Raw.currentSnapshot
  exact (if_pos context.germ.complete.1).trans
    (Macro.Raw.input_uses_the_literal_current_account context.native context.data context.reader context.germ).2.1.symm

#print axioms originalSnapshot
#print axioms the_snapshot_keeps_the_literal_original_epoch_state
#print axioms the_installed_snapshot_is_the_same_original_germ

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision
