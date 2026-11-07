import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Compilation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.GeneratedRow
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

/-- Batch coordinates belong to the actual current. Reentry changes them
while retaining this same runtime carrier and the original financial world. -/
structure Frame where
  private mk ::
  start : Physical.Cursor Party Good Port Technology Instrument
  proposal : Compile.RawInput Party Good Port Technology Instrument
  sourcePosition : Nat
  package : Inquiry.Package (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  visit : RootVisit package.frame.root.toAuthoritativeRoot.toRoot
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root (.finite visit) (package.frame.entry visit.current)
  ready : package.data.Ready visit.current
  sourceFold : Continuation.AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
    (package.frame.cursor visit.current)

variable {input depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {phase : Option (ReviewPhase.ContextAt input)}

namespace Frame
variable (frame : Frame (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

def cursor := frame.package.frame.cursor frame.visit.current
def account := frame.package.frame.account frame.visit.current

def snapshot := Inventory.physicalAfter (review := phase) input depth count prefixLimit renewalLimit frame.start frame.proposal

def presentation := Inquiry.presentation frame.package (.finite frame.visit) frame.authority

def query : frame.presentation.Query :=
  Raw.queryAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current frame.ready frame.sourceFold

theorem query_unique (candidate : frame.presentation.Query) : candidate = frame.query :=
  Raw.query_unique frame.package.source frame.package.sourceData frame.package.reader frame.visit.current frame.ready frame.sourceFold candidate

def ordinary : Frame (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount := {
  start := frame.start
  proposal := frame.proposal
  sourcePosition := frame.sourcePosition
  package := frame.package
  visit := frame.visit.next (frame.package.frame.successor frame.visit.current).next_eq
  authority := advanceAuthority frame.package frame.visit frame.authority
  ready := frame.package.data.ready_next frame.visit.current frame.ready
  sourceFold := advanceFold frame.package frame.visit.current frame.sourceFold }

def born (registered : HeadRegistration (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current) :
    Frame (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount := by
  let child := frame.package.born registered
  let initial := child.frame.root.toAuthoritativeRoot.toRoot.initialVisit
  let row := Admission.generatedRow frame.package.frame registered frame.package.basis (.finite initial) (child.frame.entry initial.current)
  have initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt child.frame.root (.finite initial) (child.frame.entry initial.current) :=
    SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow child.frame.root _ row
  exact {
    start := frame.start
    proposal := frame.proposal
    sourcePosition := frame.sourcePosition
    package := child
    visit := initial.next (child.frame.successor initial.current).next_eq
    authority := advanceAuthority child initial initialAuthority
    ready := Continuation.FinancialData.born_first_registration_is_ready frame.package.data registered frame.ready
    sourceFold := advanceFold child initial.current frame.sourceFold }

def reenter (germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current) :
    Frame (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount := by
  let child := frame.package.reentry germ
  let initial := child.frame.root.toAuthoritativeRoot.toRoot.initialVisit
  let target := (Raw.Target.generated frame.package.source frame.package.sourceData frame.package.reader
    frame.package.basis (.finite frame.visit) germ frame.authority).target
  have sameEntry : target.translatedSourceEntry = child.frame.entry initial.current :=
    Financial.Installation.entry_eq_of_key _ _
      (frame.package.reentry_initial_entry_key (.finite frame.visit) germ)
      (child.frame.open_fibres _)
  have initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt child.frame.root (.finite initial)
      (child.frame.entry initial.current) :=
    Eq.mp (congrArg (fun entry => SourceNativeLivingTemporalCausalEntryAuthorityAt child.frame.root
      (.finite initial) entry) sameEntry) target.initialAuthority
  exact {
    start := germ.snapshot
    proposal := germ.raw
    sourcePosition := 0
    package := child
    visit := initial.next (child.frame.successor initial.current).next_eq
    authority := advanceAuthority child initial initialAuthority
    ready := Continuation.FinancialData.reentry_body_generates_the_same_financial_dictionary (review := phase)
      input depth count prefixLimit renewalLimit sourceDepth sourceCount germ.snapshot germ.raw
      (Raw.Target.family frame.package.source frame.package.sourceData frame.package.reader germ)
      (Raw.Target.seedEq frame.package.source frame.package.sourceData frame.package.reader germ)
    sourceFold := advanceFold child initial.current
      (Continuation.initial_account_is_the_original_source_fold (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount germ.snapshot germ.raw 0) }

def internalNext : Frame (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount :=
  match headRegistration? (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current with
  | some registered => frame.born registered
  | none => frame.ordinary

def nextAt (chosen : frame.presentation.Query) : Frame (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount :=
  match chosen with
  | .internal _ => frame.internalNext
  | .raw germ => frame.reenter germ

def next : Frame (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount := frame.nextAt frame.query

theorem ordinary_snapshot : frame.ordinary.snapshot = frame.snapshot := rfl

theorem born_snapshot (registered : HeadRegistration (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current) :
    (frame.born registered).snapshot = frame.snapshot := rfl

theorem ordinary_account : frame.ordinary.account =
    (Accounting.next (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition frame.cursor).account :=
  congrArg Accounting.Current.account (frame.package.frame.next_exact frame.visit.current)

theorem reentry_preserves_the_literal_existing_account
    (germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current) :
    (frame.reenter germ).account = frame.account := by
  have aligned := (frame.package.reentry germ).frame.next_exact
    (Raw.Target.bodyInitial frame.package.source frame.package.sourceData frame.package.reader germ)
  exact (congrArg Accounting.Current.account aligned).trans
    (Raw.Target.first_body_retains_the_complete_original_account frame.package.source frame.package.sourceData frame.package.reader germ)

end Frame

variable (input depth count prefixLimit renewalLimit sourceDepth sourceCount)

def initialFrame
    (start : Physical.Cursor Party Good Port Technology Instrument)
    (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
    (reader : Raw.Reader input depth count)
    (nativeOrigin : Option (ReviewSource.Native.OriginAt input) := none) : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount := by
  let package := Inquiry.basePackage (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader nativeOrigin
  let initial := package.frame.root.toAuthoritativeRoot.toRoot.initialVisit
  let row := Accounting.generatedRow (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
    (.finite initial) (package.frame.entry initial.current)
  have initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root (.finite initial) (package.frame.entry initial.current) :=
    SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow package.frame.root _ row
  exact {
    start := start
    proposal := proposal
    sourcePosition := sourcePosition
    package := package
    visit := initial.next (package.frame.successor initial.current).next_eq
    authority := advanceAuthority package initial initialAuthority
    ready := Continuation.FinancialData.base_first_body_is_ready
    sourceFold := advanceFold package initial.current
      (Continuation.initial_account_is_the_original_source_fold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) }

def frames
    (start : Physical.Cursor Party Good Port Technology Instrument)
    (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
    (reader : Raw.Reader input depth count) : (tick : Nat) →
    (nativeOrigin : Option (ReviewSource.Native.OriginAt input) := none) →
    Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
  | 0, nativeOrigin => initialFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader nativeOrigin
  | tick + 1, nativeOrigin => (frames start proposal sourcePosition reader tick nativeOrigin).next

#print axioms Frame.reenter
#print axioms Frame.next
#print axioms initialFrame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
