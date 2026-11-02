import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.Continuation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData.EntryKeys
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.FoundationKeys
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Resolve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

structure Package where
  private mk ::
  source : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  sourceData : Continuation.FinancialData source
  reader : Raw.Reader input depth count
  basis : Basis source.N
  stableEntry : ∀ left right, (basis.entry left).1 = (basis.entry right).1
  familyEntryAligned : Continuation.FinancialData.EntryAligned sourceData basis

namespace Package
variable {input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition}
  {phase : Option (ReviewPhase.ContextAt input)}
  (package : Package (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

def frame := Raw.installCompleteFrame package.source package.sourceData package.reader package.basis

def data : Continuation.FinancialData package.frame :=
  Raw.installCompleteData package.source package.sourceData package.reader package.basis

theorem complete_data_entry_aligned : Continuation.FinancialData.EntryAligned package.data package.basis :=
  package.familyEntryAligned

def born {origin : package.frame.V.Current}
    (registered : HeadRegistration (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition package.frame origin) :
    Package (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition :=
  ⟨Admission.nativeFrame package.frame registered, package.data.born registered, package.reader,
    Admission.inquiryBasis package.frame registered package.basis,
    fun left right => congrArg Sum.inl (package.stableEntry left.1 right.1),
    Continuation.FinancialData.born_entry_aligned package.data package.basis
      package.complete_data_entry_aligned registered⟩

theorem born_frame_is_the_actual_target {origin : package.frame.V.Current}
    (registered : HeadRegistration (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition package.frame origin) :
    (package.born registered).frame =
      Admission.completeFrame package.frame package.data package.reader package.basis registered := rfl

def reentry {current : package.source.V.Current}
    (germ : Raw.GermAt package.source package.sourceData package.reader current) :
    Package (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount germ.snapshot germ.raw 0 :=
  ⟨Raw.Target.bareFrame package.source package.sourceData package.reader germ,
    Raw.Target.financialData package.source package.sourceData package.reader germ,
    package.reader, Raw.Target.basis package.source package.sourceData package.reader germ,
    (Raw.Target.family package.source package.sourceData package.reader germ).entry_key,
    Continuation.FinancialData.reentry_entry_aligned
      (Raw.Target.family package.source package.sourceData package.reader germ)
      (Raw.Target.seedEq package.source package.sourceData package.reader germ)⟩

theorem reentry_frame_is_the_actual_target
    (visit : SourceNativeTemporalVisitAt package.frame.root.toAuthoritativeRoot.toLedgerRoot)
    (germ : Raw.GermAt package.source package.sourceData package.reader visit.current) :
    (package.reentry germ).frame =
      Raw.Target.targetFrame package.source package.sourceData package.reader package.basis visit germ := rfl

theorem reentry_initial_entry_key
    (visit : SourceNativeTemporalVisitAt package.frame.root.toAuthoritativeRoot.toLedgerRoot)
    (germ : Raw.GermAt package.source package.sourceData package.reader visit.current) :
    ((Raw.Target.initialLedger package.source package.sourceData package.reader germ).forward
      (package.frame.entry visit.current)).1 =
      ((package.reentry germ).frame.entry
        (Raw.Target.bodyInitial package.source package.sourceData package.reader germ)).1 := by
  exact (Raw.Target.initial_ledger_preserves_responsibility package.source package.sourceData package.reader germ
    (package.frame.entry visit.current)).trans
    ((package.familyEntryAligned visit.current germ.ready (package.source.sourceSupport visit.current)).trans
      ((Raw.Target.family package.source package.sourceData package.reader germ).entry_key _ _))

end Package

def basePackage (reader : Raw.Reader input depth count)
    (nativeOrigin : Option (ReviewSource.Native.OriginAt input) := none) :
    Package (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition :=
  ⟨{ Accounting.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition with
      nativeOrigin := nativeOrigin },
    ReviewSource.Native.Macro.inheritCreator Continuation.FinancialData.base nativeOrigin, reader,
    baseBasis (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition,
    Epoch.Finance.Future.Installed.canonicalEntry_key input depth count sourceDepth sourceCount
      (Accounting.seedRun (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition),
    Continuation.FinancialData.base_entry_aligned⟩

theorem base_package_has_the_complete_fixed_query_root (reader : Raw.Reader input depth count) :
    (basePackage (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader).frame =
      Raw.installCompleteFrame
        (Accounting.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
        Continuation.FinancialData.base reader
        (baseBasis (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) := rfl

#print axioms Package.born
#print axioms Package.reentry
#print axioms Package.reentry_initial_entry_key
#print axioms basePackage

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry
