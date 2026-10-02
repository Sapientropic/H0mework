import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Runtime
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Source

/-! The same packet source installs mathematical inquiry tokens before its
emitter, retaining the original theory epoch and all material coordinates. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly
open SourceOperationEffects RootInquiryCompletion DebtActivationWorld CompilerFromPacketSourceLaw

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (packetAt : (current : V.Current) → Packet old.root.toAuthoritativeRoot.toLedgerRoot current)

abbrev U7 := Native.Request.U7 old registered
abbrev calculus := Native.Request.calculus old registered

def base := Restructuring.authoritySource old.root.toAuthoritativeRoot registered packetAt
abbrev Ledger := (base old registered packetAt).restructuringSource.toLedgerSource

def entryAt {current : Current registered}
    (occurrence : (Ledger old registered packetAt).source.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt (World registered)
      ((Ledger old registered packetAt).source.toRootSource.account.supportOf occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact mathEntry registered current

abbrev ConsumerTokenAt {current : Current registered}
    (occurrence : (Ledger old registered packetAt).source.toRootSource.actual.OccurrenceAt current) : Type u :=
  SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit (ULift.up.{u + 1, u} occurrence)
    (entryAt old registered packetAt occurrence) (Native.mathReadout registered current)

def consumerLaw : SourceNativeProjectionLaw (Ledger old registered packetAt) where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => ConsumerTokenAt old registered packetAt occurrence
  project := fun _ {_current} _ _ => .canonical

def consumerSource := (base old registered packetAt).withProjectionCoface (consumerLaw old registered packetAt)

abbrev CompilationTokenAt {current : Current registered}
    (occurrence : (Ledger old registered packetAt).source.toRootSource.actual.OccurrenceAt current) : Type u :=
  SourceNativeInquiryCompilationTokenAt (U7 := U7 old registered) (calculus := calculus old registered)
    (oldTheory := (base old registered packetAt).lawSurface) (entryAt old registered packetAt occurrence)
    PUnit.unit (ULift.up.{u + 1, u} occurrence) .answered (Native.MathReadout registered)

def compilationLaw : SourceNativeProjectionLaw (Ledger old registered packetAt) where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => CompilationTokenAt old registered packetAt occurrence
  project := fun _ {current} _ _ => .canonical (Native.mathReadout registered current)

def authoritySource := (consumerSource old registered packetAt).withProjectionCoface
  (compilationLaw old registered packetAt)

def baseInstallation : SourceNativeProjectionLaw.InstallationAt
    (base old registered packetAt).projectionLaw (authoritySource old registered packetAt).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (base old registered packetAt) (consumerLaw old registered packetAt)).trans
    (.inheritedCoface (consumerSource old registered packetAt) (compilationLaw old registered packetAt))

def consumerInstallation : SourceNativeProjectionLaw.InstallationAt
    (consumerLaw old registered packetAt) (authoritySource old registered packetAt).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (base old registered packetAt) (consumerLaw old registered packetAt)).trans
    (.inheritedCoface (consumerSource old registered packetAt) (compilationLaw old registered packetAt))

def compilationInstallation : SourceNativeProjectionLaw.InstallationAt
    (compilationLaw old registered packetAt) (authoritySource old registered packetAt).projectionLaw :=
  .componentCoface (consumerSource old registered packetAt) (compilationLaw old registered packetAt)

def oldInstallation : SourceNativeProjectionLaw.InstallationAt
    (Restructuring.projectionLaw old.root.toAuthoritativeRoot registered packetAt)
    (authoritySource old registered packetAt).projectionLaw :=
  (Restructuring.oldInstallation old.root.toAuthoritativeRoot registered packetAt).trans
    (baseInstallation old registered packetAt)

def rawInstallation : SourceNativeProjectionLaw.InstallationAt
    (Restructuring.rawLaw old.root.toAuthoritativeRoot registered packetAt)
    (authoritySource old registered packetAt).projectionLaw :=
  (Restructuring.rawInstallation old.root.toAuthoritativeRoot registered packetAt).trans
    (baseInstallation old registered packetAt)

def completeInstallation : SourceNativeProjectionLaw.InstallationAt
    (Restructuring.completeRawLaw old.root.toAuthoritativeRoot registered packetAt)
    (authoritySource old registered packetAt).projectionLaw :=
  (Restructuring.completeInstallation old.root.toAuthoritativeRoot registered packetAt).trans
    (baseInstallation old registered packetAt)

def observationInstallation : SourceNativeProjectionLaw.InstallationAt
    (Restructuring.observationLaw old.root.toAuthoritativeRoot registered packetAt)
    (authoritySource old registered packetAt).projectionLaw :=
  (Restructuring.observationInstallation old.root.toAuthoritativeRoot registered packetAt).trans
    (baseInstallation old registered packetAt)

def targetAuthority : SourceNativeAuthoritativeRootClosure (World registered) (JointV registered packetAt) where
  source := authoritySource old registered packetAt
  emitted := emitted registered packetAt
  compiler_commutes := (ledgerRoot registered packetAt).compiler_commutes

def targetRoot : SourceNativeLivingRootClosure (World registered) (JointV registered packetAt) :=
  (targetAuthority old registered packetAt).toLivingWithoutFaithfulTerminal (by
    intro current
    constructor
    intro terminal
    have actual := (packetAt current.1).actual_next
    rw [terminal.2] at actual
    cases actual)

theorem compiler_preserved : (authoritySource old registered packetAt).restructuringSource.compiler =
    (base old registered packetAt).restructuringSource.compiler := rfl

theorem law_surface_preserved : (authoritySource old registered packetAt).lawSurface =
    (base old registered packetAt).lawSurface := rfl

theorem observer_preserved {current : Current registered}
    (occurrence : (Ledger old registered packetAt).source.toRootSource.actual.OccurrenceAt current) :
    (authoritySource old registered packetAt).observationAt occurrence =
      (base old registered packetAt).observationAt occurrence := rfl

theorem target_ledger : (targetRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot =
    ledgerRoot registered packetAt := rfl

end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
