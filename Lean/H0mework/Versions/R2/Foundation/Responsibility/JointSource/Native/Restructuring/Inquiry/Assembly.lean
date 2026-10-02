import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Registration.Source
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Source

/-! The registered general source owns its math consumer and compiler tokens
before emission. All original raw, math and restructuring faces are inherited. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Assembly
open SourceOperationEffects RootInquiryCompletion

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Native.Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)

abbrev U7 := Native.Request.U7 old registered
abbrev calculus := Native.Request.calculus old registered

def base := Native.Request.Registration.authoritySource old.root.toAuthoritativeRoot program registered
abbrev Ledger := (base old program registered).restructuringSource.toLedgerSource

def entryAt {current : (Native.JointV program registered).Current}
    (occurrence : (Ledger old program registered).source.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt (World registered)
      ((Ledger old program registered).source.toRootSource.account.supportOf occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact mathSource registered current

abbrev ConsumerTokenAt {current : (Native.JointV program registered).Current}
    (occurrence : (Ledger old program registered).source.toRootSource.actual.OccurrenceAt current) : Type u :=
  SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit (ULift.up.{u + 1, u} occurrence)
    (entryAt old program registered occurrence) (mathReadout registered current)

def consumerLaw : SourceNativeProjectionLaw (Ledger old program registered) where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => ConsumerTokenAt old program registered occurrence
  project := fun _ {_current} _ _ => .canonical

def consumerSource := (base old program registered).withProjectionCoface (consumerLaw old program registered)

abbrev CompilationTokenAt {current : (Native.JointV program registered).Current}
    (occurrence : (Ledger old program registered).source.toRootSource.actual.OccurrenceAt current) : Type u :=
  SourceNativeInquiryCompilationTokenAt (U7 := U7 old registered) (calculus := calculus old registered)
    (oldTheory := TheoryState.rootSemantic (World registered)) (entryAt old program registered occurrence)
    PUnit.unit (ULift.up.{u + 1, u} occurrence) .answered (MathReadout registered)

def compilationLaw : SourceNativeProjectionLaw (Ledger old program registered) where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => CompilationTokenAt old program registered occurrence
  project := fun _ {current} _ _ => .canonical (mathReadout registered current)

def authoritySource := (consumerSource old program registered).withProjectionCoface
  (compilationLaw old program registered)

def baseInstallation : SourceNativeProjectionLaw.InstallationAt
    (base old program registered).projectionLaw (authoritySource old program registered).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (base old program registered) (consumerLaw old program registered)).trans
    (.inheritedCoface (consumerSource old program registered) (compilationLaw old program registered))

def consumerInstallation : SourceNativeProjectionLaw.InstallationAt
    (consumerLaw old program registered) (authoritySource old program registered).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (base old program registered) (consumerLaw old program registered)).trans
    (.inheritedCoface (consumerSource old program registered) (compilationLaw old program registered))

def compilationInstallation : SourceNativeProjectionLaw.InstallationAt
    (compilationLaw old program registered) (authoritySource old program registered).projectionLaw :=
  .componentCoface (consumerSource old program registered) (compilationLaw old program registered)

def oldInstallation : SourceNativeProjectionLaw.InstallationAt
    (Native.Request.Registration.base old.root.toAuthoritativeRoot program registered).projectionLaw
    (authoritySource old program registered).projectionLaw :=
  (Native.Request.Registration.oldInstallation old.root.toAuthoritativeRoot program registered).trans
    (baseInstallation old program registered)

def rawInstallation : SourceNativeProjectionLaw.InstallationAt
    (Native.Request.Registration.law old.root.toAuthoritativeRoot program registered)
    (authoritySource old program registered).projectionLaw :=
  (Native.Request.Registration.rawInstallation old.root.toAuthoritativeRoot program registered).trans
    (baseInstallation old program registered)

def completeInstallation : SourceNativeProjectionLaw.InstallationAt
    (Native.Request.Registration.completeLaw old.root.toAuthoritativeRoot program registered)
    (authoritySource old program registered).projectionLaw :=
  (Native.Request.Registration.completeInstallation old.root.toAuthoritativeRoot program registered).trans
    (baseInstallation old program registered)

theorem compiler_preserved : (authoritySource old program registered).restructuringSource.compiler =
    (base old program registered).restructuringSource.compiler := rfl

theorem law_surface_preserved : (authoritySource old program registered).lawSurface =
    (base old program registered).lawSurface := rfl

end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Assembly
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
