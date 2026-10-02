import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Authority
import H0mework.Versions.R2.Foundation.Inquiry.Engine
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

/-! A raw request uses the actual old inquiry occurrence. Its complete native
source and query faces are generated before the new emitter. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request

open SourceOperationEffects DebtActivationWorld RootInquiryCompletion

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (scope : IdentityScope program)

abbrev NewN := World registered
abbrev NewV := JointV program registered

def U7 : U7ProducerCalculus (NewN old registered) :=
  RootGeneratedDebtActivationU7.extendU7 old.U7

def calculus : U7ObstructionEvolutionCalculus (NewN old registered) (U7 old registered) :=
  RootGeneratedDebtActivationU7.extendU7Calculus old.U7 old.calculus

def baseAuthority := Native.authoritySource program registered scope
  old.root.toAuthoritativeRoot.source.projectionLaw

abbrev Ledger := (baseAuthority old program registered scope).restructuringSource.toLedgerSource

def entryAt {current : (NewV old program registered).Current}
    (occurrence : (Ledger old program registered scope).source.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt (NewN old registered)
      ((Ledger old program registered scope).source.toRootSource.account.supportOf occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact mathSource registered current

abbrev ConsumerTokenAt {current : (NewV old program registered).Current}
    (occurrence : (Ledger old program registered scope).source.toRootSource.actual.OccurrenceAt current) : Type u :=
  SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit (ULift.up.{u + 1, u} occurrence)
    (entryAt old program registered scope occurrence) (mathReadout registered current)

def consumerLaw : SourceNativeProjectionLaw (Ledger old program registered scope) where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => ConsumerTokenAt old program registered scope occurrence
  project := fun _ {_current} _ _ => .canonical

def consumerSource := (baseAuthority old program registered scope).withProjectionCoface
  (consumerLaw old program registered scope)

abbrev CompilationTokenAt {current : (NewV old program registered).Current}
    (occurrence : (Ledger old program registered scope).source.toRootSource.actual.OccurrenceAt current) : Type u :=
  SourceNativeInquiryCompilationTokenAt (U7 := U7 old registered) (calculus := calculus old registered)
    (oldTheory := TheoryState.rootSemantic (NewN old registered)) (entryAt old program registered scope occurrence)
    PUnit.unit (ULift.up.{u + 1, u} occurrence) .answered (MathReadout registered)

def compilationLaw : SourceNativeProjectionLaw (Ledger old program registered scope) where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => CompilationTokenAt old program registered scope occurrence
  project := fun _ {current} _ _ => .canonical (mathReadout registered current)

def compilationSource := (consumerSource old program registered scope).withProjectionCoface
  (compilationLaw old program registered scope)

/-- The complete before-event input remains a source restriction. In
particular unused environment coordinates are retained as data. -/
def registrationLaw : SourceNativeProjectionLaw (Ledger old program registered scope) where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => RawInputAt (Value := Value) (Var := Var) (sort := sort)
    old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current (old.root.emitted old.visit.current)
  project := fun _ {_current} _ _ => registered.input

def authoritySource := (compilationSource old program registered scope).withProjectionCoface
  (registrationLaw old program registered scope)

private theorem no_terminal (current : (NewV old program registered).Current) :
    IsEmpty ((NewV old program registered).FaithfulTerminalAt current) :=
  ⟨fun terminal => nomatch (program.emit current.1).structural_eq.symm.trans terminal.2⟩

def targetRoot : SourceNativeLivingRootClosure (NewN old registered) (NewV old program registered) :=
  (show SourceNativeAuthoritativeRootClosure (NewN old registered) (NewV old program registered) from
    { source := authoritySource old program registered scope
      emitted := emitted program registered
      compiler_commutes := (Native.authoritativeRoot program registered scope
        old.root.toAuthoritativeRoot.source.projectionLaw).compiler_commutes }).toLivingWithoutFaithfulTerminal
      (no_terminal old program registered)

def oldInstallation : SourceNativeProjectionLaw.InstallationAt
    (baseAuthority old program registered scope).projectionLaw
    (authoritySource old program registered scope).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (baseAuthority old program registered scope) (consumerLaw old program registered scope)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (consumerSource old program registered scope) (compilationLaw old program registered scope)) |>.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (compilationSource old program registered scope) (registrationLaw old program registered scope))

def consumerInstallation : SourceNativeProjectionLaw.InstallationAt
    (consumerLaw old program registered scope) (authoritySource old program registered scope).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (baseAuthority old program registered scope) (consumerLaw old program registered scope)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (consumerSource old program registered scope) (compilationLaw old program registered scope)) |>.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (compilationSource old program registered scope) (registrationLaw old program registered scope))

def compilationInstallation : SourceNativeProjectionLaw.InstallationAt
    (compilationLaw old program registered scope) (authoritySource old program registered scope).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (consumerSource old program registered scope) (compilationLaw old program registered scope)).trans
    (.inheritedCoface (compilationSource old program registered scope) (registrationLaw old program registered scope))

def registrationInstallation : SourceNativeProjectionLaw.InstallationAt
    (registrationLaw old program registered scope) (authoritySource old program registered scope).projectionLaw :=
  .componentCoface (compilationSource old program registered scope) (registrationLaw old program registered scope)

theorem target_ledger : (targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot =
    ledgerRoot program registered := rfl

end
end RootGeneratedDebtActivationJointSource.Native.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
