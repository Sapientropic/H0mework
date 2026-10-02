import H0mework.Foundation.Responsibility.JointSource.Native.Scope
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Projection
import H0mework.Versions.R2.Foundation.Runtime.AnswerNext

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native

open SourceOperationEffects DebtActivationWorld

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable (program : Program lower)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)
variable (scope : IdentityScope program)

include scope in
private theorem openAt_subsingleton (support : (World registered).Support)
    (responsibility : (World registered).Responsibility) :
    Subsingleton ((World registered).OpenAt support responsibility) := by
  rcases support with ⟨oldSupport, state⟩
  cases responsibility with
  | inl old => exact scope.openAt_subsingleton oldSupport old
  | inr debt =>
      cases state with
      | none => exact ⟨fun impossible => nomatch impossible⟩
      | some state =>
          constructor
          rintro ⟨⟨left⟩⟩ ⟨⟨right⟩⟩
          rfl

def restructuringLaw : SourceNativeLedgerRestructuringLaw (source program registered) :=
  identityOnlyWorldLedgerRestructuringLaw (source program registered) scope.defaultAnchor
    (openAt_subsingleton program registered scope)

def restructuringCertification {current : Current registered}
    (occurrence : (source program registered).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw program registered scope)
      ((ledgerCompiler program registered).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (patch_origin_injective program registered scope current)
    (patch_destination_injective program registered scope current)

def restructuringSource : SourceNativeRestructuringLedgerSource (World registered) (JointV program registered) where
  source := source program registered
  compiler :=
    { ledgerCompiler := ledgerCompiler program registered
      restructuringLaw := restructuringLaw program registered scope
      certifyRestructuring := restructuringCertification program registered scope }

private theorem source_terminal_empty (current : Current registered) :
    IsEmpty ((JointV program registered).FaithfulTerminalAt current) :=
  ⟨fun terminal => nomatch (program.emit current.1).structural_eq.symm.trans terminal.2⟩

def authoritySource (old : SourceNativeProjectionLaw lower.source) :
    SourceNativeAuthoritySource (World registered) (JointV program registered) where
  restructuringSource := restructuringSource program registered scope
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource program registered scope)
    (source_terminal_empty program registered)
  lawSurface := .rootSemantic (World registered)
  projectionLaw := projectionLaw program registered old

def authoritativeRoot (old : SourceNativeProjectionLaw lower.source) :
    SourceNativeAuthoritativeRootClosure (World registered) (JointV program registered) where
  source := authoritySource program registered scope old
  emitted := emitted program registered
  compiler_commutes := (ledgerRoot program registered).compiler_commutes

def livingRoot (old : SourceNativeProjectionLaw lower.source) :
    SourceNativeLivingRootClosure (World registered) (JointV program registered) :=
  (authoritativeRoot program registered scope old).toLivingWithoutFaithfulTerminal
    (source_terminal_empty program registered)

end RootGeneratedDebtActivationJointSource.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
