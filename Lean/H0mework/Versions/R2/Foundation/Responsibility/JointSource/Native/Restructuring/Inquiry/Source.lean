import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Assembly
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Root
import H0mework.Versions.R2.Foundation.Inquiry.Engine

/-! The original complete registration and its math inquiry tokens are
installed before the target emitter. The uniform face generates the Step. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry
open SourceOperationEffects DebtActivationWorld RootInquiryCompletion
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)

def initial : Current registered := ⟨old.visit.current, initialEvent registered⟩

def targetAuthority : SourceNativeAuthoritativeRootClosure (World registered) (JointV program registered) where
  source := Assembly.authoritySource old program registered
  emitted := emitted program registered
  compiler_commutes := (ledgerRoot program registered).compiler_commutes

def targetRoot : SourceNativeLivingRootClosure (World registered) (JointV program registered) :=
  (targetAuthority old program registered).toLivingWithoutFaithfulTerminal (by
    intro current
    constructor
    intro terminal
    exact nomatch (program.emit current.1).structural_eq.symm.trans terminal.2)

def initialVisit := SourceNativeTemporalVisitAt.finite
  (targetRoot old program registered).toAuthoritativeRoot.toRoot.initialVisit

def rawFace : SourceNativeRootSemanticFaceAt (targetRoot old program registered)
    (initialVisit old program registered) where
  projection := (Assembly.rawInstallation old program registered).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def completeFace : SourceNativeRootSemanticFaceAt (targetRoot old program registered)
    (initialVisit old program registered) where
  projection := (Assembly.completeInstallation old program registered).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def rawRead : Native.Request.Registration.UniformRaw (Value := Value) (Var := Var) (sort := sort) :=
  (rawFace old program registered).rootRead

def completeRead : RawInputAt (Value := Value) (Var := Var) (sort := sort)
    old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current (old.root.emitted old.visit.current) :=
  (completeFace old program registered).rootRead

def sourceAction : SourceOperationExecutionDebt.Settlement (initialEvent registered).state ⊕
    GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) (initialEvent registered).state :=
  SourceOperationExecutionDebt.generate (rawRead old program registered).environment
    (rawRead old program registered).expression (initialEvent registered).state

theorem sourceAction_eq : sourceAction old program registered = mathAction (initialEvent registered) := rfl

theorem complete_owner : (completeRead old program registered).owner = registered.input.owner := rfl

def oldProjection (projection : old.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    (targetRoot old program registered).toAuthoritativeRoot.source.projectionLaw.Projection :=
  (Assembly.oldInstallation old program registered).embed (.inl projection)

theorem oldProjection_injective : Function.Injective (oldProjection old program registered) := by
  intro first second same
  exact Sum.inl.inj ((Assembly.oldInstallation old program registered).embed_injective same)

theorem oldOutcome_heq (projection : old.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((targetRoot old program registered).toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (oldProjection old program registered projection) (emitted program registered (initial old registered)))
      (old.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (old.root.emitted old.visit.current)) :=
  ((Assembly.oldInstallation old program registered).outcome_heq _ (.inl projection)).trans
    (Native.original_projection_outcome program registered old.root.toAuthoritativeRoot.source.projectionLaw _ projection)

theorem target_ledger : (targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot =
    ledgerRoot program registered := rfl

end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
