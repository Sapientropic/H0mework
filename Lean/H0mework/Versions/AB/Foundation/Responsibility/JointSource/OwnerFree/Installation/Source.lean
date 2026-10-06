import H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Consumer
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

/-! An occurrence raw reader generates the whole paid mathematical result
before the mother emitter. The complete state and trace retain the source
material; this does not replace the mother's physical update. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Installation
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : {current : V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
  Raw (Value := Value) (Var := Var) (sort := sort))

abbrev SourceMaterialAt {current : V.Current}
    (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) : Type u :=
  (Σ generated : SourceNativeLedgerEvolutionAt old.toLedgerRoot.source.source occurrence,
    SourceNativeFiniteLedgerPatchAt old.toLedgerRoot.source.source
      old.toLedgerRoot.source.ledgerCompiler.ExactTransitionAt old.toLedgerRoot.source.ledgerCompiler.writeRowSource
      old.toLedgerRoot.source.ledgerCompiler.terminalRowSource generated ×
    SourceNativeLedgerRestructuringCertificationAt old.source.restructuringSource.compiler.restructuringLaw generated) ×
      (old.source.observationAt occurrence).1

def sourceMaterialAt {current : V.Current}
    (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) : SourceMaterialAt old occurrence :=
  ⟨⟨old.source.restructuringSource.compiler.ledgerCompiler.compile occurrence,
      old.source.restructuringSource.compiler.ledgerCompiler.compilePatch occurrence,
      old.source.restructuringSource.compiler.certifyRestructuring occurrence⟩,
    (old.source.observationAt occurrence).2⟩

abbrev ResultAt {current : V.Current}
    (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) : Type u :=
  Raw (Value := Value) (Var := Var) (sort := sort) ×
    SourceOperationExecutionDebt.State (reader occurrence).environment (reader occurrence).expression ×
      Value sort × SourceMaterialAt old occurrence

def resultAt {current : V.Current}
    (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) : ResultAt old reader occurrence :=
  ⟨reader occurrence, Consumer.targetState old current (fun _ => reader occurrence),
    Consumer.value old current (fun _ => reader occurrence),
    sourceMaterialAt old occurrence⟩

def resultLaw : SourceNativeProjectionLaw old.source.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => ResultAt old reader occurrence
  project := fun _ {_current} occurrence _ => resultAt old reader occurrence

def authoritySource := old.source.withProjectionCoface (resultLaw old reader)

def resultInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface old.source (resultLaw old reader)
def oldInstallation := SourceNativeProjectionLaw.InstallationAt.inheritedCoface old.source (resultLaw old reader)

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource old reader
  emitted := old.emitted
  compiler_commutes := old.compiler_commutes

theorem source_value {current : V.Current}
    (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (resultAt old reader occurrence).2.2.1 = (reader occurrence).expression.eval (reader occurrence).environment :=
  Consumer.value_source old current (fun _ => reader occurrence)

theorem source_history {current : V.Current}
    (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (resultAt old reader occurrence).2.1.2.length = remaining (reader occurrence).expression :=
  Consumer.paid_history old current (fun _ => reader occurrence)

theorem ledger_preserved : (authoritativeRoot old reader).toLedgerRoot = old.toLedgerRoot := rfl

theorem law_surface_preserved : (authoritySource old reader).lawSurface = old.source.lawSurface := rfl

theorem observer_preserved {current : V.Current}
    (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (authoritySource old reader).observationAt occurrence = old.source.observationAt occurrence := rfl

end RootGeneratedDebtActivationJointSource.OwnerFree.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
