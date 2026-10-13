import H0mework.Versions.Y.Realization.Completion.FaithfulInstallation
import H0mework.Realization.Faces.ProjectionCoface

/-!
# Source-generated faithful residual on the original root projection

The installed history/evaluator produces the residual disposition. This
component exposes that result on the same emitted occurrence; it keeps the
lower source, ledger compiler, law surface and canonical next unchanged.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalFaithfulResidualInstalledFace

open CofinalFaithfulSettlementFace
open CofinalFaithfulRealization

noncomputable section
universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {Carrier : Type u} [AddCommGroup Carrier]
variable {source : SourceNativeLedgerSource N V}

/-- The residual is computed from source-installed history/evaluator values;
no residual, branch, outcome, coverage or terminal is an input. -/
def component
    (law : SourceNativeCofinalFaithfulMaterialLaw source Carrier) :
    SourceNativeProjectionLaw source where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ =>
    RootGeneratedCofinalFaithfulRealizationAt.ResidualDispositionOutcome
      (law.faithfulAt occurrence)
  project := fun _ {_current} occurrence _ =>
    (law.faithfulAt occurrence).settleWithResidual

@[simp] theorem component_outcome
    (law : SourceNativeCofinalFaithfulMaterialLaw source Carrier)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    (component law).outcomeAt PUnit.unit occurrence =
      .inl ⟨PUnit.unit,
        (law.faithfulAt occurrence).settleWithResidual⟩ := rfl

variable {root : SourceNativeLivingRootClosure N V}
variable (recognition : SourceNativeCofinalFaithfulRecognitionAt Carrier root)

def installedSource : SourceNativeAuthoritySource N V :=
  root.toAuthoritativeRoot.source.withProjectionCoface
    (component recognition.materialLaw)

def installedRoot : SourceNativeAuthoritativeRootClosure N V where
  source := installedSource recognition
  emitted := root.emitted
  compiler_commutes := root.compiler_commutes

def componentInstallation :
    SourceNativeProjectionLaw.InstallationAt
      (component recognition.materialLaw)
      (installedSource recognition).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    root.toAuthoritativeRoot.source (component recognition.materialLaw)

def faithfulInstallation :
    SourceNativeProjectionLaw.InstallationAt
      recognition.materialLaw.toProjectionLaw
      (installedSource recognition).projectionLaw :=
  recognition.installation.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      root.toAuthoritativeRoot.source (component recognition.materialLaw))

theorem inherited_raw_at
    {current : V.Current}
    (occurrence : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current) :
    HEq
      ((installedRoot recognition).source.projectionLaw.outcomeAt
        ((faithfulInstallation recognition).embed PUnit.unit) occurrence)
      (recognition.materialLaw.toProjectionLaw.outcomeAt
        PUnit.unit occurrence) :=
  (faithfulInstallation recognition).outcome_heq occurrence PUnit.unit

theorem installed_same_lower :
    (installedRoot recognition).toLedgerRoot =
      root.toAuthoritativeRoot.toLedgerRoot := rfl

theorem installed_residual_at (current : V.Current) :
    (installedRoot recognition).source.projectionLaw.outcomeAt
      (.component PUnit.unit) ((installedRoot recognition).emitted current) =
      .inl ⟨PUnit.unit,
        (recognition.materialLaw.faithfulAt (root.emitted current)
          ).settleWithResidual⟩ := rfl

theorem installed_ledger_and_next (current : V.Current) :
    (installedRoot recognition).toLedgerRoot.generatedLedgerAt current =
      root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current ∧
    ((installedRoot recognition).toRoot.evolutionAt current).nextCurrent? =
      (root.toAuthoritativeRoot.toRoot.evolutionAt current).nextCurrent? :=
  ⟨rfl,rfl⟩

/-- The old faithful consumer reads the installed residual at its generated
occurrence. The same compiler image still supplies whole-ledger and next. -/
theorem installed_step_residual_ledger_next
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    let step := recognition.generateStepAt visit
    (installedRoot recognition).source.projectionLaw.outcomeAt
      (.component PUnit.unit) step.sourceOccurrence =
        .inl ⟨PUnit.unit, step.residualDisposition⟩ ∧
    HEq step.wholeLedgerWriteBack
      ((installedRoot recognition).toLedgerRoot.generatedLedgerAt visit.current) ∧
    step.nextCurrent = root.generatedNextCurrentAt visit ∧
    ((installedRoot recognition).toRoot.evolutionAt visit.current).nextCurrent? =
      (root.toAuthoritativeRoot.toRoot.evolutionAt visit.current).nextCurrent? := by
  exact ⟨rfl, HEq.rfl, rfl, rfl⟩

end
end CofinalFaithfulResidualInstalledFace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
