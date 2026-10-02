import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Source

/-! The entire original Fock authority family and the mathematical readout
are installed on the same complete born source before its emitter. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission

open SourceOperationEffects
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

namespace Fock
export NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
  (authoritySource projectionLaw installation baseInstallation)
end Fock

noncomputable section

variable (runtime : LivingRuntimeState process)

def physicalProjectionLaw : SourceNativeProjectionLaw
    (Joint.authoritySource (registered runtime)).restructuringSource.toLedgerSource where
  Projection := Fock.projectionLaw.Projection
  ActiveAt := fun projection {_current} occurrence =>
    Fock.projectionLaw.ActiveAt projection (Joint.originalOccurrence (registered runtime) occurrence)
  InactiveAt := fun projection {_current} occurrence =>
    Fock.projectionLaw.InactiveAt projection (Joint.originalOccurrence (registered runtime) occurrence)
  classify := fun projection {_current} occurrence =>
    Fock.projectionLaw.classify projection (Joint.originalOccurrence (registered runtime) occurrence)
  PayloadAt := fun projection {_current} occurrence active =>
    Fock.projectionLaw.PayloadAt projection (Joint.originalOccurrence (registered runtime) occurrence) active
  project := fun projection {_current} occurrence active =>
    Fock.projectionLaw.project projection (Joint.originalOccurrence (registered runtime) occurrence) active

def authoritySource :=
  (Joint.authoritySource (registered runtime)).withProjectionCoface (physicalProjectionLaw runtime)

def physicalInstallation : SourceNativeProjectionLaw.InstallationAt
    (physicalProjectionLaw runtime) (authoritySource runtime).projectionLaw :=
  .componentCoface (Joint.authoritySource (registered runtime)) (physicalProjectionLaw runtime)

def unitInstallation : SourceNativeProjectionLaw.InstallationAt
    (Joint.authoritySource (registered runtime)).projectionLaw (authoritySource runtime).projectionLaw :=
  .inheritedCoface (Joint.authoritySource (registered runtime)) (physicalProjectionLaw runtime)

def oldProjection : Fock.authoritySource.projectionLaw.Projection →
    (authoritySource runtime).projectionLaw.Projection
  | .component physical => .component physical
  | .inherited original => .inherited (.inl original)

theorem oldProjection_injective : Function.Injective (oldProjection runtime) := by
  intro first second same
  cases first <;> cases second <;> cases same <;> rfl

theorem physical_outcome {current : Joint.Current (registered runtime)}
    (occurrence : (Joint.source (registered runtime)).toRootSource.actual.OccurrenceAt current)
    (projection : Fock.projectionLaw.Projection) :
    HEq ((physicalProjectionLaw runtime).outcomeAt projection occurrence)
      (Fock.projectionLaw.outcomeAt projection (Joint.originalOccurrence (registered runtime) occurrence)) := by
  unfold SourceNativeProjectionLaw.outcomeAt
  dsimp only [physicalProjectionLaw]
  cases Fock.projectionLaw.classify projection (Joint.originalOccurrence (registered runtime) occurrence) <;> rfl

theorem oldOutcome_heq {current : Joint.Current (registered runtime)}
    (occurrence : (Joint.source (registered runtime)).toRootSource.actual.OccurrenceAt current)
    (projection : Fock.authoritySource.projectionLaw.Projection) :
    HEq ((authoritySource runtime).projectionLaw.outcomeAt (oldProjection runtime projection) occurrence)
      (Fock.authoritySource.projectionLaw.outcomeAt projection
        (Joint.originalOccurrence (registered runtime) occurrence)) := by
  cases projection with
  | component physical =>
      exact ((physicalInstallation runtime).outcome_heq occurrence physical).trans
        ((physical_outcome runtime occurrence physical).trans
          (Fock.installation.outcome_heq
            (Joint.originalOccurrence (registered runtime) occurrence) physical).symm)
  | inherited original =>
      exact ((unitInstallation runtime).outcome_heq occurrence (.inl original)).trans
        ((RootGeneratedDebtActivationJointSource.Unit.original_projection_outcome
          (registered runtime) occurrence original).trans
          (Fock.baseInstallation.outcome_heq
            (Joint.originalOccurrence (registered runtime) occurrence) original).symm)

def mathProjection : (authoritySource runtime).projectionLaw.Projection := .inherited (.inr PUnit.unit)

theorem mathOutcome_heq {current : Joint.Current (registered runtime)}
    (occurrence : (Joint.source (registered runtime)).toRootSource.actual.OccurrenceAt current) :
    HEq ((authoritySource runtime).projectionLaw.outcomeAt (mathProjection runtime) occurrence)
      (.inl ⟨PUnit.unit, Joint.mathReadout (registered runtime) current⟩ :
        SourceNativeProjectionFiberAt (Joint.authoritySource (registered runtime)).projectionLaw
          (.inr PUnit.unit) occurrence) :=
  (unitInstallation runtime).outcome_heq occurrence (.inr PUnit.unit)

def authoritativeRoot : SourceNativeAuthoritativeRootClosure
    (Joint.World (registered runtime)) (Joint.JointV (registered runtime)) where
  source := authoritySource runtime
  emitted := Joint.emitted (registered runtime)
  compiler_commutes := (Joint.authoritativeRoot (registered runtime)).compiler_commutes

def livingRoot : SourceNativeLivingRootClosure
    (Joint.World (registered runtime)) (Joint.JointV (registered runtime)) :=
  (authoritativeRoot runtime).toLivingWithoutFaithfulTerminal
    (fun _current => ⟨fun terminal => nomatch terminal⟩)

theorem ledger_source_eq :
    (authoritativeRoot runtime).toLedgerRoot.source = Joint.ledgerSource (registered runtime) := rfl

theorem initial_oldOutcome_heq (projection : Fock.authoritySource.projectionLaw.Projection) :
    HEq ((authoritySource runtime).projectionLaw.outcomeAt (oldProjection runtime projection)
      (initialOccurrence runtime))
      (Fock.authoritySource.projectionLaw.outcomeAt projection runtime.emittedOccurrence) := by
  have inherited := oldOutcome_heq runtime (initialOccurrence runtime) projection
  rw [original_initial_occurrence] at inherited
  exact inherited

theorem initial_particleWave_readout :
    HEq ((authoritySource runtime).projectionLaw.outcomeAt (.component PUnit.unit) (initialOccurrence runtime))
      (runtimeFacade.readoutAt runtime .particleWave) := by
  have physical := physical_outcome runtime (initialOccurrence runtime) PUnit.unit
  rw [original_initial_occurrence] at physical
  exact ((physicalInstallation runtime).outcome_heq (initialOccurrence runtime) PUnit.unit).trans physical

theorem initial_particleWave_payload :
    HEq ((authoritySource runtime).projectionLaw.outcomeAt (.component PUnit.unit) (initialOccurrence runtime))
      (.inl ⟨activeAt runtime, payloadAt runtime⟩ :
        SourceNativeProjectionFiberAt Fock.projectionLaw PUnit.unit runtime.emittedOccurrence) :=
  (initial_particleWave_readout runtime).trans (heq_of_eq (payload_is_readout runtime))

end
end SourcePhysicalCalculationAdmission
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
