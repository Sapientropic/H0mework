import H0mework.Chemistry.LAlanineReentry.RuntimeRuntimeLedger
import H0mework.Chemistry.LAlanineReentry.ProducerSourceGeneratedReentry

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
noncomputable section

private def reentryRestructuringLaw : SourceNativeLedgerRestructuringLaw reentrySource :=
  identityOnlyWorldLedgerRestructuringLaw reentrySource LAlanine40K2025.Source.key
    (fun support responsibility => Root.networkOpenAtSubsingleton support responsibility)

private def reentryRestructuringCompiler : SourceNativeRestructuringLedgerCompiler reentrySource where
  ledgerCompiler := reentryLedgerCompiler
  restructuringLaw := reentryRestructuringLaw
  certifyRestructuring := by
    intro current occurrence
    cases current <;> exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)
      (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)

def reentryRestructuringSource : SourceNativeRestructuringLedgerSource N ReentryV where
  source := reentrySource
  compiler := reentryRestructuringCompiler

inductive ReentryProjection
  | physical | history | clock | held | realization | generator | gradient | residual | mode | firstReentry | readiness | wholeLedger

def reentryProjectionLaw : SourceNativeProjectionLaw reentryRestructuringSource.toLedgerSource where
  Projection := ReentryProjection
  ActiveAt := fun projection {current} _ => match projection with
    | .firstReentry => match current with | .ingress => PUnit | .ready _ => PEmpty
    | .readiness => match current with | .ingress => PEmpty | .ready _ => PUnit
    | _ => PUnit
  InactiveAt := fun projection {current} _ => match projection with
    | .firstReentry => match current with | .ingress => PEmpty | .ready _ => PUnit
    | .readiness => match current with | .ingress => PUnit | .ready _ => PEmpty
    | _ => PEmpty
  classify := by
    intro projection current occurrence
    cases projection <;> try exact .inl PUnit.unit
    all_goals cases current <;> first | exact .inl PUnit.unit | exact .inr PUnit.unit
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .physical => Inertia.Interface.InertialStepReadout × Inertia.Interface.NuclearFrame × Energy.Interface.MolecularEnergyLedger
    | .history => ReentryHistory
    | .clock => ℚ × ℚ
    | .held => Matrix Basis Basis ℂ × Matrix Basis Basis ℂ
    | .realization => Matrix Basis Basis ℂ × Matrix Basis Basis ℂ × Matrix Basis Basis ℂ × Matrix Basis Basis ℂ
    | .generator => Matrix Basis Basis ℂ × Matrix Basis Basis ℂ × Matrix Basis Basis ℂ
    | .gradient => Array (Array (Array Int)) × Array (Array (Array Int)) × Force.Interface.NuclearCoordinates ×
        Force.Interface.NuclearCoordinates × Force.Interface.NuclearCoordinates × Force.Interface.NuclearCoordinates
    | .residual => Inertia.Mechanics.PhasePoint × ℚ × ℚ × ℚ × ℚ
    | .mode => RootEvolutionKind
    | .firstReentry => PLift Producer.reentryClosure
    | .readiness => ReentryResult × PLift (reentryNext current = current ∧ IsEmpty (ReentryV.NativeWriteAt current))
    | .wholeLedger => SourceNativeLedgerEvolutionAt reentrySource occurrence
  project := by
    intro projection current occurrence active
    cases projection with
    | physical => exact (reentryCurrentPacket current, reentryFrame current, reentryCurrentLedger current)
    | history => exact reentrySourceHistory
    | clock => exact (reentryPhysicalTime current, reentryPhysicalTime (reentryNext current))
    | held => exact (reentryHeld current, reentryHeld (reentryNext current))
    | realization => exact ((reentryResponse current).realized, (reentryResponse current).inheritedResidual,
        (reentryResponse current).newNumericalResidual, (reentryResponse current).totalRealizationResidual)
    | generator => exact (Source.hamiltonian, Source.crossMatrix, Producer.sourceJointUnitary)
    | gradient => exact ((reentryResponse current).nuclear.currentGradientComponents,
        (reentryResponse current).nuclear.targetGradientComponents, (reentryResponse current).nuclear.currentGradientRoundingResidual,
        (reentryResponse current).nuclear.targetGradientRoundingResidual, (reentryResponse current).nuclear.currentGradientPicohartree,
        (reentryResponse current).nuclear.targetGradientPicohartree)
    | residual => exact (⟨(reentryResponse current).nuclear.positionResidual, (reentryResponse current).nuclear.momentumResidual⟩,
        Source.recordedEnergyChange, Source.engineEnergyChange, Source.engineAccountingResidual, Producer.targetKineticResidual)
    | mode => exact (reentrySource.toRootSource.actual.compile occurrence).kind
    | firstReentry => exact ⟨Producer.sourceGeneratedReentry⟩
    | readiness =>
        cases current with
        | ingress => exact nomatch active
        | ready result => exact (result, ⟨rfl, reentryReadiness_no_native_write result⟩)
    | wholeLedger => exact reentryLedgerCompiler.compile occurrence

def reentryAuthoritySource : SourceNativeAuthoritySource N ReentryV where
  restructuringSource := reentryRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal reentryRestructuringSource (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := reentryProjectionLaw

def reentryAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N ReentryV where
  source := reentryAuthoritySource
  emitted := reentryEmitted
  compiler_commutes := by intro current; cases current <;> rfl

def reentryLivingRoot : SourceNativeLivingRootClosure N ReentryV :=
  reentryAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def reentryInitialVisit : SourceNativeTemporalVisitAt reentryLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite reentryLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
def reentryInitialGenerated := reentryLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit reentryInitialVisit
def reentryInitialEntry := entryAt reentrySupport
def reentryInitialEntryRow : reentryInitialGenerated.GeneratedEntryRowAt reentryInitialEntry :=
  (reentryInitialGenerated.canonicalGeneratedEntryRow? reentryInitialEntry).get (by rfl)
def reentryFirstSuccessor :
    SourceNativeLedgerGeneratedSuccessorAt reentryInitialGenerated.occurrence reentryInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? reentryInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
