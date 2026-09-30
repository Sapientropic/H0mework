import H0mework.Chemistry.LAlanineJointNext.RuntimeRuntimeLedger
import H0mework.Chemistry.LAlanineJointNext.ProducerSourceGeneratedJointStep

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
noncomputable section

private def jointRestructuringLaw : SourceNativeLedgerRestructuringLaw jointSource :=
  identityOnlyWorldLedgerRestructuringLaw jointSource LAlanine40K2025.Source.key
    (fun support responsibility => Root.networkOpenAtSubsingleton support responsibility)

private def jointRestructuringCompiler : SourceNativeRestructuringLedgerCompiler jointSource where
  ledgerCompiler := jointLedgerCompiler
  restructuringLaw := jointRestructuringLaw
  certifyRestructuring := by
    intro current occurrence
    cases current <;> exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)
      (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)

def jointRestructuringSource : SourceNativeRestructuringLedgerSource N JointV where
  source := jointSource
  compiler := jointRestructuringCompiler

inductive JointProjection
  | physical | history | clock | held | realization | generator | gradient | residual | mode | firstJoint | readiness | wholeLedger

def jointProjectionLaw : SourceNativeProjectionLaw jointRestructuringSource.toLedgerSource where
  Projection := JointProjection
  ActiveAt := fun projection {current} _ => match projection with
    | .firstJoint => match current with | .ingress => PUnit | .ready _ => PEmpty
    | .readiness => match current with | .ingress => PEmpty | .ready _ => PUnit
    | _ => PUnit
  InactiveAt := fun projection {current} _ => match projection with
    | .firstJoint => match current with | .ingress => PEmpty | .ready _ => PUnit
    | .readiness => match current with | .ingress => PUnit | .ready _ => PEmpty
    | _ => PEmpty
  classify := by
    intro projection current occurrence
    cases projection <;> try exact .inl PUnit.unit
    all_goals cases current <;> first | exact .inl PUnit.unit | exact .inr PUnit.unit
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .physical => Inertia.Interface.InertialStepReadout × Inertia.Interface.NuclearFrame × Energy.Interface.MolecularEnergyLedger
    | .history => Inertia.Interface.InertialStepReadout × HeldForce.Runtime.HeldForceResult
    | .clock => ℚ × ℚ
    | .held => Matrix Basis Basis ℂ × Matrix Basis Basis ℂ
    | .realization => Matrix Basis Basis ℂ × Matrix Basis Basis ℂ × Matrix Basis Basis ℂ × Matrix Basis Basis ℂ
    | .generator => Matrix Basis Basis ℂ × Matrix Basis Basis ℂ × Matrix Basis Basis ℂ
    | .gradient => Array (Array (Array Int)) × Array (Array (Array Int)) × Force.Interface.NuclearCoordinates ×
        Force.Interface.NuclearCoordinates × Force.Interface.NuclearCoordinates × Force.Interface.NuclearCoordinates
    | .residual => Inertia.Mechanics.PhasePoint × ℚ × ℚ × ℚ × ℚ
    | .mode => RootEvolutionKind
    | .firstJoint => PLift Producer.jointClosure
    | .readiness => JointResult × PLift (jointNext current = current ∧ IsEmpty (JointV.NativeWriteAt current))
    | .wholeLedger => SourceNativeLedgerEvolutionAt jointSource occurrence
  project := by
    intro projection current occurrence active
    cases projection with
    | physical => exact (jointCurrentPacket current, jointFrame current, jointCurrentLedger current)
    | history => exact (jointParentHistory, jointParentResult)
    | clock => exact (jointPhysicalTime current, jointPhysicalTime (jointNext current))
    | held => exact (jointHeld current, jointHeld (jointNext current))
    | realization => exact ((jointResponse current).realized, (jointResponse current).inheritedResidual,
        (jointResponse current).newNumericalResidual, (jointResponse current).totalRealizationResidual)
    | generator => exact (Source.hamiltonian, Source.crossMatrix, Producer.sourceJointUnitary)
    | gradient => exact ((jointResponse current).nuclear.currentGradientComponents,
        (jointResponse current).nuclear.targetGradientComponents, (jointResponse current).nuclear.currentGradientRoundingResidual,
        (jointResponse current).nuclear.targetGradientRoundingResidual, (jointResponse current).nuclear.currentGradientPicohartree,
        (jointResponse current).nuclear.targetGradientPicohartree)
    | residual => exact (⟨(jointResponse current).nuclear.positionResidual, (jointResponse current).nuclear.momentumResidual⟩,
        Source.recordedEnergyChange, Source.engineEnergyChange, Source.engineAccountingResidual, Producer.targetKineticResidual)
    | mode => exact (jointSource.toRootSource.actual.compile occurrence).kind
    | firstJoint => exact ⟨Producer.sourceGeneratedJointStep⟩
    | readiness =>
        cases current with
        | ingress => exact nomatch active
        | ready result => exact (result, ⟨rfl, jointReadiness_no_native_write result⟩)
    | wholeLedger => exact jointLedgerCompiler.compile occurrence

def jointAuthoritySource : SourceNativeAuthoritySource N JointV where
  restructuringSource := jointRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal jointRestructuringSource (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := jointProjectionLaw

def jointAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N JointV where
  source := jointAuthoritySource
  emitted := jointEmitted
  compiler_commutes := by intro current; cases current <;> rfl

def jointLivingRoot : SourceNativeLivingRootClosure N JointV :=
  jointAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def jointInitialVisit : SourceNativeTemporalVisitAt jointLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite jointLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
def jointInitialGenerated := jointLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit jointInitialVisit
def jointInitialEntry := entryAt jointSupport
def jointInitialEntryRow : jointInitialGenerated.GeneratedEntryRowAt jointInitialEntry :=
  (jointInitialGenerated.canonicalGeneratedEntryRow? jointInitialEntry).get (by rfl)
def jointFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt jointInitialGenerated.occurrence jointInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? jointInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end
end LAlanine40K2025.JointNext.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
