import H0mework.Versions.AB.Chemistry.LAlanineHeldForce.RuntimeHeldForceLedger
import H0mework.Chemistry.LAlanineHeldForce.ProducerSourceGeneratedLAlanineHeldForce

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
noncomputable section

private def heldForceRestructuringLaw : SourceNativeLedgerRestructuringLaw heldForceSource :=
  identityOnlyWorldLedgerRestructuringLaw heldForceSource LAlanine40K2025.Source.key
    (fun support responsibility => Root.networkOpenAtSubsingleton support responsibility)

private def heldForceRestructuringCompiler : SourceNativeRestructuringLedgerCompiler heldForceSource where
  ledgerCompiler := heldForceLedgerCompiler
  restructuringLaw := heldForceRestructuringLaw
  certifyRestructuring := by
    intro current occurrence
    cases current <;> exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)
      (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)

def heldForceRestructuringSource : SourceNativeRestructuringLedgerSource N HeldForceV where
  source := heldForceSource
  compiler := heldForceRestructuringCompiler

inductive HeldForceProjection
  | physical | clock | held | realization | gradient | mode | firstForce | readiness | wholeLedger

def heldForceProjectionLaw : SourceNativeProjectionLaw heldForceRestructuringSource.toLedgerSource where
  Projection := HeldForceProjection
  ActiveAt := fun projection {current} _ => match projection with
    | .firstForce => match current with | .ingress => PUnit | .ready _ => PEmpty
    | .readiness => match current with | .ingress => PEmpty | .ready _ => PUnit
    | _ => PUnit
  InactiveAt := fun projection {current} _ => match projection with
    | .firstForce => match current with | .ingress => PEmpty | .ready _ => PUnit
    | .readiness => match current with | .ingress => PUnit | .ready _ => PEmpty
    | _ => PEmpty
  classify := by
    intro projection current occurrence
    cases projection <;> try exact .inl PUnit.unit
    all_goals cases current <;> first | exact .inl PUnit.unit | exact .inr PUnit.unit
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .physical => Inertia.Interface.InertialStepReadout × Inertia.Interface.NuclearFrame × Energy.Interface.MolecularEnergyLedger
    | .clock => ℚ × ℚ
    | .held => Matrix Basis Basis ℂ × Matrix Basis Basis ℂ
    | .realization => Matrix Basis Basis ℂ × Matrix Basis Basis ℂ
    | .gradient => Array (Array (Array Int)) × Force.Interface.NuclearCoordinates ×
        Force.Interface.NuclearCoordinates × Force.Interface.NuclearCoordinates × Force.Interface.NuclearCoordinates
    | .mode => RootEvolutionKind
    | .firstForce => PLift Producer.heldForceClosure
    | .readiness => HeldForceResult × PLift
        (heldForceNext current = current ∧ IsEmpty (HeldForceV.NativeWriteAt current))
    | .wholeLedger => SourceNativeLedgerEvolutionAt heldForceSource occurrence
  project := by
    intro projection current occurrence active
    cases projection with
    | physical => exact (heldForceParentMaterial, heldForceFrame current, heldForceCurrentLedger current)
    | clock => exact (heldForcePhysicalTime current, heldForcePhysicalTime (heldForceNext current))
    | held => exact (heldForceHeld current, heldForceHeld (heldForceNext current))
    | realization => exact ((heldForceResponse current).realized, (heldForceResponse current).realizationResidual)
    | gradient =>
        exact ((heldForceResponse current).gradientComponents, (heldForceResponse current).gradientPicohartree,
          (heldForceResponse current).forcePicohartree, (heldForceResponse current).gradientResidual,
          (heldForceResponse current).stationaryCorrection)
    | mode => exact (heldForceSource.toRootSource.actual.compile occurrence).kind
    | firstForce => exact ⟨Producer.sourceGeneratedHeldForce⟩
    | readiness =>
        cases current with
        | ingress => exact nomatch active
        | ready response => exact (response, ⟨rfl, heldForceReadiness_no_native_write response⟩)
    | wholeLedger => exact heldForceLedgerCompiler.compile occurrence

def heldForceAuthoritySource : SourceNativeAuthoritySource N HeldForceV where
  restructuringSource := heldForceRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal heldForceRestructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := heldForceProjectionLaw

def heldForceAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N HeldForceV where
  source := heldForceAuthoritySource
  emitted := heldForceEmitted
  compiler_commutes := by intro current; cases current <;> rfl

def heldForceLivingRoot : SourceNativeLivingRootClosure N HeldForceV :=
  heldForceAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def heldForceInitialVisit : SourceNativeTemporalVisitAt heldForceLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite heldForceLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def heldForceInitialGenerated :=
  heldForceLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit heldForceInitialVisit

def heldForceInitialEntry := entryAt heldForceSupport
def heldForceInitialEntryRow : heldForceInitialGenerated.GeneratedEntryRowAt heldForceInitialEntry :=
  (heldForceInitialGenerated.canonicalGeneratedEntryRow? heldForceInitialEntry).get (by rfl)

def heldForceFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    heldForceInitialGenerated.occurrence heldForceInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? heldForceInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end
end LAlanine40K2025.HeldForce.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
