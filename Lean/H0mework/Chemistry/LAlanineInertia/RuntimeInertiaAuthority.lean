import H0mework.Chemistry.LAlanineInertia.RuntimeInertiaLedger
import H0mework.Chemistry.LAlanineInertia.ProducerSourceGeneratedLAlanine40KInertialStep

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

private def inertiaRestructuringLaw : SourceNativeLedgerRestructuringLaw inertiaSource :=
  identityOnlyWorldLedgerRestructuringLaw inertiaSource LAlanine40K2025.Source.key
    (fun support responsibility => Root.networkOpenAtSubsingleton support responsibility)

private def inertiaRestructuringCompiler : SourceNativeRestructuringLedgerCompiler inertiaSource where
  ledgerCompiler := inertiaLedgerCompiler
  restructuringLaw := inertiaRestructuringLaw
  certifyRestructuring := by
    intro current occurrence
    cases current <;> exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)
      (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)

def inertiaRestructuringSource : SourceNativeRestructuringLedgerSource N InertiaV where
  source := inertiaSource
  compiler := inertiaRestructuringCompiler

inductive InertiaProjection
  | material | frame | energyLedger | clock | mode | firstStep | readiness | wholeLedger

def inertiaProjectionLaw : SourceNativeProjectionLaw inertiaRestructuringSource.toLedgerSource where
  Projection := InertiaProjection
  ActiveAt := fun projection {current} _ => match projection with
    | .firstStep => match current with | .ingress => PUnit | .ready _ => PEmpty
    | .readiness => match current with | .ingress => PEmpty | .ready _ => PUnit
    | _ => PUnit
  InactiveAt := fun projection {current} _ => match projection with
    | .firstStep => match current with | .ingress => PEmpty | .ready _ => PUnit
    | .readiness => match current with | .ingress => PUnit | .ready _ => PEmpty
    | _ => PEmpty
  classify := by
    intro projection current occurrence
    cases projection <;> try exact .inl PUnit.unit
    all_goals cases current <;> first | exact .inl PUnit.unit | exact .inr PUnit.unit
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .material => Interface.InertialStepReadout
    | .frame => Interface.NuclearFrame × Interface.NuclearFrame
    | .energyLedger => Energy.Interface.MolecularEnergyLedger × Energy.Interface.MolecularEnergyLedger
    | .clock => ℚ × ℚ
    | .mode => RootEvolutionKind
    | .firstStep => PLift Producer.firstStepClosure
    | .readiness => Interface.InertialStepReadout × PLift
        (inertiaNext current = current ∧
          inertiaPhysicalTime (inertiaNext current) = inertiaPhysicalTime current ∧
          IsEmpty (InertiaV.NativeWriteAt current))
    | .wholeLedger => SourceNativeLedgerEvolutionAt inertiaSource occurrence
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact inertiaReadout current
    | frame => exact (inertiaFrame current, inertiaFrame (inertiaNext current))
    | energyLedger => exact (inertiaCurrentLedger current, inertiaCurrentLedger (inertiaNext current))
    | clock => exact (inertiaPhysicalTime current, inertiaPhysicalTime (inertiaNext current))
    | mode => exact (inertiaSource.toRootSource.actual.compile occurrence).kind
    | firstStep => exact ⟨Producer.sourceGeneratedFirstStep⟩
    | readiness =>
        cases current with
        | ingress => exact nomatch active
        | ready material => exact (material, ⟨rfl, rfl, inertiaReadiness_no_native_write material⟩)
    | wholeLedger => exact inertiaLedgerCompiler.compile occurrence

def inertiaAuthoritySource : SourceNativeAuthoritySource N InertiaV where
  restructuringSource := inertiaRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal inertiaRestructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := inertiaProjectionLaw

def inertiaAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N InertiaV where
  source := inertiaAuthoritySource
  emitted := inertiaEmitted
  compiler_commutes := by intro current; cases current <;> rfl

def inertiaLivingRoot : SourceNativeLivingRootClosure N InertiaV :=
  inertiaAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def inertiaInitialVisit : SourceNativeTemporalVisitAt inertiaLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite inertiaLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def inertiaInitialGenerated :=
  inertiaLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit inertiaInitialVisit

def inertiaInitialEntry := entryAt inertiaSupport

def inertiaInitialEntryRow : inertiaInitialGenerated.GeneratedEntryRowAt inertiaInitialEntry :=
  (inertiaInitialGenerated.canonicalGeneratedEntryRow? inertiaInitialEntry).get (by rfl)

def inertiaFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    inertiaInitialGenerated.occurrence inertiaInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? inertiaInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end
end LAlanine40K2025.Inertia.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
