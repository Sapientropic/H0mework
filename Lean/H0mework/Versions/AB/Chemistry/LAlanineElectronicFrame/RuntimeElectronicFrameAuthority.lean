import H0mework.Versions.AB.Chemistry.LAlanineElectronicFrame.RuntimeElectronicFrameLedger
import H0mework.Chemistry.LAlanineElectronicFrame.ProducerSourceGeneratedLAlanineElectronicFrame

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section

private def electronicFrameRestructuringLaw : SourceNativeLedgerRestructuringLaw electronicFrameSource :=
  identityOnlyWorldLedgerRestructuringLaw electronicFrameSource LAlanine40K2025.Source.key
    (fun support responsibility => Root.networkOpenAtSubsingleton support responsibility)

private def electronicFrameRestructuringCompiler : SourceNativeRestructuringLedgerCompiler electronicFrameSource where
  ledgerCompiler := electronicFrameLedgerCompiler
  restructuringLaw := electronicFrameRestructuringLaw
  certifyRestructuring := by
    intro current occurrence
    cases current <;> exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)
      (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)

def electronicFrameRestructuringSource : SourceNativeRestructuringLedgerSource N ElectronicFrameV where
  source := electronicFrameSource
  compiler := electronicFrameRestructuringCompiler

inductive ElectronicFrameProjection
  | physical | clock | held | pairing | targetElectronic | mode | firstFrame | readiness | wholeLedger

def electronicFrameProjectionLaw : SourceNativeProjectionLaw electronicFrameRestructuringSource.toLedgerSource where
  Projection := ElectronicFrameProjection
  ActiveAt := fun projection {current} _ => match projection with
    | .firstFrame => match current with | .ingress => PUnit | .ready _ => PEmpty
    | .readiness => match current with | .ingress => PEmpty | .ready _ => PUnit
    | _ => PUnit
  InactiveAt := fun projection {current} _ => match projection with
    | .firstFrame => match current with | .ingress => PEmpty | .ready _ => PUnit
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
    | .pairing => Matrix Basis Basis ℂ × Matrix Basis Basis ℂ × Matrix Basis Basis ℂ × Matrix Basis Basis ℂ
    | .targetElectronic => Matrix Basis Basis ℂ × Matrix Basis Basis ℂ
    | .mode => RootEvolutionKind
    | .firstFrame => PLift Producer.frameClosure
    | .readiness => Matrix Basis Basis ℂ × PLift
        (electronicFrameNext current = current ∧ IsEmpty (ElectronicFrameV.NativeWriteAt current))
    | .wholeLedger => SourceNativeLedgerEvolutionAt electronicFrameSource occurrence
  project := by
    intro projection current occurrence active
    cases projection with
    | physical => exact (electronicFrameParentMaterial, electronicFrameParentFrame, electronicFrameParentEnergyLedger)
    | clock => exact (electronicFramePhysicalTime current, electronicFramePhysicalTime (electronicFrameNext current))
    | held => exact (electronicFrameHeld current, electronicFrameHeld (electronicFrameNext current))
    | pairing => exact (Source.crossMatrix, CFC.abs Source.crossMatrix, Source.sourceUnitary, Source.sourceProjectionResidual)
    | targetElectronic => exact (activeMatrix Source.targetElectronicSource, Producer.scfBenchmark)
    | mode => exact (electronicFrameSource.toRootSource.actual.compile occurrence).kind
    | firstFrame => exact ⟨Producer.sourceGeneratedElectronicFrame⟩
    | readiness =>
        cases current with
        | ingress => exact nomatch active
        | ready held => exact (held, ⟨rfl, electronicFrameReadiness_no_native_write held⟩)
    | wholeLedger => exact electronicFrameLedgerCompiler.compile occurrence

def electronicFrameAuthoritySource : SourceNativeAuthoritySource N ElectronicFrameV where
  restructuringSource := electronicFrameRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal electronicFrameRestructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := electronicFrameProjectionLaw

def electronicFrameAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N ElectronicFrameV where
  source := electronicFrameAuthoritySource
  emitted := electronicFrameEmitted
  compiler_commutes := by intro current; cases current <;> rfl

def electronicFrameLivingRoot : SourceNativeLivingRootClosure N ElectronicFrameV :=
  electronicFrameAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def electronicFrameInitialVisit : SourceNativeTemporalVisitAt electronicFrameLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite electronicFrameLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def electronicFrameInitialGenerated :=
  electronicFrameLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit electronicFrameInitialVisit

def electronicFrameInitialEntry := entryAt electronicFrameSupport
def electronicFrameInitialEntryRow : electronicFrameInitialGenerated.GeneratedEntryRowAt electronicFrameInitialEntry :=
  (electronicFrameInitialGenerated.canonicalGeneratedEntryRow? electronicFrameInitialEntry).get (by rfl)

def electronicFrameFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    electronicFrameInitialGenerated.occurrence electronicFrameInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? electronicFrameInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end
end LAlanine40K2025.ElectronicFrame.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
