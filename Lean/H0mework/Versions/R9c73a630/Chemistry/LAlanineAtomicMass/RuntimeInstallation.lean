import H0mework.Versions.R9c73a630.Chemistry.LAlanineAtomicMass.RuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineAtomicMass.SourceClosure

/-! Install isotope identity and faithful mass as restrictions of the original Root58 event. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.AtomicMass.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Force.Interface Inertia.Mechanics
noncomputable section

structure AtomicMassMaterial where
  parent : BasinRefinement.BandConservationRuntime.BandConservationMaterial
  preparation : Source.MassPreparation
  species : Atom → Int × Int
  relativeMasses : Masses
  massNumberResiduals : Masses
  conversionResiduals : Masses
  reconstructedMasses : Masses
  atomicFibres : Atom ≃ Σ charge : Int, Σ massNumber : Int, AtomicResidual charge massNumber
  nuclearReference : PhasePoint
  targetKinetic : ℚ

def generatedAtomicMassMaterial : AtomicMassMaterial where
  parent := atomicMassParentMaterial
  preparation := Source.preparation
  species := isotopeFace
  relativeMasses := Source.relativeMass
  massNumberResiduals := Source.massNumberResidual
  conversionResiduals := Source.conversionResidual
  reconstructedMasses := Source.reconstructedMass
  atomicFibres := atomEquivIsotopeResidual
  nuclearReference := Dynamics.reconstructedReference
  targetKinetic := Dynamics.reconstructedKinetic

inductive AtomicMassProjection
  | material | certificate

def atomicMassProjectionLaw : SourceNativeProjectionLaw AtomicMassLedger where
  Projection := AtomicMassProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt AtomicMassLedger.source occurrence × AtomicMassMaterial
    | .certificate => PLift AtomicMassClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (AtomicMassLedger.ledgerCompiler.compile occurrence, generatedAtomicMassMaterial)
    | certificate => exact ⟨sourceGeneratedAtomicMassClosure⟩

def atomicMassAuthoritySource := AtomicMassBase.withProjectionCoface atomicMassProjectionLaw
def atomicMassComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt atomicMassProjectionLaw atomicMassAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface AtomicMassBase atomicMassProjectionLaw
def atomicMassInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt AtomicMassBase.projectionLaw atomicMassAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface AtomicMassBase atomicMassProjectionLaw

def atomicMassAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := atomicMassAuthoritySource
  emitted := BasinRefinement.BandConservationRuntime.bandConservationAuthoritativeRoot.emitted
  compiler_commutes := BasinRefinement.BandConservationRuntime.bandConservationAuthoritativeRoot.compiler_commutes

def atomicMassLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  atomicMassAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem atomicMass_source_and_law_unchanged :
    atomicMassAuthoritySource.restructuringSource = AtomicMassBase.restructuringSource ∧
    atomicMassAuthoritySource.eventInventoryAdmission = AtomicMassBase.eventInventoryAdmission ∧
    atomicMassAuthoritySource.lawSurface = AtomicMassBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem atomicMass_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    atomicMassAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      BasinRefinement.BandConservationRuntime.bandConservationAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.AtomicMass.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
