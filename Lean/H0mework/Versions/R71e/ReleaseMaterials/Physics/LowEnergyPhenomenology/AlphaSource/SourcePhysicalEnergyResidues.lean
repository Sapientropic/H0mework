import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhysicalEnergyChannels
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedStaticLaurent

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedEnergyPoleReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair
open FullQuantum FullSpace PreparationPhysicalChargedEnergyVariation
open PreparationVacuumChargedLongRangeRead PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalQuantumLockedCharge PreparationPhysicalChargedPacketVoltage
open PreparationVacuumObservedBoundaryResidue PreparationVacuumObservedStaticResidue
open PreparationVacuumChargedSpatialResponse PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumCausalPoleResponse PreparationVacuumStaticSimpleCoupling
open PreparationVacuumPhysicalPoleSheet PreparationVacuumObservedPoleTensor
open PreparationVacuumOriginalGreenFeedback PreparationVacuumWholeOrigin PreparationVacuumFullSlowFieldResponse
open PreparationVacuumPhysicalCharacteristic
open CanonicalGradedSpatialSource
open Filter Set
open scoped Topology BigOperators Matrix

variable (q : PhysicalResponsePoint) (shift : Position)
  (a b c d sideL edgeL sideR edgeR : Fin 2)

def sourcePhysicalEnergyBoundary (frequency : ℝ) : ℂ :=
  sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
    (sourceChargedBoundaryField q (physicalMomentum shift) frequency (sourceChargedRestIndex a b) (sourceChargedRestIndex c d))

def sourcePhysicalEnergyStaticDouble : ℂ :=
  sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
    (sourceChargedStaticDouble q (physicalMomentum shift) (sourceChargedRestIndex a b) (sourceChargedRestIndex c d))

def sourcePhysicalEnergyStaticSimple : ℂ :=
  sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
    (sourceChargedStaticSimple q (physicalMomentum shift) (sourceChargedRestIndex a b) (sourceChargedRestIndex c d))

/-- The actual complete retainer and propagating-pole residue is now read by the physical Phi observable. -/
theorem sourcePhysicalEnergyBoundary_generated (frequency : ℝ) (nonzero : frequency≠0) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)^3*
      sourceChargedModeEnergyRead q shift (sourcePoleSide frequency eta) a b c d sideL edgeL sideR edgeR)
      (𝓝[>] 0) (𝓝 (sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency)) := by
  have generated:=(sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR).continuous.continuousAt.tendsto.comp
    (sourceChargedSecondField_boundary q (physicalMomentum shift) frequency nonzero
      (sourceChargedRestIndex a b) (sourceChargedRestIndex c d))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,sourcePhysicalEnergyBoundary,
    sourcePhysicalEnergyReader_original,sourceChargedModeEnergyRead] using generated

theorem sourcePhysicalEnergyBoundary_channels (frequency : ℝ) :
    sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency=
      ∑i : Fin 3,sourceChargedDenominatorResidue (physicalMomentum shift) frequency i*
        sourceSlowRead (sourceNativeBoundaryResidue q (physicalMomentum shift) frequency
          (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)) ⟨i.val,by omega⟩*
        sourcePhysicalEnergyChannel shift (Complex.I*(frequency:ℂ)) i sideL edgeL sideR edgeR := by
  simp only [sourcePhysicalEnergyBoundary,sourceChargedBoundaryField,map_sum,map_smul,
    smul_eq_mul,←sourcePhysicalEnergyChannel_generated]

/-- The source's true static double term is retained; it is not replaced by a Coulomb coefficient. -/
theorem sourcePhysicalEnergyStaticDouble_generated (spatial : 0<spatialSquare (physicalMomentum shift)) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)^2*sourceChargedModeEnergyRead q shift (eta:ℂ) a b c d sideL edgeL sideR edgeR)
      (𝓝[>] 0) (𝓝 (sourcePhysicalEnergyStaticDouble q shift a b c d sideL edgeL sideR edgeR)) := by
  have generated:=(sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR).continuous.continuousAt.tendsto.comp
    (sourceChargedStaticDouble_generated q (physicalMomentum shift) spatial
      (sourceChargedRestIndex a b) (sourceChargedRestIndex c d))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,sourcePhysicalEnergyStaticDouble,
    sourcePhysicalEnergyReader_original,sourceChargedModeEnergyRead] using generated

/-- Subtracting the generated double coefficient leaves the actual simple coefficient with both cross legs and time jet. -/
theorem sourcePhysicalEnergyStaticSimple_generated (spatial : 0<spatialSquare (physicalMomentum shift)) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)*(sourceChargedModeEnergyRead q shift (eta:ℂ) a b c d sideL edgeL sideR edgeR-
      ((eta:ℂ)⁻¹)^2*sourcePhysicalEnergyStaticDouble q shift a b c d sideL edgeL sideR edgeR))
      (𝓝[>] 0) (𝓝 (sourcePhysicalEnergyStaticSimple q shift a b c d sideL edgeL sideR edgeR)) := by
  have generated:=(sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR).continuous.continuousAt.tendsto.comp
    (sourceChargedStaticSimple_generated q (physicalMomentum shift) spatial
      (sourceChargedRestIndex a b) (sourceChargedRestIndex c d))
  simpa only [Function.comp_def,map_smul,map_sub,smul_eq_mul,sourcePhysicalEnergyStaticDouble,
    sourcePhysicalEnergyStaticSimple,sourcePhysicalEnergyReader_original,sourceChargedModeEnergyRead] using generated

theorem sourcePhysicalEnergyStaticDouble_channels :
    sourcePhysicalEnergyStaticDouble q shift a b c d sideL edgeL sideR edgeR=
      (∑i : Fin 3,(sourceChargedDenominator (physicalMomentum shift) 0 i)⁻¹*
        sourceSlowRead (sourceStaticNative q (physicalMomentum shift)
          (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)) ⟨i.val,by omega⟩*
        sourcePhysicalEnergyChannel shift 0 i sideL edgeL sideR edgeR)+
      sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
        (sourceRegularMatrix 0*ᵥsourceStaticCurrent q (physicalMomentum shift)
          (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)) := by
  simp only [sourcePhysicalEnergyStaticDouble,sourceChargedStaticDouble,map_add,map_sum,map_smul,
    smul_eq_mul,←sourcePhysicalEnergyChannel_generated]

end LowEnergy.PreparationPhysicalChargedEnergyPoleReturn
