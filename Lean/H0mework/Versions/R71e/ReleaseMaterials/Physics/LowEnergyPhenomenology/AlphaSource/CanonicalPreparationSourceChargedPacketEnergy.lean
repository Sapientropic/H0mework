import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedPacketCurrent
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageGreenEnergy
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePacketGreenTail

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedPacketVoltage
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineCanonicalCauchyState Stage9C.Material.SpinPair Stage10
open PreparationVacuumVoltageGaussGreen PreparationPhysicalVoltageNoether
open PreparationVacuumChargedPacketGreen FullQuantum FullSpace
open CanonicalGradedSpatialSource
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb UnifiedAction.AtomicScales
open MeasureTheory Filter
open scoped Topology InnerProductSpace SchwartzMap

/-- The actual second packet's integrated current reads the Noether energy of the generated source field. -/
def sourceChargedPacketPotentialEnergy (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (sourceSide sourceEdge testSide testEdge : Fin 2) (x : Point) : ℝ :=
  -(∫y : Point,sourceVoltageRawCharge
    (sourceChargedPacketMatter testSide testEdge) (sourceChargedPacketDual testSide testEdge) y)*
    (sourceVoltageActualEnergy epsilon precision p sourceVoltageActualState
      (sourceVoltageGreenProfile (sourceChargedPacketMatter sourceSide sourceEdge)
        (sourceChargedPacketDual sourceSide sourceEdge))
      (canonicalCauchySlicePoint 0 (WithLp.toLp 2 x)) testSide testEdge testSide testEdge).re

/-- The previously generated packet Green energy is now the direct original Noether energy read. -/
theorem sourceChargedPacket_energy_generated (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (sourceSide sourceEdge testSide testEdge : Fin 2) (x : Point) :
    sourceChargedPacketPotentialEnergy epsilon precision p sourceSide sourceEdge testSide testEdge x=
      sourcePacketPotentialEnergy x := by
  unfold sourceChargedPacketPotentialEnergy
  rw [sourceChargedPacket_totalCurrent,neg_neg]
  rw [sourceVoltage_green_energy epsilon precision p]
  simp only [ite_true,mul_one,Complex.ofReal_re]
  simp_rw [StaticGreen.potential,sourceChargedPacket_raw,ActionNormalization.phaseMomentum_source]
  rfl

/-- The complete coefficient is inherited once from the original Gauss kernel and both original current legs. -/
theorem sourceChargedPacket_energy_kernel (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (sourceSide sourceEdge testSide testEdge : Fin 2) (x : Point) :
    sourceChargedPacketPotentialEnergy epsilon precision p sourceSide sourceEdge testSide testEdge x=
      ActionNormalization.phaseMomentum^2/(8*Real.pi*lapse)*
        (∫y : Point,sourcePacketDensity y*kernel (x-y)) := by
  rw [sourceChargedPacket_energy_generated,sourcePacketPotentialEnergy_kernel,
    original_coulomb_coefficient,ActionNormalization.phaseMomentum_source]

/-- The independent test packet's local current returns the physical pair energy to its unit-density read. -/
theorem sourceChargedPacket_pair_return (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (sideA edgeA sideB edgeB : Fin 2) :
    -(∫x : Point,sourceVoltageRawCharge (sourceChargedPacketMatter sideA edgeA) (sourceChargedPacketDual sideA edgeA) x*
      (sourceVoltageActualEnergy epsilon precision p sourceVoltageActualState
        (sourceVoltageGreenProfile (sourceChargedPacketMatter sideB edgeB) (sourceChargedPacketDual sideB edgeB))
        (canonicalCauchySlicePoint 0 (WithLp.toLp 2 x)) sideA edgeA sideA edgeA).re)=
      ∫x : Point,sourcePacketDensity x*
        sourceChargedPacketPotentialEnergy epsilon precision p sideB edgeB sideA edgeA x := by
  unfold sourceChargedPacketPotentialEnergy
  rw [sourceChargedPacket_totalCurrent,neg_neg]
  simp only [sourceChargedPacket_raw]
  rw [←integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- Both independent charged source preparations enter the complete pair-energy kernel. -/
theorem sourceChargedPacket_pair_energy (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (sideA edgeA sideB edgeB : Fin 2) :
    -(∫x : Point,sourceVoltageRawCharge (sourceChargedPacketMatter sideA edgeA) (sourceChargedPacketDual sideA edgeA) x*
      (sourceVoltageActualEnergy epsilon precision p sourceVoltageActualState
        (sourceVoltageGreenProfile (sourceChargedPacketMatter sideB edgeB) (sourceChargedPacketDual sideB edgeB))
        (canonicalCauchySlicePoint 0 (WithLp.toLp 2 x)) sideA edgeA sideA edgeA).re)=
      ActionNormalization.phaseMomentum^2/(8*Real.pi*lapse)*
        (∫xy : Point×Point,sourcePacketDensity xy.1*sourcePacketDensity xy.2*kernel (xy.2-xy.1)) := by
  rw [sourceVoltage_pair_energy epsilon precision p
    (sourceChargedPacketMatter sideA edgeA) (sourceChargedPacketMatter sideB edgeB)
    (sourceChargedPacketDual sideA edgeA) (sourceChargedPacketDual sideB edgeB)
    (sourceChargedPacket_integrable sideA edgeA) (sourceChargedPacket_integrable sideB edgeB)
    (‖ActionNormalization.phaseMomentum‖*HistoryPrepared.packetScale⁻¹^2)
    (sourceChargedPacket_bounded sideB edgeB)]
  simp only [sourceChargedPacket_raw]
  have factor : (fun xy : Point×Point=>
      (-ActionNormalization.phaseMomentum*sourcePacketDensity xy.1)*
        (-ActionNormalization.phaseMomentum*sourcePacketDensity xy.2)*kernel (xy.2-xy.1))=
      fun xy=>ActionNormalization.phaseMomentum^2*
        (sourcePacketDensity xy.1*sourcePacketDensity xy.2*kernel (xy.2-xy.1)) := by
    funext xy
    ring
  rw [factor,integral_const_mul]
  ring

/-- The original finite-support preparation controls the actual measured energy tail. -/
theorem sourceChargedPacket_energy_tail (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (sourceSide sourceEdge testSide testEdge : Fin 2) (x : Point) (outside : 1<distance x) :
    |sourceChargedPacketPotentialEnergy epsilon precision p sourceSide sourceEdge testSide testEdge x-
      canonicalCoulomb*kernel x|≤canonicalCoulomb/(distance x*(distance x-1)) := by
  rw [sourceChargedPacket_energy_generated]
  exact sourcePacketPotentialEnergy_tail x outside

end LowEnergy.PreparationPhysicalChargedPacketVoltage
