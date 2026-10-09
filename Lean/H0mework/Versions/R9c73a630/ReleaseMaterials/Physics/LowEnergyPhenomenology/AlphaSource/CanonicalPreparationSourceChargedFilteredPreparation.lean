import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedPacketEnergy
import H0mework.Versions.AB.Physics.LowEnergy.PacketNoise.Filtered

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedPacketQuantumReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9C.Material.SpinPair
open FullQuantum FullSpace SpatialGreen HistoryPrepared HistoryGenerator GaugeHistory
open YangMills.FullPairing Stage10
open PreparationPhysicalChargedPacketVoltage PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumElectromagneticIdentity
open MeasureTheory Filter
open scoped InnerProductSpace Topology

/-- The matching source uses the original E=0, damping=1 Dirac Green, after the actual charged preparation. -/
def sourcePacketDiracFilter : FullMatterL2→L[ℂ] FullMatterL2 := green 0 0 1 (by norm_num)

def sourceChargedRawPacket (side edge : Fin 2) : FullMatterL2 :=
  sourcePacketDiracFilter (sourceChargedSpatialPacket side edge)

theorem sourceChargedSpatialPacket_unit (side edge : Fin 2) :
    ‖sourceChargedSpatialPacket side edge‖=1 := by
  rw [sourceChargedSpatialPacket_maker,HistoryPrepared.preparation_norm]
  have unit:=actualRestState_orthonormal 0 (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge)
  rw [if_pos rfl] at unit
  have real:=congrArg Complex.re unit
  change RCLike.re (inner ℂ
    (operator (actualRestStatePreparation (sourceChargedRestIndex side edge)) (YangMills.FullPairing.prepared 0))
    (operator (actualRestStatePreparation (sourceChargedRestIndex side edge)) (YangMills.FullPairing.prepared 0)))=1 at real
  rw [inner_self_eq_norm_sq] at real
  nlinarith [norm_nonneg (operator (actualRestStatePreparation (sourceChargedRestIndex side edge))
    (YangMills.FullPairing.prepared 0))]

theorem sourceChargedRawPacket_nonzero (side edge : Fin 2) : sourceChargedRawPacket side edge≠0 := by
  apply nonzero_response 0 0 1 (by norm_num) (sourceChargedSpatialPacket side edge)
  intro zero
  have unit:=sourceChargedSpatialPacket_unit side edge
  rw [zero,norm_zero] at unit
  norm_num at unit

def sourceChargedFilter (side edge : Fin 2) : FullMatterL2→L[ℂ] FullMatterL2 :=
  ((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) • sourcePacketDiracFilter

def sourceChargedFilteredPacket (side edge : Fin 2) : FullMatterL2 :=
  sourceChargedFilter side edge (sourceChargedSpatialPacket side edge)

theorem sourceChargedFilteredPacket_unit (side edge : Fin 2) :
    ‖sourceChargedFilteredPacket side edge‖=1 := by
  change ‖((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) • sourceChargedRawPacket side edge‖=1
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sourceChargedRawPacket_nonzero side edge))

theorem sourceChargedFilteredPacket_domain (side edge : Fin 2) :
    sourceChargedFilteredPacket side edge∈Quantum.Generator.domain freeAction := by
  have raw:=(generator_domain_iff_original 0 1 (by norm_num) _).mpr
    (green_domain 0 0 1 (by norm_num) (sourceChargedSpatialPacket side edge))
  exact (Quantum.Generator.domain freeAction).smul_mem
    ((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) raw

/-- This finite source displacement precedes the filter and retains the original internal preparation. -/
def sourceChargedPreparationDistance (side edge : Fin 2) : ℝ :=
  ‖naturalCoordinates (sourceChargedRestriction side edge)-YangMills.FullPairing.prepared 0‖

theorem sourceChargedPacket_difference (side edge : Fin 2) :
    ‖sourceChargedSpatialPacket side edge-HistoryPrepared.preparedPacket‖=
      sourceChargedPreparationDistance side edge := by
  rw [sourceChargedSpatialPacket,HistoryPrepared.preparedPacket,←map_sub,HistoryPrepared.preparation_norm]
  rfl

theorem sourceChargedRawPacket_difference (side edge : Fin 2) :
    ‖sourceChargedRawPacket side edge-PacketNoise.rawPacket 0 1 (by norm_num)‖≤
      ‖sourcePacketDiracFilter‖*sourceChargedPreparationDistance side edge := by
  change ‖sourcePacketDiracFilter (sourceChargedSpatialPacket side edge)-
    sourcePacketDiracFilter HistoryPrepared.preparedPacket‖≤_
  rw [←map_sub]
  exact (sourcePacketDiracFilter.le_opNorm _).trans_eq (by rw [sourceChargedPacket_difference])

end LowEnergy.PreparationPhysicalChargedPacketQuantumReturn
