import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFilteredVoltageResponse
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.PacketNoise.Modulation

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFilteredChargeVoltage
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace FullQuantum.PerturbedGreen Stage9C.Material.SpinPair
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalVoltageEnergyIdentity
open PreparationPhysicalVoltageNoether PreparationPhysicalChargedEnergyVariation PreparationVacuumVoltageGaussGreen
open GaussHistoryHilbert MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators

/-- Momentum transfer stays inside the same two preparation maps and original quantum state. -/
def sourceFilteredChargeFormFactor (shift : Position) (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  sourceChargedQuantumRead sideL edgeL sideR edgeR
    (sourceFilteredChargeOperator.comp (PacketNoise.phaseShift shift).toContinuousLinearMap)

private theorem shifted_retained (shift : Position) (side edge : Fin 2) :
    (fun x=>sourceVoltageFiberProjection (PacketNoise.phaseShift shift (sourceChargedFilteredPacket side edge) x))=ᵐ[volume]
      PacketNoise.phaseShift shift (sourceChargedFilteredPacket side edge) := by
  filter_upwards [sourceFilteredPacket_retained_ae side edge,
    PacketNoise.phaseShift_position shift (sourceChargedFilteredPacket side edge)] with x fixed shifted
  rw [shifted,map_smul,fixed]

/-- The form factor is computed by the original canonical current, with no prescribed charge outcome. -/
theorem sourceFilteredChargeFormFactor_generated (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR=
      -(ActionNormalization.phaseMomentum:ℂ)*sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR := by
  rw [sourceFilteredChargeFormFactor,sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  rw [sourceFilteredChargeOperator,smul_apply,inner_smul_right,L2.inner_def,
    sourceChargedVoltageOverlap,L2.inner_def,←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(Electromagnetic.CanonicalPacket.densityReader
      (Stage9DEF.Compatibility.currentAction 0 HyperchargeResponse.chargeDirection)).coeFn_compLpL
        (PacketNoise.phaseShift shift (sourceChargedFilteredPacket sideR edgeR)),
    sourceFilteredPacket_retained_ae sideL edgeL,shifted_retained shift sideR edgeR] with x reader left right
  rw [reader,sourceCanonicalCharge_voltage,neg_apply,inner_neg_right]
  rw [sourceVoltageHamiltonian_pair sourceVoltageActualState
    (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint).2 1 0 _ _ left right]
  simp only [Complex.ofReal_one,one_mul,ActionNormalization.phaseMomentum_source,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

/-- The physical Fourier phase uses the paid 2pi convention, with no new normalization. -/
theorem sourceFilteredChargeFormFactor_fourier (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR=
      ∫x : Position,Complex.exp (((∑j : Fin 3,physicalMomentum shift j*x j:ℝ):ℂ)*Complex.I)*
        sourceFilteredCurrent sideL edgeL sideR edgeR x := by
  rw [sourceFilteredChargeFormFactor_generated,sourceChargedVoltageOverlap,L2.inner_def,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [sourceFilteredCurrent_pair sideL edgeL sideR edgeR,
    PacketNoise.phaseShift_physicalMomentum shift (sourceChargedFilteredPacket sideR edgeR)] with x current shifted
  rw [current,shifted,inner_smul_right]
  ring

theorem sourceFilteredChargeFormFactor_continuous (sideL edgeL sideR edgeR : Fin 2) :
    Continuous (fun shift=>sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR) := by
  simp only [sourceFilteredChargeFormFactor_generated,sourceChargedVoltageOverlap]
  exact (continuous_const.inner (PacketNoise.phaseShift_continuous _)).const_mul _

/-- The actual filtered packet's zero-transfer current is its generated source momentum charge. -/
theorem sourceFilteredChargeFormFactor_zero (side edge : Fin 2) :
    sourceFilteredChargeFormFactor 0 side edge side edge=-(ActionNormalization.phaseMomentum:ℂ) := by
  rw [sourceFilteredChargeFormFactor_generated,sourceChargedVoltageOverlap_unit,mul_one]

theorem sourceFilteredChargeFormFactor_soft (side edge : Fin 2) :
    Tendsto (fun shift=>sourceFilteredChargeFormFactor shift side edge side edge)
      (𝓝 (0:Position)) (𝓝 (-(ActionNormalization.phaseMomentum:ℂ))) := by
  simpa only [sourceFilteredChargeFormFactor_zero] using
    (sourceFilteredChargeFormFactor_continuous side edge side edge).tendsto (0:Position)

end LowEnergy.PreparationPhysicalFilteredChargeVoltage
