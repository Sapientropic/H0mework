import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhysicalEnergyWeightPrice
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFilteredSoftCharge

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalEnergyPoleChargeReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance poleChargeQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

/-- The Clifford matrix acts through the same physical matrix reader and mother-space coordinates. -/
def sourceCliffordFiber : DiracMatrix→ₗ[ℂ] FiberOperators:=sourceEnergyMatrixRead.comp spinCoordinates

theorem sourceCliffordFiber_one : sourceCliffordFiber 1=1 := by
  have identity : diracMatrixMatterAction (1:DiracMatrix)=(1:YangMills.FullPairing.Mother) := by
    apply LinearMap.ext
    intro field
    funext row
    simp [diracMatrixMatterAction,Matrix.one_apply]
  change operator (Quantum.operatorMatrix.symm (Quantum.operatorMatrix (diracMatrixMatterAction 1)))=1
  rw [AlgEquiv.symm_apply_apply,identity]
  ext x
  simp [operator]

/-- The full matter insertion remains between the two actual preparation maps and the original Phi. -/
def sourceCliffordCurrent (A : DiracMatrix) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  sourceChargedQuantumRead sideL edgeL sideR edgeR
    ((sourceCliffordFiber A).compLpL 2 volume |>.comp (PacketNoise.phaseShift shift).toContinuousLinearMap)

private theorem clifford_shift_fourier (A : DiracMatrix) (shift : Position) (side edge : Fin 2) :
    fourier ((sourceCliffordFiber A).compLpL 2 volume
      (PacketNoise.phaseShift shift (sourceChargedFilteredPacket side edge)))=ᵐ[volume]
      fun frequency=>sourceCliffordFiber A (fourier (sourceChargedFilteredPacket side edge) (frequency-shift)) := by
  rw [GaugeGreen.constant_fourier,PacketNoise.phaseShift_fourier]
  filter_upwards [(sourceCliffordFiber A).coeFn_compLpL
      (PacketNoise.frequencyShift shift (fourier (sourceChargedFilteredPacket side edge))),
    PacketNoise.frequencyShift_ae shift (fourier (sourceChargedFilteredPacket side edge))] with frequency read moved
  rw [read,moved]

theorem sourceCliffordCurrent_integrable (A : DiracMatrix) (shift : Position)
    (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (fun frequency : Position=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (sourceCliffordFiber A (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)))) volume := by
  apply (L2.integrable_inner (𝕜:=ℂ) (fourier (sourceChargedFilteredPacket sideL edgeL))
    (fourier ((sourceCliffordFiber A).compLpL 2 volume
      (PacketNoise.phaseShift shift (sourceChargedFilteredPacket sideR edgeR))))).congr
  filter_upwards [clifford_shift_fourier A shift sideR edgeR] with frequency read
  rw [read]

theorem sourceCliffordCurrent_fourier (A : DiracMatrix) (shift : Position)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourceCliffordCurrent A shift sideL edgeL sideR edgeR=
      ∫frequency : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
        (sourceCliffordFiber A (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))) := by
  rw [sourceCliffordCurrent,sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  rw [←fourier.inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [clifford_shift_fourier A shift sideR edgeR] with frequency read
  rw [read]

theorem sourceCliffordCurrent_one (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceCliffordCurrent 1 shift sideL edgeL sideR edgeR=sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR := by
  have identity (field : FullMatterL2) : (sourceCliffordFiber 1).compLpL 2 volume field=field := by
    apply Lp.ext
    filter_upwards [(sourceCliffordFiber 1).coeFn_compLpL field] with x read
    rw [read,sourceCliffordFiber_one]
    rfl
  rw [sourceCliffordCurrent,sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap,identity,sourceChargedVoltageOverlap]

/-- All three actual spatial Clifford currents remain independently readable. -/
def sourcePhysicalCliffordSpatialCurrent (j : Fin 3) (shift : Position)
    (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  sourceCliffordCurrent (diracGammaZero*diracGamma j.succ) shift sideL edgeL sideR edgeR

theorem sourcePhysicalEnergyChannel_two_currents (shift : Position) (zeta : ℂ)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyChannel shift zeta 2 sideL edgeL sideR edgeR=
      (Complex.I*zeta)*sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR-
      (Complex.I*(Real.sqrt 30:ℂ)/5)*
        (∑j : Fin 3,fixedMomentum (physicalMomentum shift) zeta j.succ*
          sourcePhysicalCliffordSpatialCurrent j shift sideL edgeL sideR edgeR) := by
  rw [sourcePhysicalEnergyChannel_weights]
  simp only [sourcePhysicalWeightIntegrand,sourcePhysicalPrimalWeight_two]
  change (∫frequency : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
    (sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum (physicalMomentum shift) zeta))
      (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))))=_
  simp only [sourcePhysicalChannelTwoClifford,map_sub,map_smul,map_sum,sub_apply,smul_apply,sum_apply,
    inner_sub_right,inner_smul_right,inner_sum]
  rw [integral_sub]
  · rw [integral_const_mul,integral_const_mul,integral_finsetSum]
    · simp only [integral_const_mul,←sourceCliffordCurrent_fourier,sourceCliffordCurrent_one,
        sourcePhysicalCliffordSpatialCurrent,fixedMomentum,fullMomentum,Fin.cases_zero]
    · intro j _
      exact (sourceCliffordCurrent_integrable (diracGammaZero*diracGamma j.succ) shift sideL edgeL sideR edgeR).const_mul _
  · exact (sourceCliffordCurrent_integrable 1 shift sideL edgeL sideR edgeR).const_mul _
  · exact (integrable_finsetSum Finset.univ (fun (j : Fin 3) _=>
      (sourceCliffordCurrent_integrable (diracGammaZero*diracGamma j.succ) shift sideL edgeL sideR edgeR).const_mul _)).const_mul _

/-- At the actual imaginary-axis frequency, the density is the original canonical current, with every spatial term retained. -/
theorem sourcePhysicalEnergyChannel_two_charge (shift : Position) (frequency : ℝ)
    (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyChannel shift (Complex.I*(frequency:ℂ)) 2 sideL edgeL sideR edgeR=
      (frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR+
      ((ActionNormalization.phaseMomentum:ℂ)*(Real.sqrt 30:ℂ)/5)*
        ∑j : Fin 3,(physicalMomentum shift j:ℂ)*sourcePhysicalCliffordSpatialCurrent j shift sideL edgeL sideR edgeR := by
  rw [sourcePhysicalEnergyChannel_two_currents,sourceFilteredChargeFormFactor_generated]
  simp only [fixedMomentum,fullMomentum,physicalSpatial,Fin.cases_succ,←Finset.mul_sum,mul_assoc]
  ring_nf
  simp only [Complex.I_sq]
  ring

end LowEnergy.PreparationPhysicalEnergyPoleChargeReturn
