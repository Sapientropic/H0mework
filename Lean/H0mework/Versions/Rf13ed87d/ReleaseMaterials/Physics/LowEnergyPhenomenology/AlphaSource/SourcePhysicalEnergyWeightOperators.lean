import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhysicalEnergyWeightsReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalEnergyWeightsReturn
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
local instance weightOperatorsQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing

/-- The three generated columns retain the twelve actual real field axes before complex continuation. -/
theorem sourcePhysicalPrimalWeight_axes (p : PhysicalMomentum) (v : Fin 4→ℂ) (i : Fin 3) :
    sourcePhysicalPrimalWeight p v i=
      ∑k : Fin 4,v k • affineMatrix
        (sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection (sourceEnergyAxisField i k))) p := by
  unfold sourcePhysicalPrimalWeight
  rw [sourceLiteralEnergyWeight_axes]
  simp_rw [sourceLiteralEnergyWeight_axis p sourceVoltageActualState (sourceState_valid sourcePoint),
    sourceNormalizedEnergySymbol_matrix p sourceVoltageActualState _ (sourceState_valid sourcePoint)]
  ext a b
  simp only [Matrix.toBlocks₁₁,Matrix.of_apply,Matrix.sum_apply,Matrix.smul_apply,
    fourierLinear,LinearMap.coe_mk,AddHom.coe_mk,realFourierMatrix,Matrix.fromBlocks_apply₁₁]

/-- The complete primal channel-two matrix, before any choice of external state. -/
def sourcePhysicalChannelTwoClifford (v : Fin 4→ℂ) : DiracMatrix :=
  (Complex.I*v 0) • 1-(Complex.I*(Real.sqrt 30:ℂ)/5) •
    (∑j : Fin 3,v j.succ • (diracGammaZero*diracGamma j.succ))

private theorem channelTwoClifford_axes (v : Fin 4→ℂ) :
    (∑k : Fin 4,v k • sourcePhysicalChannelTwoClifford (fun j=>((Pi.single k (1:ℝ):Fin 4→ℝ) j:ℂ)))=
      sourcePhysicalChannelTwoClifford v := by
  simp only [sourcePhysicalChannelTwoClifford,Fin.sum_univ_four,Fin.sum_univ_three,
    Pi.single_apply,Fin.reduceEq,if_true,if_false,Complex.ofReal_one,Complex.ofReal_zero,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  have last : (2:Fin 3).succ=(3:Fin 4):=rfl
  simp only [last,Fin.reduceEq,if_true,if_false,Complex.ofReal_one,Complex.ofReal_zero,
    one_smul,zero_smul,mul_one,mul_zero,add_zero,zero_add,smul_zero,sub_zero]
  module

theorem sourcePhysicalPrimalWeight_two (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourcePhysicalPrimalWeight p v 2=spinCoordinates (sourcePhysicalChannelTwoClifford v) := by
  unfold sourcePhysicalPrimalWeight
  change (sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 2).toBlocks₁₁=_
  rw [sourceLiteralChannelTwoEnergy,←channelTwoClifford_axes v]
  simp only [map_sum,map_smul]
  ext a b
  simp only [Matrix.toBlocks₁₁,Matrix.of_apply,Matrix.sum_apply,Matrix.smul_apply,
    SourceRealScalarFock.branches,Matrix.fromBlocks_apply₁₁,sourcePhysicalChannelTwoClifford]

theorem sourcePhysicalChannelTwo_operator (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourceEnergyMatrixRead (sourcePhysicalPrimalWeight p v 2)=
      operator (diracMatrixMatterAction (sourcePhysicalChannelTwoClifford v)) := by
  rw [sourcePhysicalPrimalWeight_two]
  change operator (Quantum.operatorMatrix.symm (Quantum.operatorMatrix _))=_
  rw [AlgEquiv.symm_apply_apply]

/-- Every spatial Clifford term acts on the actual full filtered packets, including their momentum mixing. -/
theorem sourcePhysicalEnergyChannel_two_clifford (shift : Position) (zeta : ℂ)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyChannel shift zeta 2 sideL edgeL sideR edgeR=
      ∫frequency : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
        (operator (diracMatrixMatterAction (sourcePhysicalChannelTwoClifford (fixedMomentum (physicalMomentum shift) zeta)))
          (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))) := by
  rw [sourcePhysicalEnergyChannel_weights]
  simp only [sourcePhysicalWeightIntegrand,sourcePhysicalChannelTwo_operator]

theorem sourcePhysicalChannelTwo_clifford_integrable (shift : Position) (zeta : ℂ)
    (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (fun frequency : Position=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (operator (diracMatrixMatterAction (sourcePhysicalChannelTwoClifford (fixedMomentum (physicalMomentum shift) zeta)))
        (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)))) volume := by
  apply (sourcePhysicalWeight_integrable shift zeta 2 sideL edgeL sideR edgeR).congr
  exact Filter.Eventually.of_forall (fun frequency=>by
    simp only [sourcePhysicalWeightIntegrand,sourcePhysicalChannelTwo_operator])

end LowEnergy.PreparationPhysicalEnergyWeightsReturn
