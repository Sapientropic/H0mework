import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhysicalEnergyChannels
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualEnergyChannels

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
local instance weightsQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

/-- The original physical matter read is the primal block of the complete energy weight. -/
def sourcePhysicalPrimalWeight (p : PhysicalMomentum) (v : Fin 4→ℂ) (i : Fin 3) : SourceMatrix :=
  (sourceLiteralEnergyWeight p sourceVoltageActualState v i).toBlocks₁₁

theorem sourcePhysicalPrimalWeight_source (p : PhysicalMomentum) (v : Fin 4→ℂ) (i : Fin 3) :
    sourcePhysicalPrimalWeight p v i=
      ∑j : Fin 289,sourceMatrix sourceEnergyChannelTerms v j ⟨i.val,by omega⟩ •
        affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection (fieldUnit j))) p := by
  unfold sourcePhysicalPrimalWeight
  rw [sourceLiteralEnergyWeight_generated,
    sourceFullEnergyMatrix_generated p sourceVoltageActualState (sourceState_valid sourcePoint)]
  ext a b
  simp only [Matrix.toBlocks₁₁,Matrix.of_apply,Matrix.sum_apply,Matrix.smul_apply,
    fourierLinear,LinearMap.coe_mk,AddHom.coe_mk,realFourierMatrix,Matrix.fromBlocks_apply₁₁,
    sourceEnergyChannelMatrix_entry]

/-- The same original energy matrices are evaluated on the actual filtered source packets. -/
def sourcePhysicalWeightIntegrand (shift : Position) (zeta : ℂ) (i : Fin 3)
    (sideL edgeL sideR edgeR : Fin 2) (frequency : Position) : ℂ :=
  inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
    (sourceEnergyMatrixRead
      (sourcePhysicalPrimalWeight (physicalMomentum (frequency-shift))
        (fixedMomentum (physicalMomentum shift) zeta) i)
      (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)))

theorem sourcePhysicalWeightIntegrand_source (shift : Position) (zeta : ℂ) (i : Fin 3)
    (sideL edgeL sideR edgeR : Fin 2) (frequency : Position) :
    sourcePhysicalWeightIntegrand shift zeta i sideL edgeL sideR edgeR frequency=
      ∑j : Fin 289,sourceMatrix sourceEnergyChannelTerms (fixedMomentum (physicalMomentum shift) zeta)
        j ⟨i.val,by omega⟩*
        inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
          (sourceEnergyMatrixRead
            (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection (fieldUnit j)))
              (physicalMomentum (frequency-shift)))
            (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))) := by
  simp only [sourcePhysicalWeightIntegrand,sourcePhysicalPrimalWeight_source,map_sum,map_smul,
    sum_apply,smul_apply,inner_sum,inner_smul_right]

theorem sourcePhysicalWeight_integrable (shift : Position) (zeta : ℂ) (i : Fin 3)
    (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (sourcePhysicalWeightIntegrand shift zeta i sideL edgeL sideR edgeR) volume := by
  have generated:=integrable_finsetSum Finset.univ
    (fun (j : Fin 289) _=>
      (sourceChargedEnergyRead_integrable (fieldDirection (fieldUnit j)) shift sideL edgeL sideR edgeR).const_mul
        (sourceMatrix sourceEnergyChannelTerms (fixedMomentum (physicalMomentum shift) zeta) j ⟨i.val,by omega⟩))
  exact generated.congr (Filter.Eventually.of_forall fun frequency=>
    (sourcePhysicalWeightIntegrand_source shift zeta i sideL edgeL sideR edgeR frequency).symm)

/-- Every actual channel keeps its complete original matrix under the same-Phi Fourier pairing. -/
theorem sourcePhysicalEnergyChannel_weights (shift : Position) (zeta : ℂ) (i : Fin 3)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyChannel shift zeta i sideL edgeL sideR edgeR=
      ∫frequency : Position,sourcePhysicalWeightIntegrand shift zeta i sideL edgeL sideR edgeR frequency := by
  simp_rw [sourcePhysicalWeightIntegrand_source]
  rw [integral_finsetSum]
  · simp only [integral_const_mul,sourcePhysicalEnergyChannel,sourceChargedEnergyRead_fourier]
  · intro j _
    exact (sourceChargedEnergyRead_integrable (fieldDirection (fieldUnit j)) shift sideL edgeL sideR edgeR).const_mul _

/-- The generated field is read through all three matrix-weight integrals and the original regular current. -/
theorem sourcePhysicalEnergy_three_weight_integrals (q : PhysicalResponsePoint) (shift : Position)
    (zeta : sourceCausalDomain (physicalMomentum shift))
    (sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedModeEnergyRead q shift zeta.val sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR=
      (∑i : Fin 3,(sourceChargedDenominator (physicalMomentum shift) zeta.val i)⁻¹*
        sourceSlowRead (sourceActualNativeResidue q (physicalMomentum shift) zeta.val
          (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR)) ⟨i.val,by omega⟩*
        ∫frequency : Position,sourcePhysicalWeightIntegrand shift zeta.val i sideL edgeL sideR edgeR frequency)+
      sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
        (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q (physicalMomentum shift) zeta.val
          (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR)) := by
  rw [sourcePhysicalEnergy_three_channels]
  simp only [sourcePhysicalEnergyChannel_weights]

end LowEnergy.PreparationPhysicalEnergyWeightsReturn
