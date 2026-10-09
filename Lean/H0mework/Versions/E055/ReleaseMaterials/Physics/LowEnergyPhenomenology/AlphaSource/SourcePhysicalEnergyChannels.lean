import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedFullEnergyReturn
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyChannelFrame

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedEnergyPoleReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalChargedEnergyVariation PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalNormalizedFullField PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumChargedLongRangeRead PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumChargedSpatialResponse
open PreparationVacuumCausalPoleResponse PreparationVacuumFullSlowFieldResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumWholeOrigin
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumNativeSlowCoupling PreparationVacuumQuantumSlowResidue
open MeasureTheory Filter Set
open scoped BigOperators Topology InnerProductSpace Matrix

def sourcePhysicalEnergyReader (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (Fin 289→ℂ)→L[ℂ] ℂ :=
  ∑j : Fin 289,(ContinuousLinearMap.proj j : (Fin 289→ℂ)→L[ℂ] ℂ).smulRight
    (sourceChargedEnergyRead (fieldDirection (fieldUnit j)) shift sideL edgeL sideR edgeR)

/-- This functional is the already generated full physical-space observable in the original quantum state. -/
theorem sourcePhysicalEnergyReader_original (shift : Position) (sideL edgeL sideR edgeR : Fin 2) (V : Fin 289→ℂ) :
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR V=
      sourceFullEnergyRead V shift sideL edgeL sideR edgeR := by
  rw [sourceFullEnergyRead_generated]
  simp only [sourcePhysicalEnergyReader,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]

def sourcePhysicalEnergyChannel (shift : Position) (zeta : ℂ) (i : Fin 3)
    (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  ∑j : Fin 289,sourceMatrix sourceEnergyChannelTerms (fixedMomentum (physicalMomentum shift) zeta)
    j ⟨i.val,by omega⟩*
      sourceChargedEnergyRead (fieldDirection (fieldUnit j)) shift sideL edgeL sideR edgeR

private theorem five_single (i : Fin 3) :
    fiveVector (Pi.single (⟨i.val,by omega⟩:Fin 5) (1:ℂ))=
      Pi.single (⟨i.val,by omega⟩:Fin 289) (1:ℂ) := by
  funext j
  by_cases inside : j.val<5
  · simp [fiveVector,inside,Pi.single_apply,Fin.ext_iff]
  · have different : i.val≠j.val:=by omega
    simp [fiveVector,inside,Fin.ext_iff,different]

/-- Every one of the source-generated frame's 200 terms is contracted with the actual charged packet response. -/
theorem sourcePhysicalEnergyChannel_generated (shift : Position) (zeta : ℂ) (i : Fin 3)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyChannel shift zeta i sideL edgeL sideR edgeR=
      sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR (sourceChargedChannel (physicalMomentum shift) zeta i) := by
  rw [sourcePhysicalEnergyReader_original,sourceFullEnergyRead_generated]
  simp only [sourcePhysicalEnergyChannel,sourceChargedChannel,five_single,Matrix.mulVec_single_one]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceEnergyChannelMatrix_entry]
  rfl

/-- The complete original field, including the regular/contact term, is measured in the same Phi. -/
theorem sourcePhysicalEnergy_three_channels (q : PhysicalResponsePoint) (shift : Position)
    (zeta : sourceCausalDomain (physicalMomentum shift))
    (sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedModeEnergyRead q shift zeta.val sourceSideL sourceEdgeL sourceSideR sourceEdgeR sideL edgeL sideR edgeR=
      (∑i : Fin 3,(sourceChargedDenominator (physicalMomentum shift) zeta.val i)⁻¹*
        sourceSlowRead (sourceActualNativeResidue q (physicalMomentum shift) zeta.val
          (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR)) ⟨i.val,by omega⟩*
          sourcePhysicalEnergyChannel shift zeta.val i sideL edgeL sideR edgeR)+
      sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
        (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q (physicalMomentum shift) zeta.val
          (sourceChargedRestIndex sourceSideL sourceEdgeL) (sourceChargedRestIndex sourceSideR sourceEdgeR)) := by
  rw [sourceChargedModeEnergyRead,←sourcePhysicalEnergyReader_original,
    sourceChargedSecondField_channels q (physicalMomentum shift) zeta]
  simp only [map_add,map_sum,map_smul,smul_eq_mul,←sourcePhysicalEnergyChannel_generated]

end LowEnergy.PreparationPhysicalChargedEnergyPoleReturn
