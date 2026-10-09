import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeShearEnergy

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalJointGeneratorEnergyReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9DEF Stage10 YangMills.FullPairing
open FullQuantum FullSpace FullQuantum.PerturbedGreen Electromagnetic Electromagnetic.CanonicalCoframe
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open MatterSpace.SpatialCAR
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators

/-- The original scattering kernel already contains G_D C0: its correct actual source input contains C0 inverse, once. -/
def sourceActualScatteringPreparation (side edge : Fin 2) : Hilbert→L[ℂ] FullMatterL2 :=
  ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) • (inversePrincipal 0).comp
    (HistoryPrepared.preparation.comp (operator (actualRestStatePreparation (sourceChargedRestIndex side edge))))

def sourceActualScatteringInput (side edge : Fin 2) : FullMatterL2 :=
  sourceActualScatteringPreparation side edge (YangMills.FullPairing.prepared 0)

theorem sourceActualScatteringInput_source (side edge : Fin 2) :
    sourceActualScatteringInput side edge=((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) •
      inversePrincipal 0 (sourceChargedSpatialPacket side edge) := by
  rw [sourceActualScatteringInput,sourceActualScatteringPreparation]
  simp only [smul_apply,ContinuousLinearMap.comp_apply]
  rw [←sourceChargedSpatialPacket_maker]

/-- The complete preparation maps agree after the existing kernel's first leg; the new filtered state is not filtered twice. -/
theorem sourceActualScatteringPreparation_return (side edge : Fin 2) :
    (coordinateLeg 0).comp (sourceActualScatteringPreparation side edge)=sourceChargedPreparation side edge := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [coordinateLeg_zero,CanonicalPacket.rawFilter,sourceActualScatteringPreparation,
    sourceChargedPreparation,sourceChargedFilter,sourcePacketDiracFilter,
    ContinuousLinearMap.comp_apply,smul_apply,map_smul,inversePrincipal_right]

theorem sourceActualScatteringInput_return (side edge : Fin 2) :
    coordinateLeg 0 (sourceActualScatteringInput side edge)=sourceChargedFilteredPacket side edge := by
  have returned:=DFunLike.congr_fun (sourceActualScatteringPreparation_return side edge) (YangMills.FullPairing.prepared 0)
  simpa only [ContinuousLinearMap.comp_apply,sourceActualScatteringInput,sourceChargedPreparation_applied] using returned

/-- Both independent actual preparation maps remain inside the original state observable. -/
def sourceActualScatteringMother (sideL edgeL sideR edgeR : Fin 2) (A : SpatialOperators) : YangMills.FullPairing.Mother :=
  fromOperator ((sourceActualScatteringPreparation sideL edgeL).adjoint.comp
    (A.comp (sourceActualScatteringPreparation sideR edgeR)))

def sourceActualScatteringRead (sideL edgeL sideR edgeR : Fin 2) (A : SpatialOperators) : ℂ :=
  State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
    (Compatibility.responseMatrix (sourceActualScatteringMother sideL edgeL sideR edgeR A))

theorem sourceActualScatteringRead_source (sideL edgeL sideR edgeR : Fin 2) (A : SpatialOperators) :
    sourceActualScatteringRead sideL edgeL sideR edgeR A=
      inner ℂ (sourceActualScatteringInput sideL edgeL) (A (sourceActualScatteringInput sideR edgeR)) := by
  rw [sourceActualScatteringRead,sourceActualScatteringMother,origin_response,operator_fromOperator]
  change inner ℂ (YangMills.FullPairing.prepared 0) ((sourceActualScatteringPreparation sideL edgeL).adjoint
    (A (sourceActualScatteringPreparation sideR edgeR (YangMills.FullPairing.prepared 0))))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- Reusing the full original kernel and direct contact preserves their distinct time/age roles. -/
def sourcePreparedScatteringPair (sideL edgeL sideR edgeR : Fin 2)
    (A B : TransferPair) (shift : Fin 3→ℝ) (time age : ℝ) : ℂ × ℂ :=
  (sourceActualScatteringRead sideL edgeL sideR edgeR (fieldTwoTimeKernel A B shift time age),
    sourceActualScatteringRead sideL edgeL sideR edgeR (fieldMixedContact A B time))

def sourcePreparedOrderedCAR (sideL edgeL sideR edgeR : Fin 2) (A B : Fin 4→FiberOperators)
    (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) : ℂ :=
  sourceChargedQuantumRead sideR edgeR sideR edgeR
    (wordObservable (sourceChargedFilteredPacket sideR edgeR)
      (![(orderedLeft A shift time age i).adjoint (sourceActualScatteringInput sideL edgeL),
        orderedRight B age j (sourceActualScatteringInput sideR edgeR)] : Fin 2→FullMatterL2)
      [.create none,.annihilate (some 0),.create (some 1),.annihilate none])

theorem sourcePreparedOrderedCAR_source (sideL edgeL sideR edgeR : Fin 2) (A B : Fin 4→FiberOperators)
    (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    sourcePreparedOrderedCAR sideL edgeL sideR edgeR A B shift time age i j=
      inner ℂ (sourceActualScatteringInput sideL edgeL)
        (orderedLeft A shift time age i (orderedRight B age j (sourceActualScatteringInput sideR edgeR))) := by
  rw [sourcePreparedOrderedCAR,sourceChargedQuantumRead_fullWord,spatialMoment_fourPoint]
  simp only [family,Matrix.cons_val_zero,Matrix.cons_val_one,inner_self_eq_norm_sq_to_K,
    sourceChargedFilteredPacket_unit,ContinuousLinearMap.adjoint_inner_left]
  norm_num

theorem sourcePreparedScatteringPair_fullCAR (sideL edgeL sideR edgeR : Fin 2)
    (A B : TransferPair) (shift : Fin 3→ℝ) (time age : ℝ) :
    sourcePreparedScatteringPair sideL edgeL sideR edgeR A B shift time age=
      (Complex.I*((∑i : Fin 4,∑j : Fin 4,sourcePreparedOrderedCAR sideL edgeL sideR edgeR
        (shiftCoefficients (adjointCoefficients (complexFrequencyCoefficients B.negative)) shift)
        (realReaderCoefficients A shift) (-shift) age time i j)-
        ∑i : Fin 4,∑j : Fin 4,sourcePreparedOrderedCAR sideL edgeL sideR edgeR
          (realReaderCoefficients A shift) (complexFrequencyCoefficients B.positive) shift time age i j),
        inner ℂ (sourceActualScatteringInput sideL edgeL)
          (fieldMixedContact A B time (sourceActualScatteringInput sideR edgeR))) := by
  simp only [sourcePreparedScatteringPair,sourceActualScatteringRead_source,fieldTwoTimeKernel,
    smul_apply,sub_apply,inner_smul_right,inner_sub_right,orderedWord,sum_apply,inner_sum,
    sourcePreparedOrderedCAR_source,mul_apply_eq_comp]

end LowEnergy.PreparationPhysicalJointGeneratorEnergyReturn
