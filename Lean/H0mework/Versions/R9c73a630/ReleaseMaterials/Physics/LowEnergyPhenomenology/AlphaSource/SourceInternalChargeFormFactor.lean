import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceRemainderPoleAssembly
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseChargeActual

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalInternalChargePoleReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open DiracExteriorMatterAction DiracCliffordRepresentation YangMills.FullPairing
open Stage9C.Material.SpinPair Stage10.CanonicalMatter StageNineHolonomicField
open FullQuantum FullSpace FullQuantum.Triangular FullQuantum.StateGreen FullQuantum.PerturbedGreen
open PreparationPhysicalNativePhaseChargeInventory PreparationPhysicalNativeOriginPhaseWard
open PreparationVacuumPhysicalElectromagneticDirection PreparationPhysicalFilteredLockedChargeReturn
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalVoltageEnergyIdentity
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalFilteredChargeVoltage
open GaussNativeMatter PreparationVacuumSourceActionJets PreparationVacuumActionFieldLift
open MeasureTheory
open scoped BigOperators Matrix InnerProductSpace
local instance : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

/-- The spin contribution is a source Lorentz action, retained separately from the internal phase charge. -/
def sourceInternalSpinAction : YangMills.FullPairing.Mother :=
  (Complex.I/2:ℂ) • diracMatrixMatterAction (spinRotation 2)

theorem sourceLocked_internalPhase :
    (Complex.I:ℂ) • sourceLockedAction 2=
      (1/2:ℂ) • (1:YangMills.FullPairing.Mother)-phaseInverse.comp sourcePhaseNoether+sourceInternalSpinAction := by
  rw [sourcePhaseNoether_canonical]
  apply LinearMap.ext
  intro v
  change Complex.I •
      (diracExteriorMotherLieAction (SU7MotherLieAlgebra.p286LieBlockEmbed (sourceColorP286Generator 2)) v+
        (1/2:ℂ) • diracMatrixMatterAction (spinRotation 2) v)=
    (1/2:ℂ) • v-Complex.I •
      (-diracExteriorMotherLieAction (SU7MotherLieAlgebra.p286LieBlockEmbed (sourceColorP286Generator 2)) v-
        (Complex.I/2:ℂ) • v)+(Complex.I/2:ℂ) • diracMatrixMatterAction (spinRotation 2) v
  simp only [smul_add,smul_sub,smul_neg,smul_smul]
  have coefficient : Complex.I*(Complex.I/2)= -(1/2:ℂ) := by
    rw [←mul_div_assoc,Complex.I_mul_I]
    norm_num
  rw [coefficient]
  module

theorem sourceLockedDirection_internalPhase :
    sourceLockedCurrentDirection 0 2=
      (1/2:ℂ) • (1:YangMills.FullPairing.Mother)-phaseInverse.comp sourcePhaseNoether+sourceInternalSpinAction := by
  rw [←sourceLocked_internalPhase]
  apply LinearMap.ext
  intro v
  simp only [sourceLockedCurrentDirection,sourceLockedCurrent,LinearMap.comp_apply,
    LinearMap.smul_apply,map_smul,diracGamma,Matrix.cons_val_zero,phase_inverse_source]

def sourceInternalPhaseMatrix : SourceMatrix :=
  Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)

def sourceInternalSpinMatrix : SourceMatrix := Quantum.operatorMatrix sourceInternalSpinAction

private theorem matrix_sub (A B : YangMills.FullPairing.Mother) :
    Quantum.operatorMatrix (A-B)=Quantum.operatorMatrix A-Quantum.operatorMatrix B := by
  ext i j
  simp only [Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply,LinearMap.sub_apply,
    map_sub,Finsupp.sub_apply,Matrix.sub_apply]

/-- This identity holds on the full mother representation, before any prepared-state restriction. -/
theorem sourceLockedMatrix_internalPhase :
    Quantum.operatorMatrix (sourceLockedCurrentDirection 0 2)=
      (1/2:ℂ) • (1:SourceMatrix)-sourceInternalPhaseMatrix+sourceInternalSpinMatrix := by
  rw [sourceLockedDirection_internalPhase,map_add,matrix_sub,map_smul,map_one]
  rfl

theorem sourceInternalPhaseMatrix_source :
    sourceInternalPhaseMatrix=Matrix.diagonal (fun i=> -(sourceWholeWeight i:ℂ)) :=
  sourcePhaseNoether_matrix

/-- Opposite Dirac-dual branches retain their sign; the central mother action is not replaced by full504 identity. -/
theorem sourceLockedBranches_internalPhase :
    SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceLockedCurrentDirection 0 2))=
      (1/2:ℂ) • SourceRealScalarFock.branches (1:SourceMatrix)-
        SourceRealScalarFock.branches sourceInternalPhaseMatrix+
        SourceRealScalarFock.branches sourceInternalSpinMatrix := by
  have generic (A B : Matrix Quantum.Index Quantum.Index ℂ) :
      SourceRealScalarFock.branches ((1/2:ℂ) • (1:Matrix Quantum.Index Quantum.Index ℂ)-A+B)=
        (1/2:ℂ) • SourceRealScalarFock.branches (1:Matrix Quantum.Index Quantum.Index ℂ)-
          SourceRealScalarFock.branches A+SourceRealScalarFock.branches B := by
    have starTwo : (starRingEnd ℂ) (2:ℂ)=2 := by
      change star (2:ℂ)=2
      exact star_ofNat 2
    ext i j
    cases i <;> cases j
    all_goals dsimp only [Matrix] at *
    all_goals simp [SourceRealScalarFock.branches,Matrix.fromBlocks,smul_eq_mul,Matrix.one_apply]
    all_goals split_ifs <;> norm_num
    all_goals try rw [starTwo]
    all_goals ring
  rw [sourceLockedMatrix_internalPhase]
  exact generic sourceInternalPhaseMatrix sourceInternalSpinMatrix

def sourceInternalPhaseSpatial : SpatialOperators :=
  (operator (phaseInverse.comp sourcePhaseNoether)).compLpL 2 volume

def sourceInternalSpinSpatial : SpatialOperators :=
  (operator sourceInternalSpinAction).compLpL 2 volume

private theorem operator_sub (A B : YangMills.FullPairing.Mother) : operator (A-B)=operator A-operator B := by
  ext v
  simp [operator]

private theorem operator_one : operator (1:YangMills.FullPairing.Mother)=(1:FiberOperators) := by
  ext v
  simp [operator]

private theorem spatial_sub (A B : FiberOperators) :
    (A-B).compLpL 2 (volume:Measure Position)=
      A.compLpL 2 (volume:Measure Position)-B.compLpL 2 (volume:Measure Position) := by
  rw [show A-B=A+(-1:ℂ) • B from by module,
    ContinuousLinearMap.add_compLpL,ContinuousLinearMap.smul_compLpL,neg_one_smul]
  simp only [sub_eq_add_neg]

private theorem spatial_one : (1:FiberOperators).compLpL 2 volume=(1:SpatialOperators) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [(1:FiberOperators).coeFn_compLpL v] with x acted
  exact acted

theorem sourceLockedSpatial_internalPhase :
    sourceLockedSpatialCharge=(1/2:ℂ) • (1:SpatialOperators)-
      sourceInternalPhaseSpatial+sourceInternalSpinSpatial := by
  unfold sourceLockedSpatialCharge sourceLockedFiberCharge
  rw [sourceLockedDirection_internalPhase,operator_add,operator_sub,operator_smul,operator_one]
  rw [ContinuousLinearMap.add_compLpL,spatial_sub,
    ContinuousLinearMap.smul_compLpL,spatial_one]
  rfl

def sourceInternalPhaseFormFactor (shift : Position) (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  (ActionNormalization.phaseMomentum:ℂ)*sourceChargedQuantumRead sideL edgeL sideR edgeR
    (sourceInternalPhaseSpatial.comp (PacketNoise.phaseShift shift).toContinuousLinearMap)

def sourceInternalSpinFormFactor (shift : Position) (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  (ActionNormalization.phaseMomentum:ℂ)*sourceChargedQuantumRead sideL edgeL sideR edgeR
    (sourceInternalSpinSpatial.comp (PacketNoise.phaseShift shift).toContinuousLinearMap)

/-- Both independent filtered packets and their original physical Fourier phase consume the full action identity. -/
theorem sourceLockedFormFactor_internalPhase (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceFilteredLockedFormFactor shift sideL edgeL sideR edgeR=
      (ActionNormalization.phaseMomentum:ℂ)/2*sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR-
      sourceInternalPhaseFormFactor shift sideL edgeL sideR edgeR+
      sourceInternalSpinFormFactor shift sideL edgeL sideR edgeR := by
  simp only [sourceFilteredLockedFormFactor,sourceInternalPhaseFormFactor,sourceInternalSpinFormFactor,
    sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap]
  rw [sourceLockedSpatial_internalPhase]
  simp only [add_apply,sub_apply,smul_apply,one_apply_eq_self,
    inner_add_right,inner_sub_right,inner_smul_right]
  change _=_*inner ℂ (sourceChargedFilteredPacket sideL edgeL)
    (PacketNoise.phaseShift shift (sourceChargedFilteredPacket sideR edgeR))-_+_
  ring

/-- Full phase-charge levels and their actual shifted sector matrix elements determine the internal read. -/
theorem sourceInternalPhaseFormFactor_levels (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceInternalPhaseFormFactor shift sideL edgeL sideR edgeR=
      (ActionNormalization.phaseMomentum:ℂ)*∑a : Fin 3,(-(sourcePhaseLevel a:ℂ))*
        inner ℂ (sourceChargedFilteredPacket sideL edgeL)
          (sourcePhaseSpatial a (PacketNoise.phaseShift shift (sourceChargedFilteredPacket sideR edgeR))) := by
  rw [sourceInternalPhaseFormFactor,sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply]
  unfold sourceInternalPhaseSpatial
  rw [sourcePhaseNoether_resolution]
  simp only [Fin.sum_univ_three,operator_add,operator_smul,
    ContinuousLinearMap.add_compLpL,ContinuousLinearMap.smul_compLpL,
    add_apply,smul_apply,inner_add_right,inner_smul_right,sourcePhaseSpatial,sourcePhaseFiber,
    LinearIsometry.coe_toContinuousLinearMap]

end LowEnergy.PreparationPhysicalInternalChargePoleReturn
