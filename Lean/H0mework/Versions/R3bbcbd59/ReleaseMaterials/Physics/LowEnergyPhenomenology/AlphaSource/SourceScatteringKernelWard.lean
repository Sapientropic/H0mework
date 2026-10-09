import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceScatteringChannelWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalScatteringFrequencyWard
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
local instance scatteringKernelQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

/-- The two actual source columns remain independent on the positive and negative branches. -/
def sourceChannelTwoTransfer (n : PhysicalMomentum) (positive negative : ℂ) : TransferPair:=
  originalTransferPair (sourceChargedChannel n positive 2) (sourceChargedChannel n negative 2)

private def onlyTime (T : FiberOperators) : Fin 4→FiberOperators:=fun k=>if k=0 then T else 0

private theorem onlyTime_shift (T : FiberOperators) (shift : Fin 3→ℝ) :
    shiftCoefficients (onlyTime T) shift=onlyTime T := by
  have scalarZero (a : ℂ) : a • (0:FiberOperators)=0 := @_root_.smul_zero ℂ FiberOperators _ _ a
  funext k
  cases k using Fin.cases <;> simp [shiftCoefficients,onlyTime,scalarZero]

private theorem onlyTime_adjoint (T : FiberOperators) : adjointCoefficients (onlyTime T)=onlyTime T.adjoint := by
  funext k
  by_cases zero : k=0 <;> simp [adjointCoefficients,onlyTime,zero]

private theorem zero_compLpL : (0:FiberOperators).compLpL 2 volume=(0:FullMatterL2→L[ℂ] FullMatterL2) := by
  apply norm_eq_zero.mp
  apply le_antisymm
  · simpa only [norm_zero] using ((0:FiberOperators).norm_compLpL_le (p:=2) (μ:=volume))
  · exact norm_nonneg _

private theorem word_time_right (A : Fin 4→FiberOperators) (T : FiberOperators)
    (shift : Fin 3→ℝ) (time age : ℝ) :
    orderedWord A (onlyTime T) shift time age=
      ∑i : Fin 4,orderedLeft A shift time age i*orderedRight (onlyTime T) age 0 := by
  unfold orderedWord
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single 0
  · intro j _ different
    simp only [orderedRight,onlyTime,if_neg different,zero_compLpL,zero_mul,mul_zero]
  · simp

private theorem word_time_left (T : FiberOperators) (A : Fin 4→FiberOperators)
    (shift : Fin 3→ℝ) (time age : ℝ) :
    orderedWord (onlyTime T) A shift time age=
      ∑j : Fin 4,orderedLeft (onlyTime T) shift time age 0*orderedRight A age j := by
  unfold orderedWord
  apply Finset.sum_eq_single 0
  · intro i _ different
    simp only [orderedLeft,onlyTime_shift,onlyTime,if_neg different,zero_compLpL,mul_zero,zero_mul,
      Finset.sum_const_zero]
  · simp

/-- The actual source frequency leg feeds the existing two-time kernel; every reader component and negative-branch adjoint is retained. -/
theorem sourceChannelTwoKernel_generated (A : TransferPair) (n : PhysicalMomentum) (positive negative : ℂ)
    (shift : Fin 3→ℝ) (time age : ℝ) :
    fieldTwoTimeKernel A (sourceChannelTwoTransfer n positive negative) shift time age=
      Complex.I •
        ((∑j : Fin 4,orderedLeft
          (onlyTime (sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum n negative))).adjoint)
          (-shift) age time 0*orderedRight (realReaderCoefficients A shift) time j)-
          ∑i : Fin 4,orderedLeft (realReaderCoefficients A shift) shift time age i*
            orderedRight (onlyTime (sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum n positive)))) age 0) := by
  have pos : complexFrequencyCoefficients (sourceChannelTwoTransfer n positive negative).positive=
      onlyTime (sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum n positive))) := by
    funext k
    exact sourceScatteringChannelTwo_coefficients n positive k
  have neg : complexFrequencyCoefficients (sourceChannelTwoTransfer n positive negative).negative=
      onlyTime (sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum n negative))) := by
    funext k
    exact sourceScatteringChannelTwo_coefficients n negative k
  rw [fieldTwoTimeKernel,pos,neg,onlyTime_adjoint,onlyTime_shift,word_time_left,word_time_right]

/-- The original prepared full-CAR read consumes the new source vertex; the direct mixed contact remains a separate component. -/
theorem sourceChannelTwoScattering_fullCAR (sideL edgeL sideR edgeR : Fin 2) (A : TransferPair)
    (n : PhysicalMomentum) (positive negative : ℂ) (shift : Fin 3→ℝ) (time age : ℝ) :
    sourcePreparedScatteringPair sideL edgeL sideR edgeR A (sourceChannelTwoTransfer n positive negative) shift time age=
      (Complex.I*
        ((∑j : Fin 4,sourcePreparedOrderedCAR sideL edgeL sideR edgeR
          (onlyTime (sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum n negative))).adjoint)
          (realReaderCoefficients A shift) (-shift) age time 0 j)-
          ∑i : Fin 4,sourcePreparedOrderedCAR sideL edgeL sideR edgeR
            (realReaderCoefficients A shift)
            (onlyTime (sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum n positive))))
            shift time age i 0),
        inner ℂ (sourceActualScatteringInput sideL edgeL)
          (fieldMixedContact A (sourceChannelTwoTransfer n positive negative) time
            (sourceActualScatteringInput sideR edgeR))) := by
  rw [sourcePreparedScatteringPair,sourceChannelTwoKernel_generated]
  simp only [sourceActualScatteringRead_source,smul_apply,sub_apply,sum_apply,mul_apply_eq_comp,
    inner_smul_right,inner_sub_right,inner_sum,←sourcePreparedOrderedCAR_source]

/-- The same actual kernel now reads the original full-H transfer on both source branches, with its mixed contact untouched. -/
theorem sourceChannelTwoScattering_hamiltonian (sideL edgeL sideR edgeR : Fin 2) (A : TransferPair)
    (n : PhysicalMomentum) (positive negative : ℝ) (shift : Fin 3→ℝ) (time age : ℝ) :
    sourcePreparedScatteringPair sideL edgeL sideR edgeR A
      (sourceChannelTwoTransfer n (Complex.I*(positive:ℂ)) (Complex.I*(negative:ℂ))) shift time age=
      (Complex.I*
        ((∑j : Fin 4,sourcePreparedOrderedCAR sideL edgeL sideR edgeR
          (onlyTime ((-(negative:ℂ)) • (1:FiberOperators)-(5/3:ℂ) •
            (sourceHamiltonianFiber n-sourceHamiltonianFiber 0)).adjoint)
          (realReaderCoefficients A shift) (-shift) age time 0 j)-
          ∑i : Fin 4,sourcePreparedOrderedCAR sideL edgeL sideR edgeR
            (realReaderCoefficients A shift)
            (onlyTime ((-(positive:ℂ)) • (1:FiberOperators)-(5/3:ℂ) •
              (sourceHamiltonianFiber n-sourceHamiltonianFiber 0))) shift time age i 0),
        inner ℂ (sourceActualScatteringInput sideL edgeL)
          (fieldMixedContact A (sourceChannelTwoTransfer n (Complex.I*(positive:ℂ)) (Complex.I*(negative:ℂ))) time
            (sourceActualScatteringInput sideR edgeR))) := by
  rw [sourceChannelTwoScattering_fullCAR]
  have pos : sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum n (Complex.I*(positive:ℂ))))=
      (-(positive:ℂ)) • (1:FiberOperators)-(5/3:ℂ) • (sourceHamiltonianFiber n-sourceHamiltonianFiber 0) := by
    simpa only [sub_zero] using sourceScatteringChannelTwo_hamiltonian n 0 positive
  have neg : sourceCliffordFiber (sourcePhysicalChannelTwoClifford (fixedMomentum n (Complex.I*(negative:ℂ))))=
      (-(negative:ℂ)) • (1:FiberOperators)-(5/3:ℂ) • (sourceHamiltonianFiber n-sourceHamiltonianFiber 0) := by
    simpa only [sub_zero] using sourceScatteringChannelTwo_hamiltonian n 0 negative
  rw [pos,neg]

end LowEnergy.PreparationPhysicalScatteringFrequencyWard
