import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailForm
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionNativeOperator

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTailOperator
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumRemainder PreparationVacuumWeylDomain
open PreparationVacuumFrequencyN2 CanonicalPreparationSquareCutoff MeasureTheory Filter Set
open scoped SchwartzMap ComplexConjugate FourierTransform ENNReal InnerProductSpace

open PreparationVacuumTailFourier PreparationVacuumTailSupport
open PreparationVacuumNativeClosure PreparationVacuumCompositionNative
variable (B : ℕ → Fin 5 → ArrayBound)
variable (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102)

def sourceTailOperator : FourierHilbert →L[ℂ] FourierHilbert :=
  InnerProductSpace.continuousLinearMapOfBilin (sourceContinuousForm B positive input)

theorem sourceTailOperator_left_readback (g f : FourierHilbert) :
    inner ℂ (sourceTailOperator B positive input g) f = sourceForm B g f :=
  InnerProductSpace.continuousLinearMapOfBilin_apply (sourceContinuousForm B positive input) g f

theorem sourceTailOperator_readback (g f : FourierHilbert) :
    inner ℂ g (sourceTailOperator B positive input f) = ∫ xy, conj (g xy.1) *
      tailWeylKernel B xy.1 xy.2 * f xy.2 ∂pairVolume := by
  rw [← inner_conj_symm, sourceTailOperator_left_readback B positive input, sourceForm_hermitian B]
  rfl

theorem sourceTailOperator_isSelfAdjoint : IsSelfAdjoint (sourceTailOperator B positive input) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro g f
  change inner ℂ (sourceTailOperator B positive input g) f = inner ℂ g (sourceTailOperator B positive input f)
  rw [sourceTailOperator_left_readback B positive input, sourceTailOperator_readback B positive input]
  rfl

include positive input in
theorem sourceTailOperator_norm_bound :
    ‖sourceTailOperator B positive input‖ ≤ tailSchurBound B := by
  apply (sourceTailOperator B positive input).opNorm_le_bound (tailSchurBound_nonnegative B positive)
  intro g
  change ‖(InnerProductSpace.toDual ℂ FourierHilbert).symm ((sourceContinuousForm B positive input) g)‖ ≤ _
  rw [(InnerProductSpace.toDual ℂ FourierHilbert).symm.norm_map]
  exact (ContinuousLinearMap.le_opNorm (sourceContinuousForm B positive input) g).trans
    (mul_le_mul_of_nonneg_right (sourceContinuousForm_norm_bound B positive input) (norm_nonneg g))

def nativeEnergyTail : sourceLocalSpace →L[ℂ] sourceLocalSpace :=
  (localInput.adjoint.comp (sourceTailOperator B positive input)).comp localInput

theorem nativeEnergyTail_isSelfAdjoint : IsSelfAdjoint (nativeEnergyTail B positive input) :=
  (sourceTailOperator_isSelfAdjoint B positive input).adjoint_conj localInput

def nativeEnergyTailBound : ℝ := ‖localInput‖*tailSchurBound B*‖localInput‖

include positive input in
theorem nativeEnergyTail_norm_bound : ‖nativeEnergyTail B positive input‖≤nativeEnergyTailBound B := by
  calc
    _≤‖localInput.adjoint.comp (sourceTailOperator B positive input)‖*‖localInput‖ :=
      (localInput.adjoint.comp (sourceTailOperator B positive input)).opNorm_comp_le localInput
    _≤(‖localInput.adjoint‖*‖sourceTailOperator B positive input‖)*‖localInput‖ :=
      mul_le_mul_of_nonneg_right (localInput.adjoint.opNorm_comp_le (sourceTailOperator B positive input))
        (norm_nonneg localInput)
    _=(‖localInput‖*‖sourceTailOperator B positive input‖)*‖localInput‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _≤nativeEnergyTailBound B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sourceTailOperator_norm_bound B positive input) (norm_nonneg localInput))
      (norm_nonneg localInput)

theorem nativeEnergyTail_readback (g f : sourceLocalSpace) :
    inner ℂ g (nativeEnergyTail B positive input f)=∫ xy : PhysicalMomentum × PhysicalMomentum,
      conj (localInput g xy.1)*tailWeylKernel B xy.1 xy.2*localInput f xy.2 ∂volume.prod volume := by
  rw [nativeEnergyTail,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,sourceTailOperator_readback]

def completeNativeRemainder : sourceLocalSpace →L[ℂ] sourceLocalSpace :=
  nativeEnergyTail B positive input-sourceNativeComposition

theorem completeNativeRemainder_isSelfAdjoint : IsSelfAdjoint (completeNativeRemainder B positive input) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro g f
  change inner ℂ (nativeEnergyTail B positive input g-sourceNativeComposition g) f=
    inner ℂ g (nativeEnergyTail B positive input f-sourceNativeComposition f)
  rw [inner_sub_left,inner_sub_right]
  exact congrArg₂ (fun a b : ℂ=>a-b)
    ((nativeEnergyTail_isSelfAdjoint B positive input).isSymmetric g f)
    (sourceNativeComposition_isSelfAdjoint.isSymmetric g f)

include positive input in
theorem completeNativeRemainder_norm_bound :
    ‖completeNativeRemainder B positive input‖≤nativeEnergyTailBound B+sourceNativeCompositionBound := by
  rw [completeNativeRemainder]
  exact (norm_sub_le (nativeEnergyTail B positive input) sourceNativeComposition).trans
    (add_le_add (nativeEnergyTail_norm_bound B positive input) sourceNativeComposition_norm_bound)

theorem completeNativeRemainder_readback (g f : sourceLocalSpace) :
    inner ℂ g (completeNativeRemainder B positive input f)=
      (∫ xy : PhysicalMomentum × PhysicalMomentum,
        conj (localInput g xy.1)*tailWeylKernel B xy.1 xy.2*localInput f xy.2 ∂volume.prod volume)-
      (∫ xy : PhysicalMomentum × PhysicalMomentum,
        conj (localInput g xy.1)*actualFullCompositionKernelDefect xy.1 xy.2*localInput f xy.2 ∂volume.prod volume) := by
  rw [completeNativeRemainder,sub_apply,inner_sub_right,
    nativeEnergyTail_readback,sourceNativeComposition_readback]

end LowEnergy.PreparationVacuumTailOperator
