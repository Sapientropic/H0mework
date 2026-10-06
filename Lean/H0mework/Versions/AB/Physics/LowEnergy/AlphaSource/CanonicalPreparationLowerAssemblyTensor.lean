import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerActualConsumers
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerCoframeArrays

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerAssembly
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussCoreDifferential GaussLiveMomentum
open PreparationScalarCoordinates PreparationCoordinates PreparationPhaseScalar
open PreparationVacuumLowerLeaves PreparationVacuumLowerTensor PreparationVacuumLowerTensorBudget
open PreparationVacuumTemporalOrdering PreparationVacuumLowerCorrections PreparationVacuumRationalW
open PreparationVacuumWeylOrdering PreparationVacuumCanonicalMoyal PreparationVacuumEnergyTail
open scoped BigOperators ContDiff Topology Matrix

abbrev Configuration := SourceCoordinateSlice

theorem coframe_covector_direction (i : Fin 6) (v : Ambient) (z : Configuration) :
    rawCovector (Fin.castAdd 94 i) (direction v z)=0 := by
  rw [rawCovector_read,full_blocks]
  simp [joinCoordinates,direction,i.isLt,map_zero]

theorem actual_tensor_coframe_row (n : ℝ) (b : Fin 3 → ℝ) (i : Fin 6) (k : Fin 100)
    (z : Configuration) :
    actualTimePairTensor n b (Fin.castAdd 94 i) k z=coframeTensor n (Fin.castAdd 94 i) k z := by
  unfold actualTimePairTensor
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type]
  have zero (a : GaussNativeForm.ScalarIndex) :
      rawCovector (Fin.castAdd 94 i) (sourceLeft (Sum.inl a) z)=0 := coframe_covector_direction i _ z
  simp only [zero,mul_zero,zero_mul,Finset.sum_const_zero,zero_add]
  have gauge (a : GaussNativeForm.LieIndex) (r s : Fin 3) :
      rawCovector (Fin.castAdd 94 i) (sourceLeft (Sum.inr (Sum.inl (a,r,s))) z)=0 :=
    coframe_covector_direction i _ z
  simp only [gauge,mul_zero,zero_mul,Finset.sum_const_zero,zero_add]
  exact actualTime_coframe_tensor n b _ k z

theorem actual_tensor_coframe_column (n : ℝ) (b : Fin 3 → ℝ) (i : Fin 100) (k : Fin 6)
    (z : Configuration) :
    actualTimePairTensor n b i (Fin.castAdd 94 k) z=coframeTensor n i (Fin.castAdd 94 k) z := by
  unfold actualTimePairTensor
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type]
  have zero (a : GaussNativeForm.ScalarIndex) :
      rawCovector (Fin.castAdd 94 k) (sourceRight (Sum.inl a) z)=0 := coframe_covector_direction k _ z
  simp only [zero,mul_zero,Finset.sum_const_zero,zero_add]
  have gauge (a : GaussNativeForm.LieIndex) (r s : Fin 3) :
      rawCovector (Fin.castAdd 94 k) (sourceRight (Sum.inr (Sum.inl (a,r,s))) z)=0 :=
    coframe_covector_direction k _ z
  simp only [gauge,mul_zero,Finset.sum_const_zero,zero_add]
  exact actualTime_coframe_tensor n b i _ z

theorem actual_tensor_raw94 (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (i k : Fin 94) (z : physicalChart) :
    actualTimePairTensor n b (Fin.natAdd 6 i) (Fin.natAdd 6 k) z.val=
      totalP n b (fullCoordinates z.val,0) i k := by
  apply Complex.ofReal_injective
  rw [actualTimePairTensor_extraction n b _ _ z (time_positive n b time).1.ne'
    (time_positive n b time).2.ne']
  have read := raw94_Qtime_recognition n b time (fullCoordinates z.val,0)
    (by simp) i k
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using read.symm

def wholeTensor (n : ℝ) (b : Fin 3 → ℝ) (i k : Fin 100) (z : Configuration) : ℝ :=
  Fin.addCases (fun a : Fin 6 => Fin.addCases (fun c : Fin 6 => n*K a c z)
      (fun _ : Fin 94 => 0) k)
    (fun a : Fin 94 => Fin.addCases (fun _ : Fin 6 => 0)
      (fun c : Fin 94 => totalP n b (fullCoordinates z,0) a c) k) i

theorem actual_tensor_blockdiag (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (i k : Fin 100) (z : physicalChart) :
    actualTimePairTensor n b i k z.val=wholeTensor n b i k z.val := by
  induction i using Fin.addCases (m:=6) (n:=94) with
  | left i =>
    rw [actual_tensor_coframe_row]
    simp only [coframeTensor,wholeTensor,Fin.addCases_left]
  | right i =>
    induction k using Fin.addCases (m:=6) (n:=94) with
    | left k => simp [actual_tensor_coframe_column,tensor_right,wholeTensor]
    | right k => simpa [wholeTensor] using actual_tensor_raw94 n b time i k z

theorem weighted_raw_tensor (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (i k : Fin 100) (z : physicalChart) :
    (∑ j : Fin 13,originalTemporalWeights n b j*rawPrincipalCoefficient j i k z.val)=
      wholeTensor n b i k z.val := by
  apply Complex.ofReal_injective
  have read := actualTimePairTensor_extraction n b i k z (time_positive n b time).1.ne'
    (time_positive n b time).2.ne'
  rw [actual_tensor_blockdiag n b time] at read
  simpa only [timeTensor,leafP,Complex.ofReal_sum,Complex.ofReal_mul] using read.symm

end LowEnergy.PreparationVacuumLowerAssembly
