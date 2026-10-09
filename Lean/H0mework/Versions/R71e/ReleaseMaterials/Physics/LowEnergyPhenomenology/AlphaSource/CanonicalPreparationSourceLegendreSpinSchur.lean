import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePreparedGaussKinetic

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLegendreSpinReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumSpinGaussContraction PreparationVacuumSpinCarReturn
open PreparationVacuumGaussMeasureReturn PreparationVacuumCoframeLegendreSource
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert Stage9C.Material.SpinPair
open scoped Topology BigOperators Matrix
attribute [local irreducible] sourceSpinMixedTensor sourceSpinOrderedTensor

private theorem sourceSchurConsVal5 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 5=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))):=rfl

private theorem sourceSchurConsVal6 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 6=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))) :=rfl

private theorem sourceSchurConsVal7 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 7=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))))):=rfl

def sourceMixedGramPrice : Fin 8→ℝ:=![3/4,0,0,0,-1,-1,-1,0]

def sourceMixedPolynomialGram (q : Coframe) : Matrix (Fin 8) (Fin 8) ℝ:=
  (sourceMixedPolynomial q).transpose*GaussCoframeKinetic.polynomial q*sourceMixedPolynomial q

private theorem sourceMixedPolynomialGram_entry (q : Coframe) (a b : Fin 8) :
    sourceMixedPolynomialGram q a b=∑i : Fin 6,∑j : Fin 6,
      sourceMixedPolynomial q i a*GaussCoframeKinetic.polynomial q i j*sourceMixedPolynomial q j b:=by
  simp only [sourceMixedPolynomialGram,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sourceMixedPolynomialGram_generated (q : Coframe) :
    sourceMixedPolynomialGram q=(q 0*q 2*q 5)^2 • Matrix.diagonal sourceMixedGramPrice:=by
  ext a b
  rw [sourceMixedPolynomialGram_entry]
  fin_cases a <;> fin_cases b <;>
    norm_num [sourceMixedPolynomial,GaussCoframeKinetic.polynomial,
      sourceMixedGramPrice,Matrix.diagonal_apply,Matrix.smul_apply,Fin.sum_univ_six,
      Fin.ext_iff,Fin.val_ofNat,Nat.reduceMod,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      sourceSchurConsVal5,sourceSchurConsVal6,sourceSchurConsVal7] <;> ring

def sourceLegendreSpinTensor (z : SourceCoordinateSlice) : Matrix (Fin 8) (Fin 8) ℝ:=
  (sourceSpinMixedTensor z).transpose*((1/2:ℝ) • sourceGaussVelocityInverse z)*sourceSpinMixedTensor z+
    (1/2:ℝ) • sourceSpinOrderedTensor z

def sourceLegendreSpinPrice : Fin 8→ℝ:=![0,3,3,3,-4,-4,-4,3]

theorem sourceLegendreKineticMatrix_generated (z : SourceCoordinateSlice) :
    (1/2:ℝ) • sourceGaussVelocityInverse z=
      (lapse/(4*GaussNativeEnergy.volume z)) • GaussCoframeKinetic.polynomial z.1:=by
  ext i j
  simp only [sourceGaussVelocityInverse,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,
    GaussCoframeKinetic.coefficient,GaussNativeEnergy.source_time_generated,Matrix.cons_val_zero]
  ring

theorem sourceMixedGram_generated (z : physicalChart) :
    (sourceSpinMixedTensor z.val).transpose*((1/2:ℝ) • sourceGaussVelocityInverse z.val)*
      sourceSpinMixedTensor z.val=
        (lapse/(4*GaussNativeEnergy.volume z.val)) • Matrix.diagonal sourceMixedGramPrice:=by
  rw [sourceSpinMixedTensor_generated,sourceSpinMixedNumerator_values,sourceLegendreKineticMatrix_generated]
  simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  change _ • sourceMixedPolynomialGram z.val.1=_
  rw [sourceMixedPolynomialGram_generated]
  simp only [smul_smul]
  congr 1
  have nonzero := (GaussNativeEnergy.volume_pos z).ne'
  change _*(GaussNativeEnergy.volume z.val)^2=_
  field_simp

theorem sourceLegendreSpinTensor_generated (z : physicalChart) :
    sourceLegendreSpinTensor z.val=
      (lapse/(4*GaussNativeEnergy.volume z.val)) • Matrix.diagonal sourceLegendreSpinPrice:=by
  have flat : sourceFlatOrderedTensor=Matrix.diagonal sourceFlatSpinPrice:=by
    ext a b
    exact sourceFlatOrderedTensor_values a b
  rw [sourceLegendreSpinTensor,sourceMixedGram_generated,sourceSpinOrderedTensor_generated,
    flat,sourceGaussCoframe_determinant,GaussNativeEnergy.source_time_generated]
  simp only [Matrix.cons_val_zero]
  ext a b
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply,smul_eq_mul]
  by_cases same : a=b
  · subst b
    simp only [ite_true]
    have timeNonzero := lapse_pos.ne'
    have spaceNonzero := (GaussNativeEnergy.volume_pos z).ne'
    fin_cases a <;>
      norm_num [sourceMixedGramPrice,sourceFlatSpinPrice,sourceLegendreSpinPrice,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.cons_val_four,sourceSchurConsVal5,sourceSchurConsVal6,sourceSchurConsVal7] <;>
      field_simp <;> ring
  · simp only [same,ite_false,mul_zero,add_zero]

theorem sourceLegendreSpinTensor_identity (z : physicalChart) (a : Fin 8) :
    sourceLegendreSpinTensor z.val 0 a=0 ∧ sourceLegendreSpinTensor z.val a 0=0:=by
  rw [sourceLegendreSpinTensor_generated]
  simp only [Matrix.smul_apply,Matrix.diagonal_apply,sourceLegendreSpinPrice,smul_eq_mul]
  constructor
  · split_ifs <;> norm_num [Matrix.cons_val_zero]
  · by_cases same : a=0
    · subst a
      norm_num [Matrix.cons_val_zero]
    · simp only [same,ite_false,mul_zero]

end LowEnergy.PreparationVacuumLegendreSpinReturn
