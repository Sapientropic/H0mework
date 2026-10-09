import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceHamiltonianSpinReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLegendreCurrentReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumSpinGaussContraction PreparationVacuumSpinCarReturn
open PreparationVacuumGaussMeasureReturn PreparationVacuumCoframeLegendreSource
open PreparationVacuumLegendreSpinReturn
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert Stage9C.Material.SpinPair
open scoped Topology BigOperators Matrix

private theorem sourceCurrentConsVal5 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 5=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))):=rfl

private theorem sourceCurrentConsVal6 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 6=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))) :=rfl

private theorem sourceCurrentConsVal7 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 7=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))))):=rfl

def sourceLinearPolynomial (q : Coframe) : Matrix (Fin 6) (Fin 8) ℝ:=
  -(GaussCoframeKinetic.polynomial q*sourceMixedPolynomial q)

def sourceLinearNumerator (q : Coframe) : Matrix (Fin 6) (Fin 8) ℝ:=
  let V:=q 0*q 2*q 5
  !![-V*q 0/2,0,0,0,0,0,0,0;
    -V*q 1/2,0,0,0,0,0,2*V*q 0,0;
    -V*q 2/2,0,0,0,0,0,0,0;
    -V*q 3/2,0,0,0,2*V*q 1,-2*V*q 0,0,0;
    -V*q 4/2,0,0,0,2*V*q 2,0,0,0;
    -V*q 5/2,0,0,0,0,0,0,0]

theorem sourceLinearPolynomial_generated (q : Coframe) :
    sourceLinearPolynomial q=sourceLinearNumerator q:=by
  ext i a
  fin_cases i <;> fin_cases a <;>
    norm_num [sourceLinearPolynomial,sourceLinearNumerator,sourceMixedPolynomial,
      GaussCoframeKinetic.polynomial,Matrix.neg_apply,Matrix.mul_apply,Fin.sum_univ_six,
      Fin.ext_iff,Fin.val_ofNat,Nat.reduceMod,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      sourceCurrentConsVal5,sourceCurrentConsVal6,sourceCurrentConsVal7] <;> ring

def sourceLegendreLinearTensor (z : SourceCoordinateSlice) : Matrix (Fin 6) (Fin 8) ℝ:=
  (-2:ℝ) • (((1/2:ℝ) • sourceGaussVelocityInverse z)*sourceSpinMixedTensor z)

theorem sourceLegendreLinearTensor_generated (z : physicalChart) :
    sourceLegendreLinearTensor z.val=
      (lapse/(2*(GaussNativeEnergy.volume z.val)^2)) • sourceLinearNumerator z.val.1:=by
  rw [sourceLegendreLinearTensor,sourceLegendreKineticMatrix_generated,
    sourceSpinMixedTensor_generated,sourceSpinMixedNumerator_values]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have generated:=sourceLinearPolynomial_generated z.val.1
  unfold sourceLinearPolynomial at generated
  rw [←generated,smul_neg,←neg_smul]
  congr 1
  have nonzero := (GaussNativeEnergy.volume_pos z).ne'
  field_simp
  ring

def sourceLinearRead (q : Coframe) : Matrix (Fin 6) (Fin 8) ℝ:=
  !![-q 0/4,0,0,0,0,0,0,0;
    -q 1/4,0,0,0,0,0,q 0,0;
    -q 2/4,0,0,0,0,0,0,0;
    -q 3/4,0,0,0,q 1,-q 0,0,0;
    -q 4/4,0,0,0,q 2,0,0,0;
    -q 5/4,0,0,0,0,0,0,0]

theorem sourceLegendreLinearTensor_read (z : physicalChart) :
    sourceLegendreLinearTensor z.val=
      (lapse/GaussNativeEnergy.volume z.val) • sourceLinearRead z.val.1:=by
  rw [sourceLegendreLinearTensor_generated]
  ext i a
  have nonzero := (GaussNativeEnergy.volume_pos z).ne'
  fin_cases i <;> fin_cases a <;>
    norm_num [sourceLinearNumerator,sourceLinearRead,Matrix.smul_apply,
      Fin.ext_iff,Fin.val_ofNat,Nat.reduceMod,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      sourceCurrentConsVal5,sourceCurrentConsVal6,sourceCurrentConsVal7,GaussNativeEnergy.volume] <;>
    field_simp <;> ring

theorem sourceLegendreLinearTensor_number (z : physicalChart) (i : Fin 6) :
    sourceLegendreLinearTensor z.val i 0=-(lapse/(4*GaussNativeEnergy.volume z.val))*z.val.1 i:=by
  have column (q : Coframe) (j : Fin 6) : sourceLinearRead q j 0=-q j/4:=by
    fin_cases j <;> rfl
  rw [sourceLegendreLinearTensor_read]
  change (lapse/GaussNativeEnergy.volume z.val)*sourceLinearRead z.val.1 i 0=_
  rw [column]
  ring

theorem sourceLegendreLinearTensor_current (z : physicalChart) :
    sourceLegendreLinearTensor z.val 1 6=GaussCoframeForm.currentCoefficient 0 z.val ∧
    sourceLegendreLinearTensor z.val 3 4=GaussCoframeForm.currentCoefficient 1 z.val ∧
    sourceLegendreLinearTensor z.val 3 5=-GaussCoframeForm.currentCoefficient 0 z.val ∧
    sourceLegendreLinearTensor z.val 4 4=GaussCoframeForm.currentCoefficient 2 z.val:=by
  rw [sourceLegendreLinearTensor_read]
  norm_num [sourceLinearRead,Matrix.smul_apply,GaussCoframeForm.currentCoefficient,
    GaussCoframeForm.inverseVolume,GaussNativeEnergy.source_time_generated,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,sourceCurrentConsVal5,sourceCurrentConsVal6]

end LowEnergy.PreparationVacuumLegendreCurrentReturn
