import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSpinTensorValues
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCoframeSpinConnection

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumSpinGaussContraction
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair
open PreparationVacuumGravityLegendreSource PreparationVacuumCoframeLegendreSource
open PreparationVacuumCoframeQuantumCurrent PreparationVacuumCoframeSpinReduction
open PreparationVacuumJointFieldResponse PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert SourceQuantumFockGauge
open GaussQuantumMultiplier
open scoped BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] sourceSpinCoefficientMatrix sourceFlatSpinCoefficient sourceFlatLorentzMatrix sourceFlatLorentzInverse
attribute [local irreducible] sourceGaussVelocityMatrix sourceGaussCoframe sourceLorentzInverse

private theorem sourceCurveConsVal5 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 5=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (u))))):=rfl

private theorem sourceCurveConsVal6 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 6=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (u)))))):=rfl

private theorem sourceCurveConsVal7 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 7=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (u))))))):=rfl

-- The same eliminated source momentum shift, including the identity/Number slot.
def sourceSpinMixedTensor (z : SourceCoordinateSlice) : Matrix (Fin 6) (Fin 8) ℝ:=
  sourceShiftWeight z*sourceSpinCoefficientMatrix z

def sourceSpinMixedNumerator (z : SourceCoordinateSlice) : Matrix (Fin 6) (Fin 8) ℝ:=
  -((sourceCoframeSlots (sourceGaussCoframe z)*sourceGaussVelocityMatrix z).transpose*
    sourceFlatLorentzMatrix*sourceFlatSpinCoefficient)

theorem sourceSpinMixedTensor_generated (z : physicalChart) :
    sourceSpinMixedTensor z.val=(GaussNativeEnergy.volume z.val)⁻¹ • sourceSpinMixedNumerator z.val:=by
  let E:=sourceCoframeSlots (sourceGaussCoframe z.val)
  let Q:=sourceCoframeSlots (sourceGaussCoframe z.val)⁻¹
  have inverse : E*Q=1:=
    (sourceCoframeSlots_inverse _ (sourceGaussCoframe_nondegenerate z)).1
  rw [sourceSpinMixedTensor,sourceShiftWeight,sourceSpinCoefficientMatrix_generated,
    sourceLorentzInverse_slots]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.neg_mul]
  change _ • -( (sourceGaussVelocityMatrix z.val).transpose*
    (E.transpose*sourceFlatLorentzMatrix*E)*(Q*sourceFlatSpinCoefficient))=_
  have collapse : (sourceGaussVelocityMatrix z.val).transpose*
      (E.transpose*sourceFlatLorentzMatrix*E)*(Q*sourceFlatSpinCoefficient)=
      (E*sourceGaussVelocityMatrix z.val).transpose*sourceFlatLorentzMatrix*sourceFlatSpinCoefficient:=by
    simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    rw [←Matrix.mul_assoc E Q,inverse,Matrix.one_mul]
  rw [collapse]
  change _ • sourceSpinMixedNumerator z.val=_
  congr 1
  rw [sourceGaussCoframe_determinant,GaussNativeEnergy.source_time_generated]
  simp only [Matrix.cons_val_zero]
  have timeNonzero : lapse≠0:=lapse_pos.ne'
  have spaceNonzero : GaussNativeEnergy.volume z.val≠0:=(GaussNativeEnergy.volume_pos z).ne'
  field_simp

open Lean Elab Tactic in
elab "unfold_source_velocity_coefficients" : tactic => do
  let info ← getConstInfo ``sourceGaussVelocityMatrix_coefficients
  let some gamma := info.type.getUsedConstants.find?
    (fun n=>n.toString.endsWith ".sourceGaussGammaCoefficients")
    | throwError "source velocity lost its actual BF coefficient body"
  evalTactic (← `(tactic| unfold $(mkIdent gamma)))

def sourceMixedPolynomial (q : Coframe) : Matrix (Fin 6) (Fin 8) ℝ:=
  !![q 2*q 5/2,0,0,0,0,0,0,0;
    0,0,0,0,0,0,q 2*q 5/2,0;
    q 0*q 5/2,0,0,0,0,0,-q 1*q 5/2,0;
    0,0,0,0,0,-q 2*q 5/2,0,0;
    0,0,0,0,q 0*q 5/2,q 1*q 5/2,0,0;
    q 0*q 2/2,0,0,0,-q 0*q 4/2,(q 2*q 3-q 1*q 4)/2,0,0]

private theorem sourceSpinMixedNumerator_row0 (z : SourceCoordinateSlice) (a : Fin 8) :
    sourceSpinMixedNumerator z 0 a=sourceMixedPolynomial z.1 0 a:=by
  rw [sourceSpinMixedNumerator,Matrix.transpose_mul,sourceGaussVelocityMatrix_coefficients]
  fin_cases a
  all_goals simp only [Matrix.neg_apply,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
    Fin.sum_univ_four,Fin.sum_univ_six]
  all_goals unfold_source_velocity_coefficients
  all_goals simp only [sourceCoframeSlots_entry,sourceGaussCoframe,GaussNativeEnergy.coframe,
    Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.isValue,
    mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul,neg_zero]
  all_goals norm_num [sourceFlatLorentzMatrix,Matrix.of_apply,sourceFlatLorentzInverse,
    sourceFlatSpinCoefficient_values,sourceFlatSpinSlot,sourceFlatSpinWeight,sourceMixedPolynomial,
    Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals ring


private theorem sourceSpinMixedNumerator_row1 (z : SourceCoordinateSlice) (a : Fin 8) :
    sourceSpinMixedNumerator z 1 a=sourceMixedPolynomial z.1 1 a:=by
  rw [sourceSpinMixedNumerator,Matrix.transpose_mul,sourceGaussVelocityMatrix_coefficients]
  fin_cases a
  all_goals simp only [Matrix.neg_apply,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
    Fin.sum_univ_four,Fin.sum_univ_six]
  all_goals unfold_source_velocity_coefficients
  all_goals simp only [sourceCoframeSlots_entry,sourceGaussCoframe,GaussNativeEnergy.coframe,
    Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.isValue,
    mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul,neg_zero]
  all_goals norm_num [sourceFlatLorentzMatrix,Matrix.of_apply,sourceFlatLorentzInverse,
    sourceFlatSpinCoefficient_values,sourceFlatSpinSlot,sourceFlatSpinWeight,sourceMixedPolynomial,
    Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals ring


private theorem sourceSpinMixedNumerator_row2 (z : SourceCoordinateSlice) (a : Fin 8) :
    sourceSpinMixedNumerator z 2 a=sourceMixedPolynomial z.1 2 a:=by
  rw [sourceSpinMixedNumerator,Matrix.transpose_mul,sourceGaussVelocityMatrix_coefficients]
  fin_cases a
  all_goals simp only [Matrix.neg_apply,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
    Fin.sum_univ_four,Fin.sum_univ_six]
  all_goals unfold_source_velocity_coefficients
  all_goals simp only [sourceCoframeSlots_entry,sourceGaussCoframe,GaussNativeEnergy.coframe,
    Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.isValue,
    mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul,neg_zero]
  all_goals norm_num [sourceFlatLorentzMatrix,Matrix.of_apply,sourceFlatLorentzInverse,
    sourceFlatSpinCoefficient_values,sourceFlatSpinSlot,sourceFlatSpinWeight,sourceMixedPolynomial,
    Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals ring


private theorem sourceSpinMixedNumerator_row3 (z : SourceCoordinateSlice) (a : Fin 8) :
    sourceSpinMixedNumerator z 3 a=sourceMixedPolynomial z.1 3 a:=by
  rw [sourceSpinMixedNumerator,Matrix.transpose_mul,sourceGaussVelocityMatrix_coefficients]
  fin_cases a
  all_goals simp only [Matrix.neg_apply,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
    Fin.sum_univ_four,Fin.sum_univ_six]
  all_goals unfold_source_velocity_coefficients
  all_goals simp only [sourceCoframeSlots_entry,sourceGaussCoframe,GaussNativeEnergy.coframe,
    Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.isValue,
    mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul,neg_zero]
  all_goals norm_num [sourceFlatLorentzMatrix,Matrix.of_apply,sourceFlatLorentzInverse,
    sourceFlatSpinCoefficient_values,sourceFlatSpinSlot,sourceFlatSpinWeight,sourceMixedPolynomial,
    Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals ring


private theorem sourceSpinMixedNumerator_row4 (z : SourceCoordinateSlice) (a : Fin 8) :
    sourceSpinMixedNumerator z 4 a=sourceMixedPolynomial z.1 4 a:=by
  rw [sourceSpinMixedNumerator,Matrix.transpose_mul,sourceGaussVelocityMatrix_coefficients]
  fin_cases a
  all_goals simp only [Matrix.neg_apply,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
    Fin.sum_univ_four,Fin.sum_univ_six]
  all_goals unfold_source_velocity_coefficients
  all_goals simp only [sourceCoframeSlots_entry,sourceGaussCoframe,GaussNativeEnergy.coframe,
    Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.isValue,
    mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul,neg_zero]
  all_goals norm_num [sourceFlatLorentzMatrix,Matrix.of_apply,sourceFlatLorentzInverse,
    sourceFlatSpinCoefficient_values,sourceFlatSpinSlot,sourceFlatSpinWeight,sourceMixedPolynomial,
    Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals ring


private theorem sourceSpinMixedNumerator_row5 (z : SourceCoordinateSlice) (a : Fin 8) :
    sourceSpinMixedNumerator z 5 a=sourceMixedPolynomial z.1 5 a:=by
  rw [sourceSpinMixedNumerator,Matrix.transpose_mul,sourceGaussVelocityMatrix_coefficients]
  fin_cases a
  all_goals simp only [Matrix.neg_apply,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
    Fin.sum_univ_four,Fin.sum_univ_six]
  all_goals unfold_source_velocity_coefficients
  all_goals simp only [sourceCoframeSlots_entry,sourceGaussCoframe,GaussNativeEnergy.coframe,
    Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.isValue,
    mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul,neg_zero]
  all_goals norm_num [sourceFlatLorentzMatrix,Matrix.of_apply,sourceFlatLorentzInverse,
    sourceFlatSpinCoefficient_values,sourceFlatSpinSlot,sourceFlatSpinWeight,sourceMixedPolynomial,
    Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals ring


theorem sourceSpinMixedNumerator_values (z : SourceCoordinateSlice) :
    sourceSpinMixedNumerator z=sourceMixedPolynomial z.1:=by
  ext j a
  fin_cases j
  · exact sourceSpinMixedNumerator_row0 z a
  · exact sourceSpinMixedNumerator_row1 z a
  · exact sourceSpinMixedNumerator_row2 z a
  · exact sourceSpinMixedNumerator_row3 z a
  · exact sourceSpinMixedNumerator_row4 z a
  · exact sourceSpinMixedNumerator_row5 z a

def sourceNumberConnection (q : Coframe) : Fin 6→ℝ:=
  ![1/(2*q 0),0,1/(2*q 2),0,0,1/(2*q 5)]

private theorem sourceVolume_diagonal_ne (z : physicalChart) :
    z.val.1 0≠0 ∧ z.val.1 2≠0 ∧ z.val.1 5≠0:=by
  have h:=(GaussNativeEnergy.volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5≠0 at h
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2,(mul_ne_zero_iff.mp h).2⟩

theorem sourceSpinMixedTensor_number (z : physicalChart) (j : Fin 6) :
    sourceSpinMixedTensor z.val j 0=sourceNumberConnection z.val.1 j:=by
  rw [sourceSpinMixedTensor_generated,sourceSpinMixedNumerator_values]
  obtain ⟨h0,h2,h5⟩:=sourceVolume_diagonal_ne z
  fin_cases j <;> simp [sourceMixedPolynomial,sourceNumberConnection,GaussNativeEnergy.volume,
    Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,
    Matrix.smul_apply,smul_eq_mul] <;> field_simp

theorem sourceSpinMixedTensor_rotation (z : physicalChart) (j : Fin 6) (a : Fin 3) :
    sourceSpinMixedTensor z.val j ⟨4+a.val,by omega⟩=
      -SourceCoframeSpinConnection.spinConnection z.val.1 j a:=by
  rw [sourceSpinMixedTensor_generated,sourceSpinMixedNumerator_values]
  obtain ⟨h0,h2,h5⟩:=sourceVolume_diagonal_ne z
  fin_cases j <;> fin_cases a
  all_goals simp [sourceMixedPolynomial,SourceCoframeSpinConnection.spinConnection,GaussNativeEnergy.volume,
      Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,
      Matrix.smul_apply,smul_eq_mul]
  all_goals field_simp
  all_goals ring

-- This is the existing source Gauss shift, rather than an additional prepared readout.
theorem sourceGaussSpinShift_emitted (f : Field289) (z : physicalChart) (j : Fin 6) :
    (∑i : LorentzIndex,(sourceShiftWeight z.val j i:ℂ) •
      sourceSpinFiber (f,z.val) (sourceState z.val) i)=
    ∑a : Fin 8,(sourceSpinMixedTensor z.val j a:ℂ) • quantized (sourceSpinEmittedBasis a):=by
  simp only [sourceSpinFiber_emitted,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_smul]
  congr 1
  simp only [sourceSpinMixedTensor,Matrix.mul_apply,sourceSpinCoefficientMatrix,Matrix.of_apply,
    Complex.ofReal_sum,Complex.ofReal_mul]

theorem sourceSpinMixedTensor_other (z : physicalChart) (j : Fin 6) (a : Fin 8)
    (other : a=1 ∨ a=2 ∨ a=3 ∨ a=7) : sourceSpinMixedTensor z.val j a=0:=by
  rw [sourceSpinMixedTensor_generated,sourceSpinMixedNumerator_values]
  rcases other with rfl|rfl|rfl|rfl <;> fin_cases j <;>
    simp [sourceMixedPolynomial,Matrix.smul_apply,smul_eq_mul,
      Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7]

private theorem sourceRotation_emitter (a : Fin 3) :
    quantized (sourceSpinEmittedBasis ⟨4+a.val,by omega⟩)=SourceCoframeSpinConnection.rotation a:=by
  fin_cases a <;> norm_num [sourceSpinEmittedBasis,sourceSpinPhase,SourceCoframeSpinConnection.rotation]

private theorem sourceRealFiberSmul (r : ℝ) (T : FiberEnd) : (r:ℂ) • T=r • T:=
  (RCLike.real_smul_eq_coe_smul (K:=ℂ) r T).symm

set_option backward.isDefEq.respectTransparency true in
theorem sourceGaussSpinShift_return (f : Field289) (z : physicalChart) (j : Fin 6) :
    (∑i : LorentzIndex,(sourceShiftWeight z.val j i:ℂ) •
      sourceSpinFiber (f,z.val) (sourceState z.val) i)=
      ((sourceNumberConnection z.val.1 j:ℂ)*Complex.I) • fiberNumber-
        SourceCoframeSpinConnection.connectionFiber j z.val:=by
  rw [sourceGaussSpinShift_emitted]
  have r0:=sourceSpinMixedTensor_rotation z j 0
  have r1:=sourceSpinMixedTensor_rotation z j 1
  have r2:=sourceSpinMixedTensor_rotation z j 2
  change sourceSpinMixedTensor z.val j 4=-SourceCoframeSpinConnection.spinConnection z.val.1 j 0 at r0
  change sourceSpinMixedTensor z.val j 5=-SourceCoframeSpinConnection.spinConnection z.val.1 j 1 at r1
  change sourceSpinMixedTensor z.val j 6=-SourceCoframeSpinConnection.spinConnection z.val.1 j 2 at r2
  simp only [Fin.sum_univ_eight,sourceSpinMixedTensor_number,sourceSpinIdentity_number,
    sourceSpinMixedTensor_other z j 1 (Or.inl rfl),
    sourceSpinMixedTensor_other z j 2 (Or.inr (Or.inl rfl)),
    sourceSpinMixedTensor_other z j 3 (Or.inr (Or.inr (Or.inl rfl))),
    sourceSpinMixedTensor_other z j 7 (Or.inr (Or.inr (Or.inr rfl))),r0,r1,r2,
    Complex.ofReal_zero,zero_smul,add_zero,zero_add,smul_smul]
  simp only [sourceRealFiberSmul,zero_smul,add_zero,zero_add]
  simp only [SourceCoframeSpinConnection.connectionFiber,Fin.sum_univ_three,
    ←sourceRotation_emitter,Complex.ofReal_neg,neg_smul,sub_eq_add_neg,neg_add_rev,
    sourceRealFiberSmul]
  norm_num only [Fin.val_zero,Fin.val_one,Fin.val_ofNat,Nat.reduceMod,Fin.reduceFinMk,Nat.reduceAdd]
  have zeroReal (T : FiberEnd) : (0:ℝ) • T=0:=zero_smul ℝ T
  have zeroComplex (T : FiberEnd) : (0:ℂ) • T=0:=zero_smul ℂ T
  have six : (⟨4+(2:Fin 3).val,by omega⟩:Fin 8)=6:=rfl
  simp only [six,zeroReal,zeroComplex,add_zero,zero_add,smul_smul,smul_eq_mul,neg_one_mul]
  have negativeAction (r : ℝ) (T : FiberEnd) : (-r) • T=-(r • T):=neg_smul r T
  rw [negativeAction (SourceCoframeSpinConnection.spinConnection z.val.1 j 0) (quantized (sourceSpinEmittedBasis 4)),
    negativeAction (SourceCoframeSpinConnection.spinConnection z.val.1 j 1) (quantized (sourceSpinEmittedBasis 5)),
    negativeAction (SourceCoframeSpinConnection.spinConnection z.val.1 j 2) (quantized (sourceSpinEmittedBasis 6))]
  ac_rfl

-- Number is the occupied-sector part of the original Gaussian density connection.
def sourceCoframeRay (z : SourceCoordinateSlice) (j : Fin 6) (r : ℝ) : SourceCoordinateSlice:=
  z+r • GaussCoframeCore.coframeDirection j

private theorem sourceCoframeRay_entry (z : SourceCoordinateSlice) (j i : Fin 6) :
    HasDerivAt (fun r=> (sourceCoframeRay z j r).1 i)
      ((EuclideanSpace.single j 1:Coframe) i) 0:=by
  convert! ((hasDerivAt_id (0:ℝ)).mul_const ((EuclideanSpace.single j 1:Coframe) i)).const_add (z.1 i) using 1
  all_goals simp [sourceCoframeRay,GaussCoframeCore.coframeDirection,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]

theorem sourceNumberConnection_volume (z : physicalChart) (j : Fin 6) :
    HasDerivAt (fun r=>GaussNativeEnergy.volume (sourceCoframeRay z.val j r))
      (2*sourceNumberConnection z.val.1 j*GaussNativeEnergy.volume z.val) 0:=by
  have actual:=((sourceCoframeRay_entry z.val j 0).mul (sourceCoframeRay_entry z.val j 2)).mul
    (sourceCoframeRay_entry z.val j 5)
  obtain ⟨h0,h2,h5⟩:=sourceVolume_diagonal_ne z
  convert! actual using 1
  all_goals fin_cases j <;> simp [sourceNumberConnection,sourceCoframeRay,GaussCoframeCore.coframeDirection,
      Matrix.cons_val_four,sourceCurveConsVal5,sourceCurveConsVal6,sourceCurveConsVal7,
      GaussNativeEnergy.volume,PiLp.single_apply,PiLp.smul_apply,PiLp.add_apply] <;>
      field_simp

theorem sourceNumberConnection_density (N : ℕ) (z : physicalChart) (j : Fin 6) :
    HasDerivAt (fun r=>GaussDensityCore.density N (sourceCoframeRay z.val j r))
      (2*((N:ℝ)+2)*sourceNumberConnection z.val.1 j*GaussDensityCore.density N z.val) 0:=by
  have actual:=(sourceNumberConnection_volume z j).pow (N+2)
  have weighted:=actual.const_mul (GaussHistoryHilbert.jacobian (z.val.2.2:Gauge))
  have degree : N+2-1=N+1:=by omega
  convert! weighted using 1
  · funext r
    simp [GaussDensityCore.density,sourceCoframeRay,GaussCoframeCore.coframeDirection,
      GaussNativeEnergy.volume]
  · simp only [GaussDensityCore.density,Nat.cast_add,Nat.cast_ofNat,sourceCoframeRay,
      zero_smul,add_zero,GaussNativeEnergy.volume,degree,Nat.succ_eq_add_one,
      pow_succ]
    ring

private theorem sourceWeightedSpinSquare {R : Type*} [Ring R] [Algebra ℝ R]
    (m : Matrix LorentzIndex LorentzIndex ℝ) (c : Matrix LorentzIndex (Fin 8) ℝ)
    (T : Fin 8→R) :
    (∑i : LorentzIndex,∑j : LorentzIndex,m i j •
      ((∑a : Fin 8,c i a • T a)*(∑b : Fin 8,c j b • T b)))=
    ∑a : Fin 8,∑b : Fin 8,(c.transpose*m*c) a b • (T a*T b):=by
  have shuffle (f : LorentzIndex→LorentzIndex→Fin 8→Fin 8→R) :
      (∑i,∑j,∑a,∑b,f i j a b)=(∑a,∑b,∑i,∑j,f i j a b):=by
    simpa only [Fintype.sum_prod_type] using
      (Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)
        (f:=fun ij : LorentzIndex×LorentzIndex=>fun ab : Fin 8×Fin 8=>f ij.1 ij.2 ab.1 ab.2))
  have coefficient (a b : Fin 8) :
      (c.transpose*m*c) a b=∑i : LorentzIndex,∑j : LorentzIndex,c i a*m i j*c j b:=by
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
  have product (i j : LorentzIndex) :
      (∑a : Fin 8,c i a • T a)*(∑b : Fin 8,c j b • T b)=
      ∑a : Fin 8,∑b : Fin 8,(c i a*c j b) • (T a*T b):=by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
    congr 1
    ring
  simp only [product,Finset.smul_sum,smul_smul]
  rw [shuffle]
  simp only [coefficient,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

def sourceGaussSpinConstant (f : Field289) (z : SourceCoordinateSlice) : FiberEnd:=
  ∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z i j •
    (sourceSpinFiber (f,z) (sourceState z) i*sourceSpinFiber (f,z) (sourceState z) j)

theorem sourceGaussSpinConstant_ordered (f : Field289) (z : SourceCoordinateSlice) :
    sourceGaussSpinConstant f z=quantized (sourceGaussOneBodyMatrix f z)+sourceGaussFourBody f z:=by
  simp only [sourceGaussSpinConstant,sourceSpinFiber_ordered,smul_add,Finset.sum_add_distrib]
  have oneBody : (∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z i j •
      quantized (sourceSpinFullMatrix (f,z) (sourceState z) i*sourceSpinFullMatrix (f,z) (sourceState z) j))=
      quantized (sourceGaussOneBodyMatrix f z):=by
    change (∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z i j •
      quantizer (sourceSpinFullMatrix (f,z) (sourceState z) i*sourceSpinFullMatrix (f,z) (sourceState z) j))=
      quantizer (sourceGaussOneBodyMatrix f z)
    simp only [sourceGaussOneBodyMatrix,map_sum,map_smul]
  rw [oneBody]
  rfl

theorem sourceGaussSpinConstant_generated (f : Field289) (z : physicalChart) :
    sourceGaussSpinConstant f z.val=
      (-lapse/(2*GaussNativeEnergy.volume z.val)) •
        ∑a : Fin 8,sourceFlatSpinPrice a •
          (quantized (sourceSpinEmittedBasis a)*quantized (sourceSpinEmittedBasis a)):=by
  have emitter (i : LorentzIndex) : sourceSpinFiber (f,z.val) (sourceState z.val) i=
      ∑a : Fin 8,sourceSpinCoefficientMatrix z.val i a • quantized (sourceSpinEmittedBasis a):=by
    rw [sourceSpinFiber_emitted]
    apply Finset.sum_congr rfl
    intro a _
    simp only [sourceSpinCoefficientMatrix,Matrix.of_apply]
    exact sourceRealFiberSmul (sourceGaussRealSpinCoefficient z.val i a) (quantized (sourceSpinEmittedBasis a))
  have realWeight (i j : LorentzIndex) : sourcePotentialWeight z.val i j=
      ((-(1/2:ℝ)*sourceLorentzInverse (sourceGaussCoframe z.val) i j:ℝ):ℂ):=by
    simp [sourcePotentialWeight,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_div]
  change (∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z.val i j •
    (sourceSpinFiber (f,z.val) (sourceState z.val) i*sourceSpinFiber (f,z.val) (sourceState z.val) j))=_
  simp only [emitter,realWeight,←RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  change (∑i : LorentzIndex,∑j : LorentzIndex,
    ((-(1/2:ℝ)) • sourceLorentzInverse (sourceGaussCoframe z.val)) i j •
      ((∑a : Fin 8,sourceSpinCoefficientMatrix z.val i a • quantized (sourceSpinEmittedBasis a))*
        (∑b : Fin 8,sourceSpinCoefficientMatrix z.val j b • quantized (sourceSpinEmittedBasis b))))=_
  rw [sourceWeightedSpinSquare (R:=FiberEnd)
    ((-(1/2:ℝ)) • sourceLorentzInverse (sourceGaussCoframe z.val))
    (sourceSpinCoefficientMatrix z.val) (fun a=>quantized (sourceSpinEmittedBasis a))]
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  change (∑a : Fin 8,∑b : Fin 8,((-(1/2:ℝ)) • sourceSpinOrderedTensor z.val) a b •
    (quantized (sourceSpinEmittedBasis a)*quantized (sourceSpinEmittedBasis b)))=_
  rw [sourceSpinOrderedTensor_generated]
  simp only [Matrix.smul_apply,smul_eq_mul,sourceFlatOrderedTensor_values,mul_ite,mul_zero,
    ite_smul,zero_smul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.smul_sum,smul_smul,zero_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceGaussCoframe_determinant,GaussNativeEnergy.source_time_generated]
  simp only [Matrix.cons_val_zero]
  have timeNonzero : lapse≠0:=lapse_pos.ne'
  have spaceNonzero : GaussNativeEnergy.volume z.val≠0:=(GaussNativeEnergy.volume_pos z).ne'
  field_simp
  ring_nf
  have actualZero (T : FiberEnd) : (0:ℝ) • T=0:=zero_smul ℝ T
  simp only [actualZero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end LowEnergy.PreparationVacuumSpinGaussContraction
