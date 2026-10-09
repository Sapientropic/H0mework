import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLegendreSpinSchur

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLegendreSpinReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumSpinGaussContraction PreparationVacuumSpinCarReturn
open PreparationVacuumGaussMeasureReturn PreparationVacuumCoframeLegendreSource
open PreparationVacuumCoframeQuantumCurrent PreparationVacuumCoframeSpinReduction
open PreparationVacuumGravityLegendreSource PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential Stage9C.Material.SpinPair
open scoped Topology BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder

private theorem sourceLegendreWeightedSquare {ι R : Type*} [Fintype ι] [Ring R] [Algebra ℝ R]
    (m : Matrix ι ι ℝ) (c : Matrix ι (Fin 8) ℝ)
    (T : Fin 8→R) :
    (∑i : ι,∑j : ι,m i j •
      ((∑a : Fin 8,c i a • T a)*(∑b : Fin 8,c j b • T b)))=
    ∑a : Fin 8,∑b : Fin 8,(c.transpose*m*c) a b • (T a*T b):=by
  classical
  have shuffle (f : ι→ι→Fin 8→Fin 8→R) :
      (∑i,∑j,∑a,∑b,f i j a b)=(∑a,∑b,∑i,∑j,f i j a b):=by
    simpa only [Fintype.sum_prod_type] using
      (Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)
        (f:=fun ij : ι×ι=>fun ab : Fin 8×Fin 8=>f ij.1 ij.2 ab.1 ab.2))
  have coefficient (a b : Fin 8) :
      (c.transpose*m*c) a b=∑i : ι,∑j : ι,c i a*m i j*c j b:=by
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
  have product (i j : ι) :
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

def sourceCanonicalSpinShift (field : Field289) (z : SourceCoordinateSlice) (j : Fin 6) : FiberEnd:=
  ∑i : LorentzIndex,(sourceShiftWeight z j i:ℂ) • sourceSpinFiber (field,z) (sourceState z) i

theorem sourceCanonicalSpinShift_emitted (field : Field289) (z : physicalChart) (j : Fin 6) :
    sourceCanonicalSpinShift field z.val j=
      ∑a : Fin 8,sourceSpinMixedTensor z.val j a • quantized (sourceSpinEmittedBasis a):=by
  have actual (i : LorentzIndex) := sourceSpinFiber_emitted field z i
  have realAction (r : ℝ) (T : FiberEnd) : r • T=(r:ℂ) • T:=
    RCLike.real_smul_eq_coe_smul (K:=ℂ) r T
  simp only [sourceCanonicalSpinShift,actual,←realAction,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [sourceSpinMixedTensor,Matrix.mul_apply,sourceSpinCoefficientMatrix,
    Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact (Finset.sum_smul (R:=ℝ) (M:=FiberEnd)
    (f:=fun i : LorentzIndex=>sourceShiftWeight z.val j i*sourceGaussRealSpinCoefficient z.val i a)
    (s:=Finset.univ) (x:=quantized (sourceSpinEmittedBasis a))).symm

def sourceCanonicalSpinHamiltonian (field : Field289) (z : SourceCoordinateSlice) : FiberEnd:=
  (∑i : Fin 6,∑j : Fin 6,((1/2:ℝ)*sourceGaussVelocityInverse z i j) •
    (sourceCanonicalSpinShift field z i*sourceCanonicalSpinShift field z j))-
      sourceGaussSpinConstant field z

theorem sourceCanonicalSpinHamiltonian_tensor (field : Field289) (z : physicalChart) :
    sourceCanonicalSpinHamiltonian field z.val=
      ∑a : Fin 8,∑b : Fin 8,sourceLegendreSpinTensor z.val a b •
        (quantized (sourceSpinEmittedBasis a)*quantized (sourceSpinEmittedBasis b)):=by
  rw [sourceCanonicalSpinHamiltonian]
  simp only [sourceCanonicalSpinShift_emitted]
  change (∑i : Fin 6,∑j : Fin 6,((1/2:ℝ) • sourceGaussVelocityInverse z.val) i j •
    ((∑a : Fin 8,sourceSpinMixedTensor z.val i a • quantized (sourceSpinEmittedBasis a))*
      (∑b : Fin 8,sourceSpinMixedTensor z.val j b • quantized (sourceSpinEmittedBasis b))))-
        sourceGaussSpinConstant field z.val=_
  rw [sourceLegendreWeightedSquare (R:=FiberEnd)
    ((1/2:ℝ) • sourceGaussVelocityInverse z.val) (sourceSpinMixedTensor z.val)
    (fun a=>quantized (sourceSpinEmittedBasis a))]
  have constant := sourceGaussSpinConstant_generated field z
  rw [constant,sourceLegendreSpinTensor_generated,sourceMixedGram_generated]
  have timeNonzero := lapse_pos.ne'
  have spaceNonzero := (GaussNativeEnergy.volume_pos z).ne'
  simp only [Matrix.smul_apply,Matrix.diagonal_apply,smul_eq_mul,mul_ite,mul_zero,ite_smul,
    zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.smul_sum,smul_smul]
  have zeroReal (T : FiberEnd) : (0:ℝ) • T=0:=zero_smul ℝ T
  simp only [zeroReal,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [←sub_smul]
  congr 1
  have prices : sourceMixedGramPrice a+2*sourceFlatSpinPrice a=sourceLegendreSpinPrice a:=by
    fin_cases a <;> norm_num [sourceMixedGramPrice,sourceFlatSpinPrice,sourceLegendreSpinPrice,
      Fin.sum_univ_succ,Matrix.cons_val]
  rw [←prices]
  field_simp
  ring

theorem sourceCanonicalSpinHamiltonian_generated (field : Field289) (z : physicalChart) :
    sourceCanonicalSpinHamiltonian field z.val=
      (lapse/(4*GaussNativeEnergy.volume z.val)) •
        ∑a : Fin 8,sourceLegendreSpinPrice a •
          (quantized (sourceSpinEmittedBasis a)*quantized (sourceSpinEmittedBasis a)):=by
  rw [sourceCanonicalSpinHamiltonian_tensor,sourceLegendreSpinTensor_generated]
  have zeroReal (T : FiberEnd) : (0:ℝ) • T=0:=zero_smul ℝ T
  simp only [Matrix.smul_apply,Matrix.diagonal_apply,smul_eq_mul,mul_ite,mul_zero,
    ite_smul,zeroReal,Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.smul_sum,smul_smul]

def sourceHamiltonianSpinWeight (b : Fin 7) : ℂ:=
  (sourceLegendreSpinPrice b.succ/4:ℝ)*sourceSpinPhase b.succ*sourceSpinPhase b.succ

private theorem sourceReturnConsVal5 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 5=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))):=rfl

private theorem sourceReturnConsVal6 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 6=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))) :=rfl

private theorem sourceReturnConsVal7 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 7=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))))):=rfl

theorem sourceHamiltonianSpinWeight_original (b : Fin 7) :
    sourceHamiltonianSpinWeight b=(GaussCoframeForm.spinWeight b:ℂ):=by
  fin_cases b <;>
    norm_num [sourceHamiltonianSpinWeight,sourceLegendreSpinPrice,sourceSpinPhase,
      GaussCoframeForm.spinWeight,Fin.val_succ,Fin.coe_ofNat_eq_mod,Nat.reduceMod,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,sourceReturnConsVal5,sourceReturnConsVal6,sourceReturnConsVal7] <;>
    simp only [mul_assoc,Complex.I_mul_I,mul_neg_one]

theorem sourceCanonicalSpinHamiltonian_original_fiber (field : Field289) (z : physicalChart) :
    sourceCanonicalSpinHamiltonian field z.val=
      (lapse/GaussNativeEnergy.volume z.val:ℂ) •
        ∑b : Fin 7,(GaussCoframeForm.spinWeight b:ℂ) •
          (quantized (GaussCoframeSpin.full b)*quantized (GaussCoframeSpin.full b)):=by
  rw [sourceCanonicalSpinHamiltonian_generated]
  have zeroReal (T : FiberEnd) : (0:ℝ) • T=0:=zero_smul ℝ T
  rw [Fin.sum_univ_succ]
  simp only [sourceLegendreSpinPrice,Matrix.cons_val_zero,zeroReal,zero_add]
  have realAction (r : ℝ) (T : FiberEnd) : r • T=(r:ℂ) • T:=
    RCLike.real_smul_eq_coe_smul (K:=ℂ) r T
  simp only [realAction,Finset.smul_sum,sourceSpinEmittedBasis,Fin.cases_succ]
  change (∑b : Fin 7,(lapse/(4*GaussNativeEnergy.volume z.val):ℝ) •
    ((sourceLegendreSpinPrice b.succ:ℝ) •
      (quantizer (sourceSpinPhase b.succ • GaussCoframeSpin.full b)*
        quantizer (sourceSpinPhase b.succ • GaussCoframeSpin.full b))))=_
  simp only [map_smul,smul_mul_assoc,mul_smul_comm,smul_smul,realAction]
  apply Finset.sum_congr rfl
  intro b _
  have weight:=sourceHamiltonianSpinWeight_original b
  unfold sourceHamiltonianSpinWeight at weight
  rw [←weight]
  congr 1
  push_cast
  ring

theorem sourceCanonicalSpinHamiltonian_original_action (field : Field289) (f : QuantumTest)
    (z : physicalChart) :
    sourceCanonicalSpinHamiltonian field z.val (f z.val)=
      (∑b : Fin 7,GaussCoframeForm.spinSquare b) f z.val:=by
  rw [sourceCanonicalSpinHamiltonian_original_fiber]
  have currentValue (b : Fin 7) (g : QuantumTest) : GaussCoframeSpin.current b g z.val=
      quantized (GaussCoframeSpin.full b) (g z.val):=rfl
  simp only [sum_apply,smul_apply,LinearMap.sum_apply,GaussCoframeForm.spinSquare,
    LinearMap.smul_apply,LinearMap.comp_apply,currentValue,GaussNativeForm.multiply_apply,map_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_apply_eq_comp,GaussCoframeForm.inverseVolume,
    GaussNativeEnergy.source_time_generated,Matrix.cons_val_zero,smul_smul]
  congr 1
  push_cast
  ring

end LowEnergy.PreparationVacuumLegendreSpinReturn
