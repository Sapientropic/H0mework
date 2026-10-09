import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSpinMixedReturn
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCoframeSpinContraction

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSpinCarReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumSpinGaussContraction PreparationVacuumCoframeSpinReduction
open PreparationVacuumCoframeQuantumCurrent PreparationVacuumCoframeLegendreSource
open PreparationVacuumGravityLegendreSource PreparationVacuumSourceFieldFamily
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open Stage9C.Material.SpinPair PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open GaussHistoryHilbert GaussQuantumMultiplier SourceCoframeSpinNormalOrder
open scoped Topology BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=LinearOrder.toDecidableEq

private theorem sourceCarConsVal5 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 5=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))):=rfl

private theorem sourceCarConsVal6 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 6=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))) :=rfl

private theorem sourceCarConsVal7 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 7=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))))):=rfl

def sourceEmittedSquareCoefficient : Fin 8→ℂ:=![-1,-1/4,-1/4,-1/4,1/4,1/4,1/4,1/4]

theorem sourceEmittedSquare_generated (a : Fin 8) :
    sourceSpinEmittedBasis a*sourceSpinEmittedBasis a=
      sourceEmittedSquareCoefficient a • (1:Matrix Mode Mode ℂ):=by
  cases a using Fin.cases with
  | zero=>
    simp only [sourceSpinEmittedBasis,Fin.cases_zero,sourceEmittedSquareCoefficient,
      Matrix.cons_val_zero,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul]
    norm_num [Complex.I_sq]
    ext i j
    by_cases h : i=j <;> simp [Matrix.one_apply,h]
  | succ b=>
    simp only [sourceSpinEmittedBasis,Fin.cases_succ,Matrix.smul_mul,Matrix.mul_smul,
      SourceCoframeSpinContraction.original_full_spin_square,smul_smul]
    apply congrArg (fun c : ℂ=>c • (1:Matrix Mode Mode ℂ))
    fin_cases b <;>
      norm_num [sourceSpinPhase,sourceEmittedSquareCoefficient,Fin.val_succ,
        Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,
        sourceCarConsVal5,sourceCarConsVal6,sourceCarConsVal7,Nat.reduceMod,Complex.I_sq] <;>
        simp only [←mul_assoc,Complex.I_mul_I,neg_one_mul]

private theorem sourceQuantizedOne : quantized (1:Matrix Mode Mode ℂ)=fiberNumber:=by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro word
  rw [fiberNumber_apply]
  change Fermion.quantize (Matrix.diagonal (fun _ : Mode=>(1:ℂ))) (fiberCoordinates v) word=
    (word.card:ℂ)*v word
  have original:=Fermion.occupationCharge_original_quantize (fun _ : Mode=>(1:ℂ))
  convert! (congrFun (LinearMap.congr_fun original (fiberCoordinates v)) word).trans
    (SourceFockRaising.total_apply (fiberCoordinates v) word) using 1

def sourceEightOneBody : SourceCoframeSpinNormalOrder.FiberEnd:=
  ∑a : Fin 8,(sourceFlatSpinPrice a:ℂ) •
    quantized (sourceSpinEmittedBasis a*sourceSpinEmittedBasis a)

def sourceEightNormalFiber : SourceCoframeSpinNormalOrder.FiberEnd:=
  ∑a : Fin 8,(sourceFlatSpinPrice a:ℂ) •
    normalFiber (sourceSpinEmittedBasis a) (sourceSpinEmittedBasis a)

def sourceEightNormalKernel (i j k l : Mode) : ℂ:=
  ∑a : Fin 8,(sourceFlatSpinPrice a:ℂ)*
    (sourceSpinEmittedBasis a i j*sourceSpinEmittedBasis a k l)

theorem sourceEightNormal_coordinates (psi : FockFiber) :
    fiberCoordinates (sourceEightNormalFiber psi)=
      ∑i : Mode,∑j : Mode,∑k : Mode,∑l : Mode,sourceEightNormalKernel i j k l •
        ((Fermion.creation i*Fermion.creation k*Fermion.annihilation l*Fermion.annihilation j)
          (fiberCoordinates psi)):=by
  have original (A B : Matrix Mode Mode ℂ) (v : FockFiber) :
      fiberCoordinates (normalFiber A B v)=Fermion.normalProduct A B (fiberCoordinates v):=rfl
  simp only [sourceEightNormalFiber,sum_apply,smul_apply,map_sum,map_smul,original]
  simp only [Fermion.normalProduct,LinearMap.sum_apply,LinearMap.smul_apply,
    Finset.smul_sum,smul_smul,sourceEightNormalKernel,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

theorem sourceEightOneBody_generated : sourceEightOneBody=(-3/2:ℂ) • fiberNumber:=by
  simp only [sourceEightOneBody,sourceEmittedSquare_generated]
  change (∑a : Fin 8,(sourceFlatSpinPrice a:ℂ) •
    quantizer (sourceEmittedSquareCoefficient a • (1:Matrix Mode Mode ℂ)))=_
  simp only [map_smul,smul_smul]
  change (∑a : Fin 8,((sourceFlatSpinPrice a:ℂ)*sourceEmittedSquareCoefficient a) •
    quantized (1:Matrix Mode Mode ℂ))=_
  rw [sourceQuantizedOne,←Finset.sum_smul]
  congr 1
  norm_num [sourceFlatSpinPrice,sourceEmittedSquareCoefficient,Fin.sum_univ_succ,
    Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,
    sourceCarConsVal5,sourceCarConsVal6,sourceCarConsVal7]

theorem sourceEightOrdered_generated :
    (∑a : Fin 8,(sourceFlatSpinPrice a:ℂ) •
      (quantized (sourceSpinEmittedBasis a)*quantized (sourceSpinEmittedBasis a)))=
      (-3/2:ℂ) • fiberNumber+sourceEightNormalFiber:=by
  simp only [original_fiber_normal_order,smul_add,Finset.sum_add_distrib]
  change sourceEightOneBody+sourceEightNormalFiber=_
  rw [sourceEightOneBody_generated]

theorem sourceGaussSpinConstant_normal (f : Field289) (z : physicalChart) :
    sourceGaussSpinConstant f z.val=
      ((3*lapse/(4*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber+
        ((-lapse/(2*GaussNativeEnergy.volume z.val):ℝ):ℂ) • sourceEightNormalFiber:=by
  rw [sourceGaussSpinConstant_generated]
  have realAction (r : ℝ) (A : SourceCoframeSpinNormalOrder.FiberEnd) : r • A=(r:ℂ) • A:=
    RCLike.real_smul_eq_coe_smul (K:=ℂ) r A
  simp only [realAction]
  rw [sourceEightOrdered_generated]
  simp only [smul_add,smul_smul]
  congr 1
  push_cast
  ring_nf

theorem sourceGaussOrderedConstant_normal (f : Field289) (z : physicalChart)
    (de : Fin 4→LorentzianCoframe) :
    sourceGaussOrderedConstant f z.val de=
      sourceGaussGeometryConstant z.val de • (1:SourceCoframeSpinNormalOrder.FiberEnd)+sourceGaussMixedSpin f z.val de+
        ((3*lapse/(4*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber+
          ((-lapse/(2*GaussNativeEnergy.volume z.val):ℝ):ℂ) • sourceEightNormalFiber:=by
  calc
    sourceGaussOrderedConstant f z.val de=
        sourceGaussGeometryConstant z.val de • (1:SourceCoframeSpinNormalOrder.FiberEnd)+sourceGaussMixedSpin f z.val de+
          sourceGaussSpinConstant f z.val:=by
      rw [sourceGaussSpinConstant_ordered]
      simpa only [add_assoc] using sourceGaussOrderedConstant_generated f z.val de
    _= _:=by rw [sourceGaussSpinConstant_normal];simp only [add_assoc]

end LowEnergy.PreparationVacuumSpinCarReturn
