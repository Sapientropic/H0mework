import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceLegendreLinearCurrent

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLegendreCurrentReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumSpinGaussContraction PreparationVacuumSpinCarReturn
open PreparationVacuumGaussMeasureReturn PreparationVacuumLegendreSpinReturn
open PreparationVacuumCoframeSpinReduction PreparationVacuumCoframeQuantumCurrent
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreDifferential GaussQuantumMultiplier
open Stage9C.Material.SpinPair
open scoped Topology ContDiff BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder

private theorem sourceCurrentConsVal5 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 5=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))):=rfl

private theorem sourceCurrentConsVal6 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 6=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))) :=rfl

private theorem sourceCurrentConsVal7 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 7=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))))):=rfl


def sourceLinearFiber (z : SourceCoordinateSlice) (i : Fin 6) : FiberEnd:=
  ∑a : Fin 8,sourceLegendreLinearTensor z i a • quantized (sourceSpinEmittedBasis a)

def sourceRadialCoefficient (i : Fin 6) (z : SourceCoordinateSlice) : ℝ:=
  -(lapse/(4*GaussNativeEnergy.volume z))*z.1 i

theorem sourceRadialCoefficient_smooth (i : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceRadialCoefficient i) z.val:=by
  have same : sourceRadialCoefficient i=fun w=>(-1/4:ℝ)*GaussCoframeForm.currentCoefficient i w:=by
    funext w
    simp only [sourceRadialCoefficient,GaussCoframeForm.currentCoefficient,
      GaussCoframeForm.inverseVolume,GaussNativeEnergy.source_time_generated,Matrix.cons_val_zero]
    ring
  rw [same]
  exact contDiffAt_const.mul (GaussCoframeForm.currentCoefficient_smooth i z)

def sourceRadialAction (i : Fin 6) : QuantumTest→ₗ[ℂ] QuantumTest:=
  GaussNativeForm.multiply (sourceRadialCoefficient i) (sourceRadialCoefficient_smooth i)

def sourceNumberLinearAction (i : Fin 6) : QuantumTest→ₗ[ℂ] QuantumTest:=
  Complex.I • (sourceRadialAction i*GaussCoframeForm.number)

theorem sourceLinearFiber_read (z : physicalChart) (i : Fin 6) (f : QuantumTest) :
    sourceLinearFiber z.val i (f z.val)=
      SourceCoframeCovariantAction.currentRow i f z.val+sourceNumberLinearAction i f z.val:=by
  rw [sourceLinearFiber,sourceLegendreLinearTensor_read]
  have realAction (r : ℝ) (T : FiberEnd) : r • T=(r:ℂ) • T:=
    RCLike.real_smul_eq_coe_smul (K:=ℂ) r T
  have zeroReal (T : FiberEnd) : (0:ℝ) • T=0:=zero_smul ℝ T
  have current (b : Fin 7) : GaussCoframeSpin.current b f z.val=
      quantized (GaussCoframeSpin.full b) (f z.val):=rfl
  have number : GaussCoframeForm.number f z.val=fiberNumber (f z.val):=by
    apply PiLp.ext
    intro word
    exact (GaussCoframeForm.number_apply f z.val word).trans (fiberNumber_apply (f z.val) word).symm
  have four : quantized (sourceSpinEmittedBasis 4)=quantized (GaussCoframeSpin.full 3):=by
    change quantizer ((1:ℂ) • GaussCoframeSpin.full 3)=_
    rw [one_smul]
    rfl
  have five : quantized (sourceSpinEmittedBasis 5)=quantized (GaussCoframeSpin.full 4):=by
    change quantizer ((1:ℂ) • GaussCoframeSpin.full 4)=_
    rw [one_smul]
    rfl
  have six : quantized (sourceSpinEmittedBasis 6)=quantized (GaussCoframeSpin.full 5):=by
    change quantizer ((1:ℂ) • GaussCoframeSpin.full 5)=_
    rw [one_smul]
    rfl
  fin_cases i <;>
    norm_num [Matrix.smul_apply,sourceLinearRead,Fin.sum_univ_eight,
      Fin.reduceFinMk,Fin.val_ofNat,Nat.reduceMod,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,sourceCurrentConsVal5,sourceCurrentConsVal6,sourceCurrentConsVal7,
      zeroReal,realAction,sourceSpinIdentity_number,four,five,six,sum_apply,smul_apply,
      sourceNumberLinearAction,sourceRadialAction,LinearMap.smul_apply,Module.End.mul_apply,
      LinearMap.comp_apply,GaussNativeForm.multiply_apply,number,
      SourceCoframeCovariantAction.currentRow,GaussCoframeForm.currentCoefficient,
      GaussCoframeForm.inverseVolume,GaussNativeEnergy.source_time_generated,current,
      sourceRadialCoefficient,map_smul,smul_smul,smul_eq_mul]
  all_goals simp only [show (2 : Fin 6)=⟨2,by decide⟩ from rfl,
    show (3 : Fin 6)=⟨3,by decide⟩ from rfl,
    show (4 : Fin 6)=⟨4,by decide⟩ from rfl,
    show (5 : Fin 6)=⟨5,by decide⟩ from rfl]
  all_goals module


def sourceLinearCoefficient (i : Fin 6) (a : Fin 8) (z : SourceCoordinateSlice) : ℝ:=
  (lapse/GaussNativeEnergy.volume z)*sourceLinearRead z.1 i a

theorem sourceLinearCoefficient_smooth (i : Fin 6) (a : Fin 8) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceLinearCoefficient i a) z.val:=by
  unfold sourceLinearCoefficient
  have inverse : ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice=>lapse/GaussNativeEnergy.volume w) z.val:=
    contDiffAt_const.div GaussNativeEnergy.volume_smooth.contDiffAt (GaussNativeEnergy.volume_pos z).ne'
  apply inverse.mul
  fin_cases i <;> fin_cases a <;>
    norm_num [sourceLinearRead,Matrix.of_apply,Fin.reduceFinMk,Fin.val_ofNat,Nat.reduceMod,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,sourceCurrentConsVal5,sourceCurrentConsVal6,sourceCurrentConsVal7] <;> fun_prop

def sourceLinearAction (i : Fin 6) : QuantumTest→ₗ[ℂ] QuantumTest:=
  ∑a : Fin 8,GaussNativeForm.multiply (sourceLinearCoefficient i a)
    (sourceLinearCoefficient_smooth i a)*
      GaussQuantumMultiplier.action (fun _=>sourceSpinEmittedBasis a) (fun _=>contDiffAt_const)

theorem sourceLinearAction_actual (i : Fin 6) (f : QuantumTest) (z : physicalChart) :
    sourceLinearAction i f z.val=sourceLinearFiber z.val i (f z.val):=by
  simp only [sourceLinearAction,sourceLinearFiber,LinearMap.sum_apply,Module.End.mul_apply,
    sum_apply,smul_apply,GaussNativeForm.multiply_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceLegendreLinearTensor_read]
  change (((lapse/GaussNativeEnergy.volume z.val)*sourceLinearRead z.val.1 i a:ℝ):ℂ) •
    quantized (sourceSpinEmittedBasis a) (f z.val)=_
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  rfl

theorem sourceLinearAction_generated (i : Fin 6) :
    sourceLinearAction i=SourceCoframeCovariantAction.currentRow i+sourceNumberLinearAction i:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases inside : z∈physicalChart
  · exact (sourceLinearAction_actual i f ⟨z,inside⟩).trans (sourceLinearFiber_read ⟨z,inside⟩ i f)
  · have outside (g : QuantumTest) : g z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>inside (g.tsupport_subset h))
    exact (outside _).trans (outside _).symm

def sourceCanonicalLinearMomentum : QuantumTest→ₗ[ℂ] QuantumTest:=
  ∑i : Fin 6,sourceLinearAction i*GaussCoframeCore.momentum i

def sourceNumberRadialMomentum : QuantumTest→ₗ[ℂ] QuantumTest:=
  ∑i : Fin 6,sourceNumberLinearAction i*GaussCoframeCore.momentum i

theorem sourceCanonicalLinearMomentum_split :
    sourceCanonicalLinearMomentum=
      (∑i : Fin 6,SourceCoframeCovariantAction.currentRow i*GaussCoframeCore.momentum i)+
        sourceNumberRadialMomentum:=by
  simp only [sourceCanonicalLinearMomentum,sourceLinearAction_generated,add_mul,
    Finset.sum_add_distrib,sourceNumberRadialMomentum]


-- The source-generated identity row is retained separately from the original four current rows.
def sourceRotationLinearAction (i : Fin 6) : QuantumTest→ₗ[ℂ] QuantumTest:=
  sourceLinearAction i-sourceNumberLinearAction i

def sourceOrderedCurrentAction : QuantumTest→ₗ[ℂ] QuantumTest:=
  (1/2:ℂ) • ∑i : Fin 6,
    (sourceRotationLinearAction i*GaussCoframeCore.momentum i+
      GaussCoframeCore.adjoint i*sourceRotationLinearAction i)

private theorem sourceSpinScalarCommute (a : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussCoframeSpin.current a) (GaussNativeForm.multiply c smooth):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (GaussCoframeSpin.full a)) (c z:ℂ) (f z)

set_option synthInstance.maxHeartbeats 120000 in
private theorem sourceMixedOrdered (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    GaussCoframeForm.mixed i a c smooth=(1/2:ℂ) •
      ((GaussNativeForm.multiply c smooth*GaussCoframeSpin.current a)*GaussCoframeCore.momentum i+
        GaussCoframeCore.adjoint i*(GaussNativeForm.multiply c smooth*GaussCoframeSpin.current a)):=by
  change (1/2:ℂ) • (GaussCoframeSpin.current a*(GaussNativeForm.multiply c smooth*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(GaussNativeForm.multiply c smooth*GaussCoframeSpin.current a))=_
  rw [←mul_assoc,(sourceSpinScalarCommute a c smooth).eq]

theorem sourceOrderedCurrentAction_original :
    sourceOrderedCurrentAction=GaussCoframeForm.currentAction:=by
  have rotation (i : Fin 6) : sourceRotationLinearAction i=SourceCoframeCovariantAction.currentRow i:=by
    rw [sourceRotationLinearAction,sourceLinearAction_generated,add_sub_cancel_right]
  norm_num [sourceOrderedCurrentAction,rotation,Fin.sum_univ_six,Fin.reduceFinMk,Fin.val_ofNat,Nat.reduceMod,
    SourceCoframeCovariantAction.currentRow,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceCurrentConsVal5,
    zero_mul,mul_zero,add_zero,zero_add,add_mul,mul_add,
    GaussCoframeForm.currentAction,sourceMixedOrdered,smul_add]
  module

end LowEnergy.PreparationVacuumLegendreCurrentReturn
