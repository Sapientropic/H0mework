import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNumberRadialPairReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNumberRadialReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumLegendreCurrentReturn PreparationVacuumLegendreSpinReturn
open PreparationVacuumGaussMeasureReturn PreparationVacuumSpinGaussContraction PreparationVacuumSpinCarReturn
open PreparationVacuumCoframeLegendreSource PreparationVacuumCoframeQuantumCurrent
open PreparationVacuumCoframeSpinReduction PreparationVacuumGravityLegendreSource
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreDifferential GaussQuantumMultiplier Stage9C.Material.SpinPair
open scoped Topology ContDiff BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder

private def sourceSpinEvaluation (f : QuantumTest) (z : SourceCoordinateSlice) : SourceRadialEnd→ₗ[ℂ] FockFiber where
  toFun A:=A f z
  map_add' _A _B:=rfl
  map_smul' _c _A:=rfl

def sourcePreparedShiftRight (i : Fin 6) : SourceRadialEnd:=
  Complex.I • sourceNumberScalarAction i-SourceCoframeCovariantAction.connectionAction i

def sourcePreparedShiftLeft (i : Fin 6) : SourceRadialEnd:=
  (-Complex.I) • sourceNumberScalarAction i-SourceCoframeCovariantAction.connectionAction i

theorem sourcePreparedShiftRight_actual (field : Field289) (z : physicalChart) (i : Fin 6) (f : QuantumTest) :
    sourcePreparedShiftRight i f z.val=sourceCanonicalSpinShift field z.val i (f z.val):=by
  rw [sourceCanonicalSpinShift,sourceGaussSpinShift_return]
  change Complex.I • ((sourceNumberConnection z.val.1 i:ℂ) • fiberNumber (f z.val))-
    SourceCoframeSpinConnection.connectionFiber i z.val (f z.val)=_
  simp only [sub_apply,smul_apply,smul_smul]
  module

private theorem sourceMetricMixed_row (z : physicalChart) (i : Fin 6) (a : Fin 8) :
    (∑j : Fin 6,sourceKineticCoefficient i j z.val*sourceSpinMixedTensor z.val j a)=
      (-1/2:ℝ)*sourceLegendreLinearTensor z.val i a:=by
  change (∑j : Fin 6,((1/2:ℝ) • sourceGaussVelocityInverse z.val) i j*sourceSpinMixedTensor z.val j a)=_
  change (((1/2:ℝ) • sourceGaussVelocityInverse z.val)*sourceSpinMixedTensor z.val) i a=_
  simp only [sourceLegendreLinearTensor,Matrix.smul_apply,smul_eq_mul]
  ring

private theorem sourceWeightedRow {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : Matrix (Fin 6) (Fin 6) ℝ) (c : Matrix (Fin 6) (Fin 8) ℝ) (T : Fin 8→E) (i : Fin 6) :
    (∑j : Fin 6,m i j • ∑a : Fin 8,c j a • T a)=∑a : Fin 8,(m*c) i a • T a:=by
  simp only [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_smul]
  rfl

set_option backward.isDefEq.respectTransparency true in
theorem sourcePreparedShiftRight_contract (i : Fin 6) :
    (∑j : Fin 6,sourceKineticMetric i j*sourcePreparedShiftRight j)=(-1/2:ℂ) • sourceLinearAction i:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases inside : z∈physicalChart
  · let point : physicalChart:=⟨z,inside⟩
    change sourceSpinEvaluation f z (∑j : Fin 6,sourceKineticMetric i j*sourcePreparedShiftRight j)=_
    rw [map_sum]
    change (∑j : Fin 6,(sourceKineticCoefficient i j point.val:ℂ) • sourcePreparedShiftRight j f point.val)=
      (-1/2:ℂ) • sourceLinearAction i f point.val
    simp_rw [sourcePreparedShiftRight_actual 0 point,sourceCanonicalSpinShift_emitted 0 point]
    have realAction (r : ℝ) (v : FockFiber) : (r:ℂ) • v=r • v:=
      (RCLike.real_smul_eq_coe_smul (K:=ℂ) r v).symm
    simp only [sum_apply,smul_apply,realAction]
    change (∑j : Fin 6,((1/2:ℝ) • sourceGaussVelocityInverse point.val) i j •
      (∑a : Fin 8,sourceSpinMixedTensor point.val j a • quantized (sourceSpinEmittedBasis a) (f point.val)))=_
    rw [sourceWeightedRow]
    have coefficient (a : Fin 8) :
        (((1/2:ℝ) • sourceGaussVelocityInverse point.val)*sourceSpinMixedTensor point.val) i a=
          (-1/2:ℝ)*sourceLegendreLinearTensor point.val i a:=sourceMetricMixed_row point i a
    simp_rw [coefficient]
    rw [sourceLinearAction_actual i f point]
    change (∑a : Fin 8,((-1/2:ℝ)*sourceLegendreLinearTensor z i a) •
      (quantized (sourceSpinEmittedBasis a) (f z)))=((-1/2:ℂ) • sourceLinearFiber z i) (f z)
    simp only [sourceLinearFiber,Finset.smul_sum,smul_smul,sum_apply,smul_apply,
      RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    push_cast
    ring
  · have outside (g : QuantumTest) : g z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>inside (g.tsupport_subset h))
    exact (outside _).trans (outside _).symm

theorem sourceNumberMetric_contract (i : Fin 6) :
    (∑j : Fin 6,sourceKineticMetric i j*sourceNumberScalarAction j)=
      (-1/2:ℂ) • (sourceRadialAction i*GaussCoframeForm.number):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases inside : z∈physicalChart
  · let point : physicalChart:=⟨z,inside⟩
    change sourceSpinEvaluation f z (∑j : Fin 6,sourceKineticMetric i j*sourceNumberScalarAction j)=_
    rw [map_sum]
    change (∑j : Fin 6,(sourceKineticCoefficient i j z:ℂ) •
      ((sourceNumberConnection z.1 j:ℂ) • fiberNumber (f z)))=_
    have number : GaussCoframeForm.number f z=fiberNumber (f z):=by
      apply PiLp.ext
      intro word
      exact (GaussCoframeForm.number_apply f z word).trans (fiberNumber_apply (f z) word).symm
    change _=(-1/2:ℂ) • ((sourceRadialCoefficient i z:ℂ) • GaussCoframeForm.number f z)
    rw [number]
    simp only [smul_smul,←Finset.sum_smul,←Complex.ofReal_mul,←Complex.ofReal_sum]
    have generated:=sourceMetricMixed_row point i 0
    simp_rw [sourceSpinMixedTensor_number point] at generated
    rw [sourceLegendreLinearTensor_number] at generated
    change (∑j : Fin 6,sourceKineticCoefficient i j z*sourceNumberConnection z.1 j)=
      (-1/2:ℝ)*sourceRadialCoefficient i z at generated
    rw [generated,Complex.ofReal_mul]
    norm_num
  · have outside (g : QuantumTest) : g z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>inside (g.tsupport_subset h))
    exact (outside _).trans (outside _).symm

private theorem sourceMetric_scalar_commute (i j : Fin 6) (k : Fin 6) :
    Commute (sourcePreparedShiftLeft k) (sourceKineticMetric i j):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have number (g : QuantumTest) : sourceNumberScalarAction k g z=
      (sourceNumberConnection z.1 k:ℂ) • fiberNumber (g z):=rfl
  have connection (g : QuantumTest) : SourceCoframeCovariantAction.connectionAction k g z=
      SourceCoframeSpinConnection.connectionFiber k z (g z):=rfl
  change (-Complex.I) • sourceNumberScalarAction k (sourceKineticMetric i j f) z-
    SourceCoframeCovariantAction.connectionAction k (sourceKineticMetric i j f) z=
      (sourceKineticCoefficient i j z:ℂ) • sourcePreparedShiftLeft k f z
  rw [number,connection]
  change (-Complex.I) • ((sourceNumberConnection z.1 k:ℂ) •
      fiberNumber ((sourceKineticCoefficient i j z:ℂ) • f z))-
    SourceCoframeSpinConnection.connectionFiber k z ((sourceKineticCoefficient i j z:ℂ) • f z)=_
  rw [map_smul,map_smul]
  change _=(sourceKineticCoefficient i j z:ℂ) •
    ((-Complex.I) • ((sourceNumberConnection z.1 k:ℂ) • fiberNumber (f z))-
      SourceCoframeSpinConnection.connectionFiber k z (f z))
  simp only [smul_sub,smul_smul]
  module

theorem sourcePreparedShiftLeft_contract (j : Fin 6) :
    (∑i : Fin 6,sourcePreparedShiftLeft i*sourceKineticMetric i j)=
      (-1/2:ℂ) • (SourceCoframeCovariantAction.currentRow j-sourceNumberLinearAction j):=by
  have metric (i : Fin 6) : sourceKineticMetric i j=sourceKineticMetric j i:=by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change (sourceKineticCoefficient i j z:ℂ) • f z=(sourceKineticCoefficient j i z:ℂ) • f z
    rw [sourceKineticCoefficient_original,sourceKineticCoefficient_original,
      GaussCoframeKinetic.coefficient_symmetric]
  have left (i : Fin 6) : sourcePreparedShiftLeft i=
      sourcePreparedShiftRight i-(2*Complex.I) • sourceNumberScalarAction i:=by
    simp only [sourcePreparedShiftLeft,sourcePreparedShiftRight]
    module
  simp_rw [(sourceMetric_scalar_commute _ _ _).eq,metric,left]
  simp only [mul_sub,mul_smul_comm,Finset.sum_sub_distrib,←Finset.smul_sum,
    sourcePreparedShiftRight_contract,sourceNumberMetric_contract,smul_smul]
  rw [sourceLinearAction_generated]
  simp only [sourceNumberLinearAction]
  module

-- Both source momentum directions and the variable metric retain their original order.
def sourcePreparedShiftGram : SourceRadialEnd:=
  ∑i : Fin 6,∑j : Fin 6,sourcePreparedShiftLeft i*sourceKineticMetric i j*sourcePreparedShiftRight j

theorem sourcePreparedKinetic_ordered :
    sourcePreparedKinetic=GaussCoframeKinetic.kinetic+sourceOrderedCurrentAction-
      (1/2:ℂ) • (sourceNumberRadialReverse+sourceNumberRadialMomentum)+sourcePreparedShiftGram:=by
  have right (j : Fin 6) : sourceNoetherMomentumRight j=GaussCoframeCore.momentum j-sourcePreparedShiftRight j:=by
    simp only [sourceNoetherMomentumRight,sourcePreparedShiftRight]
    abel
  have left (i : Fin 6) : sourceNoetherMomentumLeft i=GaussCoframeCore.adjoint i-sourcePreparedShiftLeft i:=by
    simp only [sourceNoetherMomentumLeft,sourcePreparedShiftLeft]
    module
  have expansion : sourcePreparedKinetic=GaussCoframeKinetic.kinetic-
      (∑i : Fin 6,∑j : Fin 6,GaussCoframeCore.adjoint i*sourceKineticMetric i j*sourcePreparedShiftRight j)-
      (∑i : Fin 6,∑j : Fin 6,sourcePreparedShiftLeft i*sourceKineticMetric i j*GaussCoframeCore.momentum j)+
        sourcePreparedShiftGram:=by
    have kinetic : (∑i : Fin 6,∑j : Fin 6,GaussCoframeCore.adjoint i*sourceKineticMetric i j*GaussCoframeCore.momentum j)=
        GaussCoframeKinetic.kinetic:=by
      simp only [sourceKineticMetric_original,SourceCoframeCovariantAction.metricAction]
      rfl
    simp only [sourcePreparedKinetic,right,left,sub_mul,mul_sub,Finset.sum_sub_distrib,
      sourcePreparedShiftGram,kinetic]
    abel
  have crossRight : (∑i : Fin 6,∑j : Fin 6,GaussCoframeCore.adjoint i*sourceKineticMetric i j*sourcePreparedShiftRight j)=
      (-1/2:ℂ) • ∑i : Fin 6,GaussCoframeCore.adjoint i*sourceLinearAction i:=by
    simp only [mul_assoc,←Finset.mul_sum,sourcePreparedShiftRight_contract,mul_smul_comm,Finset.smul_sum]
  have crossLeft : (∑i : Fin 6,∑j : Fin 6,sourcePreparedShiftLeft i*sourceKineticMetric i j*GaussCoframeCore.momentum j)=
      (-1/2:ℂ) • ∑j : Fin 6,(SourceCoframeCovariantAction.currentRow j-sourceNumberLinearAction j)*GaussCoframeCore.momentum j:=by
    rw [Finset.sum_comm]
    simp only [←Finset.sum_mul,sourcePreparedShiftLeft_contract,smul_mul_assoc,Finset.smul_sum]
  rw [expansion,crossRight,crossLeft]
  have rotation (i : Fin 6) : sourceRotationLinearAction i=SourceCoframeCovariantAction.currentRow i:=by
    rw [sourceRotationLinearAction,sourceLinearAction_generated,add_sub_cancel_right]
  have numberReverse : (∑i : Fin 6,GaussCoframeCore.adjoint i*sourceNumberLinearAction i)=-sourceNumberRadialReverse:=by
    have commute (i : Fin 6) : sourceRadialAction i*GaussCoframeForm.number=GaussCoframeForm.number*sourceRadialAction i:=by
      apply LinearMap.ext
      intro f
      apply DFunLike.ext
      intro z
      apply PiLp.ext
      intro word
      change (sourceRadialCoefficient i z:ℂ)*GaussCoframeForm.number f z word=
        GaussCoframeForm.number (sourceRadialAction i f) z word
      rw [GaussCoframeForm.number_apply,GaussCoframeForm.number_apply]
      change (sourceRadialCoefficient i z:ℂ)*((word.card:ℂ)*f z word)=
        (word.card:ℂ)*((sourceRadialCoefficient i z:ℂ)*f z word)
      ring
    simp only [sourceNumberLinearAction,sourceNumberRadialReverse,commute,mul_smul_comm,
      mul_assoc,neg_smul,Finset.sum_neg_distrib,neg_neg]
  simp only [sourceOrderedCurrentAction,rotation,sourceLinearAction_generated,mul_add,
    sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,sourceNumberRadialMomentum,
    numberReverse,smul_add,smul_sub,smul_neg]
  module


attribute [local irreducible] sourceSpinMixedTensor sourceGaussVelocityInverse

private def sourceShiftSign (a : Fin 8) : ℝ:=if a=0 then -1 else 1

private def sourceShiftRightFiber (z : SourceCoordinateSlice) (i : Fin 6) : FiberEnd:=
  ((sourceNumberConnection z.1 i:ℂ)*Complex.I) • fiberNumber-SourceCoframeSpinConnection.connectionFiber i z

private def sourceShiftLeftFiber (z : SourceCoordinateSlice) (i : Fin 6) : FiberEnd:=
  (-((sourceNumberConnection z.1 i:ℂ)*Complex.I)) • fiberNumber-SourceCoframeSpinConnection.connectionFiber i z

private theorem sourceShiftRightFiber_emitted (field : Field289) (z : physicalChart) (i : Fin 6) :
    sourceShiftRightFiber z.val i=
      ∑a : Fin 8,sourceSpinMixedTensor z.val i a • quantized (sourceSpinEmittedBasis a):=by
  have original:=sourceGaussSpinShift_return field z i
  change sourceCanonicalSpinShift field z.val i=sourceShiftRightFiber z.val i at original
  rw [←original,sourceCanonicalSpinShift_emitted]

private theorem sourceShiftLeftFiber_emitted (field : Field289) (z : physicalChart) (i : Fin 6) :
    sourceShiftLeftFiber z.val i=
      ∑a : Fin 8,(sourceShiftSign a*sourceSpinMixedTensor z.val i a) • quantized (sourceSpinEmittedBasis a):=by
  have difference : sourceShiftLeftFiber z.val i=sourceShiftRightFiber z.val i-
      (2:ℝ) • (sourceSpinMixedTensor z.val i 0 • quantized (sourceSpinEmittedBasis 0)):=by
    rw [sourceSpinMixedTensor_number,sourceSpinIdentity_number]
    simp only [sourceShiftLeftFiber,sourceShiftRightFiber,smul_smul,
      ]
    module
  rw [difference,sourceShiftRightFiber_emitted field z i]
  rw [Fin.sum_univ_succ (n:=7),Fin.sum_univ_succ (n:=7)]
  simp only [sourceShiftSign,ite_true,Fin.succ_ne_zero,ite_false,one_mul,neg_one_mul]
  module

private theorem sourceSignedWeightedSquare {ι R : Type*} [Fintype ι] [Ring R] [Algebra ℝ R]
    (m : Matrix ι ι ℝ) (c : Matrix ι (Fin 8) ℝ) (eps : Fin 8→ℝ) (T : Fin 8→R) :
    (∑i : ι,∑j : ι,m i j •
      ((∑a : Fin 8,(eps a*c i a) • T a)*(∑b : Fin 8,c j b • T b)))=
      ∑a : Fin 8,∑b : Fin 8,(eps a*(c.transpose*m*c) a b) • (T a*T b):=by
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
      (∑a : Fin 8,(eps a*c i a) • T a)*(∑b : Fin 8,c j b • T b)=
        ∑a : Fin 8,∑b : Fin 8,(eps a*c i a*c j b) • (T a*T b):=by
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
  simp only [coefficient,Finset.mul_sum,Finset.sum_smul]
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

private def sourceSpinFiberEvaluation (v : FockFiber) : FiberEnd→ₗ[ℂ] FockFiber where
  toFun A:=A v
  map_add' _A _B:=rfl
  map_smul' _c _A:=rfl

private theorem sourcePreparedShiftGram_value (f : QuantumTest) (z : SourceCoordinateSlice) :
    sourcePreparedShiftGram f z=
      (∑i : Fin 6,∑j : Fin 6,sourceKineticCoefficient i j z •
        (sourceShiftLeftFiber z i*sourceShiftRightFiber z j)) (f z):=by
  change sourceSpinEvaluation f z (∑i : Fin 6,∑j : Fin 6,
      sourcePreparedShiftLeft i*sourceKineticMetric i j*sourcePreparedShiftRight j)=
    sourceSpinFiberEvaluation (f z) (∑i : Fin 6,∑j : Fin 6,
      sourceKineticCoefficient i j z • (sourceShiftLeftFiber z i*sourceShiftRightFiber z j))
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change sourcePreparedShiftLeft i (sourceKineticMetric i j (sourcePreparedShiftRight j f)) z=
    (sourceKineticCoefficient i j z • (sourceShiftLeftFiber z i*sourceShiftRightFiber z j)) (f z)
  have left (g : QuantumTest) : sourcePreparedShiftLeft i g z=sourceShiftLeftFiber z i (g z):=by
    change (-Complex.I) • ((sourceNumberConnection z.1 i:ℂ) • fiberNumber (g z))-
      SourceCoframeSpinConnection.connectionFiber i z (g z)=_
    simp only [sourceShiftLeftFiber,sub_apply,smul_apply,smul_smul]
    congr 1
    module
  have right : sourcePreparedShiftRight j f z=sourceShiftRightFiber z j (f z):=by
    change Complex.I • ((sourceNumberConnection z.1 j:ℂ) • fiberNumber (f z))-
      SourceCoframeSpinConnection.connectionFiber j z (f z)=_
    simp only [sourceShiftRightFiber,sub_apply,smul_apply,smul_smul]
    congr 1
    module
  rw [left]
  change sourceShiftLeftFiber z i ((sourceKineticCoefficient i j z:ℂ) • sourcePreparedShiftRight j f z)=_
  rw [right,map_smul]
  change _=sourceKineticCoefficient i j z • (sourceShiftLeftFiber z i (sourceShiftRightFiber z j (f z)))
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _).symm

private theorem sourceSignedSpinGram_generated (_field : Field289) (z : physicalChart) (eps : Fin 8→ℝ) :
    (∑i : Fin 6,∑j : Fin 6,sourceKineticCoefficient i j z.val •
      ((∑a : Fin 8,(eps a*sourceSpinMixedTensor z.val i a) • quantized (sourceSpinEmittedBasis a))*
        (∑b : Fin 8,sourceSpinMixedTensor z.val j b • quantized (sourceSpinEmittedBasis b))))=
      ∑a : Fin 8,(eps a*(lapse/(4*GaussNativeEnergy.volume z.val))*sourceMixedGramPrice a) •
        (quantized (sourceSpinEmittedBasis a)*quantized (sourceSpinEmittedBasis a)):=by
  change (∑i : Fin 6,∑j : Fin 6,((1/2:ℝ) • sourceGaussVelocityInverse z.val) i j •
      ((∑a : Fin 8,(eps a*sourceSpinMixedTensor z.val i a) • quantized (sourceSpinEmittedBasis a))*
        (∑b : Fin 8,sourceSpinMixedTensor z.val j b • quantized (sourceSpinEmittedBasis b))))=_
  rw [sourceSignedWeightedSquare (R:=FiberEnd),sourceMixedGram_generated]
  have zeroReal (T : FiberEnd) : (0:ℝ) • T=0:=zero_smul ℝ T
  simp only [Matrix.smul_apply,Matrix.diagonal_apply,smul_eq_mul,mul_ite,mul_zero,ite_smul,
    zeroReal,Finset.sum_ite_eq,Finset.mem_univ,ite_true,mul_assoc]

theorem sourcePreparedShiftGram_source (field : Field289) (f : QuantumTest) (z : physicalChart) :
    sourcePreparedShiftGram f z.val=
      sourceCanonicalSpinHamiltonian field z.val (f z.val)+sourceGaussSpinConstant field z.val (f z.val)+
        ((3*lapse/(8*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber (fiberNumber (f z.val)):=by
  rw [sourcePreparedShiftGram_value]
  have signed:=sourceSignedSpinGram_generated field z sourceShiftSign
  have ordinary:=sourceSignedSpinGram_generated field z (fun _=>1)
  simp only [one_mul] at ordinary
  have square : (∑i : Fin 6,∑j : Fin 6,sourceKineticCoefficient i j z.val •
      (sourceCanonicalSpinShift field z.val i*sourceCanonicalSpinShift field z.val j))=
      sourceCanonicalSpinHamiltonian field z.val+sourceGaussSpinConstant field z.val:=by
    simp only [sourceCanonicalSpinHamiltonian,sourceKineticCoefficient,sub_add_cancel]
  simp_rw [sourceCanonicalSpinShift_emitted field z] at square
  rw [ordinary] at square
  have difference : (∑a : Fin 8,(sourceShiftSign a*(lapse/(4*GaussNativeEnergy.volume z.val))*sourceMixedGramPrice a) •
      (quantized (sourceSpinEmittedBasis a)*quantized (sourceSpinEmittedBasis a)))=
    (∑a : Fin 8,((lapse/(4*GaussNativeEnergy.volume z.val))*sourceMixedGramPrice a) •
      (quantized (sourceSpinEmittedBasis a)*quantized (sourceSpinEmittedBasis a)))+
        ((3*lapse/(8*GaussNativeEnergy.volume z.val):ℝ):ℂ) • (fiberNumber*fiberNumber):=by
    rw [Fin.sum_univ_succ (n:=7),Fin.sum_univ_succ (n:=7)]
    have realAction (r : ℝ) (T : FiberEnd) : r • T=(r:ℂ) • T:=
      RCLike.real_smul_eq_coe_smul (K:=ℂ) r T
    simp only [sourceShiftSign,ite_true,Fin.succ_ne_zero,ite_false,one_mul,neg_one_mul,
      sourceMixedGramPrice,Matrix.cons_val_zero,sourceSpinIdentity_number,
      smul_mul_assoc,mul_smul_comm,smul_smul,Complex.I_mul_I,
      realAction,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_div,
      Complex.ofReal_ofNat]
    module
  simp_rw [sourceShiftLeftFiber_emitted field z,sourceShiftRightFiber_emitted field z]
  rw [signed,difference,square]
  simp only [add_apply,smul_apply,mul_apply_eq_comp]

theorem sourcePreparedSpinLoaded_coframe (field : Field289) (f : QuantumTest) (z : physicalChart) :
    sourcePreparedKinetic f z.val-sourceGaussSpinConstant field z.val (f z.val)=
      (GaussCoframeKinetic.kinetic+GaussCoframeForm.currentAction+
        (∑b : Fin 7,GaussCoframeForm.spinSquare b)+GaussCoframeForm.numberShift) f z.val:=by
  rw [sourcePreparedKinetic_ordered,sourceOrderedCurrentAction_original]
  have spin:=sourcePreparedShiftGram_source field f z
  have number:=sourceNumberRadial_original_number f z
  change (1/2:ℂ) • ((sourceNumberRadialReverse+sourceNumberRadialMomentum) f z.val)+
    GaussCoframeForm.numberShift f z.val=
      ((3*lapse/(8*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber (fiberNumber (f z.val)) at number
  have oldSpin:=sourceCanonicalSpinHamiltonian_original_action field f z
  change (GaussCoframeKinetic.kinetic f z.val+GaussCoframeForm.currentAction f z.val-
    (1/2:ℂ) • ((sourceNumberRadialReverse+sourceNumberRadialMomentum) f z.val)+sourcePreparedShiftGram f z.val)-
      sourceGaussSpinConstant field z.val (f z.val)=_
  rw [spin,oldSpin]
  change _=GaussCoframeKinetic.kinetic f z.val+GaussCoframeForm.currentAction f z.val+
    (∑b : Fin 7,GaussCoframeForm.spinSquare b) f z.val+GaussCoframeForm.numberShift f z.val
  have numberReturn : -(1/2:ℂ) • ((sourceNumberRadialReverse+sourceNumberRadialMomentum) f z.val)+
      ((3*lapse/(8*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber (fiberNumber (f z.val))=
        GaussCoframeForm.numberShift f z.val:=by
    rw [←number]
    module
  rw [show (GaussCoframeKinetic.kinetic f z.val+GaussCoframeForm.currentAction f z.val-
      (1/2:ℂ) • ((sourceNumberRadialReverse+sourceNumberRadialMomentum) f z.val)+
        ((∑b : Fin 7,GaussCoframeForm.spinSquare b) f z.val+sourceGaussSpinConstant field z.val (f z.val)+
          ((3*lapse/(8*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber (fiberNumber (f z.val))))-
            sourceGaussSpinConstant field z.val (f z.val)=
      GaussCoframeKinetic.kinetic f z.val+GaussCoframeForm.currentAction f z.val+
        (∑b : Fin 7,GaussCoframeForm.spinSquare b) f z.val+
          (-(1/2:ℂ) • ((sourceNumberRadialReverse+sourceNumberRadialMomentum) f z.val)+
            ((3*lapse/(8*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber (fiberNumber (f z.val))) from by module]
  rw [numberReturn]

theorem sourcePreparedSpinLoaded_fullcoframe (field : Field289) (f : QuantumTest) (z : physicalChart) :
    sourcePreparedKinetic f z.val-sourceGaussSpinConstant field z.val (f z.val)+
      ((3*(sourceGaussCoframe z.val).det:ℝ):ℂ) • f z.val=GaussCoframeForm.coframeAction f z.val:=by
  rw [sourcePreparedSpinLoaded_coframe,sourceGaussCoframe_determinant]
  change _=(GaussCoframeKinetic.kinetic+GaussCoframeForm.currentAction+
    (∑b : Fin 7,GaussCoframeForm.spinSquare b)+GaussCoframeForm.numberShift) f z.val+
      (GaussCoframeForm.volumePotential z.val:ℂ) • f z.val
  simp only [GaussCoframeForm.volumePotential,GaussNativeEnergy.source_time_generated,Matrix.cons_val_zero]
  congr 1
  push_cast
  module

end LowEnergy.PreparationVacuumNumberRadialReturn
