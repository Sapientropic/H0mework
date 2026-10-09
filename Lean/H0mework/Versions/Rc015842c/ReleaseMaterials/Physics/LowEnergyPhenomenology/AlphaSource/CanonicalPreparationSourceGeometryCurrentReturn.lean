import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSpinCarContraction

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
open GaussHistoryHilbert GaussQuantumMultiplier
open scoped Topology BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] sourceSpinCoefficientMatrix sourceFlatSpinCoefficient sourceFlatLorentzMatrix
attribute [local irreducible] sourceGaussCoframe sourceLorentzInverse

-- This is the original BF boundary first variation, before scalar or spin contractions.
def sourceGeometrySpinCoefficient (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) : Fin 8→ℝ:=
  -(((sourceSpinCoefficientMatrix z).transpose*sourceLorentzInverse (sourceGaussCoframe z)).mulVec
    (sourceLorentzGeometryLoad (sourceGaussCoframe z) de))

def sourceGeometrySpinNumerator (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) : Fin 8→ℝ:=
  -((sourceFlatSpinCoefficient.transpose*sourceFlatLorentzMatrix).mulVec
    ((sourceCoframeSlots (sourceGaussCoframe z)).mulVec
      (sourceLorentzGeometryLoad (sourceGaussCoframe z) de)))

theorem sourceGeometrySpinCoefficient_generated (z : physicalChart)
    (de : Fin 4→LorentzianCoframe) :
    sourceGeometrySpinCoefficient z.val de=
      (GaussNativeEnergy.volume z.val)⁻¹ • sourceGeometrySpinNumerator z.val de:=by
  let E:=sourceCoframeSlots (sourceGaussCoframe z.val)
  let Q:=sourceCoframeSlots (sourceGaussCoframe z.val)⁻¹
  have inverse : E*Q=1:=
    (sourceCoframeSlots_inverse _ (sourceGaussCoframe_nondegenerate z)).1
  have transposeInverse : Q.transpose*E.transpose=1:=by
    rw [←Matrix.transpose_mul,inverse,Matrix.transpose_one]
  rw [sourceGeometrySpinCoefficient,sourceSpinCoefficientMatrix_generated,
    sourceLorentzInverse_slots,Matrix.transpose_smul,Matrix.transpose_mul]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.smul_mulVec]
  have collapse : sourceFlatSpinCoefficient.transpose*Q.transpose*
      (E.transpose*sourceFlatLorentzMatrix*E)=sourceFlatSpinCoefficient.transpose*sourceFlatLorentzMatrix*E:=by
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc Q.transpose E.transpose,transposeInverse,Matrix.one_mul]
  change -( _ • ((sourceFlatSpinCoefficient.transpose*Q.transpose*
      (E.transpose*sourceFlatLorentzMatrix*E)).mulVec
        (sourceLorentzGeometryLoad (sourceGaussCoframe z.val) de)))=_
  rw [collapse,←Matrix.mulVec_mulVec]
  simp only [←smul_neg]
  change _ • sourceGeometrySpinNumerator z.val de=_
  congr 1
  rw [sourceGaussCoframe_determinant,GaussNativeEnergy.source_time_generated]
  simp only [Matrix.cons_val_zero]
  have timeNonzero : lapse≠0:=lapse_pos.ne'
  have spaceNonzero : GaussNativeEnergy.volume z.val≠0:=(GaussNativeEnergy.volume_pos z).ne'
  field_simp

private theorem sourceMixedCoefficient {ι α R : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [AddCommGroup R] [Module ℝ R]
    (m : Matrix ι ι ℝ) (symmetric : m.transpose=m)
    (c : Matrix ι α ℝ) (J : ι→ℝ) (T : α→R) :
    (∑i : ι,∑j : ι,(-(1/2:ℝ)*m i j) •
      (J i • (∑a : α,c j a • T a)+J j • (∑a : α,c i a • T a)))=
      ∑a : α,-((c.transpose*m).mulVec J a) • T a:=by
  classical
  let F : ι→R:=fun i=>∑a : α,c i a • T a
  have entry (i j : ι) : m j i=m i j:=congrFun (congrFun symmetric i) j
  have exchange : (∑i : ι,∑j : ι,m i j • (J i • F j))=
      ∑i : ι,∑j : ι,m i j • (J j • F i):=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [entry]
  have coefficient (a : α) : (c.transpose*m).mulVec J a=
      ∑i : ι,∑j : ι,c i a*m i j*J j:=by
    simp only [Matrix.mulVec,dotProduct,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
  have reverse : (∑i : ι,∑j : ι,m i j • (J j • F i))=
      ∑a : α,((c.transpose*m).mulVec J a) • T a:=by
    have shuffle (g : ι→ι→α→R) :
        (∑i : ι,∑j : ι,∑a : α,g i j a)=(∑a : α,∑i : ι,∑j : ι,g i j a):=by
      simpa only [Fintype.sum_prod_type] using
        (Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)
          (f:=fun ij : ι×ι=>fun a : α=>g ij.1 ij.2 a))
    simp only [F,Finset.smul_sum,smul_smul]
    rw [shuffle]
    simp only [coefficient,Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  have half : (∑i : ι,∑j : ι,(-(1/2:ℝ)*m i j) • (J i • F j+J j • F i))=
      (-(1/2:ℝ)) • ((∑i : ι,∑j : ι,m i j • (J i • F j))+
        (∑i : ι,∑j : ι,m i j • (J j • F i))):=by
    simp only [smul_add,Finset.sum_add_distrib,Finset.smul_sum,smul_smul,mul_assoc]
  change (∑i : ι,∑j : ι,(-(1/2:ℝ)*m i j) • (J i • F j+J j • F i))=_
  rw [half,exchange,reverse]
  simp only [Finset.smul_sum,smul_add,smul_smul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [←add_smul]
  congr 1
  ring

theorem sourceGaussMixedSpin_emitted (f : Field289) (z : physicalChart)
    (de : Fin 4→LorentzianCoframe) :
    sourceGaussMixedSpin f z.val de=
      ∑a : Fin 8,(sourceGeometrySpinCoefficient z.val de a:ℂ) •
        quantized (sourceSpinEmittedBasis a):=by
  have realAction (r : ℝ) (A : FiberEnd) : r • A=(r:ℂ) • A:=
    RCLike.real_smul_eq_coe_smul (K:=ℂ) r A
  have emitter (i : LorentzIndex) : sourceSpinFiber (f,z.val) (sourceState z.val) i=
      ∑a : Fin 8,sourceSpinCoefficientMatrix z.val i a • quantized (sourceSpinEmittedBasis a):=by
    rw [sourceSpinFiber_emitted]
    apply Finset.sum_congr rfl
    intro a _
    simp only [sourceSpinCoefficientMatrix,Matrix.of_apply]
    exact (realAction _ _).symm
  have realWeight (i j : LorentzIndex) : sourcePotentialWeight z.val i j=
      ((-(1/2:ℝ)*sourceLorentzInverse (sourceGaussCoframe z.val) i j:ℝ):ℂ):=by
    simp [sourcePotentialWeight,Complex.ofReal_mul,Complex.ofReal_neg]
  simp only [sourceGaussMixedSpin,realWeight,emitter,←realAction,
    sourceGeometrySpinCoefficient,Pi.neg_apply]
  exact sourceMixedCoefficient (sourceLorentzInverse (sourceGaussCoframe z.val))
    (sourceLorentzInverse_symmetric _ (sourceGaussCoframe_nondegenerate z))
    (sourceSpinCoefficientMatrix z.val) (sourceLorentzGeometryLoad (sourceGaussCoframe z.val) de)
    (fun a=>quantized (sourceSpinEmittedBasis a))

theorem sourceGaussOrderedConstant_emitted (f : Field289) (z : physicalChart)
    (de : Fin 4→LorentzianCoframe) :
    sourceGaussOrderedConstant f z.val de=
      sourceGaussGeometryConstant z.val de • (1:FiberEnd)+
        (∑a : Fin 8,(sourceGeometrySpinCoefficient z.val de a:ℂ) •
          quantized (sourceSpinEmittedBasis a))+
          ((3*lapse/(4*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber+
            ((-lapse/(2*GaussNativeEnergy.volume z.val):ℝ):ℂ) • sourceEightNormalFiber:=by
  rw [sourceGaussOrderedConstant_normal,sourceGaussMixedSpin_emitted]

end LowEnergy.PreparationVacuumSpinCarReturn
