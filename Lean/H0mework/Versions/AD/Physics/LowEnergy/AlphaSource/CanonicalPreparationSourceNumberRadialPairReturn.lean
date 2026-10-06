import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRadialCoefficientJets

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNumberRadialReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumLegendreCurrentReturn PreparationVacuumGaussMeasureReturn
open PreparationVacuumSpinGaussContraction
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussQuantumMultiplier
open Stage9C.Material.SpinPair
open scoped Topology ContDiff BigOperators Matrix
abbrev SourceRadialEnd:=QuantumTest→ₗ[ℂ] QuantumTest

def sourceRadialDerivativeCoefficient (i : Fin 6) (z : SourceCoordinateSlice) : ℝ:=
  -(lapse/(4*GaussNativeEnergy.volume z))*(1-2*z.1 i*sourceNumberConnection z.1 i)

theorem sourceRadialDerivativeCoefficient_smooth (i : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceRadialDerivativeCoefficient i) z.val:=by
  have inverse : ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice=>-(lapse/(4*GaussNativeEnergy.volume w))) z.val:=
    (contDiffAt_const.div (contDiffAt_const.mul GaussNativeEnergy.volume_smooth.contDiffAt)
      (mul_ne_zero (by norm_num) (GaussNativeEnergy.volume_pos z).ne')).neg
  apply inverse.mul
  exact contDiffAt_const.sub
    ((contDiffAt_const.mul (by fun_prop)).mul (sourceNumberConnection_smooth i z))

def sourceRadialDerivativeAction (i : Fin 6) : SourceRadialEnd:=
  GaussNativeForm.multiply (sourceRadialDerivativeCoefficient i) (sourceRadialDerivativeCoefficient_smooth i)

theorem sourceRadialMomentum_derivative (i : Fin 6) :
    GaussCoframeCore.momentum i*sourceRadialAction i=
      sourceRadialAction i*GaussCoframeCore.momentum i-Complex.I • sourceRadialDerivativeAction i:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases inside : z∈physicalChart
  · have scalar:=Complex.ofRealCLM.hasFDerivAt.comp z
      ((sourceRadialCoefficient_smooth i ⟨z,inside⟩).differentiableAt (by simp)).hasFDerivAt
    change HasFDerivAt (fun w : SourceCoordinateSlice=>(sourceRadialCoefficient i w:ℂ)) _ z at scalar
    have value : (sourceRadialAction i f : SourceCoordinateSlice→FockFiber)=
        fun w=>(sourceRadialCoefficient i w:ℂ) • f w:=rfl
    change (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)
        (sourceRadialAction i f) z=
      (sourceRadialCoefficient i z:ℂ) • ((-Complex.I) •
        GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z)-
          Complex.I • ((sourceRadialDerivativeCoefficient i z:ℂ) • f z)
    rw [GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply,value,
      fderiv_fun_smul scalar.differentiableAt (f.contDiff.differentiable (by simp)).differentiableAt,scalar.fderiv]
    change (-Complex.I) • ((sourceRadialCoefficient i z:ℂ) •
      fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
        (fderiv ℝ (sourceRadialCoefficient i) z (GaussCoframeCore.coframeDirection i):ℂ) • f z)=_
    rw [sourceRadialCoefficient_derivative ⟨z,inside⟩ i i]
    simp only [ite_true]
    change (-Complex.I) • ((sourceRadialCoefficient i z:ℂ) •
      fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+(sourceRadialDerivativeCoefficient i z:ℂ) • f z)=_
    simp only [smul_add,smul_smul]
    module
  · have outside (g : QuantumTest) : g z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>inside (g.tsupport_subset h))
    exact (outside _).trans (outside _).symm

theorem sourceNumberMomentum_commute (i : Fin 6) :
    Commute GaussCoframeForm.number (GaussCoframeCore.momentum i):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let T:=fiberNumber.restrictScalars ℝ
  have value : (GaussCoframeForm.number f : SourceCoordinateSlice→FockFiber)=T ∘ f:=by
    funext w
    apply PiLp.ext
    intro word
    exact (GaussCoframeForm.number_apply f w word).trans (fiberNumber_apply (f w) word).symm
  have actual:=T.hasFDerivAt.comp z (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have number (g : QuantumTest) : GaussCoframeForm.number g z=fiberNumber (g z):=by
    apply PiLp.ext
    intro word
    exact (GaussCoframeForm.number_apply g z word).trans (fiberNumber_apply (g z) word).symm
  change GaussCoframeForm.number (GaussCoframeCore.momentum i f) z=
    (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (GaussCoframeForm.number f) z
  rw [number,GaussCoframeCore.derivative_apply,value,actual.fderiv]
  change fiberNumber ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z)=_
  rw [GaussCoframeCore.derivative_apply,map_smul]
  rfl

private theorem sourceNumberScalar_commute (i : Fin 6) : Commute GaussCoframeForm.number (sourceRadialAction i):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change GaussCoframeForm.number (sourceRadialAction i f) z word=
    (sourceRadialCoefficient i z:ℂ)*GaussCoframeForm.number f z word
  rw [GaussCoframeForm.number_apply,GaussCoframeForm.number_apply]
  change (word.card:ℂ)*((sourceRadialCoefficient i z:ℂ)*f z word)=_
  ring

-- This is the actual reverse order for the original prepared Gram pairing.
def sourceNumberRadialReverse : SourceRadialEnd:=
  ∑i : Fin 6,(-Complex.I) •
    (GaussCoframeCore.adjoint i*GaussCoframeForm.number*sourceRadialAction i)

theorem sourceNumberRadial_pair (f g : QuantumTest) :
    sourcePair f (sourceNumberRadialMomentum g)=sourcePair (sourceNumberRadialReverse f) g:=by
  simp only [sourceNumberRadialMomentum,sourceNumberLinearAction,sourceNumberRadialReverse,
    smul_mul_assoc,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_sum,inner_sum,sum_inner,map_smul,inner_smul_right,inner_smul_left,
    map_neg,Complex.conj_I,neg_neg]
  apply Finset.sum_congr rfl
  intro i _
  change Complex.I*sourcePair f (sourceRadialAction i (GaussCoframeForm.number (GaussCoframeCore.momentum i g)))=
    Complex.I*sourcePair (GaussCoframeCore.adjoint i (GaussCoframeForm.number (sourceRadialAction i f))) g
  rw [show sourcePair f (sourceRadialAction i (GaussCoframeForm.number (GaussCoframeCore.momentum i g)))=
      sourcePair (sourceRadialAction i f) (GaussCoframeForm.number (GaussCoframeCore.momentum i g)) from
        GaussNativeForm.multiply_pair _ _ _ _,GaussCoframeForm.number_pair,GaussCoframeCore.momentum_pair]

set_option synthInstance.maxHeartbeats 120000 in
private theorem sourceRadialReverse_contact (i : Fin 6) :
    (-Complex.I) • (GaussCoframeCore.adjoint i*GaussCoframeForm.number*sourceRadialAction i)+
      sourceNumberLinearAction i*GaussCoframeCore.momentum i=
        -(sourceRadialDerivativeAction i*GaussCoframeForm.number)-
          sourceDensityDrift i*sourceRadialAction i*GaussCoframeForm.number:=by
  let P:=GaussCoframeCore.momentum i
  let N:=GaussCoframeForm.number
  let A:=sourceRadialAction i
  let D:=sourceDensityDrift i
  let J:=sourceRadialDerivativeAction i
  have NP : N*P=P*N:=(sourceNumberMomentum_commute i).eq
  have NA : N*A=A*N:=(sourceNumberScalar_commute i).eq
  have PA : P*A=A*P-Complex.I • J:=sourceRadialMomentum_derivative i
  rw [sourceCoframeAdjoint_generated,sourceNumberLinearAction]
  change (-Complex.I) • ((P-Complex.I • D)*N*A)+(Complex.I • (A*N))*P=-(J*N)-D*A*N
  rw [mul_assoc _ N A,NA,←mul_assoc _ A N,sub_mul,PA]
  simp only [sub_mul,smul_mul_assoc,smul_sub,smul_smul,neg_mul,Complex.I_mul_I]
  rw [mul_assoc A P N,←NP,←mul_assoc A N P]
  module

private theorem sourceRadialContact_value (i : Fin 6) (f : QuantumTest)
    (z : SourceCoordinateSlice) (word : Occupation) :
    (-(sourceRadialDerivativeAction i*GaussCoframeForm.number)-
      sourceDensityDrift i*sourceRadialAction i*GaussCoframeForm.number) f z word=
      -(sourceRadialDerivativeCoefficient i z:ℂ)*(word.card:ℂ)*f z word-
        (2*sourceNumberConnection z.1 i:ℂ)*(word.card+2:ℂ)*(sourceRadialCoefficient i z:ℂ)*
          (word.card:ℂ)*f z word:=by
  change -sourceRadialDerivativeAction i (GaussCoframeForm.number f) z word-
    sourceDensityDrift i (sourceRadialAction i (GaussCoframeForm.number f)) z word=_
  rw [sourceDensityDrift_apply]
  simp only [sourceRadialDerivativeAction,sourceRadialAction,GaussNativeForm.multiply_apply,PiLp.smul_apply,smul_eq_mul]
  change -((sourceRadialDerivativeCoefficient i z:ℂ)*GaussCoframeForm.number f z word)-
    (2*(word.card+2:ℝ)*sourceNumberConnection z.1 i:ℂ)*
      ((sourceRadialCoefficient i z:ℂ)*GaussCoframeForm.number f z word)=_
  rw [GaussCoframeForm.number_apply]
  push_cast
  ring

private def sourceRadialEvaluation (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    SourceRadialEnd→ₗ[ℂ] ℂ where
  toFun A:=A f z word
  map_add' _A _B:=rfl
  map_smul' _c _A:=rfl

theorem sourceNumberRadial_contact (f : QuantumTest) (z : physicalChart) :
    (sourceNumberRadialReverse+sourceNumberRadialMomentum) f z.val=
      ((3*lapse/(4*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber (fiberNumber (f z.val))+
        ((9*lapse/(4*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber (f z.val):=by
  rw [show sourceNumberRadialReverse+sourceNumberRadialMomentum=
      ∑i : Fin 6,((-Complex.I) • (GaussCoframeCore.adjoint i*GaussCoframeForm.number*sourceRadialAction i)+
        sourceNumberLinearAction i*GaussCoframeCore.momentum i) from by
          simp only [sourceNumberRadialReverse,sourceNumberRadialMomentum,Finset.sum_add_distrib],
    show (∑i : Fin 6,((-Complex.I) • (GaussCoframeCore.adjoint i*GaussCoframeForm.number*sourceRadialAction i)+
        sourceNumberLinearAction i*GaussCoframeCore.momentum i))=
      ∑i : Fin 6,(-(sourceRadialDerivativeAction i*GaussCoframeForm.number)-
        sourceDensityDrift i*sourceRadialAction i*GaussCoframeForm.number) from
          Finset.sum_congr rfl (fun i _=>sourceRadialReverse_contact i)]
  apply PiLp.ext
  intro word
  change sourceRadialEvaluation f z.val word
    (∑i : Fin 6,(-(sourceRadialDerivativeAction i*GaussCoframeForm.number)-
      sourceDensityDrift i*sourceRadialAction i*GaussCoframeForm.number))=_
  rw [map_sum]
  change (∑i : Fin 6,(-(sourceRadialDerivativeAction i*GaussCoframeForm.number)-
      sourceDensityDrift i*sourceRadialAction i*GaussCoframeForm.number) f z.val word)=_
  simp only [sourceRadialContact_value,PiLp.add_apply,PiLp.smul_apply,fiberNumber_apply,smul_eq_mul,Finset.sum_sub_distrib]
  have derivative : (∑i : Fin 6,sourceRadialDerivativeCoefficient i z.val)=
      -3*lapse/(4*GaussNativeEnergy.volume z.val):=by
    have result:=sourceRadialCoefficient_divergence z
    simpa only [sourceRadialCoefficient_derivative,ite_true,sourceRadialDerivativeCoefficient] using result
  have density:=sourceRadialCoefficient_density z
  have derivativeComplex:=congrArg Complex.ofReal derivative
  have densityComplex:=congrArg Complex.ofReal density
  push_cast at derivativeComplex densityComplex
  -- Sum scalar coefficients before reading the original all-occupation Number action.
  have collect : (∑i : Fin 6,(2*sourceNumberConnection z.val.1 i:ℂ)*(word.card+2:ℂ)*
      (sourceRadialCoefficient i z.val:ℂ)*(word.card:ℂ)*f z.val word)=
      (2:ℂ)*(word.card+2:ℂ)*(word.card:ℂ)*f z.val word*
        ∑i : Fin 6,(sourceRadialCoefficient i z.val:ℂ)*(sourceNumberConnection z.val.1 i:ℂ):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [collect,densityComplex]
  simp only [←Finset.sum_mul]
  rw [Finset.sum_neg_distrib,derivativeComplex]
  push_cast
  ring

theorem sourceNumberRadial_original_number (f : QuantumTest) (z : physicalChart) :
    ((1/2:ℂ) • (sourceNumberRadialReverse+sourceNumberRadialMomentum)+GaussCoframeForm.numberShift) f z.val=
      ((3*lapse/(8*GaussNativeEnergy.volume z.val):ℝ):ℂ) • fiberNumber (fiberNumber (f z.val)):=by
  change (1/2:ℂ) • ((sourceNumberRadialReverse+sourceNumberRadialMomentum) f z.val)+
    GaussCoframeForm.numberShift f z.val=_
  rw [sourceNumberRadial_contact]
  apply PiLp.ext
  intro word
  have numberShift : GaussCoframeForm.numberShift f z.val word=(1/2:ℂ)*
      (GaussCoframeForm.number
        (GaussNativeForm.multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth f) z.val word+
      (GaussNativeForm.multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth
        (GaussCoframeForm.number f)) z.val word):=rfl
  simp only [PiLp.add_apply,PiLp.smul_apply,fiberNumber_apply,smul_eq_mul]
  rw [numberShift]
  rw [GaussCoframeForm.number_apply]
  simp only [GaussNativeForm.multiply_apply,PiLp.smul_apply,smul_eq_mul]
  rw [GaussCoframeForm.number_apply]
  simp only [GaussCoframeForm.numberCoefficient,GaussCoframeForm.inverseVolume,
    GaussNativeEnergy.source_time_generated,Matrix.cons_val_zero]
  push_cast
  ring

end LowEnergy.PreparationVacuumNumberRadialReturn
