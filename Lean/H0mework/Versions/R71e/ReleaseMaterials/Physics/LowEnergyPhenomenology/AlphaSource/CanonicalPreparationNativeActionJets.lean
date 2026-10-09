import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNativeStateContact

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeLocalWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumScalarChart SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceQuantumConfigurationHilbert GaussHistoryHilbert GaussNativeMatter GaussQuantumMultiplier
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumNoetherChart
open Filter Set
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

def contactLinear (n : Fin 9) (theta : ℝ) : ActionState→ₗ[ℝ] ActionState where
  toFun:=stateContact n theta
  map_add' a b:=by
    apply Prod.ext
    · change (theta • nativeFrameGenerator n)*(a.1+b.1)=
        (theta • nativeFrameGenerator n)*a.1+(theta • nativeFrameGenerator n)*b.1
      exact mul_add _ _ _
    apply Prod.ext
    · funext mu
      change theta • (nativeMatterGenerator n*(a.2.1 mu+b.2.1 mu)-(a.2.1 mu+b.2.1 mu)*nativeMatterGenerator n)=
        theta • (nativeMatterGenerator n*a.2.1 mu-a.2.1 mu*nativeMatterGenerator n)+
          theta • (nativeMatterGenerator n*b.2.1 mu-b.2.1 mu*nativeMatterGenerator n)
      simp only [mul_add,add_mul,smul_add,smul_sub]
      abel
    · change theta • (nativeMatterGenerator n*(a.2.2+b.2.2)-(a.2.2+b.2.2)*nativeMatterGenerator n)=
        theta • (nativeMatterGenerator n*a.2.2-a.2.2*nativeMatterGenerator n)+
          theta • (nativeMatterGenerator n*b.2.2-b.2.2*nativeMatterGenerator n)
      simp only [mul_add,add_mul,smul_add,smul_sub]
      abel
  map_smul' r a:=by
    apply Prod.ext
    · change (theta • nativeFrameGenerator n)*(r • a.1)=r • ((theta • nativeFrameGenerator n)*a.1)
      exact mul_smul_comm _ _ _
    apply Prod.ext
    · funext mu
      change theta • (nativeMatterGenerator n*(r • a.2.1 mu)-(r • a.2.1 mu)*nativeMatterGenerator n)=
        r • (theta • (nativeMatterGenerator n*a.2.1 mu-a.2.1 mu*nativeMatterGenerator n))
      simp only [mul_smul_comm,smul_mul_assoc,←smul_sub,smul_comm theta r]
    · change theta • (nativeMatterGenerator n*(r • a.2.2)-(r • a.2.2)*nativeMatterGenerator n)=
        r • (theta • (nativeMatterGenerator n*a.2.2-a.2.2*nativeMatterGenerator n))
      simp only [mul_smul_comm,smul_mul_assoc,←smul_sub,smul_comm theta r]

 theorem stateVariation_smooth (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ) :
    ContDiff ℝ ∞ (stateVariation n theta derivative) :=by
  have shape (s : ActionState) : stateVariation n theta derivative s=
      stateVariation n theta derivative 0+contactLinear n theta s:=by
    change stateVariation n theta derivative s=stateVariation n theta derivative 0+stateContact n theta s
    simpa only [zero_add,one_smul] using
      stateVariation_affine n theta derivative 0 s 1
  have actual : ContDiff ℝ ∞ (fun x : ActionState=>stateVariation n theta derivative 0+
      (contactLinear n theta).toContinuousLinearMap x):=
    contDiff_const.add (contactLinear n theta).toContinuousLinearMap.contDiff
  have same : stateVariation n theta derivative=(fun x : ActionState=>
      stateVariation n theta derivative 0+(contactLinear n theta).toContinuousLinearMap x):=funext shape
  rw [same]
  exact actual

/-- Differentiation is along the original field-dependent local transformation. -/
def nativeFirst (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (s : ActionState) : FullMatrix:=
  symbolFirst p s (stateVariation n theta derivative s)

def nativeMixed (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (s : ActionState) : FullMatrix:=
  symbolSecond p s (stateVariation n theta derivative s) (fieldDirection force)+
    symbolFirst p s (stateContact n theta (fieldDirection force))

 theorem nativeFirst_smooth (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    ContDiffAt ℝ ∞ (nativeFirst n theta derivative p) s :=
  ((sourceSymbol_smooth p s valid).fderiv_right (m:=∞) (by simp)).clm_apply
    (stateVariation_smooth n theta derivative).contDiffAt

 theorem nativeFirst_generated (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>sourceSymbol p (sourceState z.val+
      r • stateVariation n theta derivative (sourceState z.val)))
      (nativeFirst n theta derivative p (sourceState z.val)) 0 :=
  symbol_first_generated p (sourceState z.val) (stateVariation n theta derivative (sourceState z.val))
    ⟨coframe_nondegenerate z,temporal_noncharacteristic z⟩

 theorem nativeMixed_generated (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>nativeFirst n theta derivative p
      (sourceState z.val+r • fieldDirection force))
      (nativeMixed n theta derivative force p (sourceState z.val)) 0 :=by
  let s:=sourceState z.val
  have valid : s∈validStates:=⟨coframe_nondegenerate z,temporal_noncharacteristic z⟩
  have outer:=((sourceSymbol_smooth p s valid).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have D:=outer.hasFDerivAt.comp_hasDerivAt_of_eq 0 (state_line s (fieldDirection force)) (by simp)
  have native:=stateContact_generated n theta derivative s (fieldDirection force)
  have generated:=D.clm_apply native
  convert! generated using 1
  simp only [nativeMixed,symbolSecond,symbolFirst,Function.comp_apply,zero_smul,add_zero,s]

 def nativeRaw (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (s : ActionState) : FullMatrix:=
  -(4:ℂ) • (sourceActionWeight s*nativeFirst n theta derivative p s)

 def nativeRawMixed (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (s : ActionState) : FullMatrix:=
  -(4:ℂ) • (actionWeightFirst s (fieldDirection force)*nativeFirst n theta derivative p s+
    sourceActionWeight s*nativeMixed n theta derivative force p s)

 theorem nativeRaw_smooth (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    ContDiffAt ℝ ∞ (nativeRaw n theta derivative p) s :=
  ((sourceActionWeight_smooth s valid).mul (nativeFirst_smooth n theta derivative p s valid)).const_smul _

 theorem nativeRawMixed_generated (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>nativeRaw n theta derivative p (sourceState z.val+r • fieldDirection force))
      (nativeRawMixed n theta derivative force p (sourceState z.val)) 0 :=by
  let s:=sourceState z.val
  have valid : s∈validStates:=⟨coframe_nondegenerate z,temporal_noncharacteristic z⟩
  have DW:=(sourceActionWeight_smooth s valid).differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (state_line s (fieldDirection force)) (by simp)
  have actual:=(DW.mul (nativeMixed_generated n theta derivative force p z)).const_smul (-(4:ℂ))
  convert! actual using 1
  simp only [nativeRawMixed,actionWeightFirst,Function.comp_apply,zero_smul,add_zero,s]

 def nativeNoether (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (base candidate : ActionState) : FullMatrix:=
  -(4:ℂ) • (sourceActionWeight base*nativeFirst n theta derivative p candidate)

 def nativeNoetherMixed (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (base candidate : ActionState) : FullMatrix:=
  -(4:ℂ) • (sourceActionWeight base*nativeMixed n theta derivative force p candidate)

 theorem nativeNoether_source (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (s : ActionState) :
    nativeNoether n theta derivative p s s=nativeRaw n theta derivative p s :=rfl

 theorem nativeNoether_smooth (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (base candidate : ActionState) (valid : candidate∈validStates) :
    ContDiffAt ℝ ∞ (nativeNoether n theta derivative p base) candidate :=
  (contDiffAt_const.mul (nativeFirst_smooth n theta derivative p candidate valid)).const_smul _

 theorem nativeNoetherMixed_generated (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>nativeNoether n theta derivative p (sourceState z.val)
      (sourceState z.val+r • fieldDirection force))
      (nativeNoetherMixed n theta derivative force p (sourceState z.val) (sourceState z.val)) 0 :=by
  have actual:=((nativeMixed_generated n theta derivative force p z).const_mul (sourceActionWeight (sourceState z.val))).const_smul (-(4:ℂ))
  exact actual

 theorem nativeNoetherMixed_rawContact (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (s : ActionState) :
    nativeNoetherMixed n theta derivative force p s s=
      nativeRawMixed n theta derivative force p s-
        (-(4:ℂ) • (actionWeightFirst s (fieldDirection force)*nativeFirst n theta derivative p s)) :=by
  simp only [nativeNoetherMixed,nativeRawMixed,smul_add,neg_smul]
  abel

 theorem nativeNoether_transport (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (base candidate : ActionState) (valid : candidate∈validStates) :
    nativeNoether n theta derivative p base candidate=
      SourceRealScalarFock.branches (rawMomentumMatrix base)*
        SourceRealScalarFock.branches (rawMomentumInverse candidate)*nativeRaw n theta derivative p candidate :=by
  have cancel : SourceRealScalarFock.branches (rawMomentumInverse candidate)*
      SourceRealScalarFock.branches (rawMomentumMatrix candidate)=(1:FullMatrix):=by
    have original:=(rawMomentum_two_sided candidate valid).2
    simp only [SourceRealScalarFock.branches,Matrix.fromBlocks_multiply,neg_mul_neg]
    have conjugate : (rawMomentumInverse candidate).map star*(rawMomentumMatrix candidate).map star=
        ((1:SourceMatrix).map star):=by
      change (rawMomentumInverse candidate).map (starRingEnd ℂ)*
        (rawMomentumMatrix candidate).map (starRingEnd ℂ)=((1:SourceMatrix).map (starRingEnd ℂ))
      rw [←Matrix.map_mul,original]
    rw [original,conjugate]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.map_apply,Matrix.one_apply]
  have weight : nativeRaw n theta derivative p candidate=
      -(SourceRealScalarFock.branches (rawMomentumMatrix candidate)*nativeFirst n theta derivative p candidate) :=by
    rw [nativeRaw,rawMomentum_source_weight]
    simp only [smul_mul_assoc,neg_smul]
  rw [weight,mul_neg,←mul_assoc]
  rw [mul_assoc (SourceRealScalarFock.branches (rawMomentumMatrix base))
    (SourceRealScalarFock.branches (rawMomentumInverse candidate))
    (SourceRealScalarFock.branches (rawMomentumMatrix candidate)),cancel,mul_one,rawMomentum_source_weight]
  simp only [nativeNoether,smul_mul_assoc,neg_smul]

/-- The original source force reads this same native derivative before raw normalization. -/
 theorem nativeFirst_field_readback (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (s : ActionState)
    (sameDirection : stateVariation n theta derivative s=fieldDirection force) (valid : s∈validStates) :
    nativeRaw n theta derivative p s=rawActionSymbol force p s :=by
  rw [rawActionSymbol_source force p s valid]
  simp only [nativeRaw,nativeFirst,sameDirection]

 def nativeNoetherFiber (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (base candidate : ActionState) : FockFiber→L[ℂ] FockFiber:=
  quantizer (nativeNoether n theta derivative p base candidate)

 theorem nativeNoetherFiber_generated (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>nativeNoetherFiber n theta derivative p (sourceState z.val)
      (sourceState z.val+r • fieldDirection force))
      (quantizer (nativeNoetherMixed n theta derivative force p (sourceState z.val) (sourceState z.val))) 0 :=
  (quantizer.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (nativeNoetherMixed_generated n theta derivative force p z)

def nativeHamiltonianCoefficient (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (s : ActionState) (i : Fin 4) : SourceMatrix:=
  fderiv ℝ (fun u=>stateHamiltonian u i) s (stateVariation n theta derivative s)

 theorem nativeFirst_fourier (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    nativeFirst n theta derivative p s=fourierLinear p (nativeHamiltonianCoefficient n theta derivative s) :=by
  let d:=stateVariation n theta derivative s
  have each:=hasDerivAt_pi.mpr (fun i=>
    ((stateHamiltonian_smooth s valid.1 valid.2 i).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
      (state_line s d) (by simp))
  have lifted:=(fourierLinear p).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 each
  exact (symbol_first_generated p s d valid).unique lifted

 theorem nativeNoether_rawFourier (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (base candidate : ActionState) (valid : candidate∈validStates) :
    nativeNoether n theta derivative p base candidate=
      rawFourier p (fun i=> -(rawMomentumMatrix base*nativeHamiltonianCoefficient n theta derivative candidate i)) :=by
  have affine (q : PhysicalMomentum) :
      affineMatrix (fun i=> -(rawMomentumMatrix base*nativeHamiltonianCoefficient n theta derivative candidate i)) q=
        -(rawMomentumMatrix base*affineMatrix (nativeHamiltonianCoefficient n theta derivative candidate) q) :=by
    simp only [affineMatrix,smul_neg,Finset.sum_neg_distrib,mul_add,Finset.mul_sum,mul_smul_comm]
    abel
  rw [nativeNoether,nativeFirst_fourier n theta derivative p candidate valid,
    neg_smul,←smul_mul_assoc,←rawMomentum_source_weight base]
  change -(SourceRealScalarFock.branches (rawMomentumMatrix base)*
    realFourierMatrix (nativeHamiltonianCoefficient n theta derivative candidate) p)=_
  rw [rawFourier_blocks,realFourierMatrix,SourceRealScalarFock.branches,
    Matrix.fromBlocks_multiply,affine,affine]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks,Matrix.map_apply,Matrix.mul_apply,map_sum,map_mul]

 theorem nativeNoetherFiber_original_halves (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (base candidate : ActionState) (valid : candidate∈validStates)
    (v : FockFiber) :
    fiberCoordinates (nativeNoetherFiber n theta derivative p base candidate v)=
      (1/2:ℂ) •
        (plusDensity (affineMatrix (fun i=> -(rawMomentumMatrix base*
          nativeHamiltonianCoefficient n theta derivative candidate i)) p) (fiberCoordinates v)-
          oppositeDensity (affineMatrix (fun i=> -(rawMomentumMatrix base*
            nativeHamiltonianCoefficient n theta derivative candidate i)) (-p)) (fiberCoordinates v)) :=by
  rw [nativeNoetherFiber,nativeNoether_rawFourier n theta derivative p base candidate valid,rawFourier_blocks]
  change Fermion.quantize (Matrix.fromBlocks _ 0 0 ((_ : SourceMatrix).map star)) (fiberCoordinates v)=_
  rw [←rawPairDensity_quantize]
  simp only [rawPairDensity,LinearMap.smul_apply,LinearMap.sub_apply]

 theorem nativeNoether_fullCAR (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (base candidate : ActionState) (valid : candidate∈validStates)
    (v : FockFiber) :
    fiberCoordinates (nativeNoetherFiber n theta derivative p base candidate v)=
      Fermion.quantize (SourceRealScalarFock.branches (rawMomentumMatrix base)*
        SourceRealScalarFock.branches (rawMomentumInverse candidate))
          (Fermion.quantize (nativeRaw n theta derivative p candidate) (fiberCoordinates v))-
      Fermion.normalProduct (SourceRealScalarFock.branches (rawMomentumMatrix base)*
        SourceRealScalarFock.branches (rawMomentumInverse candidate))
          (nativeRaw n theta derivative p candidate) (fiberCoordinates v) :=by
  have normal:=LinearMap.congr_fun (Fermion.quantize_normal_order
    (SourceRealScalarFock.branches (rawMomentumMatrix base)*SourceRealScalarFock.branches (rawMomentumInverse candidate))
    (nativeRaw n theta derivative p candidate)) (fiberCoordinates v)
  rw [nativeNoetherFiber,nativeNoether_transport n theta derivative p base candidate valid]
  change Fermion.quantize ((_ * _) * _) (fiberCoordinates v)=_
  simp only [LinearMap.add_apply,Module.End.mul_apply] at normal
  rw [normal]
  abel

end LowEnergy.PreparationVacuumNativeLocalWard
