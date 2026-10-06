import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeDivergence
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaGradedEuler
import Mathlib.Analysis.InnerProductSpace.Trace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialNativeHessian
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussLiveMomentum GaussNativeEnergy GaussRadialDomain GaussYukawaCoefficient GaussNativePotential
open SourceScalarRadialContact SourcePhysicalKineticSquare SourceScalarDoubleCurrent SourceScalarPairedTransport
open SourceClockYukawaRadialNativeDivergence SourceNativeCoframeCompatibility SourceNativeDensityTrace
open SourceMixedNativeReturn SourceLocalizedInverseFormPayment GaussQuantumMultiplier GaussNativeMatter SourceScalarGaugeForce
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore StageNineHolonomicField
open scoped ContDiff InnerProductSpace BigOperators Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber
private def alpha : End := (-(sourceTime 0:ℂ)/4) • inverseVolumeAction
private def powerProfile (n : ℕ) : End := (n:ℂ) • (alpha*inverseAction^(n+2))
private def eulerForm (P : End) : End := (1/2:ℂ) •
  (scalarEulerAction*P+P*scalarEulerAction+(61:ℂ) • P)

private theorem real_fock_smul (c : ℝ) (v : FockFiber) : c • v=(c:ℂ) • v := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem inverse_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((inverseAction^n) f) z=(reciprocal z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (reciprocal z:ℂ) • (((inverseAction^n) f) z)=_
    rw [ih,pow_succ',mul_smul]

private def profileCoefficient (n : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  -(sourceTime 0)/4*reciprocalVolume z*(n:ℝ)*reciprocal z^(n+2)
private theorem profile_smooth (n : ℕ) (z : physicalChart) : ContDiffAt ℝ ∞ (profileCoefficient n) z.val :=
  ((contDiffAt_const.mul (reciprocal_volume_smooth z)).mul contDiffAt_const).mul
    (reciprocal_smooth.pow (n+2)).contDiffAt

private theorem power_profile_real (n : ℕ) : powerProfile n=multiply (profileCoefficient n) (profile_smooth n) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold powerProfile
  simp only [LinearMap.smul_apply,Module.End.mul_apply]
  change (n:ℂ) • ((-(sourceTime 0:ℂ)/4) •
    ((reciprocalVolume z:ℂ) • (((inverseAction^(n+2)) f) z)))=_
  rw [inverse_power_apply]
  apply PiLp.ext
  intro word
  change (n:ℂ)*((-(sourceTime 0:ℂ)/4)*((reciprocalVolume z:ℂ)*((reciprocal z:ℂ)^(n+2)*f z word)))=
    (profileCoefficient n z:ℂ)*f z word
  unfold profileCoefficient
  push_cast
  ring

private theorem weight_contact (a : ScalarIndex) :
    multiply scalarWeight scalarWeight_smooth*GaussRadialMomentum.commutatorAction (scalarDirection a)=
      Complex.I • (SourceGammaNativeBudget.scalarColumn a*powerProfile 1) := by
  rw [power_profile_real]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (scalarWeight z:ℂ)*((-Complex.I)*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)*f z word)=
    Complex.I*((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z:ℂ)*
      ((profileCoefficient 1 z:ℂ)*f z word))
  unfold scalarWeight GaussRadialMomentum.radialDerivative SourceClosedCostNativeProbe.coordinate
    profileCoefficient reciprocalVolume reciprocal
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

private theorem contact_weight (a : ScalarIndex) :
    GaussRadialMomentum.commutatorAction (scalarDirection a)*multiply scalarWeight scalarWeight_smooth=
      Complex.I • (powerProfile 1*SourceGammaNativeBudget.scalarColumn a) := by
  rw [power_profile_real]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change ((-Complex.I)*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ))*
      ((scalarWeight z:ℂ)*f z word)=
    Complex.I*((profileCoefficient 1 z:ℂ)*
      ((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z:ℂ)*f z word))
  unfold scalarWeight GaussRadialMomentum.radialDerivative SourceClosedCostNativeProbe.coordinate
    profileCoefficient reciprocalVolume reciprocal
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

private theorem contact_term (A W C Q G P : End)
    (hw : W*C=Complex.I • (Q*G)) (hc : C*W=Complex.I • (G*Q)) :
    A*W*C+C*W*P=Complex.I • (A*Q*G+G*(Q*P)) := by
  calc
    _=A*(W*C)+(C*W)*P := by noncomm_ring
    _=A*(Complex.I • (Q*G))+(Complex.I • (G*Q))*P := by rw [hw,hc]
    _=_ := by simp only [mul_smul_comm,smul_mul_assoc,←smul_add,mul_assoc]

private theorem base_current : GaussRadialHamiltonian.radialAction=eulerForm (powerProfile 1) := by
  have h (a : ScalarIndex) : GaussRadialHamiltonian.radialTerm (scalarDirection a)=
      Complex.I • (GaussMomentumAdjoint.adjoint (scalarDirection a)*
        SourceGammaNativeBudget.scalarColumn a*powerProfile 1+
        powerProfile 1*(SourceGammaNativeBudget.scalarColumn a*covariantMomentum (scalarDirection a))) := by
    simpa only [GaussRadialHamiltonian.radialTerm,←Module.End.mul_eq_comp,mul_assoc] using!
      contact_term (GaussMomentumAdjoint.adjoint (scalarDirection a)) (multiply scalarWeight scalarWeight_smooth)
        (GaussRadialMomentum.commutatorAction (scalarDirection a)) (SourceGammaNativeBudget.scalarColumn a)
        (powerProfile 1) (covariantMomentum (scalarDirection a)) (weight_contact a) (contact_weight a)
  have he : GaussRadialHamiltonian.radialAction=(Complex.I/2) •
      (radialAdjoint*powerProfile 1+powerProfile 1*radialMomentum) := by
    simp only [GaussRadialHamiltonian.radialAction,h,←Finset.smul_sum,smul_smul,Finset.sum_add_distrib,
      ←Finset.sum_mul,←Finset.mul_sum,radialAdjoint,radialMomentum]
    congr 1
    ring
  rw [he,scalar_adjoint_contraction,scalar_native_contraction]
  simp only [smul_mul_assoc,mul_smul_comm,←smul_add,smul_smul]
  have hi : (Complex.I/2)*(-Complex.I)=(1/2:ℂ) := by
    calc _= -(Complex.I*Complex.I)/2 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi]
  unfold eulerForm
  simp only [add_mul,smul_mul_assoc,one_mul]
  module

private theorem euler_inverse : bracket scalarEulerAction inverseAction=inverseAction^3-inverseAction := by
  have hd (z : SourceCoordinateSlice) : fderiv ℝ reciprocal z (scalarEuler z)=reciprocal z^3-reciprocal z := by
    rw [GaussRadialMomentum.reciprocal_derivative]
    change -inner ℝ (z.2.1:Scalar) (z.2.1:Scalar)/(4*radius z^3)=_
    rw [real_inner_self_eq_norm_sq]
    have hs := Real.sq_sqrt (show 0≤1+‖(z.2.1:Scalar)‖^2/4 by positivity)
    change radius z^2=1+‖(z.2.1:Scalar)‖^2/4 at hs
    unfold reciprocal
    field_simp [(radius_pos z).ne']
    nlinarith only [hs]
  have he (f : QuantumTest) (z : SourceCoordinateSlice) :
      scalarEulerAction (inverseAction f) z=reciprocal z • scalarEulerAction f z+
        (reciprocal z^3-reciprocal z) • f z := by
    rw [scalar_euler_apply,GaussRadialMomentum.inverseAction_real,
      fderiv_fun_smul (reciprocal_smooth.differentiable (by simp)).differentiableAt
        (f.contDiff.differentiable (by simp)).differentiableAt]
    change reciprocal z • fderiv ℝ f z (scalarEuler z)+
      fderiv ℝ reciprocal z (scalarEuler z) • f z=_
    rw [hd,scalar_euler_apply]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change scalarEulerAction (inverseAction f) z-inverseAction (scalarEulerAction f) z=
    ((inverseAction^3) f) z-inverseAction f z
  rw [he,inverse_power_apply]
  change reciprocal z • scalarEulerAction f z+(reciprocal z^3-reciprocal z) • f z-
    (reciprocal z:ℂ) • scalarEulerAction f z=
      (reciprocal z:ℂ)^3 • f z-(reciprocal z:ℂ) • f z
  rw [real_fock_smul,real_fock_smul]
  push_cast
  module

private theorem bracket_product (A B C : End) :
    bracket A (B*C)=bracket A B*C+B*bracket A C := by unfold bracket;noncomm_ring

private theorem euler_power (n : ℕ) :
    bracket scalarEulerAction (inverseAction^n)=(n:ℂ) • (inverseAction^n*(inverseAction^2-1)) := by
  induction n with
  | zero => simp [bracket]
  | succ n ih =>
    rw [pow_succ,bracket_product,ih,euler_inverse]
    have he : inverseAction^n*(inverseAction^3-inverseAction)=inverseAction^(n+1)*(inverseAction^2-1) := by
      rw [pow_succ]
      noncomm_ring
    have hn : (inverseAction^n*(inverseAction^2-1))*inverseAction=inverseAction^(n+1)*(inverseAction^2-1) := by
      rw [pow_succ]
      noncomm_ring
    simp only [Nat.cast_succ,add_smul,one_smul,smul_mul_assoc]
    rw [he,hn]
    simp only [pow_succ]


private theorem inverse_coefficient_source (a : ScalarIndex) :
    GaussRadialMomentum.commutatorAction (scalarDirection a)=(-Complex.I) • inverseCoefficientCore a := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (-Complex.I*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)) • f z=
    (-Complex.I) • (directionAction a ((inverseAction^2) f)) z
  rw [pow_two]
  change _=(-Complex.I) • ((directionWeight a z:ℂ) • ((reciprocal z:ℂ) • ((reciprocal z:ℂ) • f z)))
  simp only [smul_smul]
  congr 1
  unfold GaussRadialMomentum.radialDerivative directionWeight reciprocal scalarDirection
  push_cast
  field_simp [(show (radius z:ℂ)≠0 by exact_mod_cast (radius_pos z).ne')]

private theorem weight_inverse_coefficient (a : ScalarIndex) :
    multiply scalarWeight scalarWeight_smooth*inverseCoefficientCore a=
      -(SourceGammaNativeBudget.scalarColumn a*powerProfile 1) := by
  have h := weight_contact a
  rw [inverse_coefficient_source,mul_smul_comm] at h
  have hh := congrArg (fun A : End => Complex.I • A) h
  have hi : Complex.I*(-Complex.I)=1 := by rw [mul_neg,Complex.I_mul_I,neg_neg]
  simpa only [smul_smul,hi,Complex.I_mul_I,one_smul,neg_one_smul] using hh

private theorem inverse_divergence_source : GaussRadialHamiltonian.radialAction=
    (scalarEulerAction+(61:ℂ) • (1:End))*powerProfile 1+
      (-Complex.I/2:ℂ) • ∑ a : ScalarIndex,inverseZeroCore a := by
  apply LinearMap.ext
  intro f
  have h := original_native_mixed_forcing false 0 0 (0:QuantumTest) f 0
  simp only [map_zero,zero_add,add_zero,sub_zero,nativeDivergenceWord,sourceZeroOrderWord,
    Finset.sum_const_zero] at h
  change GaussRadialHamiltonian.radialAction f=(-Complex.I) •
    (∑ a : ScalarIndex,GaussMomentumAdjoint.adjoint (scalarDirection a)
      (multiply scalarWeight scalarWeight_smooth (inverseCoefficientCore a f)))+
    (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,inverseZeroCore a f) at h
  have hw : (∑ a : ScalarIndex,GaussMomentumAdjoint.adjoint (scalarDirection a)
      (multiply scalarWeight scalarWeight_smooth (inverseCoefficientCore a f)))=-(radialAdjoint (powerProfile 1 f)) := by
    have he (a : ScalarIndex) : multiply scalarWeight scalarWeight_smooth (inverseCoefficientCore a f)=
        -(SourceGammaNativeBudget.scalarColumn a (powerProfile 1 f)) :=
      LinearMap.congr_fun (weight_inverse_coefficient a) f
    simp only [he,map_neg,radialAdjoint,LinearMap.sum_apply,Module.End.mul_apply,
      ←Finset.sum_neg_distrib]
  rw [hw,scalar_adjoint_contraction] at h
  have hi : (-Complex.I)*Complex.I=1 := by rw [neg_mul,Complex.I_mul_I,neg_neg]
  simpa only [LinearMap.smul_apply,LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,
    smul_neg,neg_smul,neg_neg,smul_smul,hi,one_smul] using h

private theorem euler_volume : Commute scalarEulerAction inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change scalarEulerAction (inverseVolumeAction f) z=inverseVolumeAction (scalarEulerAction f) z
  by_cases hz : z∈physicalChart
  · have hv := (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z)
    have hu := (hasDerivAt_inv (volume_pos ⟨z,hz⟩).ne').comp_hasFDerivAt z hv
    have hd : fderiv ℝ reciprocalVolume z (scalarEuler z)=0 := by
      change fderiv ℝ ((fun y : ℝ => y⁻¹) ∘ volume) z (scalarEuler z)=0
      rw [hu.fderiv]
      have he : fderiv ℝ volume z (scalarEuler z)=0 := by
        rw [SourceCoframeVolume.volume_derivative]
        simp [scalarEuler]
      change -(volume z^2)⁻¹*fderiv ℝ volume z (scalarEuler z)=0
      rw [he,mul_zero]
    rw [scalar_euler_apply]
    have hf : (inverseVolumeAction f : SourceCoordinateSlice → FockFiber)=
      fun x => (reciprocalVolume x:ℂ) • f x := rfl
    rw [hf]
    change fderiv ℝ (fun x => (Complex.ofRealCLM ∘ reciprocalVolume) x • f x) z (scalarEuler z)=_
    rw [fderiv_fun_smul ((Complex.ofRealCLM.contDiff.contDiffAt.comp z (reciprocal_volume_smooth ⟨z,hz⟩)).differentiableAt (by simp))
      (f.contDiff.differentiable (by simp)).differentiableAt]
    change (reciprocalVolume z:ℂ) • fderiv ℝ f z (scalarEuler z)+
      fderiv ℝ (fun x => (reciprocalVolume x:ℂ)) z (scalarEuler z) • f z=_
    have hc : fderiv ℝ (fun x => (reciprocalVolume x:ℂ)) z (scalarEuler z)=0 := by
      change fderiv ℝ (Complex.ofRealCLM ∘ ((fun y : ℝ => y⁻¹) ∘ volume)) z (scalarEuler z)=0
      rw [(Complex.ofRealCLM.hasFDerivAt.comp z (hu:HasFDerivAt reciprocalVolume _ z)).fderiv]
      have ht : fderiv ℝ reciprocalVolume z=-(volume z^2)⁻¹ • fderiv ℝ volume z := hu.fderiv
      rw [ht] at hd
      exact congrArg (fun r : ℝ => (r:ℂ)) hd
    rw [hc,zero_smul,add_zero,inverseVolumeAction,multiply_apply,scalar_euler_apply]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem profile_euler_derivative : bracket scalarEulerAction (powerProfile 1)=
    (3:ℂ) • (alpha*(inverseAction^5-inverseAction^3)) := by
  have hA : bracket scalarEulerAction alpha=0 := by
    unfold alpha bracket
    have h := euler_volume.eq
    simp only [smul_mul_assoc,mul_smul_comm]
    rw [h,sub_self]
  rw [powerProfile,Nat.cast_one,one_smul,bracket_product,hA,zero_mul,zero_add,euler_power]
  simp only [mul_smul_comm]
  congr 1
  change alpha*(inverseAction^3*(inverseAction^2-1))=alpha*(inverseAction^5-inverseAction^3)
  rw [mul_sub,mul_one,←pow_add]

/-- The actual scalar61 transpose contracts every native/density index response into the original radius polynomial. -/
theorem original_inverse_hessian_source :
    (∑ a : ScalarIndex,inverseZeroCore a)=
      (Complex.I*(sourceTime 0:ℂ)/4) •
        (inverseVolumeAction*((58:ℂ) • inverseAction^3+(3:ℂ) • inverseAction^5)) := by
  have h := inverse_divergence_source
  rw [base_current] at h
  have hs : (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,inverseZeroCore a)=
      -(1/2:ℂ) • (bracket scalarEulerAction (powerProfile 1)+(61:ℂ) • powerProfile 1) := by
    unfold eulerForm at h
    simp only [add_mul,smul_mul_assoc,one_mul] at h
    unfold bracket
    linear_combination (norm := module) -h
  have he := congrArg (fun A : End => (2*Complex.I) • A) hs
  have hi : (2*Complex.I)*(-Complex.I/2)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  simp only [smul_smul,hi,one_smul] at he
  have hg : powerProfile 1=alpha*inverseAction^3 := by simp only [powerProfile,Nat.cast_one,one_smul]
  rw [profile_euler_derivative,hg] at he
  simp only [alpha,mul_add,mul_sub,mul_smul_comm,smul_mul_assoc,smul_add,smul_sub,smul_smul] at he ⊢
  linear_combination (norm := module) he

private def scalarInverseLie (z : SourceCoordinateSlice) : Scalar →ₗ[ℝ] NativeLie :=
  (inverseLie z).comp (LinearMap.inl ℝ Scalar Gauge)
private def connectionVector (z : SourceCoordinateSlice) : Scalar :=
  ∑ a : ScalarIndex,SourceQuantumScalarChart.action (scalarBasis a) (scalarInverseLie z (scalarBasis a))

def gammaGradient (z : SourceCoordinateSlice) : Scalar :=
  ∑ a : ScalarIndex,gammaDensity (scalarDirection a) z • scalarBasis a

private theorem scalar_skew (a : NativeLie) (x y : Scalar) :
    inner ℝ (SourceQuantumScalarChart.action x a) y+inner ℝ x (SourceQuantumScalarChart.action y a)=0 := by
  have h := SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm a)) x y
  rw [original_scalar_pairing,original_scalar_pairing] at h
  exact h

private theorem intrinsic_scalar_component (z : SourceCoordinateSlice) (a : ScalarIndex) :
    intrinsicDensity (scalarDirection a) z=-inner ℝ (connectionVector z) (scalarBasis a) := by
  have he : sourceLieResponse (scalarDirection a) z=
      (scalarInverseLie z).comp (SourceQuantumScalarChart.action (scalarBasis a)) := by
    apply LinearMap.ext
    intro b
    change inverseLie z (SourceQuantumScalarChart.action (scalarBasis a) b,GaussLiveMomentum.nativeGauge b 0)=_
    rw [map_zero]
    rfl
  unfold intrinsicDensity
  rw [he,LinearMap.trace_comp_comm',LinearMap.trace_eq_sum_inner _ scalarBasis]
  simp only [LinearMap.comp_apply]
  unfold connectionVector
  rw [sum_inner,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have h := scalar_skew (scalarInverseLie z (scalarBasis b)) (scalarBasis b) (scalarBasis a)
  linarith

private theorem connection_density_scalar (z : SourceCoordinateSlice) :
    connectionVector z+(∑ a : ScalarIndex,nativeDensityCorrection (scalarDirection a) z • scalarBasis a)=-gammaGradient z := by
  have hc : (∑ a : ScalarIndex,intrinsicDensity (scalarDirection a) z • scalarBasis a)=-connectionVector z := by
    simp_rw [intrinsic_scalar_component,neg_smul]
    rw [Finset.sum_neg_distrib]
    congr 1
    simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm] using scalarBasis.sum_repr (connectionVector z)
  simp only [nativeDensityCorrection,sub_smul,Finset.sum_sub_distrib]
  rw [hc]
  unfold gammaGradient
  module

/-- All seventy full-CAR connection rows and intrinsic density traces cancel in the source; only the broken gamma-gradient remains. -/
theorem original_constant_density_hessian (sharp : Bool) (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,
      (connection (scalarDirection a) z*branchMap sharp (scalarBasis a)-
        branchMap sharp (scalarBasis a)*connection (scalarDirection a) z+
        (nativeDensityCorrection (scalarDirection a) z:ℂ) • branchMap sharp (scalarBasis a)))=
      -branchMap sharp (gammaGradient z) := by
  have h (a : ScalarIndex) : connection (scalarDirection a) z*branchMap sharp (scalarBasis a)-
      branchMap sharp (scalarBasis a)*connection (scalarDirection a) z=
        branchMap sharp (SourceQuantumScalarChart.action (scalarBasis a) (scalarInverseLie z (scalarBasis a))) := by
    exact original_branch_native sharp (scalarInverseLie z (scalarBasis a)) (scalarBasis a)
  simp_rw [h]
  have hm (c : ℝ) (phi : Scalar) : (c:ℂ) • branchMap sharp phi=branchMap sharp (c • phi) := by
    rw [map_smul]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) c (branchMap sharp phi)).symm
  simp_rw [hm,←map_add]
  rw [←map_sum]
  have hc := connection_density_scalar z
  unfold connectionVector at hc
  rw [←Finset.sum_add_distrib] at hc
  rw [hc,map_neg]

end LowEnergy.SourceClockYukawaRadialNativeHessian
