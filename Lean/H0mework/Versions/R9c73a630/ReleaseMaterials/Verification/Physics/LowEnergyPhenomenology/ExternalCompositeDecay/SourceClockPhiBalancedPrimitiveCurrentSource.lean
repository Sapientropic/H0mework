import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedNativeForceCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeGaugeScalarReductionSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPrimitiveCurrentCancellation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ScalarBalancedPrimitive
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussMatterCore
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarGaugeScale SourceCoframeVolume SourceDilationRemainder
open SourcePhysicalKineticSquare SourceClockPhiRadiusSourceCurrent SourceClockPhiRadiusAcceleration
open SourceClockPhiMatchedElectricSource SourceClockPhiOriginalGaussianH0RealPrimitives
open SourceGaugeRadialCurrent SourceGaugeRadiusMetric SourceGaugeRadialPair
open FirstCurrentClockPrimitive ReverseNativeClock ReverseNativeOuterSource ReverseBalancedForcePayer
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev Phi:End:=SourceScalarAffineScaleTransport.generator
private abbrev G:End:=SourceGaugeScaleTransport.generator
private abbrev E:End:=electricAction
private abbrev P:End:=positivePrimitive
private abbrev A:End:=gaugeBalancedNativeForce
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic matterAction positivePrimitive
  gaugeBalancedNativeForce sourcePair embed SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator
private theorem badd(T C D:End):bracket T (C+D)=bracket T C+bracket T D:=by unfold bracket;noncomm_ring
private theorem bsmul(T C:End)(c:ℂ):bracket T (c • C)=c • bracket T C:=by
  unfold bracket;simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem bprod(T C D:End):bracket T (C*D)=bracket T C*D+C*bracket T D:=by unfold bracket;noncomm_ring
private theorem jacobi(T C D:End):bracket T (bracket C D)=bracket (bracket T C) D+bracket C (bracket T D):=by
  unfold bracket;noncomm_ring
private theorem real_commute(c d:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)
private theorem real_phi_square(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val):bracket (multiply c hc) phiSquare=0:=by
  apply sub_eq_zero.mpr
  exact ((real_commute c phiRadius hc _).pow_right 2).eq
private theorem matter_phi_square:bracket matterAction phiSquare=0:=
  sub_eq_zero.mpr (original_phi_radius_non_scalar_commute.2.2.1.pow_right 2).eq
private theorem scalar_phi_square:bracket scalarKinetic phiSquare=(n/2:ℂ) • (U*Phi):=by
  have h:bracket diagonalAction phiSquare=bracket scalarKinetic phiSquare:=by
    have he:=(original_phi_radius_non_scalar_commute.2.2.2.pow_right 2).eq
    change (diagonalAction-scalarKinetic)*phiSquare=phiSquare*(diagonalAction-scalarKinetic) at he
    unfold bracket
    linear_combination (norm:=noncomm_ring) he
  rw [←h]
  exact original_phi_square_current

/-- The complete compensated force retains only the original scalar derivative of the radius square. -/
theorem actual_balanced_force_phi_square:
    bracket A phiSquare=(-3*(n:ℂ)) • (U*Phi):=by
  have hc:bracket centeredAction phiSquare=0:=real_phi_square _ _
  have hv:bracket vacuumLinearAction phiSquare=0:=real_phi_square _ _
  have hm:bracket magneticAction phiSquare=0:=real_phi_square _ _
  have hl:bracket localAction phiSquare=0:=real_phi_square _ _
  have hs:bracket scalarSpatialAction phiSquare=0:=real_phi_square _ _
  have hk:=scalar_phi_square
  have hM:=matter_phi_square
  rw [show A=gaugeBalancedNativeForce from rfl,actual_balanced_native_departments]
  unfold bracket at hc hv hm hl hs hk hM ⊢
  linear_combination (norm:=(noncomm_ring;module)) (-6:ℂ) • hk-(24:ℂ) • hM+
    (6:ℂ) • hc-(6:ℂ) • hv-(72:ℂ) • hm-(36:ℂ) • hl-(42:ℂ) • hs

private theorem electric_smooth_local(z:physicalChart):ContDiffAt ℝ ∞ electricWeight z.val:=
  (reciprocal_volume_smooth z).mul (SourceGaugeRadialCurrent.electric_square_smooth z)
private theorem real_multiply(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:QuantumTest):
    (multiply c hc f:SourceCoordinateSlice→FockFiber)=(fun z=>c z • f z):=by
  funext z;apply PiLp.ext;intro word
  exact Complex.real_smul.symm
private theorem electric_gauge_derivative(z:physicalChart):
    fderiv ℝ electricWeight z.val (gaugeEuler z.val)=2*electricWeight z.val := by
  have hc:=((electric_smooth_local z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (gauge_scale_derivative z.val 1) (gauge_scale_one z.val).symm
  have hs(r:ℝ):electricWeight (gaugeScale r z.val)=r^2*electricWeight z.val:=by
    unfold electricWeight
    rw [electric_square_scale]
    change reciprocalVolume z.val*(r^2*electricSquare z.val)=_
    ring
  have ht:HasDerivAt (fun r:ℝ=>electricWeight (gaugeScale r z.val)) (2*electricWeight z.val) 1:=by
    simpa only [hs,id_eq,Pi.pow_apply,one_pow,mul_one,Nat.cast_ofNat,Nat.reduceSub] using!
      ((hasDerivAt_id (1:ℝ)).pow 2).mul_const (electricWeight z.val)
  exact hc.unique ht
private theorem electric_gauge:bracket G electricAction=(2:ℂ) • electricAction := by
  have h:bracket gaugeEulerAction electricAction=(2:ℂ) • electricAction:=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    by_cases hz:z∈physicalChart
    · change gaugeEulerAction (electricAction f) z-(electricWeight z:ℂ) • gaugeEulerAction f z=(2:ℂ) • ((electricWeight z:ℂ) • f z)
      rw [gauge_euler_apply]
      change fderiv ℝ (multiply electricWeight electric_smooth_local f) z (gaugeEuler z)-_=_
      rw [real_multiply,
        fderiv_fun_smul ((electric_smooth_local ⟨z,hz⟩).differentiableAt (by simp))
          (f.contDiff.differentiable (by simp)).differentiableAt]
      change electricWeight z • fderiv ℝ f z (gaugeEuler z)+
        fderiv ℝ electricWeight z (gaugeEuler z) • f z-(electricWeight z:ℂ) • gaugeEulerAction f z=_
      rw [electric_gauge_derivative ⟨z,hz⟩,gauge_euler_apply]
      apply PiLp.ext;intro word
      simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul,smul_eq_mul]
      push_cast
      ring
    · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
      exact (h0 _).trans (h0 _).symm
  unfold G SourceGaugeScaleTransport.generator bracket at *
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  linear_combination (norm:=module) h

private theorem gauge_inverse:bracket G U=0:=by
  have h:=SourceGaugeScaleTransport.generator_commutator U
  rw [gauge_invariant_local U (fun z=>(reciprocalVolume z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _=>rfl) (fun _ _=>rfl)] at h
  exact h
private theorem gauge_full_electric:bracket G (bracket diagonalAction E)=
    (2:ℂ) • bracket diagonalAction E+(4:ℂ) • (U*G):=by
  have hc:bracket G GaussCoframeForm.coframeAction=0:=by
    have h:=SourceGaugeScaleTransport.generator_commutator GaussCoframeForm.coframeAction
    rw [original_coframe_gauge] at h
    exact h
  have hcf:bracket G coframeElectricCurrent=(2:ℂ) • coframeElectricCurrent:=by
    unfold coframeElectricCurrent
    rw [bsmul,jacobi,hc,electric_gauge,bsmul]
    simp only [bracket,zero_mul,mul_zero,sub_self,zero_add]
    module
  have hU:bracket G (U*G)=0:=by
    rw [bprod,gauge_inverse]
    simp only [bracket,sub_self,zero_mul,mul_zero,add_zero]
  have he:= (actual_matched_electric_source 0 0 ∅ Complex.I (by simp) 0).1
  change (1/2:ℂ) • bracket diagonalAction E=coframeElectricCurrent-U*G at he
  have hhe:=congrArg (bracket G) he
  rw [bsmul] at hhe
  unfold bracket at hcf hU he hhe ⊢
  linear_combination (norm:=(noncomm_ring;module)) (2:ℂ) • hhe+(2:ℂ) • hcf-(2:ℂ) • hU-(4:ℂ) • he

/-- Gauge compensation removes the full electric force, including the covariant coframe current. -/
theorem actual_balanced_force_electric:bracket A E=0:=by
  have h:=jacobi G diagonalAction E
  rw [gauge_full_electric,electric_gauge,bsmul] at h
  have he:bracket (bracket G diagonalAction) E=(4:ℂ) • (U*G):=by
    linear_combination (norm:=module) -h
  have hz:=actual_reverse_force_electric ∅ (0:diagonal.domain)
  unfold A gaugeBalancedNativeForce
  unfold bracket at he hz ⊢
  linear_combination (norm:=(noncomm_ring;module)) hz-(9:ℂ) • he

private theorem n_ne:(n:ℂ)≠0:=by
  apply Complex.ofReal_ne_zero.mpr
  change sourceTime 0≠0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos.ne'

/-- The literal positive primitive eliminates every gauge and coframe force in the compensated current. -/
theorem actual_balanced_primitive_current:
    bracket A P=(-6:ℂ) • (U*Phi):=by
  unfold P positivePrimitive
  rw [badd,bsmul,bsmul,actual_balanced_force_phi_square,actual_balanced_force_electric,smul_zero,add_zero,smul_smul]
  congr 1
  change (2/(n:ℂ))*(-3*(n:ℂ))=(-6:ℂ)
  calc _= -6*((n:ℂ)/(n:ℂ)):=by ring
       _= -6:=by rw [div_self n_ne];ring

private theorem phi_electric:bracket Phi E=0:=by
  have h:=SourceScalarAffineScaleTransport.generator_commutator E
  rw [phi_invariant_local E (fun z=>(electricWeight z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _=>rfl) (fun _ _=>rfl)] at h
  exact h
private theorem phi_square:bracket Phi phiSquare=(2:ℂ) • (phiSquare-1):=by
  have hr:bracket Phi phiRadiusAction=phiRadiusAction-phiInverseAction:=by
    have h:=original_phi_euler_radius
    unfold bracket at h
    unfold Phi SourceScalarAffineScaleTransport.generator bracket
    linear_combination (norm:=noncomm_ring) h
  have hi:phiRadiusAction*phiInverseAction=(1:End):=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
    rw [smul_smul,←Complex.ofReal_mul]
    have hp:0<phiRadius z:=Real.sqrt_pos.2 (by positivity)
    unfold phiReciprocal
    rw [mul_inv_cancel₀ hp.ne',Complex.ofReal_one,one_smul]
  have hi':phiInverseAction*phiRadiusAction=(1:End):=
    (real_commute _ _ _ _).eq.trans hi
  unfold phiSquare
  rw [pow_two,bprod,hr]
  change (phiRadiusAction-phiInverseAction)*phiRadiusAction+
    phiRadiusAction*(phiRadiusAction-phiInverseAction)=(2:ℂ) • (phiRadiusAction*phiRadiusAction-1)
  simp only [sub_mul,mul_sub,hi,hi']
  module
private theorem primitive_inverse:bracket U P=0:=by
  have hphi:bracket U phiSquare=0:=real_phi_square reciprocalVolume reciprocal_volume_smooth
  have hE:bracket U E=0:=sub_eq_zero.mpr (real_commute _ _ _ _).eq
  unfold P positivePrimitive
  rw [badd,bsmul,bsmul,hphi,hE,smul_zero,smul_zero,add_zero]

/-- The second primitive current is the original nonnegative scalar-radius multiplier, with its exact negative orientation. -/
theorem actual_balanced_primitive_double_current:
    bracket (bracket A P) P=(-24/(n:ℂ)) • (U*(phiSquare-1)):=by
  have hp:bracket Phi P=(4/(n:ℂ)) • (phiSquare-1):=by
    unfold P positivePrimitive
    rw [badd,bsmul,bsmul,phi_square,phi_electric,smul_zero,add_zero,smul_smul]
    congr 1
    ring
  rw [actual_balanced_primitive_current]
  have hs(c:ℂ)(T C:End):bracket (c • T) C=c • bracket T C:=by
    unfold bracket;simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
  rw [hs]
  have h:bracket (U*Phi) P=U*bracket Phi P+bracket U P*Phi:=by unfold bracket;noncomm_ring
  rw [h,hp,primitive_inverse,zero_mul,add_zero,mul_smul_comm,smul_smul]
  congr 1
  ring
end LowEnergy.ScalarBalancedPrimitive
