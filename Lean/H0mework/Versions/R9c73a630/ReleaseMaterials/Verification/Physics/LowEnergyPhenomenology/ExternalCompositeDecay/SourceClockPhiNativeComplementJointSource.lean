import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPositiveTimeWorkGenerator
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiComparisonNativeClosedGraph
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCoframeCovariantSquare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NativePointReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory SourceScalarDoubleCurrent SourcePhysicalKineticSquare
open SourceCoframeCovariantAction SourceClockPhiNativeMatchedSource
open SourceClockPhiMatchedDiffusionSource SourceClockPhiComparisonNativeClosedGraph
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev B:End:=driftClock
private abbrev U:End:=inverseVolumeAction
private abbrev A:End:=SourceClockPhiCombinedScalePressure.combinedConjugate
def nativeComplement:End:=diagonalAction-covariantKinetic
attribute [local irreducible] nativeComplement diagonalAction covariantKinetic sourcePair embed driftClock

private theorem covariant_adjoint_pair (i:Fin 6)(f g:QuantumTest):
    sourcePair f (covariantAdjoint i g)=sourcePair (covariantMomentum i f) g:=by
  have h:=congrArg (starRingEnd ℂ) (original_covariant_pair i g f)
  rw [pair_conjugate,pair_conjugate] at h
  exact h.symm

private theorem covariant_term_pair(i j:Fin 6)(f g:QuantumTest):
    sourcePair f ((covariantAdjoint i*metricAction i j*covariantMomentum j) g)=
      sourcePair ((covariantAdjoint j*metricAction j i*covariantMomentum i) f) g:=by
  simp only [Module.End.mul_apply]
  rw [covariant_adjoint_pair]
  change sourcePair (covariantMomentum i f)
    (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)
      (covariantMomentum j g))=_
  rw [multiply_pair,original_covariant_pair]
  exact congrArg (fun q:QuantumTest=>sourcePair (covariantAdjoint j q) g)
    (congrArg (fun T:End=>T (covariantMomentum i f))
      (show metricAction i j=metricAction j i by
        apply LinearMap.ext
        intro q
        apply DFunLike.ext
        intro z
        change (GaussCoframeKinetic.coefficient i j z:ℂ) • q z=
          (GaussCoframeKinetic.coefficient j i z:ℂ) • q z
        rw [GaussCoframeKinetic.coefficient_symmetric]))

private theorem pair_sum_r(f:QuantumTest)(q:Fin 6→QuantumTest):
    sourcePair f (∑i,q i)=∑i,sourcePair f (q i):=by
  simp only [sourcePair,map_sum,inner_sum]
private theorem pair_sum_l(f:QuantumTest)(q:Fin 6→QuantumTest):
    sourcePair (∑i,q i) f=∑i,sourcePair (q i) f:=by
  simp only [sourcePair,map_sum,sum_inner]

theorem actual_covariant_kinetic_pair(f g:QuantumTest):
    sourcePair f (covariantKinetic g)=sourcePair (covariantKinetic f) g:=by
  unfold covariantKinetic
  simp_rw [LinearMap.sum_apply,pair_sum_r,pair_sum_l,covariant_term_pair]
  rw [Finset.sum_comm]

theorem actual_native_complement_pair(f g:QuantumTest):
    sourcePair f (nativeComplement g)=sourcePair (nativeComplement f) g:=by
  have h1:=diagonalAction_pair f g
  have h2:=actual_covariant_kinetic_pair f g
  simp only [nativeComplement,LinearMap.sub_apply,sourcePair,map_sub,inner_sub_left,inner_sub_right] at h1 h2 ⊢
  exact congrArg₂ (·-·) h1 h2

private theorem B_pair(f g:QuantumTest):sourcePair (B f) g= -sourcePair f (B g):=by
  have h:=actual_B3_formal_pair (coreEquiv f) (coreEquiv g)
  change inner ℂ (embed (B (coreEquiv.symm (coreEquiv f)))) (embed g)=
    inner ℂ (embed f) (embed ((-B) (coreEquiv.symm (coreEquiv g)))) at h
  have hl:=congrArg (fun q:QuantumTest=>inner ℂ (embed (B q)) (embed g))
    (coreEquiv.symm_apply_apply f)
  have hr:=congrArg (fun q:QuantumTest=>inner ℂ (embed f) (embed ((-B) q)))
    (coreEquiv.symm_apply_apply g)
  have result:=hl.symm.trans (h.trans hr)
  simpa only [sourcePair,LinearMap.neg_apply,map_neg,inner_neg_right] using result

private theorem M_difference:matchedTester=B-U:=by
  unfold matchedTester B driftClock
  module

/-- The actual native/local double current and complete forcing cross form one original Q word. -/
theorem actual_native_joint_Q_source(w:QuantumTest):
    (sourcePair w (bracket A (bracket A nativeComplement) w)).re-
      6*(sourcePair (matchedTester w) (nativeComplement w)).re=
    (sourcePair w (completeCurrent nativeComplement w)).re:=by
  have hN:=actual_native_complement_pair w (B w)
  have hU:=actual_native_complement_pair w (U w)
  have hB:=B_pair w (nativeComplement w)
  have hUg:sourcePair w (U (nativeComplement w))=sourcePair (U w) (nativeComplement w):=
    multiply_pair _ _ _ _
  have hsym:=congrArg Complex.re (pair_conjugate (nativeComplement w) (B w))
  have husym:=congrArg Complex.re (pair_conjugate (nativeComplement w) (U w))
  have he:completeCurrent nativeComplement=bracket A (bracket A nativeComplement)+
      (3:ℂ) • bracket B nativeComplement+(3:ℂ) • (U*nativeComplement+nativeComplement*U):=by
    change (A*A+(3:ℂ) • B)*nativeComplement+nativeComplement*(A*A-(3:ℂ) • B)-
      (2:ℂ) • (A*nativeComplement*A)+(3:ℂ) • (U*nativeComplement+nativeComplement*U)=_
    unfold bracket
    simp only [add_mul,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,smul_sub]
    noncomm_ring
    module
  rw [he,M_difference]
  simp only [bracket,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.mul_apply,sourcePair,map_add,map_sub,map_smul,inner_add_right,inner_sub_left,
    inner_sub_right,inner_smul_right,Complex.add_re,Complex.sub_re] at hN hU hB hUg hsym husym ⊢
  simp only [Complex.conj_re] at hsym husym
  simp only [Complex.mul_re,Complex.re_ofNat,
    Complex.im_ofNat,zero_mul,sub_zero] at hN hU hB hUg ⊢
  have hrN:=congrArg Complex.re hN
  have hrU:=congrArg Complex.re hU
  have hrB:=congrArg Complex.re hB
  have hrUg:=congrArg Complex.re hUg
  simp only [Complex.neg_re,Complex.add_re,Complex.sub_re] at hrN hrU hrB hrUg ⊢
  linarith only [hrN,hrU,hrB,hrUg,hsym,husym]

end LowEnergy.NativePointReturn
