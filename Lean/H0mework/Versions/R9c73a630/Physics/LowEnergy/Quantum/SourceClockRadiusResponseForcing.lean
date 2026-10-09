import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaQ8RadiusBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockRadiusSourceGeometry
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialJoinedHessian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockRadiusResponseForcing
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceClockYukawaCubicCurrent SourceClockYukawaQ8RadiusBudget SourceClockRadiusSourceGeometry
open SourceClockYukawaRadialNativeDivergence SourceClockYukawaRadialNativeHessian SourceClockYukawaRadialJoinedHessian
open SourceLocalizedInverseFormPayment PositiveScalarCoefficientDecay SourcePhysicalKineticSquare
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev W : End := multiply scalarWeight scalarWeight_smooth
private abbrev r : End := GaussYukawaOperator.radiusAction
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev Pa (a : ScalarIndex) : End := GaussMomentumAdjoint.adjoint (scalarDirection a)
private abbrev d (a : ScalarIndex) : End := directionAction a
private abbrev dt (a : ScalarIndex) (m ell : ℕ) : End := derivativeAction a m ell
attribute [local irreducible] compressionCore defectAction resolventCore diagonalAction

private theorem theta_contact (a : ScalarIndex) (m ell : ℕ) :
    SourceNativeCutoffContact.contactAction (scalarDirection a) m ell=(-Complex.I) • dt a m ell := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change ((-Complex.I)*(SourceNativeCutoffContact.thetaDerivative (scalarDirection a) m ell x:ℂ)) • f x=
    (-Complex.I) • ((SourceNativeCutoffContact.thetaDerivative (scalarDirection a) m ell x:ℂ) • f x)
  exact mul_smul _ _ _
private theorem theta_adjoint (a : ScalarIndex) (m ell : ℕ) :
    bracket (Pa a) (thetaAction m ell)=(-Complex.I) • dt a m ell := by
  apply LinearMap.ext
  intro f
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
  rw [thetaAction,←SourceNativeCutoffContact.theta_action_polynomial,
    SourceNativeCutoffContact.sharp_core_contact,add_sub_cancel_left]
  exact LinearMap.congr_fun (theta_contact a m ell) f
private theorem theta_weight (m ell : ℕ) : Commute (thetaAction m ell) W := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  rw [thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact smul_comm (SourceNativeCutoffContact.theta m ell x:ℂ) (scalarWeight x:ℂ) (f x)

private theorem theta_native_source (m ell : ℕ) : bracket diagonalAction (thetaAction m ell)=
    (-Complex.I/2:ℂ) • ∑ a : ScalarIndex,(Pa a*W*dt a m ell+dt a m ell*W*P a) := by
  have h := SourceGammaNativeBudget.full_cutoff_contact m ell
  change diagonalAction*thetaAction m ell=thetaAction m ell*diagonalAction+_ at h
  have he : bracket diagonalAction (thetaAction m ell)=SourceGammaNativeBudget.scalarContact m ell :=
    sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))
  rw [he,SourceGammaNativeBudget.scalarContact]
  simp only [theta_contact,mul_smul_comm,smul_mul_assoc,←smul_add,←Finset.smul_sum,smul_smul]
  congr 1
  ring

/-- All native derivatives of the same actual radius response stay in this single seventy-column vector. -/
def nativeVector (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (a : ScalarIndex) : QuantumTest :=
  dt a m ell (bracket r (resolventCore F z hz) (coreEquiv.symm g))-
    thetaAction m ell (d a (resolventCore F z hz (coreEquiv.symm g)))
def thetaZero (a : ScalarIndex) (m ell : ℕ) : End := dt a m ell*W*P a-Pa a*W*dt a m ell

def nativeDivergence (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  (-Complex.I) • ∑ a : ScalarIndex,Pa a (W (nativeVector m ell F z hz g a))
def radialZero (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,thetaZero a m ell (bracket r (resolventCore F z hz) (coreEquiv.symm g)))+
    (Complex.I/2:ℂ) • thetaAction m ell ((∑ a : ScalarIndex,radiusZeroCore a) (resolventCore F z hz (coreEquiv.symm g)))-
      ∑ a : ScalarIndex,dt a m ell (W (d a (resolventCore F z hz (coreEquiv.symm g))))

def nativeSource (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  bracket diagonalAction (thetaAction m ell) (bracket r (resolventCore F z hz) (coreEquiv.symm g))+
    thetaAction m ell (radiusCurrent (resolventCore F z hz (coreEquiv.symm g)))

private theorem theta_radius_row (T D K W P Pa : End) (ht : Commute T W)
    (hP : bracket Pa T=(-Complex.I) • D) :
    T*((Complex.I/2:ℂ) • (Pa*W*K+K*W*P))=
      Complex.I • (Pa*W*T*K)+
        (Complex.I/2:ℂ) • (T*(K*W*P-Pa*W*K))-D*W*K := by
  have hp : T*Pa=Pa*T+Complex.I • D := by
    unfold bracket at hP
    linear_combination (norm := module) -hP
  have hrew : T*(Pa*W*K)=(Pa*W*T*K)+Complex.I • (D*W*K) := by
    calc
      _=(T*Pa)*W*K := by noncomm_ring
      _=(Pa*T+Complex.I • D)*W*K := by rw [hp]
      _=Pa*(T*W)*K+Complex.I • (D*W*K) := by simp only [add_mul,smul_mul_assoc,mul_assoc]
      _=_ := by rw [ht.eq];noncomm_ring
  have hc : (Complex.I/2)*Complex.I= -(1/2:ℂ) := by
    calc _=(1/2:ℂ)*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  simp only [mul_smul_comm,mul_add,mul_sub,hrew,smul_add,smul_sub,smul_smul,hc]
  module

/-- The original radius forcing has only the full native divergence and its contracted radial zero-order word. -/
theorem actual_radius_native_forcing (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    nativeSource m ell F z hz g=nativeDivergence m ell F z hz g+radialZero m ell F z hz g := by
  let q := resolventCore F z hz (coreEquiv.symm g)
  let v := bracket r (resolventCore F z hz) (coreEquiv.symm g)
  have hrow (a : ScalarIndex) :
      (-Complex.I/2:ℂ) • ((Pa a*W*dt a m ell+dt a m ell*W*P a) v)+
        thetaAction m ell (((Complex.I/2:ℂ) • (Pa a*W*d a+d a*W*P a)) q)=
      (-Complex.I) • (Pa a (W (dt a m ell v-thetaAction m ell (d a q))))+
        (-Complex.I/2:ℂ) • (thetaZero a m ell v)+
        (Complex.I/2:ℂ) • thetaAction m ell (radiusZeroCore a q)-dt a m ell (W (d a q)) := by
    have hr := LinearMap.congr_fun (theta_radius_row (thetaAction m ell) (dt a m ell) (d a) W (P a) (Pa a)
      (theta_weight m ell) (theta_adjoint a m ell)) q
    have hs : (-Complex.I/2:ℂ) • (Pa a*W*dt a m ell+dt a m ell*W*P a)=
        (-Complex.I) • (Pa a*W*dt a m ell)+(-Complex.I/2:ℂ) • thetaZero a m ell := by
      unfold thetaZero
      module
    have hv := LinearMap.congr_fun hs v
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sub,map_smul] at hr hv ⊢
    unfold radiusZeroCore at *
    simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,map_add] at *
    linear_combination (norm := module) hv+hr
  have h := congrArg (fun f : ScalarIndex → QuantumTest => ∑ a,f a) (funext hrow)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.smul_sum,←map_sum] at h
  unfold nativeSource nativeDivergence radialZero nativeVector
  rw [theta_native_source]
  unfold radiusCurrent
  simp only [LinearMap.smul_apply,LinearMap.sum_apply]
  simpa only [LinearMap.smul_apply,←Finset.smul_sum,map_smul,add_assoc,add_sub_assoc] using h

open FullYSourceResolventGraphSplice SourceResolventBandLimit

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem core_inverses (F : Index) (z : ℂ) (hz : z.im≠0) :
    (compressionCore F-z • (1:End))*resolventCore F z hz=1 ∧
      resolventCore F z hz*(compressionCore F-z • (1:End))=1 := by
  constructor
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      map_sub,map_smul,compression_embed,resolvent_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self] using h
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      resolvent_embed,map_sub,map_smul,compression_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_left (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul] using h


/-- All three moving defect terms are retained by the one original radial commutator. -/
def coherentDefect (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  thetaAction m ell ((r*defectAction F*resolventCore F z hz-defectAction F*resolventCore F z hz*r)
    (coreEquiv.symm g))

/-- The complete original H0 source equation uses no moving graph premise. -/
theorem actual_radius_response_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    diagonalAction (radiusResponseCore m ell F z hz g)=
      nativeDivergence m ell F z hz g+radialZero m ell F z hz g+
        coherentDefect m ell F z hz g+z • radiusResponseCore m ell F z hz g := by
  have hR := (core_inverses F z hz).1
  have hm (H D T A R : End) (h : (H-D-z • (1:End))*R=1) :
      H*T*bracket A R=bracket H T*bracket A R+T*bracket H A*R+
        T*(A*D*R-D*R*A)+z • (T*bracket A R) := by
    unfold bracket
    linear_combination (norm := noncomm_ring) T*A*h-T*h*A
    all_goals module
  have he : diagonalAction-defectAction F=compressionCore F := by unfold defectAction;abel
  have h := LinearMap.congr_fun
    (hm diagonalAction (defectAction F) (thetaAction m ell) r (resolventCore F z hz) (by rw [he];exact hR))
    (coreEquiv.symm g)
  rw [original_radius_hamiltonian_current] at h
  change diagonalAction (radiusResponseCore m ell F z hz g)=
    nativeSource m ell F z hz g+coherentDefect m ell F z hz g+z • radiusResponseCore m ell F z hz g at h
  rw [actual_radius_native_forcing] at h
  exact h

/-- The radius-response energy is sourced by the full native word and coherent defect before any estimate. -/
theorem actual_radius_response_mu_ward (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    z.im*‖embed (radiusResponseCore m ell F z hz g)‖^2=
      -(sourcePair (radiusResponseCore m ell F z hz g)
        (nativeDivergence m ell F z hz g+radialZero m ell F z hz g+coherentDefect m ell F z hz g)).im := by
  let v := radiusResponseCore m ell F z hz g
  have h0 : (sourcePair v (diagonalAction v)).im=0 := by
    have hp := congrArg Complex.im (GaussNativeForm.pair_conjugate v (diagonalAction v))
    rw [←diagonalAction_pair] at hp
    simp only [Complex.conj_im] at hp
    linarith only [hp]
  let f := nativeDivergence m ell F z hz g+radialZero m ell F z hz g+coherentDefect m ell F z hz g
  have he : diagonalAction v=f+z • v := actual_radius_response_source m ell F z hz g
  have hp : sourcePair v (diagonalAction v)=sourcePair v f+z*sourcePair v v := by
    rw [he]
    simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right]
  have h := congrArg Complex.im hp
  rw [h0] at h
  have hn : sourcePair v v=((‖embed v‖^2:ℝ):ℂ) := by
    simpa only [sourcePair,Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed v)
  rw [hn] at h
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add] at h
  change z.im*‖embed v‖^2=-(sourcePair v f).im
  linarith only [h]

end LowEnergy.SourceClockRadiusResponseForcing
