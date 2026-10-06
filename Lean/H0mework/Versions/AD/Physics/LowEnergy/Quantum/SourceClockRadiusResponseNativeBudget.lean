import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockRadiusResponseForcing
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockRadiusBoundaryFamilyTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockRadiusResponseNativeBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourcePhysicalKineticSquare SourceClockReflectedForm SourceHamiltonianVolume SourceCoframeVolume
open SourceClockYukawaCubicCurrent SourceClockYukawaQ8RadiusBudget SourceClockRadiusResponseForcing
open SourceLocalizedInverseFormPayment PositiveScalarCoefficientDecay SourceClockRadiusBoundaryFamilyTail
open SourceRelativePowerTail SourceRetardedForcingTail SourceClockYukawaRadialMixedBudget
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
private abbrev r : End := GaussYukawaOperator.radiusAction
private def boundaryCore (n : ℕ) : End := (n+1:ℂ) • (inverseAction*(1-inverseAction)^n)
attribute [local irreducible] resolventCore state compressionCore defectAction inverseRadius

private theorem complement_core (n : ℕ) (f : QuantumTest) :
    (sourceComplement^n) (embed f)=embed (((1-inverseAction)^n) f) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change (sourceComplement^n) (embed f)-inverseRadius ((sourceComplement^n) (embed f))=
      embed (((1-inverseAction)^n) f-inverseAction (((1-inverseAction)^n) f))
    rw [ih,inverse_core,map_sub]
private theorem boundary_core (n : ℕ) (f : QuantumTest) : boundaryOperator n (embed f)=embed (boundaryCore n f) := by
  simp only [boundaryOperator,boundaryCore,smul_apply,mul_apply_eq_comp,LinearMap.smul_apply,
    Module.End.mul_apply,complement_core,inverse_core,map_smul]
private theorem geometric_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    ((1-inverseAction)^n) f x=((1-reciprocal x:ℝ):ℂ)^n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ((1-inverseAction)^n) f x-(reciprocal x:ℂ) • (((1-inverseAction)^n) f x)=_
    rw [ih,pow_succ',mul_smul]
    push_cast
    module
private theorem boundary_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    boundaryCore n f x=(((n+1:ℝ)*reciprocal x*(1-reciprocal x)^n:ℝ):ℂ) • f x := by
  change (n+1:ℂ) • ((reciprocal x:ℂ) • (((1-inverseAction)^n) f x))=_
  rw [geometric_point]
  push_cast
  simp only [smul_smul]
  congr 1
  ring
private theorem radius_point (f : QuantumTest) (x : SourceCoordinateSlice) : r f x=(radius x:ℂ) • f x := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul
private theorem derivative_radius (a : ScalarIndex) (m ell : ℕ) :
    derivativeAction a m ell*r=directionAction a*(boundaryCore ell-boundaryCore m) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change (SourceNativeCutoffContact.thetaDerivative (scalarDirection a) m ell x:ℂ) • (r f x)=
    (directionWeight a x:ℂ) • (boundaryCore ell f x-boundaryCore m f x)
  rw [radius_point,boundary_point,boundary_point]
  have h := congrArg (fun t : ℝ => (t:ℂ)) (original_radial_derivative_peaks a m ell x)
  push_cast at h
  simp only [smul_smul,←sub_smul]
  congr 1
  push_cast
  exact (mul_comm _ _).trans h
private theorem inverse_radius_end : inverseAction*r=(1:End) := by
  apply LinearMap.ext
  exact inverse_radius_action
private theorem derivative_boundary (a : ScalarIndex) (m ell : ℕ) :
    derivativeAction a m ell=directionAction a*(boundaryCore ell-boundaryCore m)*inverseAction := by
  have h := congrArg (fun A : End => A*inverseAction) (derivative_radius a m ell)
  have hr : r*inverseAction=(1:End) := by
    have hc : Commute r inverseAction := by
      apply LinearMap.ext
      intro f
      apply DFunLike.ext
      intro x
      change r (inverseAction f) x=inverseAction (r f) x
      rw [radius_point]
      change (radius x:ℂ) • ((reciprocal x:ℂ) • f x)=inverseAction (r f) x
      change _=(reciprocal x:ℂ) • r f x
      rw [radius_point]
      exact smul_comm _ _ _
    rw [hc.eq,inverse_radius_end]
  rw [mul_assoc,hr,mul_one] at h
  exact h

/-- One bounded scalar reader generates all seventy native forcing rows. -/
def gradientInput (m ell : ℕ) (F : Index) (z : ℂ) (g : diagonal.domain) : H :=
  (boundaryOperator ell-boundaryOperator m-relativeTail m ell) (finiteResolvent F z (g:H))-
    (boundaryOperator ell-boundaryOperator m) (inverseRadius (finiteResolvent F z (radiusSource g:H)))

def nativeEnergy (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  ∑ a : ScalarIndex,‖embed (nativeVector m ell F z hz g a)‖^2

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem source_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g:H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)
private theorem radius_source_embed (g : diagonal.domain) : embed (r (coreEquiv.symm g))=(radiusSource g:H) := rfl

private theorem native_vector_core (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain)
    (a : ScalarIndex) : embed (nativeVector m ell F z hz g a)=directionOperator a (gradientInput m ell F z g) := by
  let q := resolventCore F z hz (coreEquiv.symm g)
  let t := resolventCore F z hz (r (coreEquiv.symm g))
  let B : End := boundaryCore ell-boundaryCore m
  have hq : embed q=finiteResolvent F z (g:H) := by rw [resolvent_embed,source_embed]
  have ht : embed t=finiteResolvent F z (radiusSource g:H) := by rw [resolvent_embed,radius_source_embed]
  have hc : Commute (thetaAction m ell) (directionAction a) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro x
    rw [thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
    exact smul_comm (SourceNativeCutoffContact.theta m ell x:ℂ) (directionWeight a x:ℂ) (f x)
  have hB (f : QuantumTest) : (boundaryOperator ell-boundaryOperator m) (embed f)=embed (B f) := by
    simp only [sub_apply,boundary_core,B,LinearMap.sub_apply,map_sub]
  have hg : gradientInput m ell F z g=embed (B q-thetaAction m ell q-B (inverseAction t)) := by
    unfold gradientInput
    rw [←hq,←ht,sub_apply,hB,theta_core,inverse_core,hB]
    rw [map_sub,map_sub]
  rw [hg,original_direction_core]
  apply congrArg embed
  have h1 := LinearMap.congr_fun (derivative_radius a m ell) q
  have h2 := LinearMap.congr_fun (derivative_boundary a m ell) t
  have h3 := LinearMap.congr_fun hc.eq q
  change derivativeAction a m ell (r q)=directionAction a (B q) at h1
  change derivativeAction a m ell t=directionAction a (B (inverseAction t)) at h2
  change thetaAction m ell (directionAction a q)=directionAction a (thetaAction m ell q) at h3
  change derivativeAction a m ell (r q-t)-thetaAction m ell (directionAction a q)=_
  rw [map_sub,h1,h2,h3,map_sub,map_sub]
  abel

private theorem native_energy_bound (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    nativeEnergy m ell F z hz g≤(1/4:ℝ)*‖gradientInput m ell F z g‖^2 := by
  simp only [nativeEnergy,native_vector_core]
  rw [original_direction_energy]
  nlinarith only [sq_nonneg ‖inverseRadius (gradientInput m ell F z g)‖]
private theorem boundary_inverse (n : ℕ) : Commute (boundaryOperator n) inverseRadius := by
  have hQ : Commute sourceComplement inverseRadius := by
    unfold sourceComplement
    exact (Commute.one_left _).sub_left (Commute.refl _)
  exact (((Commute.refl inverseRadius).mul_left (hQ.pow_left n)).smul_left (n+1:ℂ))
private theorem inverse_norm : ‖inverseRadius‖≤1 := by
  unfold inverseRadius
  exact GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem three_square (x y z : H) : ‖x-y-z‖^2≤3*(‖x‖^2+‖y‖^2+‖z‖^2) := by
  have h := (norm_sub_le (x-y) z).trans (add_le_add (norm_sub_le x y) (le_refl _))
  have hp := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith only [hp,sq_nonneg (‖x‖-‖y‖),sq_nonneg (‖x‖-‖z‖),sq_nonneg (‖y‖-‖z‖)]
private theorem native_three_bound (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    nativeEnergy m ell F z hz g≤
      ‖(boundaryOperator ell-boundaryOperator m) (finiteResolvent F z (g:H))‖^2+
      ‖relativeTail m ell (finiteResolvent F z (g:H))‖^2+
      ‖(boundaryOperator ell-boundaryOperator m) (finiteResolvent F z (radiusSource g:H))‖^2 := by
  let x := (boundaryOperator ell-boundaryOperator m) (finiteResolvent F z (g:H))
  let y := relativeTail m ell (finiteResolvent F z (g:H))
  let t := (boundaryOperator ell-boundaryOperator m) (finiteResolvent F z (radiusSource g:H))
  have hc := ((boundary_inverse ell).sub_left (boundary_inverse m)).eq
  have he : gradientInput m ell F z g=x-y-inverseRadius t := by
    unfold gradientInput
    change _=x-y-(inverseRadius*(boundaryOperator ell-boundaryOperator m)) (finiteResolvent F z (radiusSource g:H))
    rw [←hc]
    rfl
  have hb := native_energy_bound m ell F z hz g
  rw [he] at hb
  have hs := three_square x y (inverseRadius t)
  have hi := (inverseRadius.le_opNorm t).trans
    ((mul_le_mul_of_nonneg_right inverse_norm (norm_nonneg t)).trans_eq (one_mul _))
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  change _≤‖x‖^2+‖y‖^2+‖t‖^2
  nlinarith only [hb,hs,hi2,sq_nonneg ‖x‖,sq_nonneg ‖y‖,sq_nonneg ‖t‖]

private theorem line_nonreal (μ : ℝ) (hμ : 0<μ) (w : ℝ) : (line μ w).im≠0 := by
  simpa only [line_im] using hμ.ne'

/-- The actual seventy-column energy is measurable before applying the fixed source filter. -/
theorem actual_radius_native_energy_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (nativeEnergy m ell F (line μ w) (line_nonreal μ hμ w) g)) := by
  simp only [nativeEnergy,native_vector_core]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hg : Continuous (fun w : ℝ => gradientInput m ell F (line μ w) g) := by
    unfold gradientInput
    exact (((boundaryOperator ell-boundaryOperator m-relativeTail m ell).continuous.comp (hr.clm_apply continuous_const)).sub
      ((boundaryOperator ell-boundaryOperator m).continuous.comp (inverseRadius.continuous.comp (hr.clm_apply continuous_const))))
  apply Measurable.ennreal_ofReal
  exact Finset.measurable_sum Finset.univ (fun a _ => ((directionOperator a).continuous.comp hg).norm.pow 2 |>.measurable)

/-- Every native forcing row is paid at one common cutoff by the actual two fixed resolvent inputs. -/
theorem actual_radius_native_energy_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (nativeEnergy m ell F (line μ w) (line_nonreal μ hμ w) g))≤ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨NX,hX⟩ := actual_boundary_difference_common_tail μ hμ (g:H) (ε/3) (by positivity)
  obtain ⟨NY,hY⟩ := actual_theta_full_frequency_tail μ hμ g (ε/3) (by positivity)
  obtain ⟨NZ,hZ⟩ := actual_boundary_difference_common_tail μ hμ (radiusSource g:H) (ε/3) (by positivity)
  refine ⟨max NX (max NY NZ),fun m hm ell hml => ?_⟩
  filter_upwards [hX m (by omega) ell hml,hY m (by omega) ell hml,hZ m (by omega) ell hml] with F hxf hy hzf
  have hx := hxf false
  have hz := hzf false
  simp only [actualFrequency,Bool.false_eq_true,ite_false] at hx hz
  let X := fun w : ℝ => ENNReal.ofReal (‖(boundaryOperator ell-boundaryOperator m) (finiteResolvent F (line μ w) (g:H))‖^2)
  let Y := fun w : ℝ => ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2)
  let Z := fun w : ℝ => ENNReal.ofReal (‖(boundaryOperator ell-boundaryOperator m) (finiteResolvent F (line μ w) (radiusSource g:H))‖^2)
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have my : Measurable Y := (((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  have mz : Measurable Z := (((boundaryOperator ell-boundaryOperator m).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ w : ℝ,X w+Y w+Z w := by
      apply lintegral_mono
      intro w
      change ENNReal.ofReal (nativeEnergy m ell F (line μ w) (line_nonreal μ hμ w) g)≤_
      exact (ENNReal.ofReal_le_ofReal (native_three_bound m ell F (line μ w) (line_nonreal μ hμ w) g)).trans
        (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl))
    _ = (∫⁻ w : ℝ,X w)+(∫⁻ w : ℝ,Y w)+(∫⁻ w : ℝ,Z w) := by
      rw [lintegral_add_right _ mz,lintegral_add_right _ my]
    _ ≤ ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3) :=
      add_le_add (add_le_add hx hy) hz
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

private theorem native_inverse (v : Ambient) : Commute (covariantMomentum v) inverseVolumeAction := by
  have h := SourceHamiltonianVolume.native_momentum_volume v
  have hVU : Commute inverseVolumeAction SourceCoframeVolume.volumeAction := by
    unfold inverseVolumeAction
    exact SourceHamiltonianVolume.real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (SourceCoframeVolume.volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold inverseVolumeAction
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem native_row_pair (a : ScalarIndex) (p f : QuantumTest) :
    sourcePair p (GaussMomentumAdjoint.adjoint (scalarDirection a) (multiply scalarWeight scalarWeight_smooth f))=
      (-(sourceTime 0:ℂ))*sourcePair (covariantMomentum (scalarDirection a) (inverseVolumeAction p)) f := by
  rw [GaussNativeForm.adjoint_pair,weight_inverse,LinearMap.smul_apply]
  rw [show sourcePair (covariantMomentum (scalarDirection a) p) ((-(sourceTime 0:ℂ)) • inverseVolumeAction f)=
      (-(sourceTime 0:ℂ))*sourcePair (covariantMomentum (scalarDirection a) p) (inverseVolumeAction f) by
        simp only [sourcePair,map_smul,inner_smul_right]]
  have hp : sourcePair (covariantMomentum (scalarDirection a) p) (inverseVolumeAction f)=
      sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) p)) f := multiply_pair _ _ _ _
  have hc := LinearMap.congr_fun (native_inverse (scalarDirection a)).eq p
  change covariantMomentum (scalarDirection a) (inverseVolumeAction p)=
    inverseVolumeAction (covariantMomentum (scalarDirection a) p) at hc
  rw [hp,←hc]


private theorem gram_bound {ι : Type*} [Fintype ι] (p q : ι → QuantumTest) :
    ‖∑ a,sourcePair (p a) (q a)‖^2 ≤ (∑ a,‖embed (p a)‖^2)*(∑ a,‖embed (q a)‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ι) (fun a => sourcePair (p a) (q a))).trans
    (Finset.sum_le_sum (fun a _ => norm_inner_le_norm (𝕜 := ℂ) (embed (p a)) (embed (q a))))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖embed (p a)‖) (fun a => ‖embed (q a)‖))

private theorem young_square (a p e η : ℝ) (hp : 0≤p) (he : 0≤e) (hη : 0<η)
    (hs : a^2≤p*e) : a≤η*p+e/(4*η) := by
  have hi : 4*(η*p)*(e/(4*η))=p*e := by field_simp [hη.ne']
  have hr : 0≤η*p+e/(4*η) := add_nonneg (mul_nonneg hη.le hp) (div_nonneg he (by positivity))
  nlinarith only [hs,hi,hr,sq_nonneg (η*p-e/(4*η))]


private theorem native_pair (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (p : QuantumTest) :
    sourcePair p (nativeDivergence m ell F z hz g)=
      (Complex.I*(sourceTime 0:ℂ))*(∑ a : ScalarIndex,sourcePair
        (covariantMomentum (scalarDirection a) (inverseVolumeAction p)) (nativeVector m ell F z hz g a)) := by
  unfold nativeDivergence
  simp only [sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  change (-Complex.I)*(∑ a : ScalarIndex,sourcePair p
    (GaussMomentumAdjoint.adjoint (scalarDirection a) (multiply scalarWeight scalarWeight_smooth (nativeVector m ell F z hz g a))))=_
  simp_rw [native_row_pair]
  rw [←Finset.mul_sum]
  simp only [sourcePair]
  ring

/-- The exact response's positive scalar slot pays the complete native divergence with its already-generated small energy. -/
theorem actual_radius_native_pair_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain)
    (η : ℝ) (hη : 0<η) :
    ‖sourcePair (radiusResponseCore m ell F z hz g) (nativeDivergence m ell F z hz g)‖ ≤
      η*((sourceTime 0)^2*scalarForm (inverseVolumeAction (radiusResponseCore m ell F z hz g)))+
        nativeEnergy m ell F z hz g/(4*η) := by
  let p := radiusResponseCore m ell F z hz g
  have hs : ‖sourcePair p (nativeDivergence m ell F z hz g)‖^2≤
      ((sourceTime 0)^2*scalarForm (inverseVolumeAction p))*nativeEnergy m ell F z hz g := by
    rw [native_pair,norm_mul,mul_pow]
    have hn : ‖Complex.I*(sourceTime 0:ℂ)‖^2=(sourceTime 0)^2 := by
      simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [hn]
    exact (mul_le_mul_of_nonneg_left (gram_bound
      (fun a => covariantMomentum (scalarDirection a) (inverseVolumeAction p))
      (fun a => nativeVector m ell F z hz g a)) (sq_nonneg (sourceTime 0))).trans_eq (by
        simp only [scalarForm,nativeEnergy,mul_assoc])
  have hp : 0≤(sourceTime 0)^2*scalarForm (inverseVolumeAction p) := by
    unfold scalarForm
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have he : 0≤nativeEnergy m ell F z hz g := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact young_square _ _ _ η hp he hη hs

end LowEnergy.SourceClockRadiusResponseNativeBudget
