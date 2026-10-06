import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockReflectedForm
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceLowerStripRadiusPrice
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceRadiusHalfSourceBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceRadiusHalfContactTail
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceRadiusHalfKineticTime
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceSelfAdjointTimeBalance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockWindowTime
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumScalarChart
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceKineticTranspose SourceDilationRemainder
open SourceClockAcceleration SourceClockReflectedForm SourceRadiusHalfWindow SourceRadiusHalfHamiltonian
open SourceRadiusHalfResponse SourceRadiusHalfKinetic SourceRadiusHalfSourceBudget SourceRadiusHalfContactTail
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceResolventBandLimit FullYSourceResolventGraphSplice
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction clockBulk dilation

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem half_pair (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (halfAction m ell q)=sourcePair (halfAction m ell p) q := multiply_pair _ _ _ _
private theorem real_half (m ell : ℕ) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) (halfAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z:ℂ) (halfCoefficient m ell z:ℂ) (f z)
private theorem local_half (m ell : ℕ) (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hA : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val) : Commute (localMultiplier A hA) (halfAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (A z) (halfCoefficient m ell z:ℂ) (f z)
private theorem contact_volume (m ell : ℕ) (v : Ambient) : Commute (halfContact v m ell) volumeAction :=
  (scalar_volume_commutes _ _).mul_left (SourceHamiltonianVolume.real_volume _ _)
private theorem radial_volume (m ell : ℕ) : Commute (radialAction m ell) volumeAction := by
  unfold radialAction radialTerm
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  exact ((SourceHamiltonianVolume.native_adjoint_volume (scalarDirection a)).mul_left
    ((SourceHamiltonianVolume.real_volume _ _).mul_left (contact_volume m ell _))).add_left
      ((contact_volume m ell _).mul_left ((SourceHamiltonianVolume.real_volume _ _).mul_left
        (SourceHamiltonianVolume.native_momentum_volume (scalarDirection a))))

private theorem volume_half (m ell : ℕ) : Commute volumeAction (halfAction m ell) := real_half _ _ _ _
private theorem inverse_half (m ell : ℕ) : Commute inverseVolumeAction (halfAction m ell) := real_half _ _ _ _

private theorem dilation_half (m ell : ℕ) : Commute dilation (halfAction m ell) := by
  have hh : diagonalAction*halfAction m ell-halfAction m ell*diagonalAction=radialAction m ell := by
    rw [original_diagonal_current,add_sub_cancel_left]
  have hu := (volume_half m ell).eq
  have hr := (radial_volume m ell).eq
  have hc : (diagonalAction*volumeAction-volumeAction*diagonalAction)*halfAction m ell-
      halfAction m ell*(diagonalAction*volumeAction-volumeAction*diagonalAction)=0 := by
    linear_combination (norm := noncomm_ring) diagonalAction*hu-hu*diagonalAction+hh*volumeAction-volumeAction*hh+hr
  rw [SourceHamiltonianVolume.full_source_volume_current,smul_mul_assoc,mul_smul_comm,←smul_sub] at hc
  have hn : (-3*Complex.I*(sourceTime 0:ℂ)/4)≠0 := by
    apply div_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast lapse_pos.ne')
    · norm_num
  exact sub_eq_zero.mp ((smul_eq_zero.mp hc).resolve_left hn)

private theorem gauge_contact_zero (m ell : ℕ) (v : Ambient) (hv : v.1=0) : halfContact v m ell=(0:End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((-Complex.I)*(SourceRadiusBandGradient.derivative v m ell z:ℂ)) • ((chainFactor m ell z:ℂ) • f z)=0
  simp [SourceRadiusBandGradient.derivative,GaussRadialMomentum.radialDerivative,hv]
private theorem gauge_half (m ell : ℕ) : Commute gaugeKinetic (halfAction m ell) := by
  have hp (i : Fin 3) (a : LieIndex) : Commute (covariantMomentum (gaugeDirection i a)) (halfAction m ell) := by
    apply LinearMap.ext
    intro f
    simpa only [Module.End.mul_apply,gauge_contact_zero m ell (gaugeDirection i a) rfl,LinearMap.zero_apply,add_zero]
      using original_half_native_contact (gaugeDirection i a) m ell f
  have ha (i : Fin 3) (a : LieIndex) : Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)) (halfAction m ell) := by
    apply LinearMap.ext
    intro f
    simpa only [Module.End.mul_apply,gauge_contact_zero m ell (gaugeDirection i a) rfl,LinearMap.zero_apply,add_zero]
      using original_half_adjoint_contact m ell (gaugeDirection i a) f
  unfold gaugeKinetic
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  exact (ha i a).mul_left ((real_half m ell _ _).mul_left (hp j a))
private theorem matter_half (m ell : ℕ) : Commute GaussMatterCore.matterAction (halfAction m ell) := by
  unfold GaussMatterCore.matterAction
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro b _
  exact local_half m ell _ _

private def bracket (H : End) : End →ₗ[ℂ] End where
  toFun A := H*A-A*H
  map_add' A B := by noncomm_ring
  map_smul' c A := by simp only [mul_smul_comm,smul_mul_assoc,smul_sub];rfl
private theorem bracket_product (H A B : End) : bracket H (A*B)=bracket H A*B+A*bracket H B := by
  change H*(A*B)-(A*B)*H=(H*A-A*H)*B+A*(H*B-B*H)
  noncomm_ring
private theorem bracket_zero {A B : End} (h : Commute A B) : bracket B A=0 := by
  change B*A-A*B=0
  rw [h.eq,sub_self]

private theorem kinetic_half (m ell : ℕ) :
    bracket (halfAction m ell) kineticAction= -radialAction m ell := by
  have hh := original_diagonal_current m ell
  rw [original_action_split] at hh
  have hm := (matter_half m ell).eq
  have hl := (real_half m ell localPotential local_smooth).eq
  have hs := (real_half m ell spatialPotential spatial_smooth).eq
  change localAction*halfAction m ell=halfAction m ell*localAction at hl
  change spatialAction*halfAction m ell=halfAction m ell*spatialAction at hs
  change halfAction m ell*kineticAction-kineticAction*halfAction m ell=_
  linear_combination (norm := noncomm_ring) -hh+hm+hl+hs

private theorem clock_half_current (m ell : ℕ) :
    bracket (halfAction m ell) clockBulk=(sourceTime 0:ℂ) • (volumeAction*radialAction m ell) := by
  have hD := bracket_zero (dilation_half m ell)
  have hU := bracket_zero (volume_half m ell)
  have hG := bracket_zero (gauge_half m ell)
  have hL : bracket (halfAction m ell) localAction=0 := bracket_zero (real_half m ell localPotential local_smooth)
  have hS : bracket (halfAction m ell) spatialAction=0 := bracket_zero (real_half m ell spatialPotential spatial_smooth)
  unfold clockBulk
  rw [SourceOriginalKineticSquare.symmetric_scale_source]
  simp only [map_add,map_sub,map_smul,bracket_product,hD,hU,hG,hL,hS,kinetic_half,
    mul_zero,zero_mul,zero_add,add_zero,smul_zero,neg_mul,mul_neg]
  rw [(radial_volume m ell).eq]
  module

private theorem half_clock_curvature (m ell : ℕ) :
    halfAction m ell*(clockBulk*halfAction m ell-halfAction m ell*clockBulk)-
      (clockBulk*halfAction m ell-halfAction m ell*clockBulk)*halfAction m ell=
      (-(sourceTime 0:ℂ)) • (volumeAction*curvature m ell) := by
  have hh : clockBulk*halfAction m ell-halfAction m ell*clockBulk=
      (-(sourceTime 0:ℂ)) • (volumeAction*radialAction m ell) := by
    have h := clock_half_current m ell
    change halfAction m ell*clockBulk-clockBulk*halfAction m ell=_ at h
    rw [←neg_sub (halfAction m ell*clockBulk),h]
    module
  rw [hh]
  simp only [mul_smul_comm,smul_mul_assoc,←smul_sub]
  congr 1
  unfold curvature
  linear_combination (norm := noncomm_ring) -(volume_half m ell).eq*radialAction m ell

/-- Unweighted native70 contacts on the original source core; no volume operator is hidden here. -/
def freeContact (m ell : ℕ) (p q : QuantumTest) : ℂ :=
  ∑ a : ScalarIndex,sourcePair (halfContact (scalarDirection a) m ell p) (halfContact (scalarDirection a) m ell q)

private theorem root_volume_pair (p q : QuantumTest) :
    sourcePair (inverseRootAction (volumeAction p)) (inverseRootAction q)=sourcePair p q := by
  have hR (a b : QuantumTest) : sourcePair (inverseRootAction a) b=sourcePair a (inverseRootAction b) :=
    (multiply_pair inverseRootVolume inverse_root_volume_smooth a b).symm
  rw [hR,inverse_root_square]
  have hi : inverseVolumeAction (volumeAction p)=p := by
    have hc : Commute inverseVolumeAction volumeAction := SourceHamiltonianVolume.real_volume _ _
    exact (LinearMap.congr_fun hc.eq p).trans (volume_inverse p)
  have h := multiply_pair reciprocalVolume reciprocal_volume_smooth (volumeAction p) q
  change sourcePair (volumeAction p) (inverseVolumeAction q)=sourcePair (inverseVolumeAction (volumeAction p)) q at h
  rw [hi] at h
  exact h
private theorem contact_volume_pair (m ell : ℕ) (p q : QuantumTest) :
    contactGram m ell (volumeAction p) q=freeContact m ell p q := by
  unfold contactGram freeContact weightedContact
  apply Finset.sum_congr rfl
  intro a _
  simp only [Module.End.mul_apply]
  rw [show halfContact (scalarDirection a) m ell (volumeAction p)=
    volumeAction (halfContact (scalarDirection a) m ell p) from LinearMap.congr_fun (contact_volume m ell _).eq p]
  exact root_volume_pair _ _

/-- Full complex polarization pays the original clock half-window curvature with the free native70 contact Gram. -/
theorem original_clock_half_curvature (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p ((halfAction m ell*(clockBulk*halfAction m ell-halfAction m ell*clockBulk)-
      (clockBulk*halfAction m ell-halfAction m ell*clockBulk)*halfAction m ell) q)=
      (sourceTime 0:ℂ)^2*freeContact m ell p q := by
  rw [half_clock_curvature,LinearMap.smul_apply]
  change sourcePair p ((-(sourceTime 0:ℂ)) • volumeAction (curvature m ell q))=_
  have hU : sourcePair p (volumeAction (curvature m ell q))=sourcePair (volumeAction p) (curvature m ell q) :=
    multiply_pair _ _ _ _
  simp only [sourcePair,map_smul,inner_smul_right]
  change (-(sourceTime 0:ℂ))*sourcePair p (volumeAction (curvature m ell q))=_
  rw [hU,original_half_curvature,contact_volume_pair]
  ring

/-- The whole clock form has a free, positive half-window IMS correction on the same two original legs. -/
theorem original_clock_half_ims (m ell : ℕ) (p q : QuantumTest) :
    sourcePair (halfAction m ell p) (clockBulk (halfAction m ell q))=
      (1/2:ℂ)*(sourcePair (halfAction m ell (halfAction m ell p)) (clockBulk q)+
        sourcePair p (clockBulk (halfAction m ell (halfAction m ell q))))+
      ((sourceTime 0:ℂ)^2/2)*freeContact m ell p q := by
  have h := original_clock_half_curvature m ell p q
  have he : halfAction m ell*(clockBulk*halfAction m ell-halfAction m ell*clockBulk)-
      (clockBulk*halfAction m ell-halfAction m ell*clockBulk)*halfAction m ell=
      (2:ℂ) • (halfAction m ell*clockBulk*halfAction m ell)-
        halfAction m ell*halfAction m ell*clockBulk-clockBulk*halfAction m ell*halfAction m ell := by
    simp only [two_smul]
    noncomm_ring
  rw [he] at h
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,sourcePair,map_sub,map_smul,
    inner_sub_right,inner_smul_right] at h
  change (2:ℂ)*sourcePair p (halfAction m ell (clockBulk (halfAction m ell q)))-
    sourcePair p (halfAction m ell (halfAction m ell (clockBulk q)))-
    sourcePair p (clockBulk (halfAction m ell (halfAction m ell q)))=_ at h
  rw [half_pair,half_pair,half_pair] at h
  linear_combination (1/2:ℂ)*h

private theorem free_contact_real (m ell : ℕ) (f : QuantumTest) :
    (freeContact m ell f f).re=∑ a : ScalarIndex,‖embed (halfContact (scalarDirection a) m ell f)‖^2 := by
  unfold freeContact
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [sourcePair] using! inner_self_eq_norm_sq (𝕜 := ℂ) (embed (halfContact (scalarDirection a) m ell f))

/-- Literal IMS difference, rather than a supplied energy or graph bound. -/
def clockError (m ell : ℕ) (f : QuantumTest) : ℝ :=
  (sourcePair (halfAction m ell f) (clockBulk (halfAction m ell f))).re-
    (1/2:ℝ)*(sourcePair (halfAction m ell (halfAction m ell f)) (clockBulk f)+
      sourcePair f (clockBulk (halfAction m ell (halfAction m ell f)))).re

private theorem clock_error_source (m ell : ℕ) (f : QuantumTest) :
    clockError m ell f=(sourceTime 0)^2/2*(freeContact m ell f f).re := by
  unfold clockError
  rw [original_clock_half_ims]
  have hc : (sourceTime 0:ℂ)^2/2=(((sourceTime 0)^2/2:ℝ):ℂ) := by push_cast;rfl
  rw [hc]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  norm_num

private theorem actual_clock_error (advanced : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (w : ℝ) :
    clockError m ell (state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g)=
      (sourceTime 0)^2/2*frequencyError advanced m ell F μ hμ g w := by
  rw [clock_error_source,free_contact_real]
  unfold frequencyError causalPoint
  simp only [original_half_native_contact,add_sub_cancel_left]

/-- All frequencies and both actual causal legs pay the new clock IMS correction by the original fixed source norm. -/
theorem actual_clock_error_full_frequency (advanced : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (clockError m ell
      (state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g)))  ≤
      ENNReal.ofReal ((3*(sourceTime 0)^2/(8*(m+1:ℝ)))*(Real.pi/μ*‖(g:H)‖^2)) := by
  have hc : 0 ≤ (sourceTime 0)^2/2 := by positivity
  conv_lhs =>
    enter [2,w]
    rw [actual_clock_error advanced m ell F μ hμ g w,ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h := mul_le_mul (le_refl (ENNReal.ofReal ((sourceTime 0)^2/2)))
    (actual_half_contact_full_frequency advanced m ell F μ hμ g) bot_le bot_le
  rw [←ENNReal.ofReal_mul hc] at h
  exact h.trans_eq (congrArg ENNReal.ofReal (by field_simp [hμ.ne'];ring))

/-- One source-generated lower window pays the clock contact for every upper window, every original F and both causal legs. -/
theorem actual_clock_error_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell : ℕ,∀ F : Index,∀ advanced : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (clockError m ell
        (state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g))) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let c : ℝ := (sourceTime 0)^2/2
  have hc : 0<c := div_pos (sq_pos_of_pos lapse_pos) (by norm_num)
  obtain ⟨N,hN⟩ := actual_half_contact_common_tail μ hμ g (ε/c) (div_pos hε hc)
  refine ⟨N,fun m hm ell F advanced => ?_⟩
  conv_lhs =>
    enter [2,w]
    rw [actual_clock_error advanced m ell F μ hμ g w,ENNReal.ofReal_mul hc.le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h := mul_le_mul (le_refl (ENNReal.ofReal c)) (hN m hm ell F advanced) bot_le bot_le
  rw [←ENNReal.ofReal_mul hc.le,mul_div_cancel₀ _ hc.ne'] at h
  exact h

private theorem clock_current_pair (f g : QuantumTest) :
    sourcePair f (clockCurrent g)=sourcePair (clockCurrent f) g := by
  have hV (a b : QuantumTest) : sourcePair a (inverseVolumeAction b)=sourcePair (inverseVolumeAction a) b :=
    multiply_pair _ _ _ _
  rw [original_clock_current]
  simp only [LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,sourcePair,map_smul,map_add,
    inner_smul_left,inner_smul_right,inner_add_left,inner_add_right,map_div₀,map_mul,map_ofNat,Complex.conj_ofReal]
  change _*(sourcePair f (inverseVolumeAction (dilation g))+sourcePair f (dilation (inverseVolumeAction g)))=
    _*(sourcePair (inverseVolumeAction (dilation f)) g+sourcePair (dilation (inverseVolumeAction f)) g)
  rw [hV,SourceCoframeDilation.dilation_pair,SourceCoframeDilation.dilation_pair,←hV]
  ring
private theorem clock_current_real (f : QuantumTest) : (sourcePair f (clockCurrent f)).im=0 := by
  have h := congrArg Complex.im (GaussNativeForm.pair_conjugate f (clockCurrent f))
  rw [←clock_current_pair] at h
  simp only [Complex.conj_im] at h
  linarith
private theorem inverse_real (f : QuantumTest) : (sourcePair f (inverseVolumeAction f)).im=0 := by
  have hp : sourcePair f (inverseVolumeAction f)=sourcePair (inverseVolumeAction f) f := multiply_pair _ _ _ _
  have h := congrArg Complex.im (GaussNativeForm.pair_conjugate f (inverseVolumeAction f))
  rw [←hp] at h
  simp only [Complex.conj_im] at h
  linarith

private theorem completed_pair_source (f : QuantumTest) :
    (sourcePair f (completedAcceleration f)).re=
      2*(sourcePair (diagonalAction f) (clockCurrent f)).im+
      (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) (diagonalAction f)).re := by
  have hJ := clock_current_pair f (diagonalAction f)
  have hH := diagonalAction_pair f (clockCurrent f)
  have hV : sourcePair f (inverseVolumeAction (diagonalAction f))=
      sourcePair (inverseVolumeAction f) (diagonalAction f) := multiply_pair _ _ _ _
  have hVH := diagonalAction_pair f (inverseVolumeAction f)
  have hconj := GaussNativeForm.pair_conjugate (diagonalAction f) (clockCurrent f)
  have hconjV := GaussNativeForm.pair_conjugate (inverseVolumeAction f) (diagonalAction f)
  unfold completedAcceleration clockAcceleration
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_add,map_sub,map_smul,inner_add_right,inner_sub_right,inner_smul_right]
  change (((-Complex.I)*(sourcePair f (diagonalAction (clockCurrent f))-
    sourcePair f (clockCurrent (diagonalAction f))))+
    ((sourceTime 0:ℂ)/4)*(sourcePair f (inverseVolumeAction (diagonalAction f))+
      sourcePair f (diagonalAction (inverseVolumeAction f)))).re=_
  rw [hJ,hH,hV,hVH,←hconj,←hconjV]
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.div_re,Complex.div_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re]
  norm_num
  simp only [sourcePair]
  ring

/-- The current keeps the complete raised defect, fixed input, real frequency and damping terms on this same source leg. -/
def sourcePrice (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  let q := state F z hz g
  let f := halfAction m ell q
  let u := halfAction m ell (coreEquiv.symm g)+raisedDefect F (halfAction m ell) q
  2*(sourcePair u (clockCurrent f)).im-2*z.im*(sourcePair f (clockCurrent f)).re+
    (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) u).re+
    (sourceTime 0/2)*z.re*(sourcePair f (inverseVolumeAction f)).re+
    (sourceTime 0)^2*spinForm (inverseVolumeAction f)+
    (sourceTime 0)^2*densityForm (inverseVolumeAction f)-
    sourceTime 0*gaugeForm (inverseVolumeAction f)-sourceTime 0*spatialForm (inverseVolumeAction f)

/-- The full actual half-window source equation generates this nonnegative clock/radius responsibility; no graph or tail is supplied. -/
theorem actual_clock_source_price (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    sourcePrice F m ell z hz g=
      (sourceTime 0)^2/4*coframeGram (inverseVolumeAction (halfAction m ell (state F z hz g)))+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction (halfAction m ell (state F z hz g)))+
      2*(sourceTime 0)^2*radiusForm (halfAction m ell (state F z hz g)) := by
  let q := state F z hz g
  let f := halfAction m ell q
  let u := halfAction m ell (coreEquiv.symm g)+raisedDefect F (halfAction m ell) q
  have he : diagonalAction f=u+z • f := by
    have h := actual_raised_source F z hz g (halfAction m ell)
    change diagonalAction f=halfAction m ell (coreEquiv.symm g)+z • f+raisedDefect F (halfAction m ell) q at h
    rw [h]
    dsimp only [u]
    abel
  have hb := completed_pair_source f
  rw [he] at hb
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_smul_left,inner_add_right,inner_smul_right] at hb
  change (sourcePair f (completedAcceleration f)).re=
    2*(sourcePair u (clockCurrent f)+(starRingEnd ℂ z)*sourcePair f (clockCurrent f)).im+
      (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) u+z*sourcePair (inverseVolumeAction f) f).re at hb
  have hv : sourcePair (inverseVolumeAction f) f=sourcePair f (inverseVolumeAction f) := (multiply_pair _ _ _ _).symm
  rw [hv] at hb
  simp only [Complex.add_im,Complex.add_re,Complex.mul_im,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    clock_current_real,inverse_real,mul_zero,sub_zero] at hb
  have hs := original_completed_square_form f
  unfold sourcePrice
  change _=(sourceTime 0)^2/4*coframeGram (inverseVolumeAction f)+
    (sourceTime 0)^2/2*scalarForm (inverseVolumeAction f)+2*(sourceTime 0)^2*radiusForm f
  change 2*(sourcePair u (clockCurrent f)).im-2*z.im*(sourcePair f (clockCurrent f)).re+
    (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) u).re+
    (sourceTime 0/2)*z.re*(sourcePair f (inverseVolumeAction f)).re+
    (sourceTime 0)^2*spinForm (inverseVolumeAction f)+
    (sourceTime 0)^2*densityForm (inverseVolumeAction f)-
    sourceTime 0*gaugeForm (inverseVolumeAction f)-sourceTime 0*spatialForm (inverseVolumeAction f)=_
  linarith only [hb,hs]

private theorem density_nonnegative (f : QuantumTest) (z : SourceCoordinateSlice) : 0 ≤ (densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · have h := GaussBoundedMultiplier.weighted_square (fun N => GaussDensityCore.density N z)
      (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
    exact (sq_nonneg _).trans_eq h.symm
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem radius_floor (f : QuantumTest) : 3*‖embed f‖^2 ≤ radiusForm f := by
  let c : SourceCoordinateSlice → ℝ := fun z => 4*(GaussYukawaCoefficient.radius z)^2-1
  have hc : ContDiff ℝ ∞ c := (contDiff_const.mul (GaussYukawaCoefficient.radius_smooth.pow 2)).sub contDiff_const
  let A : End := multiply c (fun _ => hc.contDiffAt)
  have hr : radiusForm f=(sourcePair f (A f)).re := rfl
  have hpair : (sourcePair f (A f)).re=∫ z : SourceCoordinateSlice,(densityPair f (A f) z).re
      ∂GaussHistoryHilbert.configurationMeasure := by
    rw [sourcePair_integral]
    exact (integral_re (densityPair_integrable f (A f))).symm
  rw [hr,hpair,GaussBoundedMultiplier.norm_square_integral,←integral_const_mul]
  apply integral_mono ((densityPair_integrable f f).re.const_mul 3) (densityPair_integrable f (A f)).re
  intro z
  change 3*(densityPair f f z).re ≤ (densityPair f (A f) z).re
  have he : densityPair f (A f) z=(c z:ℂ)*densityPair f f z := inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hr := GaussRadialDomain.one_le_radius z
  have hc3 : 3 ≤ c z := by dsimp only [c];nlinarith only [hr]
  exact mul_le_mul_of_nonneg_right hc3 (density_nonnegative f z)

private theorem source_price_floor (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    6*(sourceTime 0)^2*‖embed (halfAction m ell (state F z hz g))‖^2 ≤ sourcePrice F m ell z hz g := by
  rw [actual_clock_source_price]
  have hc := original_coframe_gram_nonnegative (inverseVolumeAction (halfAction m ell (state F z hz g)))
  have hs : 0 ≤ scalarForm (inverseVolumeAction (halfAction m ell (state F z hz g))) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hr := mul_le_mul_of_nonneg_left (radius_floor (halfAction m ell (state F z hz g)))
    (by positivity : 0 ≤ 2*(sourceTime 0)^2)
  have hc' := mul_nonneg (show 0 ≤ (sourceTime 0)^2/4 by positivity) hc
  have hs' := mul_nonneg (show 0 ≤ (sourceTime 0)^2/2 by positivity) hs
  nlinarith only [hr,hc',hs']

private theorem weighted_young (a b η : ℝ) (hη : 0<η) : 2*a*b ≤ η*a^2+η⁻¹*b^2 := by
  calc
    _ ≤ (η^2*a^2+b^2)/η := by
      apply (le_div_iff₀ hη).mpr
      nlinarith only [sq_nonneg (η*a-b)]
    _=_ := by field_simp

/-- The actual first-radius moment is paid by the new literal clock source price and a freely small original norm term. -/
theorem actual_radius_clock_price (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    SourceRadiusPairedScalarPrice.radiusMoment m ell (finiteResolvent F z (g:H)) ≤
      η*‖finiteResolvent F z (g:H)‖^2+
      ((1+η⁻¹)/(6*(sourceTime 0)^2))*sourcePrice F m ell z hz g := by
  let q := state F z hz g
  have hq : embed q=finiteResolvent F z (g:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [←hq,original_radius_half_identity]
  have hinner : (sourcePair q (halfAction m ell q)).re ≤ ‖embed q‖*‖embed (halfAction m ell q)‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hy := weighted_young ‖embed q‖ ‖embed (halfAction m ell q)‖ η hη
  have hf := source_price_floor F m ell z hz g
  change 6*(sourceTime 0)^2*‖embed (halfAction m ell q)‖^2 ≤ sourcePrice F m ell z hz g at hf
  have hc : 0 ≤ (1+η⁻¹)/(6*(sourceTime 0)^2) := by positivity
  have hpaid := mul_le_mul_of_nonneg_left hf hc
  have hn : sourceTime 0≠0 := lapse_pos.ne'
  have he : ((1+η⁻¹)/(6*(sourceTime 0)^2))*(6*(sourceTime 0)^2*‖embed (halfAction m ell q)‖^2)=
      (1+η⁻¹)*‖embed (halfAction m ell q)‖^2 := by field_simp
  rw [he] at hpaid
  linarith only [hinner,hy,hpaid]

/-- Same-F, actual retarded or advanced clock-source responsibility on the complete frequency line. -/
def sourceBudget (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (sourcePrice F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g)

/-- Whole-frequency first-radius payment keeps the original causal source, with no regularity or uniform-F premise. -/
theorem actual_causal_radius_budget (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    (∫⁻ w : ℝ,ENNReal.ofReal (SourceRadiusPairedScalarPrice.radiusMoment m ell
      (finiteResolvent F (causalPoint advanced μ w) (g:H)))) ≤
      ENNReal.ofReal (η*(Real.pi/μ*‖(g:H)‖^2))+
      ENNReal.ofReal ((1+η⁻¹)/(6*(sourceTime 0)^2))*sourceBudget advanced m ell F μ hμ g := by
  have hc : 0 ≤ (1+η⁻¹)/(6*(sourceTime 0)^2) := by positivity
  have hn (w : ℝ) : ‖finiteResolvent F (causalPoint advanced μ w) (g:H)‖=
      ‖finiteResolvent F (line μ w) (g:H)‖ := by
    cases advanced
    · rfl
    · exact SourceInverseSourceLeg.actual_conjugate_leg_norm F (line μ w)
        (by simpa only [line_im] using hμ.ne') (g:H)
  have hm : Measurable (fun w : ℝ => ENNReal.ofReal (η*‖finiteResolvent F (line μ w) (g:H)‖^2)) :=
    (continuous_const.mul (((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const).norm.pow 2)).measurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (η*‖finiteResolvent F (line μ w) (g:H)‖^2)+
      ENNReal.ofReal ((1+η⁻¹)/(6*(sourceTime 0)^2))*
        ENNReal.ofReal (sourcePrice F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g) := by
      apply lintegral_mono
      intro w
      dsimp only
      have hp : 0 ≤ sourcePrice F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g :=
        (by positivity : 0 ≤ 6*(sourceTime 0)^2*‖embed (halfAction m ell (state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g))‖^2).trans
          (source_price_floor F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g)
      rw [←ENNReal.ofReal_mul hc,←ENNReal.ofReal_add (by positivity) (mul_nonneg hc hp)]
      have h := actual_radius_clock_price F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g η hη
      rw [hn] at h
      exact ENNReal.ofReal_le_ofReal h
    _=_ := by
      rw [lintegral_add_left hm]
      simp_rw [ENNReal.ofReal_mul hη.le]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have he := SourceActualResolventEnergy.actual_square_lintegral F μ hμ (g:H)
      have he' : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (g:H)‖^2))=
          ENNReal.ofReal (Real.pi/μ*‖(g:H)‖^2) := by simpa only [line,mul_comm] using he
      rw [he',←ENNReal.ofReal_mul hη.le]
      rfl

private theorem moment_nonnegative (m ell : ℕ) (x : H) :
    0 ≤ SourceRadiusPairedScalarPrice.radiusMoment m ell x := by
  have hp : 0 ≤ SourceRadiusPairedScalarPrice.radiusBand m ell := by
    unfold SourceRadiusPairedScalarPrice.radiusBand
    exact Finset.sum_nonneg (fun j _ => CStarAlgebra.pow_nonneg SourceRelativePowerTail.source_complement_nonnegative j)
  simpa only [SourceRadiusPairedScalarPrice.radiusMoment,RCLike.re_to_complex] using
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hp).re_inner_nonneg_right x

/-- No finite-reader norm enters the lower-strip source price. -/
def legPrice (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (η : ℝ) : ENNReal :=
  ENNReal.ofReal (η*(Real.pi/μ*‖(g:H)‖^2))+
    ENNReal.ofReal ((1+η⁻¹)/(6*(sourceTime 0)^2))*sourceBudget advanced m ell F μ hμ g

private theorem strip_source_price (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ENNReal.ofReal (SourceLowerStripRadiusPrice.stripEnergy advanced m ell F μ (g:H)) ≤
      legPrice advanced m ell F μ hμ g η := by
  have hn (w : ℝ) : 0 ≤ SourceLowerStripRadiusPrice.stripMoment advanced m ell F μ (g:H) w :=
    moment_nonnegative _ _ _
  have hle : ENNReal.ofReal (SourceLowerStripRadiusPrice.stripEnergy advanced m ell F μ (g:H)) ≤
      ∫⁻ w : ℝ,ENNReal.ofReal (SourceLowerStripRadiusPrice.stripMoment advanced m ell F μ (g:H) w) := by
    by_cases hi : Integrable (SourceLowerStripRadiusPrice.stripMoment advanced m ell F μ (g:H))
    · exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)).le
    · simp only [SourceLowerStripRadiusPrice.stripEnergy,integral_undef hi,ENNReal.ofReal_zero,zero_le]
  exact hle.trans (actual_causal_radius_budget advanced m ell F μ hμ g η hη)

/-- The original same-F paired radius cost consumes the two actual signed clock source prices on a lower strip. -/
theorem actual_paired_radius_clock_budget (m ell : ℕ) (F : Index) (ν μ : ℝ)
    (hν : 0<ν) (hδ : ν<μ) (g k : diagonal.domain) (ηg ηk : ℝ) (hηg : 0<ηg) (hηk : 0<ηk) :
    SourceRadiusClosedJointCost.pairedRadiusCost m ell F μ g k ≤
      ENNReal.ofReal (1/(4*Real.pi*(μ-ν)))*
        legPrice true m ell F ν hν k ηk*legPrice false m ell F ν hν g ηg := by
  have h := SourceLowerStripRadiusPrice.actual_lower_strip_paired_price m ell F ν μ hν hδ g k
  have hc : 0 ≤ 1/(4*Real.pi*(μ-ν)) := by positivity
  have hk : 0 ≤ SourceLowerStripRadiusPrice.stripEnergy true m ell F ν (k:H) :=
    integral_nonneg (fun _ => moment_nonnegative _ _ _)
  rw [ENNReal.ofReal_mul (mul_nonneg hc hk),ENNReal.ofReal_mul hc] at h
  apply h.trans
  have hp := mul_le_mul (strip_source_price true m ell F ν hν k ηk hηk)
    (strip_source_price false m ell F ν hν g ηg hηg) bot_le bot_le
  have hmul := mul_le_mul (le_refl (ENNReal.ofReal (1/(4*Real.pi*(μ-ν))))) hp bot_le bot_le
  simpa only [mul_assoc] using hmul

end LowEnergy.SourceClockWindowTime
