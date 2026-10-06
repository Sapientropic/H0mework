import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaCubicCurrent
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceYukawaMixedCurvature
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaMixedEndpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaMixedBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussHistoryHilbert SourceQuantumConfigurationHilbert
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPositiveBulkWard SourceScalarPairedTransport
open SourceClockYukawaCubicCurrent SourceClockYukawaHamiltonianCurrent SourceYukawaMixedCurvature
open SourceClockYukawaCurrent SourceRelativePowerTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] state fullAction compressionCore defectAction thetaAction resolventCore
  SourceClockYukawaHamiltonianCurrent.correctedCurrent

private theorem starNonreal (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

private theorem core_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore
  change embed (state F z hz (coreEquiv f))=_
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem finite_adjoint (F : Index) (z : ℂ) :
    (finiteResolvent F z).adjoint=finiteResolvent F (star z) := by
  change star (finiteResolvent F z)=_
  unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
  rw [←Ring.inverse_star,star_sub,star_smul,star_one,
    (GaussGradedCompression.compression_selfAdjoint F).star_eq]

private theorem core_pair (F : Index) (z : ℂ) (hz : z.im≠0) (p q : QuantumTest) :
    sourcePair p (resolventCore F z hz q)=
      sourcePair (resolventCore F (star z) (starNonreal z hz) p) q := by
  simp only [sourcePair,core_embed]
  rw [←finite_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_left _ _ _).symm

private theorem full_pair (s : Bool) (p q : QuantumTest) :
    sourcePair p (fullAction s q)=sourcePair (fullAction (!s) p) q := by
  unfold SourceMixedNativeReturn.fullAction
  cases s
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair q p)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair p q

private theorem theta_pair (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (thetaAction m ell q)=sourcePair (thetaAction m ell p) q := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact GaussNativeForm.multiply_pair _ _ _ _

private theorem derivative_mul (s : Bool) (A B : End) :
    sourceDerivative s (A*B)=sourceDerivative s A*B+A*sourceDerivative s B := by
  unfold sourceDerivative bracket
  noncomm_ring
private theorem derivative_add (s : Bool) (A B : End) :
    sourceDerivative s (A+B)=sourceDerivative s A+sourceDerivative s B := by
  unfold sourceDerivative bracket
  noncomm_ring
private theorem derivative_neg (s : Bool) (A : End) :
    sourceDerivative s (-A)= -sourceDerivative s A := by
  unfold sourceDerivative bracket
  noncomm_ring

private theorem derivative_theta (s : Bool) (m ell : ℕ) : sourceDerivative s (thetaAction m ell)=0 := by
  apply sub_eq_zero.mpr
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases s
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z))
      (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z))
      (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)).symm

private theorem pair_sub_left (p q r : QuantumTest) : sourcePair (p-q) r=sourcePair p r-sourcePair q r := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_right (p q r : QuantumTest) : sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_add_right (p q r : QuantumTest) : sourcePair p (q+r)=sourcePair p q+sourcePair p r := by
  simp only [sourcePair,map_add,inner_add_right]

private theorem derivative_pair (s : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (p q : QuantumTest) :
    sourcePair p (sourceDerivative s (resolventCore F (star z) (starNonreal z hz)) q)=
      -sourcePair (sourceDerivative (!s) (resolventCore F z hz) p) q := by
  simp only [sourceDerivative,bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_left,pair_sub_right,
    core_pair,star_star,full_pair]
  ring

def mixedResponse (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  let R := resolventCore F z hz
  let D := SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F
  let Dbar := SourceClockYukawaHamiltonianCurrent.correctedCurrent (!sharp) F
  R*Dbar*R*D*R+R*D*R*Dbar*R-R*correctedMixedCurvature sharp F*R

/-- The mixed response consumes the complete original scalar/spin/matter curvature
and both compression derivatives at the same original F. -/
theorem actual_mixed_response (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) :
    sourceDerivative (!sharp) (sourceDerivative sharp (resolventCore F z hz))=mixedResponse sharp F z hz := by
  rw [actual_resolvent_first_source]
  have hm : sourceDerivative (!sharp) (SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F)=
      correctedMixedCurvature sharp F := actual_mixed_compression_source sharp F
  simp only [derivative_neg,derivative_mul,actual_resolvent_first_source,hm]
  unfold mixedResponse
  noncomm_ring

def mixedEdge (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  mixedResponse sharp F (star z) (starNonreal z hz)*(thetaAction m ell*thetaAction m ell)*resolventCore F z hz+
    resolventCore F (star z) (starNonreal z hz)*(thetaAction m ell*thetaAction m ell)*mixedResponse sharp F z hz

abbrev mixedEndpoint := SourceClockYukawaMixedEndpoint.mixedEndpoint

def currentThetaEnergy (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) : ℝ :=
  ‖embed (thetaAction m ell (sourceDerivative sharp (resolventCore F z hz) g))‖^2

private theorem mixed_product (s : Bool) (L W R : End)
    (hW : sourceDerivative s W=0) (hWbar : sourceDerivative (!s) W=0) :
    sourceDerivative (!s) (sourceDerivative s (L*W*R))=
      sourceDerivative (!s) (sourceDerivative s L)*W*R+
      sourceDerivative s L*W*sourceDerivative (!s) R+
      sourceDerivative (!s) L*W*sourceDerivative s R+
      L*W*sourceDerivative (!s) (sourceDerivative s R) := by
  simp only [derivative_mul,derivative_add,hW,hWbar,mul_zero,add_zero]
  noncomm_ring

private theorem theta_square_re (m ell : ℕ) (f : QuantumTest) :
    (sourcePair f (thetaAction m ell (thetaAction m ell f))).re=‖embed (thetaAction m ell f)‖^2 := by
  rw [theta_pair]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (embed (thetaAction m ell f))

/-- The two mixed-sharp cross terms are the actual positive theta-current squares. -/
theorem actual_mixed_positive_ims (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : QuantumTest) :
    currentThetaEnergy sharp m ell F z hz g+currentThetaEnergy (!sharp) m ell F z hz g=
      (sourcePair g (mixedEdge sharp m ell F z hz g)).re-
      (sourcePair g (mixedEndpoint sharp m ell F z hz g)).re := by
  have hW (s : Bool) : sourceDerivative s (thetaAction m ell*thetaAction m ell)=0 := by
    simp only [derivative_mul,derivative_theta,zero_mul,mul_zero,add_zero]
  have h := mixed_product sharp (resolventCore F (star z) (starNonreal z hz))
    (thetaAction m ell*thetaAction m ell) (resolventCore F z hz) (hW sharp) (hW (!sharp))
  rw [actual_mixed_response,actual_mixed_response] at h
  have hp := congrArg (fun A : End => (sourcePair g (A g)).re) h
  simp only [LinearMap.add_apply,Module.End.mul_apply,pair_add_right,
    derivative_pair sharp F z hz,derivative_pair (!sharp) F z hz,Bool.not_not,
    Complex.add_re,Complex.neg_re,theta_square_re] at hp
  change _=_ at hp
  simp only [mixedEdge,currentThetaEnergy,LinearMap.add_apply,Module.End.mul_apply,pair_add_right,Complex.add_re]
  change _=_ at hp
  dsimp only [mixedEndpoint,SourceClockYukawaMixedEndpoint.mixedEndpoint,
    SourceClockYukawaMixedEndpoint.thetaGram] at *
  linarith

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem derivative_embed (s : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (sourceDerivative s (resolventCore F z hz) f)= -currentResponse s F z hz (coreEquiv f) := by
  have h := actual_yukawa_resolvent_transport s F z hz (coreEquiv f)
  simp only [yukawaSource,coreEquiv.symm_apply_apply] at h
  rw [show state F z hz (coreEquiv f)=resolventCore F z hz f from (by unfold resolventCore;rfl)] at h
  change embed (fullAction s (resolventCore F z hz f))=
    finiteResolvent F z (embed (fullAction s f))+currentResponse s F z hz (coreEquiv f) at h
  simp only [sourceDerivative,bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub,core_embed]
  linear_combination (norm := module) -h

def basicAmplitude (m ell : ℕ) (F : Index) (z : ℂ) (g k : diagonal.domain) : ℂ :=
  inner ℂ (finiteResolvent F (star z) (k:H)) (relativeTail m ell (finiteResolvent F z (g:H)))

def rightFixedAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g k : diagonal.domain) : ℂ :=
  basicAmplitude m ell F z (yukawaSource sharp g) k

def rightCurrentAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) : ℂ :=
  inner ℂ (finiteResolvent F (star z) (k:H)) (relativeTail m ell (currentResponse sharp F z hz g))

private theorem basic_pair (m ell : ℕ) (F : Index) (z : ℂ) (g k : diagonal.domain) :
    basicAmplitude m ell F z g k=inner ℂ (k:H)
      (finiteResolvent F z (relativeTail m ell (finiteResolvent F z (g:H)))) := by
  rw [basicAmplitude,←finite_adjoint,ContinuousLinearMap.adjoint_inner_left]

private theorem basic_continuous (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) : Continuous (fun w : ℝ => basicAmplitude m ell F (line μ w) g k) := by
  simp_rw [basic_pair]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  exact continuous_const.inner (hr.clm_apply ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const)))

private theorem basic_square_bound (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) (w : ℝ) :
    ‖basicAmplitude m ell F (line μ w) g k‖^2 ≤ ((1/μ)*‖(k:H)‖)^2*
      ‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2 := by
  have hr : ‖finiteResolvent F (star (line μ w)) (k:H)‖ ≤ (1/μ)*‖(k:H)‖ := by
    apply ((finiteResolvent F _).le_opNorm _).trans
    have hb := finite_resolvent_norm F (star (line μ w))
      (starNonreal (line μ w) (by simpa only [line_im] using hμ.ne'))
    simp only [Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ] at hb
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have h := (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg (relativeTail m ell (finiteResolvent F (line μ w) (g:H)))))
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [basicAmplitude,mul_pow] using hh

private theorem basic_tail (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖basicAmplitude m ell F (line μ w) g k‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := ((1/μ)*‖(k:H)‖)^2
  have hC : 0 ≤ C := sq_nonneg _
  obtain ⟨N,hN⟩ := SourceRetardedForcingTail.actual_theta_full_frequency_tail μ hμ g (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal C*
        ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (basic_square_bound m ell F μ hμ g k w)
    _ = ENNReal.ofReal C*(∫⁻ w : ℝ,
        ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) := mul_le_mul (le_refl _) hF bot_le bot_le
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      have hp : 0<C+1 := by positivity
      exact (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+1) (div_pos hε hp).le).trans_eq
        (mul_div_cancel₀ ε hp.ne')

/-- The same original Yukawa increment can transport its right leg to the true fixed Y source. -/
theorem actual_increment_right_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    inner ℂ (finiteResolvent F (star z) (k:H))
      (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g:H)))=
      rightFixedAmplitude sharp m ell F z g k+rightCurrentAmplitude sharp m ell F z hz g k := by
  have hc : Commute (thetaAction m ell) (fullAction sharp) := sub_eq_zero.mp (derivative_theta sharp m ell)
  rw [←state_embed F z hz g,SourceCutoffDilationWard.literal_increment_core,literal_full_return]
  change inner ℂ _ (embed (fullAction sharp (thetaAction m ell (state F z hz g))))=_
  have hc' := LinearMap.congr_fun hc.eq (state F z hz g)
  simp only [Module.End.mul_apply] at hc'
  rw [←hc',←theta_core,
    actual_yukawa_resolvent_transport,map_add,inner_add_right]
  rfl

private theorem current_right_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    currentAmplitude sharp m ell F z hz g k=
      rightFixedAmplitude sharp m ell F z g k+rightCurrentAmplitude sharp m ell F z hz g k-
        fixedAmplitude sharp m ell F z g k := by
  have h := (actual_increment_current_split sharp m ell F z hz g k).symm.trans
    (actual_increment_right_split sharp m ell F z hz g k)
  linear_combination h

/-- The actual retarded theta-current square prices the original paired amplitude. -/
theorem actual_right_current_price (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    ‖rightCurrentAmplitude sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2 ≤
      ((1/μ)*‖(k:H)‖)^2*currentThetaEnergy sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') (coreEquiv.symm g) := by
  have h := derivative_embed sharp F (line μ w) (by simpa only [line_im] using hμ.ne') (coreEquiv.symm g)
  rw [coreEquiv.apply_symm_apply] at h
  have hθ := congrArg (relativeTail m ell) h
  rw [theta_core,map_neg] at hθ
  have he : ‖relativeTail m ell (currentResponse sharp F (line μ w)
      (by simpa only [line_im] using hμ.ne') g)‖^2=
      currentThetaEnergy sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') (coreEquiv.symm g) := by
    unfold currentThetaEnergy
    rw [hθ,norm_neg]
  have hr : ‖finiteResolvent F (star (line μ w)) (k:H)‖ ≤ (1/μ)*‖(k:H)‖ := by
    apply ((finiteResolvent F _).le_opNorm _).trans
    have hb := finite_resolvent_norm F (star (line μ w))
      (starNonreal (line μ w) (by simpa only [line_im] using hμ.ne'))
    simp only [Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ] at hb
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hn := (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg (relativeTail m ell
      (currentResponse sharp F (line μ w) (by simpa only [line_im] using hμ.ne') g))))
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  simpa only [rightCurrentAmplitude,mul_pow,he] using hh

def thetaCurrentCost (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : QuantumTest) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (currentThetaEnergy sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g)

private theorem three_square (a b c : ℂ) :
    ‖a+b-c‖^2 ≤ 3*‖a‖^2+3*‖b‖^2+3*‖c‖^2 := by
  have hn := (norm_sub_le (a+b) c).trans (add_le_add (norm_add_le a b) (le_refl _))
  have h := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith only [h,sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

private theorem current_integral_upper (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    currentCost sharp m ell F μ hμ g k ≤
      3*(∫⁻ w : ℝ,ENNReal.ofReal (‖rightFixedAmplitude sharp m ell F (line μ w) g k‖^2))+
      (3*ENNReal.ofReal (((1/μ)*‖(k:H)‖)^2))*thetaCurrentCost sharp m ell F μ hμ (coreEquiv.symm g)+
      3*(∫⁻ w : ℝ,ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2)) := by
  have hmR : Measurable (fun w : ℝ => (3:ENNReal)*
      ENNReal.ofReal (‖rightFixedAmplitude sharp m ell F (line μ w) g k‖^2)) :=
    (((basic_continuous m ell F μ hμ (yukawaSource sharp g) k).norm.pow 2).measurable.ennreal_ofReal).const_mul _
  have hmL : Measurable (fun w : ℝ => (3:ENNReal)*
      ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2)) :=
    (((basic_continuous m ell F μ hμ g (yukawaSource (!sharp) k)).norm.pow 2).measurable.ennreal_ofReal).const_mul _
  let K : ℝ := ((1/μ)*‖(k:H)‖)^2
  have hK : 0 ≤ K := sq_nonneg _
  calc
    _ ≤ ∫⁻ w : ℝ,(3:ENNReal)*ENNReal.ofReal (‖rightFixedAmplitude sharp m ell F (line μ w) g k‖^2)+
        (3*ENNReal.ofReal K)*ENNReal.ofReal (currentThetaEnergy sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') (coreEquiv.symm g))+
        3*ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      have h := three_square (rightFixedAmplitude sharp m ell F (line μ w) g k)
        (rightCurrentAmplitude sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k)
        (fixedAmplitude sharp m ell F (line μ w) g k)
      rw [←current_right_split] at h
      have hp := actual_right_current_price sharp m ell F μ hμ g k w
      have he : ‖currentAmplitude sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2 ≤
          3*‖rightFixedAmplitude sharp m ell F (line μ w) g k‖^2+
          (3*K)*currentThetaEnergy sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') (coreEquiv.symm g)+
          3*‖fixedAmplitude sharp m ell F (line μ w) g k‖^2 := by nlinarith only [h,hp]
      apply (ENNReal.ofReal_le_ofReal he).trans
      have hh := (ENNReal.ofReal_add_le (p := 3*‖rightFixedAmplitude sharp m ell F (line μ w) g k‖^2+
          (3*K)*currentThetaEnergy sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') (coreEquiv.symm g))
        (q := 3*‖fixedAmplitude sharp m ell F (line μ w) g k‖^2)).trans
        (add_le_add ENNReal.ofReal_add_le (le_refl _))
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 3*K),ENNReal.ofReal_mul hK,
        ENNReal.ofReal_ofNat,mul_assoc] using hh
    _ = _ := by
      rw [lintegral_add_right _ hmL,lintegral_add_left hmR,
        lintegral_const_mul' _ _ (by norm_num),lintegral_const_mul' _ _ (by finiteness),
        lintegral_const_mul' _ _ (by norm_num)]
      rfl

private theorem original_theta_current_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        ENNReal.ofReal (SourceFourPoleEnergyClosed.closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+9*ENNReal.ofReal (((1/μ)*‖(k:H)‖)^2)*
            thetaCurrentCost sharp m ell F μ hμ (coreEquiv.symm g) := by
  intro ε hε
  obtain ⟨N0,h0⟩ := actual_original_yukawa_current_budget sharp μ hμ g k (ε/3) (by positivity)
  obtain ⟨N1,h1⟩ := basic_tail μ hμ (yukawaSource sharp g) k (ε/27) (by positivity)
  obtain ⟨N2,h2⟩ := actual_fixed_yukawa_common_tail sharp μ hμ g k (ε/27) (by positivity)
  refine ⟨max N0 (max N1 N2),fun m hm ell hell => ?_⟩
  filter_upwards [h0 m (by omega) ell hell,h1 m (by omega) ell hell,h2 m (by omega) ell hell] with F hF0 hF1 hF2
  have hb := current_integral_upper sharp m ell F μ hμ g k
  have hh : currentCost sharp m ell F μ hμ g k ≤ 3*ENNReal.ofReal (ε/27)+
      (3*ENNReal.ofReal (((1/μ)*‖(k:H)‖)^2))*thetaCurrentCost sharp m ell F μ hμ (coreEquiv.symm g)+
      3*ENNReal.ofReal (ε/27) := hb.trans
    (add_le_add (add_le_add (mul_le_mul (le_refl _) hF1 bot_le bot_le) (le_refl _))
      (mul_le_mul (le_refl _) hF2 bot_le bot_le))
  have he : ENNReal.ofReal (ε/3)+9*ENNReal.ofReal (ε/27)+9*ENNReal.ofReal (ε/27)=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_ofNat (n := 9),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9),
      ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc
    _ ≤ ENNReal.ofReal (ε/3)+(3:ENNReal)*(3*ENNReal.ofReal (ε/27)+
        (3*ENNReal.ofReal (((1/μ)*‖(k:H)‖)^2))*thetaCurrentCost sharp m ell F μ hμ (coreEquiv.symm g)+
        3*ENNReal.ofReal (ε/27)) := by
      simpa only [ENNReal.ofReal_ofNat] using hF0.trans (add_le_add (le_refl _) (mul_le_mul (le_refl _) hh bot_le bot_le))
    _ = (ENNReal.ofReal (ε/3)+9*ENNReal.ofReal (ε/27)+9*ENNReal.ofReal (ε/27))+
        9*ENNReal.ofReal (((1/μ)*‖(k:H)‖)^2)*thetaCurrentCost sharp m ell F μ hμ (coreEquiv.symm g) := by ring
    _ = _ := by rw [he]

def mixedEdgeCost (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : QuantumTest) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal ((sourcePair g
    (mixedEdge sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)).re)

private theorem endpoint_continuous (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : QuantumTest) : Continuous (fun w : ℝ => sourcePair g
      (mixedEndpoint sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) := by
  have hc (p q : QuantumTest) : Continuous (fun w : ℝ =>
      SourceClockYukawaMixedEndpoint.thetaPair m ell F (line μ w) p q) := by
    have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
    exact ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const)).inner
      ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const))
  simp_rw [SourceClockYukawaMixedEndpoint.original_mixed_endpoint_fixed_sources]
  exact (((hc _ _).sub (hc _ _)).sub (hc _ _)).add (hc _ _)

private theorem theta_edge_integral_upper (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : QuantumTest) :
    thetaCurrentCost sharp m ell F μ hμ g ≤ mixedEdgeCost sharp m ell F μ hμ g+
      ∫⁻ w : ℝ,ENNReal.ofReal (‖sourcePair g
        (mixedEndpoint sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖) := by
  have hm := (endpoint_continuous sharp m ell F μ hμ g).norm.measurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal ((sourcePair g
          (mixedEdge sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)).re)+
        ENNReal.ofReal (‖sourcePair g
          (mixedEndpoint sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖) := by
      apply lintegral_mono
      intro w
      dsimp only
      have hi := actual_mixed_positive_ims sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g
      have hn : 0 ≤ currentThetaEnergy (!sharp) m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g := sq_nonneg _
      have he : -(sourcePair g (mixedEndpoint sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g)).re ≤
          ‖sourcePair g (mixedEndpoint sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g)‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      have hb : currentThetaEnergy sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g ≤
          (sourcePair g (mixedEdge sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g)).re+
          ‖sourcePair g (mixedEndpoint sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g)‖ := by linarith
      exact (ENNReal.ofReal_le_ofReal hb).trans ENNReal.ofReal_add_le
    _ = _ := lintegral_add_right _ hm

/-- The original closed Gamma is paid by one complete signed mixed source edge.
Fixed Yukawa sources, the Hardy word and the mixed endpoint are internal common-cutoff payments. -/
theorem actual_original_mixed_source_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        ENNReal.ofReal (SourceFourPoleEnergyClosed.closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (9*(((1/μ)*‖(k:H)‖)^2))*
            mixedEdgeCost sharp m ell F μ hμ (coreEquiv.symm g) := by
  intro ε hε
  let K : ℝ := ((1/μ)*‖(k:H)‖)^2
  have hK : 0 ≤ K := sq_nonneg _
  obtain ⟨N0,h0⟩ := original_theta_current_budget sharp μ hμ g k (ε/2) (by positivity)
  obtain ⟨N1,h1⟩ := SourceClockYukawaMixedEndpoint.actual_mixed_endpoint_common_tail sharp μ hμ (coreEquiv.symm g)
    (ε/(18*(K+1))) (by positivity)
  refine ⟨max N0 N1,fun m hm ell hell => ?_⟩
  filter_upwards [h0 m (by omega) ell hell,h1 m (by omega) ell hell] with F hF0 hF1
  have hc := (theta_edge_integral_upper sharp m ell F μ hμ (coreEquiv.symm g)).trans
    (add_le_add (le_refl _) hF1)
  have he : ENNReal.ofReal (ε/2)+9*ENNReal.ofReal K*ENNReal.ofReal (ε/(18*(K+1))) ≤ ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_ofNat (n := 9),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9),
      ←ENNReal.ofReal_mul (by positivity : 0 ≤ 9*K),←ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hp : 0<K+1 := by positivity
    have hk : K/(K+1) ≤ 1 := (div_le_one hp).mpr (by linarith)
    have hh : 9*K*(ε/(18*(K+1)))=(ε/2)*(K/(K+1)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [hh]
    nlinarith only [mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ ε/2)]
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9),ENNReal.ofReal_ofNat]
  change _ ≤ ENNReal.ofReal ε+9*ENNReal.ofReal K*mixedEdgeCost sharp m ell F μ hμ (coreEquiv.symm g)
  calc
    _ ≤ ENNReal.ofReal (ε/2)+(9*ENNReal.ofReal K)*
        (mixedEdgeCost sharp m ell F μ hμ (coreEquiv.symm g)+ENNReal.ofReal (ε/(18*(K+1)))) :=
      hF0.trans (add_le_add (le_refl _) (mul_le_mul (le_refl _) hc bot_le bot_le))
    _ = (ENNReal.ofReal (ε/2)+9*ENNReal.ofReal K*ENNReal.ofReal (ε/(18*(K+1))))+
        9*ENNReal.ofReal K*mixedEdgeCost sharp m ell F μ hμ (coreEquiv.symm g) := by ring
    _ ≤ _ := add_le_add he (le_refl _)

end LowEnergy.SourceClockYukawaMixedBudget
