import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialMixedCore
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialMixedBudget
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockSourceTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialMixedClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory GaussAdjointHistory GaussCoframeForm
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourcePhysicalKineticSquare
open SourceClockAcceleration SourceClockReflectedForm SourceClockSourceTail
open SourceRadiusHalfWindow SourceRadiusHalfSourceBudget SourceCoframeBlockHardy
open SourceInverseGapWardFirstJet SourceInverseChannelSourceJets
open GaussYukawaCoefficient GaussRadialDomain SourceRadiusBandGradient SourceRadiusBandPolynomial
open SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceClockYukawaCubicCurrent SourceClockYukawaRadialMixedCore
open SourceResolventBandLimit FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore defectAction state clockCurrent dilation
  resolventCore sourceMixedResponse

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

/-- The forcing is the ordered whole native mixed word at the original F. -/
def mixedForcing (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  let h := coreEquiv.symm (SourceClockYukawaRadialMixedBudget.radiusSource g)
  let R := resolventCore F z hz
  let q := R h
  correctedCutoffCore sharp m ell F (R (SourceRadiusResponseDecay.radialCurrent F q))+
    SourceRadiusResponseDecay.radialCurrent F (R (correctedCutoffCore sharp m ell F q))-
    correctedJoinedCore sharp m ell F q

def mixedState (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  sourceMixedResponse sharp m ell F z hz
    (coreEquiv.symm (SourceClockYukawaRadialMixedBudget.radiusSource g))

attribute [local irreducible] mixedForcing mixedState

private theorem response_forcing (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    mixedState sharp m ell F z hz g=resolventCore F z hz (mixedForcing sharp m ell F z hz g) := by
  simp only [mixedState,mixedForcing,sourceMixedResponse,LinearMap.add_apply,LinearMap.sub_apply,
    Module.End.mul_apply,map_add,map_sub]

private theorem resolvent_source (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    diagonalAction (resolventCore F z hz f)=f+z • resolventCore F z hz f+
      defectAction F (resolventCore F z hz f) := by
  have h := actual_raised_source F z hz (coreEquiv f) (1:End)
  simp only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,LinearMap.zero_apply,zero_add,
    coreEquiv.symm_apply_apply] at h
  unfold resolventCore
  exact h

/-- The exact mixed response carries its actual complete inhomogeneous source equation. -/
theorem actual_mixed_source_equation (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    diagonalAction (mixedState sharp m ell F z hz g)=mixedForcing sharp m ell F z hz g+
      z • mixedState sharp m ell F z hz g+defectAction F (mixedState sharp m ell F z hz g) := by
  rw [response_forcing]
  exact resolvent_source F z hz _

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

/-- The clock price retains the same full defect and all signed sectors on the actual M state. -/
def mixedPrice (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  let f := mixedState sharp m ell F z hz g
  let u := mixedForcing sharp m ell F z hz g+defectAction F f
  2*(sourcePair u (clockCurrent f)).im-2*z.im*(sourcePair f (clockCurrent f)).re+
    (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) u).re+
    (sourceTime 0/2)*z.re*(sourcePair f (inverseVolumeAction f)).re+
    (sourceTime 0)^2*spinForm (inverseVolumeAction f)+
    (sourceTime 0)^2*densityForm (inverseVolumeAction f)-
    sourceTime 0*gaugeForm (inverseVolumeAction f)-sourceTime 0*spatialForm (inverseVolumeAction f)

attribute [local irreducible] mixedPrice

/-- The actual unwindowed mixed source generates all three positive native squares. -/
theorem actual_complete_mixed_clock_price (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    mixedPrice sharp m ell F z hz g=
      (sourceTime 0)^2/4*coframeGram (inverseVolumeAction (mixedState sharp m ell F z hz g))+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction (mixedState sharp m ell F z hz g))+
      2*(sourceTime 0)^2*radiusForm (mixedState sharp m ell F z hz g) := by
  let f := mixedState sharp m ell F z hz g
  let u := mixedForcing sharp m ell F z hz g+defectAction F f
  have he : diagonalAction f=u+z • f := by
    have h := actual_mixed_source_equation sharp m ell F z hz g
    change diagonalAction f=mixedForcing sharp m ell F z hz g+z • f+defectAction F f at h
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
  unfold mixedPrice
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

/-- The same source price pays each native dual leg and the response norm; no graph bound is supplied. -/
theorem actual_mixed_positive_payment (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    let f := mixedState sharp m ell F z hz g
    let p := mixedPrice sharp m ell F z hz g
    (sourceTime 0)^2/4*coframeGram (inverseVolumeAction f) ≤ p ∧
    (sourceTime 0)^2/2*scalarForm (inverseVolumeAction f) ≤ p ∧
    6*(sourceTime 0)^2*‖embed f‖^2 ≤ p ∧
    ‖embed (clockCurrent f)‖^2 ≤ (3/2:ℝ)*p := by
  let f := mixedState sharp m ell F z hz g
  have hc := original_coframe_gram_nonnegative (inverseVolumeAction f)
  have hs : 0 ≤ scalarForm (inverseVolumeAction f) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hr := radius_floor f
  have hcn := mul_nonneg (show 0≤(sourceTime 0)^2/4 by positivity) hc
  have hsn := mul_nonneg (show 0≤(sourceTime 0)^2/2 by positivity) hs
  have hrr := mul_le_mul_of_nonneg_left hr (show 0≤2*(sourceTime 0)^2 by positivity)
  have hJ := original_clock_current_gram f
  have he := actual_complete_mixed_clock_price sharp m ell F z hz g
  change mixedPrice sharp m ell F z hz g=(sourceTime 0)^2/4*coframeGram (inverseVolumeAction f)+
    (sourceTime 0)^2/2*scalarForm (inverseVolumeAction f)+2*(sourceTime 0)^2*radiusForm f at he
  change _ ∧ _ ∧ _ ∧ _
  constructor
  · nlinarith only [he,hcn,hsn,hrr,sq_nonneg ‖embed f‖,sq_nonneg (sourceTime 0)]
  constructor
  · nlinarith only [he,hcn,hsn,hrr,sq_nonneg ‖embed f‖,sq_nonneg (sourceTime 0)]
  constructor
  · nlinarith only [he,hcn,hsn,hrr]
  · nlinarith only [he,hcn,hsn,hrr,hJ,sq_nonneg ‖embed f‖,sq_nonneg (sourceTime 0)]

private theorem compression_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (compressionCore F q)=sourcePair (compressionCore F p) q := by
  have he (f : QuantumTest) : embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [sourcePair,he]
  exact (GaussGradedCompression.compression_pair F _ _).symm

/-- The original imaginary Ward tests the same full mixed response; its complete defect cancels as a single selfadjoint leg. -/
theorem actual_mixed_mu_ward (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    z.im*‖embed (mixedState sharp m ell F z hz g)‖^2=
      -(sourcePair (mixedState sharp m ell F z hz g) (mixedForcing sharp m ell F z hz g)).im := by
  let f := mixedState sharp m ell F z hz g
  have hroute : compressionCore F f=mixedForcing sharp m ell F z hz g+z • f := by
    have h := actual_mixed_source_equation sharp m ell F z hz g
    change diagonalAction f=mixedForcing sharp m ell F z hz g+z • f+defectAction F f at h
    unfold defectAction at h
    simp only [LinearMap.sub_apply] at h
    linear_combination (norm := module) h
  have hreal : (sourcePair f (compressionCore F f)).im=0 := by
    have h := congrArg Complex.im (pair_conjugate f (compressionCore F f))
    rw [←compression_pair] at h
    simp only [Complex.conj_im] at h
    linarith
  have hn : inner ℂ (embed f) (embed f)=((‖embed f‖^2:ℝ):ℂ) := by
    simpa only [Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed f)
  have h := congrArg (fun q => (sourcePair f q).im) hroute
  rw [hreal] at h
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right] at h
  rw [hn] at h
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add] at h
  change z.im*‖embed f‖^2=-(sourcePair f (mixedForcing sharp m ell F z hz g)).im
  change 0=(sourcePair f (mixedForcing sharp m ell F z hz g)).im+z.im*‖embed f‖^2 at h
  linarith only [h]


private theorem actual_mixed_amplitude (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    SourceClockYukawaRadialMixedBudget.mixedAmplitude sharp m ell F z g k=
      inner ℂ (k:H) (finiteResolvent F z (embed (mixedState sharp m ell F z hz g))) := by
  unfold SourceClockYukawaRadialMixedBudget.mixedAmplitude mixedState
  have he : embed (coreEquiv.symm (SourceClockYukawaRadialMixedBudget.radiusSource g))=
      (SourceClockYukawaRadialMixedBudget.radiusSource g:H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [←he,actual_mixed_response_source sharp m ell F z hz]

def sourceNormFactor (μ : ℝ) (k : diagonal.domain) : ℝ :=
  ((1/μ)*‖(k:H)‖)^2/(6*(sourceTime 0)^2)

def mixedClockBudget (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (mixedPrice sharp m ell F (SourceResolventBandLimit.line μ w)
    (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g)

private theorem reordered_square (a b c : ℝ) : (a*(b*c))^2=(b*a)^2*c^2 := by ring

private theorem amplitude_clock_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    ‖SourceClockYukawaRadialMixedBudget.mixedAmplitude sharp m ell F (SourceResolventBandLimit.line μ w) g k‖^2 ≤
      sourceNormFactor μ k*mixedPrice sharp m ell F (SourceResolventBandLimit.line μ w)
        (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g := by
  let z := SourceResolventBandLimit.line μ w
  have hz : z.im≠0 := by simpa only [z,SourceResolventBandLimit.line_im] using hμ.ne'
  let f := mixedState sharp m ell F z hz g
  have hR : ‖finiteResolvent F z‖ ≤ 1/μ := by
    simpa only [z,SourceResolventBandLimit.line_im,abs_of_pos hμ] using finite_resolvent_norm F z hz
  have hret : ‖finiteResolvent F z (embed f)‖ ≤ (1/μ)*‖embed f‖ :=
    ((finiteResolvent F z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hi := (norm_inner_le_norm (𝕜 := ℂ) (k:H) (finiteResolvent F z (embed f))).trans
    (mul_le_mul_of_nonneg_left hret (norm_nonneg (k:H)))
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  have hp := (actual_mixed_positive_payment sharp m ell F z hz g).2.2.1
  have hC : 0 ≤ sourceNormFactor μ k := by unfold sourceNormFactor;positivity
  have hs := mul_le_mul_of_nonneg_left hp hC
  have hn := lapse_pos.ne'
  have hc : sourceNormFactor μ k*(6*(sourceTime 0)^2*‖embed f‖^2)=
      ((1/μ)*‖(k:H)‖)^2*‖embed f‖^2 := by unfold sourceNormFactor;field_simp [hn]
  change sourceNormFactor μ k*(6*(sourceTime 0)^2*‖embed f‖^2) ≤ _ at hs
  rw [hc] at hs
  rw [actual_mixed_amplitude sharp m ell F _ hz]
  change ‖inner ℂ (k:H) (finiteResolvent F z (embed f))‖^2 ≤ _
  rw [reordered_square] at hi2
  exact hi2.trans hs

private theorem actual_mixed_clock_cost (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    SourceClockYukawaRadialMixedBudget.mixedResponseCost sharp m ell F μ hμ g k ≤
      ENNReal.ofReal (sourceNormFactor μ k)*mixedClockBudget sharp m ell F μ hμ g := by
  have hC : 0 ≤ sourceNormFactor μ k := by unfold sourceNormFactor;positivity
  unfold SourceClockYukawaRadialMixedBudget.mixedResponseCost mixedClockBudget
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (sourceNormFactor μ k)*ENNReal.ofReal
        (mixedPrice sharp m ell F (SourceResolventBandLimit.line μ w)
          (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') g) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (amplitude_clock_bound sharp m ell F μ hμ g k w)
    _=_ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Original Gamma consumes this generated clock price with one cutoff for both sharp branches. -/
theorem actual_original_mixed_clock_budget (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        ENNReal.ofReal (SourceFourPoleEnergyClosed.closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (3*sourceNormFactor μ k)*mixedClockBudget sharp m ell F μ hμ g := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := SourceClockYukawaRadialMixedBudget.actual_original_mixed_response_budget false μ hμ g k ε hε
  obtain ⟨N₁,h₁⟩ := SourceClockYukawaRadialMixedBudget.actual_original_mixed_response_budget true μ hμ g k ε hε
  refine ⟨max N₀ N₁,fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m ((le_max_left _ _).trans hm) ell hml,h₁ m ((le_max_right _ _).trans hm) ell hml] with F hf ht
  intro sharp
  have h := hf
  cases sharp with
  | false =>
    apply h.trans
    apply add_le_add (le_refl _)
    have hc := mul_le_mul (le_refl (ENNReal.ofReal (3:ℝ)))
      (actual_mixed_clock_cost false m ell F μ hμ g k) bot_le bot_le
    rwa [←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)] at hc
  | true =>
    apply ht.trans
    apply add_le_add (le_refl _)
    have hc := mul_le_mul (le_refl (ENNReal.ofReal (3:ℝ)))
      (actual_mixed_clock_cost true m ell F μ hμ g k) bot_le bot_le
    rwa [←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)] at hc

end LowEnergy.SourceClockYukawaRadialMixedClock
