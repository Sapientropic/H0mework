import Mathlib.Algebra.Order.Chebyshev
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricWindowDecay
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockWindowTime
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockFixedInputSeed
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCoframeBlockHardy
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeGapWardFirstJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockSourceTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory GaussAdjointHistory GaussCoframeForm
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourcePhysicalKineticSquare
open SourceClockAcceleration SourceClockReflectedForm SourceClockWindowTime
open SourceRadiusHalfWindow SourceRadiusHalfSourceBudget SourceCoframeBlockHardy
open SourceInverseGapWardFirstJet SourceInverseChannelSourceJets
open GaussYukawaCoefficient GaussRadialDomain SourceRadiusBandGradient SourceRadiusBandPolynomial
open SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceResolventBandLimit FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore defectAction state clockCurrent inverseVolumeAction

private theorem compression_equation (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    compressionCore F (state F z hz g)=coreEquiv.symm g+z • state F z hz g := by
  have h := actual_raised_source F z hz g (1 : End)
  simp only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,LinearMap.zero_apply,zero_add,
    defectAction,LinearMap.sub_apply] at h
  linear_combination (norm := module) h

private theorem inverse_real (f : QuantumTest) : (sourcePair f (inverseVolumeAction f)).im=0 := by
  have hp : sourcePair f (inverseVolumeAction f)=sourcePair (inverseVolumeAction f) f := by
    unfold inverseVolumeAction
    exact multiply_pair _ _ _ _
  have h := congrArg Complex.im (pair_conjugate f (inverseVolumeAction f))
  rw [←hp] at h
  simp only [Complex.conj_im] at h
  linarith

/-- The fixed input and real frequency are one same-F first-source pairing, before either causal orientation is selected. -/
theorem actual_inverse_frequency_source (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (m ell : ℕ) (z : ℂ) (hz : z.im≠0),
      (sourcePair (inverseVolumeAction (halfAction m ell (state F z hz g)))
        (halfAction m ell (coreEquiv.symm g))).re+
      z.re*(sourcePair (halfAction m ell (state F z hz g))
        (inverseVolumeAction (halfAction m ell (state F z hz g)))).re=
      (sourcePair (inverseVolumeAction (halfAction m ell (state F z hz g)))
        (halfAction m ell (state F z hz (iterate 1 g)))).re := by
  filter_upwards [actual_retarded_source_step g] with F hF m ell z hz
  rw [←hF z hz,compression_equation,map_add,map_smul]
  have hv : sourcePair (inverseVolumeAction (halfAction m ell (state F z hz g)))
      (halfAction m ell (state F z hz g))=
      sourcePair (halfAction m ell (state F z hz g))
        (inverseVolumeAction (halfAction m ell (state F z hz g))) := by
    unfold inverseVolumeAction
    exact (multiply_pair _ _ _ _).symm
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right]
  change _=(sourcePair (inverseVolumeAction (halfAction m ell (state F z hz g)))
    (halfAction m ell (coreEquiv.symm g))+z*sourcePair
      (inverseVolumeAction (halfAction m ell (state F z hz g)))
      (halfAction m ell (state F z hz g))).re
  rw [hv]
  simp only [Complex.add_re,Complex.mul_re,inverse_real,mul_zero,sub_zero]
  rfl

private theorem number_nonnegative (f : QuantumTest) : 0 ≤ (sourcePair f (number f)).re := by
  rw [sourcePair_integral]
  change 0 ≤ RCLike.re (∫ z,densityPair f (number f) z ∂GaussHistoryHilbert.configurationMeasure)
  rw [←integral_re (densityPair_integrable f (number f))]
  apply integral_nonneg
  intro z
  change 0 ≤ (densityPair f (number f) z).re
  by_cases hz : z∈physicalChart
  · rw [densityPair_sum]
    simp only [Complex.re_sum,GaussCoframeForm.number_apply]
    apply Finset.sum_nonneg
    intro word _
    have hd := (GaussDensityCore.density_pos word.card ⟨z,hz⟩).le
    have he : (GaussDensityCore.complexDensity word.card z*star (f z word)*
        ((word.card:ℂ)*f z word)).re=
        GaussDensityCore.density word.card z*(word.card:ℝ)*‖f z word‖^2 := by
      rw [GaussDensityCore.complexDensity]
      have hh : (star (f z word))*(f z word)=((‖f z word‖^2:ℝ):ℂ) := by
        simpa only [RCLike.inner_apply,mul_comm,starRingEnd_apply,Complex.ofReal_pow] using!
          inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (f z word)
      calc
        _=(((GaussDensityCore.density word.card z:ℂ)*(word.card:ℂ))*
            (star (f z word)*f z word)).re := by congr 1;ring
        _=_ := by
          rw [hh]
          norm_cast
          rw [←Complex.ofReal_mul,Complex.ofReal_re]
    rw [he]
    positivity
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

/-- All three actual Number-weighted blocks pay the inverse-volume norm without an added graph hypothesis. -/
theorem original_inverse_coframe_floor (f : QuantumTest) :
    25*‖embed f‖^2 ≤ coframeGram f := by
  have h := original_coframe_three_block_hardy f
  have hc : 0 ≤ ∑ b : Fin 3,‖embed (centeredBlock b f)‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn := number_nonnegative f
  have hn2 := sq_nonneg ‖embed (number f)‖
  nlinarith only [h,hc,hn,hn2]

private theorem inverse_young (f h : QuantumTest) :
    (sourceTime 0/2)*|(sourcePair (inverseVolumeAction f) h).re| ≤
      (sourceTime 0)^2/8*coframeGram (inverseVolumeAction f)+(1/50:ℝ)*‖embed h‖^2 := by
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hp := (Complex.abs_re_le_norm (sourcePair (inverseVolumeAction f) h)).trans
    (norm_inner_le_norm (𝕜 := ℂ) (embed (inverseVolumeAction f)) (embed h))
  have hfloor := original_inverse_coframe_floor (inverseVolumeAction f)
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ sourceTime 0/2 by positivity)
  have hf' := mul_le_mul_of_nonneg_left hfloor (show 0 ≤ (sourceTime 0)^2/8 by positivity)
  nlinarith only [hp',hf',sq_nonneg (5*sourceTime 0*‖embed (inverseVolumeAction f)‖- (2/5:ℝ)*‖embed h‖)]

/-- The joint V/frequency forcing consumes half of the true reflected coframe square, leaving only a fixed H0 input half-window. -/
theorem actual_inverse_frequency_absorption (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (m ell : ℕ) (z : ℂ) (hz : z.im≠0),
      (sourceTime 0/2)*|(sourcePair (inverseVolumeAction (halfAction m ell (state F z hz g)))
        (halfAction m ell (coreEquiv.symm g))).re+
        z.re*(sourcePair (halfAction m ell (state F z hz g))
          (inverseVolumeAction (halfAction m ell (state F z hz g)))).re| ≤
      (sourceTime 0)^2/8*coframeGram (inverseVolumeAction (halfAction m ell (state F z hz g)))+
        (1/50:ℝ)*‖embed (halfAction m ell (state F z hz (iterate 1 g)))‖^2 := by
  filter_upwards [actual_inverse_frequency_source g] with F hF m ell z hz
  rw [hF m ell z hz]
  exact inverse_young _ _

/-- The full unpriced signed source after the joint V/frequency input has been absorbed. -/
def remainingPrice (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  let q := state F z hz g
  let f := halfAction m ell q
  let d := raisedDefect F (halfAction m ell) q
  2*(sourcePair (halfAction m ell (coreEquiv.symm g)+d) (clockCurrent f)).im-
    2*z.im*(sourcePair f (clockCurrent f)).re+
    (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) d).re+
    (sourceTime 0)^2*spinForm (inverseVolumeAction f)+
    (sourceTime 0)^2*densityForm (inverseVolumeAction f)-
    sourceTime 0*gaugeForm (inverseVolumeAction f)-sourceTime 0*spatialForm (inverseVolumeAction f)

/-- The actual positive clock/radius source spends half its coframe Gram on the same-F V/input/w word. -/
theorem actual_source_price_absorption (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (m ell : ℕ) (z : ℂ) (hz : z.im≠0),
      (sourceTime 0)^2/8*coframeGram (inverseVolumeAction (halfAction m ell (state F z hz g)))+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction (halfAction m ell (state F z hz g)))+
      2*(sourceTime 0)^2*radiusForm (halfAction m ell (state F z hz g)) ≤
        remainingPrice F m ell z hz g+
          (1/50:ℝ)*‖embed (halfAction m ell (state F z hz (iterate 1 g)))‖^2 := by
  filter_upwards [actual_inverse_frequency_absorption g] with F hF m ell z hz
  have h := hF m ell z hz
  have hn : 0 ≤ sourceTime 0/2 := by
    exact div_nonneg (by
      rw [source_time_generated]
      exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos.le) (by norm_num)
  have ha := mul_le_mul_of_nonneg_left (le_abs_self
    ((sourcePair (inverseVolumeAction (halfAction m ell (state F z hz g)))
      (halfAction m ell (coreEquiv.symm g))).re+
      z.re*(sourcePair (halfAction m ell (state F z hz g))
        (inverseVolumeAction (halfAction m ell (state F z hz g)))).re)) hn
  have he := actual_clock_source_price F m ell z hz g
  unfold sourcePrice at he
  unfold remainingPrice
  simp only [sourcePair,map_add,inner_add_right,Complex.add_re] at he ⊢
  change _ ≤ _ at h
  simp only [sourcePair] at h ha
  nlinarith only [he,h,ha]

private theorem dilation_centered :
    dilation=(2/3:ℂ) • (∑ b : Fin 3,centeredBlock b) := by
  rw [dilation_operator]
  simp [centeredBlock,blockMomentum,blockDensity,blockIndices,eulerAction,
    GaussCoframeCore.momentum,Fin.sum_univ_succ]
  module

private theorem dilation_gram (f : QuantumTest) :
    ‖embed (dilation f)‖^2 ≤ (4/3:ℝ)*(∑ b : Fin 3,‖embed (centeredBlock b f)‖^2) := by
  have ht := norm_sum_le (Finset.univ : Finset (Fin 3)) (fun b => embed (centeredBlock b f))
  have ht2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
    (f := fun b => ‖embed (centeredBlock b f)‖)
  norm_num only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] at hs
  rw [dilation_centered]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,norm_smul,mul_pow]
  norm_num
  nlinarith only [ht2,hs]

private theorem inverse_dilation : dilation*inverseVolumeAction-inverseVolumeAction*dilation=
    (2*Complex.I) • inverseVolumeAction := by
  have h := congrArg (fun A : End => (-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) •
      (dilation*inverseVolumeAction-inverseVolumeAction*dilation))=
    (-2*Complex.I/3) • ((-3:ℂ) • inverseVolumeAction) at h
  simp only [smul_smul] at h
  have hi : (-2*Complex.I/3)*(3*Complex.I/2)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring

private theorem clock_norm (f : QuantumTest) :
    ‖embed (clockCurrent f)‖^2=(9*(sourceTime 0)^2/16)*
      (‖embed (dilation (inverseVolumeAction f))‖^2+‖embed (inverseVolumeAction f)‖^2) := by
  have he : clockCurrent=(3*(sourceTime 0:ℂ)/4) •
      ((dilation-Complex.I • (1:End))*inverseVolumeAction) := by
    rw [original_clock_current]
    linear_combination (norm := (noncomm_ring;module)) (-3*(sourceTime 0:ℂ)/8) • inverse_dilation
  have hp := SourceCoframeDilation.dilation_pair (inverseVolumeAction f) (inverseVolumeAction f)
  have hc := congrArg Complex.im (pair_conjugate (inverseVolumeAction f) (dilation (inverseVolumeAction f)))
  rw [hp] at hc
  simp only [Complex.conj_im] at hc
  have hi : (inner ℂ (embed (dilation (inverseVolumeAction f))) (embed (inverseVolumeAction f))).im=0 := by
    change (sourcePair (dilation (inverseVolumeAction f)) (inverseVolumeAction f)).im=0
    linarith only [hc]
  rw [he]
  simp only [LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,Module.End.one_apply,
    map_smul,map_sub,norm_smul,mul_pow]
  rw [norm_sub_sq (𝕜 := ℂ),inner_smul_right]
  simp only [norm_smul,Complex.norm_I,one_mul]
  norm_num [Complex.norm_div,Complex.norm_mul,sq_abs,RCLike.re_to_complex,hi]
  exact Or.inl (by rw [div_pow,mul_pow,sq_abs];ring)

/-- The source clock current is paid by the same completed coframe Gram, including its Number-density rows. -/
theorem original_clock_current_gram (f : QuantumTest) :
    ‖embed (clockCurrent f)‖^2 ≤ (3*(sourceTime 0)^2/8)*coframeGram (inverseVolumeAction f) := by
  rw [clock_norm]
  have hd := dilation_gram (inverseVolumeAction f)
  have hc := original_coframe_three_block_hardy (inverseVolumeAction f)
  have hn := number_nonnegative (inverseVolumeAction f)
  have hs : 0 ≤ ∑ b : Fin 3,‖embed (centeredBlock b (inverseVolumeAction f))‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn2 := sq_nonneg ‖embed (number (inverseVolumeAction f))‖
  have hg2 := sq_nonneg ‖embed (inverseVolumeAction f)‖
  have hbase : (9/16:ℝ)*(‖embed (dilation (inverseVolumeAction f))‖^2+
      ‖embed (inverseVolumeAction f)‖^2) ≤ (3/8:ℝ)*coframeGram (inverseVolumeAction f) := by
    nlinarith only [hd,hc,hn,hs,hn2,hg2]
  nlinarith only [mul_le_mul_of_nonneg_left hbase (sq_nonneg (sourceTime 0))]

private theorem damping_gram (ν : ℝ) (f : QuantumTest) :
    2 * |ν| * |(sourcePair f (clockCurrent f)).re| ≤
      (sourceTime 0)^2/16*coframeGram (inverseVolumeAction f)+6*ν^2*‖embed f‖^2 := by
  have hp := (Complex.abs_re_le_norm (sourcePair f (clockCurrent f))).trans
    (norm_inner_le_norm (𝕜 := ℂ) (embed f) (embed (clockCurrent f)))
  have hc := original_clock_current_gram f
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * |ν| by positivity)
  have hs := sq_nonneg (‖embed (clockCurrent f)‖-6 * |ν| * ‖embed f‖)
  nlinarith only [hm,hc,hs,sq_abs ν]

private theorem half_square_radius (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    halfCoefficient m ell z^2 ≤ radius z^2/(m+2:ℝ) := by
  have hq : 0 ≤ 1-reciprocal z := sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_radius z))
  have hA : 0 ≤ coefficient m ell z := by
    unfold coefficient band
    exact Finset.sum_nonneg (fun j _ => pow_nonneg hq _)
  have hs := Real.sq_sqrt (show 0 ≤ 1+coefficient m ell z by linarith)
  have hp := Real.one_le_sqrt.mpr (show 1 ≤ 1+coefficient m ell z by linarith)
  have hhalf : halfCoefficient m ell z^2 ≤ coefficient m ell z := by
    unfold halfCoefficient
    nlinarith only [hs,hp]
  have he : coefficient m ell z*reciprocal z=SourceNativeCutoffContact.theta m ell z := by
    have hb : band m ell (1-reciprocal z)=
        ∑ j∈Finset.Ico (m+1) (ell+1),(1-reciprocal z)^j :=
      Finset.sum_Ico_add' _ m ell 1
    change band m ell (1-reciprocal z)*reciprocal z=_
    rw [hb]
    simpa only [show 1-(1-reciprocal z)=reciprocal z by ring,SourceNativeCutoffContact.theta] using
      geom_sum_Ico_mul_neg (1-reciprocal z) (show m+1 ≤ ell+1 by omega)
  have hw := (abs_le.mp (SourceInverseElectricWindowDecay.original_inverse_window_bound m ell hml z)).2
  have hc : coefficient m ell z=radius z^2*(reciprocal z*SourceNativeCutoffContact.theta m ell z) := by
    rw [←he]
    unfold reciprocal
    field_simp [(radius_pos z).ne']
  calc
    _ ≤ coefficient m ell z := hhalf
    _ = radius z^2*(reciprocal z*SourceNativeCutoffContact.theta m ell z) := hc
    _ ≤ radius z^2*(1/(m+2:ℝ)) := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
    _ = _ := by ring

private theorem half_density (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (densityPair (halfAction m ell f) (halfAction m ell f) z).re=
      halfCoefficient m ell z^2*(densityPair f f z).re := by
  change (inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z)
    ((halfCoefficient m ell z:ℂ) • f z)) ((halfCoefficient m ell z:ℂ) • f z)).re=_
  rw [map_smul,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero,sub_zero]
  change _=halfCoefficient m ell z^2*(inner ℂ (GaussFockWeights.weight
    (fun N => GaussDensityCore.complexDensity N z) (f z)) (f z)).re
  ring

private theorem density_nonneg (f : QuantumTest) (z : SourceCoordinateSlice) : 0 ≤ (densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · change 0 ≤ RCLike.re (inner ℂ (GaussFockWeights.weight
      (fun N => (GaussDensityCore.density N z:ℂ)) (f z)) (f z))
    rw [GaussBoundedMultiplier.weighted_square _ (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le)]
    exact sq_nonneg _
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem radius_density (f : QuantumTest) :
    radiusForm f=∫ z : SourceCoordinateSlice,(4*radius z^2-1)*(densityPair f f z).re
      ∂GaussHistoryHilbert.configurationMeasure := by
  let c : SourceCoordinateSlice → ℝ := fun z => 4*radius z^2-1
  have hc : ContDiff ℝ ∞ c := (contDiff_const.mul (radius_smooth.pow 2)).sub contDiff_const
  let A : End := multiply c (fun _ => hc.contDiffAt)
  have he : radiusForm f=(sourcePair f (A f)).re := rfl
  rw [he,sourcePair_integral]
  change RCLike.re (∫ z,densityPair f (A f) z ∂GaussHistoryHilbert.configurationMeasure)=_
  rw [←integral_re (densityPair_integrable f (A f))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    change (inner ℂ _ ((c z:ℂ) • f z)).re=c z*(densityPair f f z).re
    rw [inner_smul_right]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl)

private theorem radius_density_integrable (f : QuantumTest) :
    Integrable (fun z : SourceCoordinateSlice => (4*radius z^2-1)*(densityPair f f z).re)
      GaussHistoryHilbert.configurationMeasure := by
  let c : SourceCoordinateSlice → ℝ := fun z => 4*radius z^2-1
  have hc : ContDiff ℝ ∞ c := (contDiff_const.mul (radius_smooth.pow 2)).sub contDiff_const
  have h := (densityPair_integrable f (multiply c (fun _ => hc.contDiffAt) f)).re
  apply h.congr
  exact Filter.Eventually.of_forall (fun z => by
    change (inner ℂ _ ((c z:ℂ) • f z)).re=c z*(densityPair f f z).re
    rw [inner_smul_right]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl)

/-- The actual window pays every fixed norm coefficient through its own radius square and a shrinking, unweighted source error. -/
theorem original_half_radius_absorption (K α : ℝ) (hK : 0 ≤ K) (hα : 0<α)
    (m ell : ℕ) (hml : m ≤ ell) (q : QuantumTest) :
    K*‖embed (halfAction m ell q)‖^2 ≤ α*radiusForm (halfAction m ell q)+
      (K*(K+α)/(4*α*(m+2:ℝ)))*‖embed q‖^2 := by
  have hp (z : SourceCoordinateSlice) : K*halfCoefficient m ell z^2 ≤
      α*(4*radius z^2-1)*halfCoefficient m ell z^2+K*(K+α)/(4*α*(m+2:ℝ)) := by
    have hh := half_square_radius m ell hml z
    by_cases h : K ≤ α*(4*radius z^2-1)
    · have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (halfCoefficient m ell z))
      have he : 0 ≤ K*(K+α)/(4*α*(m+2:ℝ)) := by positivity
      linarith only [hm,he]
    · have hr : radius z^2 ≤ (K+α)/(4*α) := by
        apply (le_div_iff₀ (by positivity : 0<4*α)).mpr
        linarith only [not_le.mp h]
      have hprice : K*halfCoefficient m ell z^2 ≤ K*(K+α)/(4*α*(m+2:ℝ)) := by
        calc
          _ ≤ K*(radius z^2/(m+2:ℝ)) := mul_le_mul_of_nonneg_left hh hK
          _ ≤ K*(((K+α)/(4*α))/(m+2:ℝ)) := by gcongr
          _ = _ := by field_simp
      have hc : 0 ≤ α*(4*radius z^2-1)*halfCoefficient m ell z^2 := by
        have hrad := one_le_radius z
        have hrad0 := radius_pos z
        have hh : 0 ≤ 4*radius z^2-1 := by nlinarith
        positivity
      linarith only [hprice,hc]
  rw [GaussBoundedMultiplier.norm_square_integral,GaussBoundedMultiplier.norm_square_integral,radius_density,
    ←integral_const_mul,←integral_const_mul,←integral_const_mul,
    ←integral_add ((radius_density_integrable (halfAction m ell q)).const_mul α)
      ((densityPair_integrable q q).re.const_mul _)]
  apply integral_mono ((densityPair_integrable (halfAction m ell q) (halfAction m ell q)).re.const_mul K)
    (((radius_density_integrable (halfAction m ell q)).const_mul α).add
      ((densityPair_integrable q q).re.const_mul _))
  intro z
  change K*(densityPair (halfAction m ell q) (halfAction m ell q) z).re ≤ _
  rw [half_density]
  have hm := mul_le_mul_of_nonneg_right (hp z) (density_nonneg q z)
  change _ ≤ α*((4*radius z^2-1)*(densityPair (halfAction m ell q) (halfAction m ell q) z).re)+_
  rw [half_density]
  dsimp only
  simpa only [RCLike.re_to_complex] using! (show K*(halfCoefficient m ell z^2*(densityPair q q z).re) ≤
    α*((4*radius z^2-1)*(halfCoefficient m ell z^2*(densityPair q q z).re))+
      K*(K+α)/(4*α*(m+2:ℝ))*(densityPair q q z).re from by nlinarith only [hm])

/-- Both causal damping signs spend true clock/coframe and radius squares; the remaining error is paid by the original resolvent norm. -/
theorem original_damping_absorption (ν : ℝ) (m ell : ℕ) (hml : m ≤ ell) (q : QuantumTest) :
    2 * |ν| * |(sourcePair (halfAction m ell q) (clockCurrent (halfAction m ell q))).re| ≤
      (sourceTime 0)^2/16*coframeGram (inverseVolumeAction (halfAction m ell q))+
      (sourceTime 0)^2*radiusForm (halfAction m ell q)+
      (6*ν^2*(6*ν^2+(sourceTime 0)^2)/(4*(sourceTime 0)^2*(m+2:ℝ)))*‖embed q‖^2 := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hg := damping_gram ν (halfAction m ell q)
  have hr := original_half_radius_absorption (6*ν^2) ((sourceTime 0)^2)
    (by positivity) (sq_pos_of_pos hn) m ell hml q
  linarith only [hg,hr]

def dampingError (ν : ℝ) (m ell : ℕ) (q : QuantumTest) : ℝ :=
  max 0 (2 * |ν| * |(sourcePair (halfAction m ell q) (clockCurrent (halfAction m ell q))).re|-
    (sourceTime 0)^2/16*coframeGram (inverseVolumeAction (halfAction m ell q))-
    (sourceTime 0)^2*radiusForm (halfAction m ell q))

private theorem damping_error_bound (ν : ℝ) (m ell : ℕ) (hml : m ≤ ell) (q : QuantumTest) :
    dampingError ν m ell q ≤
      (6*ν^2*(6*ν^2+(sourceTime 0)^2)/(4*(sourceTime 0)^2*(m+2:ℝ)))*‖embed q‖^2 := by
  unfold dampingError
  apply max_le
  · positivity
  · have h := original_damping_absorption ν m ell hml q
    linarith only [h]

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- The positive error left after absorbing the actual clock damping has a uniform whole-frequency source price. -/
theorem actual_damping_error_full_frequency (advanced : Bool) (m ell : ℕ) (hml : m ≤ ell)
    (F : Index) (ν : ℝ) (hν : 0<ν) (g : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (dampingError ν m ell
      (state F (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g))) ≤
      ENNReal.ofReal ((6*ν^2*(6*ν^2+(sourceTime 0)^2)/(4*(sourceTime 0)^2*(m+2:ℝ)))*
        (Real.pi/ν*‖(g:H)‖^2)) := by
  let c : ℝ := 6*ν^2*(6*ν^2+(sourceTime 0)^2)/(4*(sourceTime 0)^2*(m+2:ℝ))
  have hc : 0 ≤ c := by dsimp only [c];positivity
  have hn (w : ℝ) : ‖finiteResolvent F (causalPoint advanced ν w) (g:H)‖=
      ‖finiteResolvent F (line ν w) (g:H)‖ := by
    cases advanced
    · rfl
    · exact SourceInverseSourceLeg.actual_conjugate_leg_norm F (line ν w)
        (by simpa only [line_im] using hν.ne') (g:H)
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (c*‖finiteResolvent F (line ν w) (g:H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      have h := damping_error_bound ν m ell hml
        (state F (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g)
      rw [state_embed,hn] at h
      exact ENNReal.ofReal_le_ofReal h
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul hc]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have he := SourceActualResolventEnergy.actual_square_lintegral F ν hν (g:H)
      have he' : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line ν w) (g:H)‖^2))=
          ENNReal.ofReal (Real.pi/ν*‖(g:H)‖^2) := by simpa only [line,mul_comm] using he
      rw [he',←ENNReal.ofReal_mul hc]

/-- The same cutoff pays the actual damping error before F and either causal leg are selected. -/
theorem actual_damping_error_common_tail (ν : ℝ) (hν : 0<ν) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,∀ advanced : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (dampingError ν m ell
        (state F (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g))) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := (6*ν^2*(6*ν^2+(sourceTime 0)^2)/(4*(sourceTime 0)^2))*(Real.pi/ν*‖(g:H)‖^2)
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hml F advanced => ?_⟩
  have hm' : (N:ℝ) ≤ m := by exact_mod_cast hm
  have hC : C<(N:ℝ)*ε := (div_lt_iff₀ hε).mp hN
  have hp : C/(m+2:ℝ) ≤ ε := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hm',hC,hε]
  have he : (6*ν^2*(6*ν^2+(sourceTime 0)^2)/(4*(sourceTime 0)^2*(m+2:ℝ)))*
      (Real.pi/ν*‖(g:H)‖^2)=C/(m+2:ℝ) := by dsimp only [C];field_simp
  exact (actual_damping_error_full_frequency advanced m ell hml F ν hν g).trans
    (ENNReal.ofReal_le_ofReal (he.trans_le hp))

/-- The remaining source keeps the full raised defect and all signed spin, density, gauge and spatial fields. -/
def undampedRemainder (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  let q := state F z hz g
  let f := halfAction m ell q
  let d := raisedDefect F (halfAction m ell) q
  2*(sourcePair (halfAction m ell (coreEquiv.symm g)+d) (clockCurrent f)).im+
    (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) d).re+
    (sourceTime 0)^2*spinForm (inverseVolumeAction f)+
    (sourceTime 0)^2*densityForm (inverseVolumeAction f)-
    sourceTime 0*gaugeForm (inverseVolumeAction f)-sourceTime 0*spatialForm (inverseVolumeAction f)

/-- The whole source consumes both new absorptions, retaining positive coframe, native70 and radius rows on its left. -/
theorem actual_joint_source_absorption (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (m ell : ℕ) (z : ℂ) (hz : z.im≠0),
      (sourceTime 0)^2/16*coframeGram (inverseVolumeAction (halfAction m ell (state F z hz g)))+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction (halfAction m ell (state F z hz g)))+
      (sourceTime 0)^2*radiusForm (halfAction m ell (state F z hz g)) ≤
        undampedRemainder F m ell z hz g+
          (1/50:ℝ)*‖embed (halfAction m ell (state F z hz (iterate 1 g)))‖^2+
          dampingError z.im m ell (state F z hz g) := by
  filter_upwards [actual_source_price_absorption g] with F hF m ell z hz
  have h := hF m ell z hz
  have hd := le_max_right 0 (2 * |z.im| *
    |(sourcePair (halfAction m ell (state F z hz g)) (clockCurrent (halfAction m ell (state F z hz g)))).re|-
    (sourceTime 0)^2/16*coframeGram (inverseVolumeAction (halfAction m ell (state F z hz g)))-
    (sourceTime 0)^2*radiusForm (halfAction m ell (state F z hz g)))
  have ha := neg_le_abs (z.im*(sourcePair (halfAction m ell (state F z hz g))
    (clockCurrent (halfAction m ell (state F z hz g)))).re)
  rw [abs_mul] at ha
  change _ ≤ dampingError z.im m ell (state F z hz g) at hd
  unfold remainingPrice at h
  unfold undampedRemainder
  nlinarith only [h,hd,ha]

private theorem radius_nonnegative (f : QuantumTest) : 0 ≤ radiusForm f := by
  rw [radius_density]
  apply integral_nonneg
  intro z
  change 0 ≤ (4*radius z^2-1)*(densityPair f f z).re
  apply mul_nonneg _ (density_nonneg f z)
  have h := one_le_radius z
  nlinarith only [h,sq_nonneg (radius z-1)]

/-- Direct sourceBudget integrand consumer: the V/frequency and damping slots have been replaced by the fixed H0 half-window and the paid common error. -/
theorem actual_source_price_joint_upper (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (m ell : ℕ) (z : ℂ) (hz : z.im≠0),
      sourcePrice F m ell z hz g ≤ 4*undampedRemainder F m ell z hz g+
        (2/25:ℝ)*‖embed (halfAction m ell (state F z hz (iterate 1 g)))‖^2+
        4*dampingError z.im m ell (state F z hz g) := by
  filter_upwards [actual_joint_source_absorption g] with F hF m ell z hz
  have h := hF m ell z hz
  rw [actual_clock_source_price]
  have hs : 0 ≤ scalarForm (inverseVolumeAction (halfAction m ell (state F z hz g))) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hr := radius_nonnegative (halfAction m ell (state F z hz g))
  have hs' := mul_nonneg (sq_nonneg (sourceTime 0)) hs
  have hr' := mul_nonneg (sq_nonneg (sourceTime 0)) hr
  nlinarith only [h,hs',hr']

end LowEnergy.SourceClockSourceTail
