import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFirstCurrentJointPayment
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiMatchedElectricSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.JointElectricSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceClockAcceleration SourceClockPhiRadiusAcceleration
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourceLocalizedInverseFormPayment SourceScalarPositiveBulkWard
open SourceResolventBandLimit SourceJointResidualEnergy SourceInverseNoetherChannelGap FullYSourceResolventGraphSplice
open SourceInverseElectricMomentChannels SourceClockPhiNativeJointPayment SourceClockPhiNormalizedScalarBudget
open SourceClockPhiMatchedElectricSource SourceClockPhiNativeMatchedSource SourceClockPhiWholeSignedWorkIntegrable
open FinitePhysicalSource MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev CE : End := fullElectricCurrent
private abbrev E : End := electricAction
private abbrev U : End := inverseVolumeAction
private abbrev L : End := electricLyapunov
private abbrev P : End := electricPrimitive
private abbrev H0 : End := diagonalAction
private abbrev n : ℝ := sourceTime 0
attribute [local irreducible] diagonalAction compressionCore defectAction sourcePair embed

private theorem lapse_pos : 0 < n := by
  change 0 < sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_sub_l (f g h : QuantumTest) : sourcePair (f-g) h = sourcePair f h-sourcePair g h := by
  simp only [sourcePair, map_sub, inner_sub_left]
private theorem pair_sub_r (f g h : QuantumTest) : sourcePair f (g-h) = sourcePair f g-sourcePair f h := by
  simp only [sourcePair, map_sub, inner_sub_right]
private theorem pair_add_l (f g h : QuantumTest) : sourcePair (f+g) h = sourcePair f h+sourcePair g h := by
  simp only [sourcePair, map_add, inner_add_left]
private theorem pair_add_r (f g h : QuantumTest) : sourcePair f (g+h) = sourcePair f g+sourcePair f h := by
  simp only [sourcePair, map_add, inner_add_right]
private theorem pair_smul_l (a : ℂ) (f g : QuantumTest) : sourcePair (a • f) g = star a*sourcePair f g := by
  simp only [sourcePair, map_smul, inner_smul_left, starRingEnd_apply]
private theorem pair_smul_r (a : ℂ) (f g : QuantumTest) : sourcePair f (a • g) = a*sourcePair f g := by
  simp only [sourcePair, map_smul, inner_smul_right]
private theorem pair_self (f : QuantumTest) : (sourcePair f f).re = ‖embed f‖^2 := by
  simpa only [sourcePair, RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) (embed f)).symm
private theorem E_pair (f g : QuantumTest) : sourcePair f (E g) = sourcePair (E f) g := multiply_pair _ _ f g
private theorem U_pair (f g : QuantumTest) : sourcePair f (U g) = sourcePair (U f) g := multiply_pair _ _ f g
private theorem CE_pair (f g : QuantumTest) : sourcePair f (CE g) = -sourcePair (CE f) g := by
  have h1 : sourcePair f (H0 (E g)) = sourcePair (E (H0 f)) g := by
    rw [diagonalAction_pair f (E g), E_pair (H0 f) g]
  have h2 : sourcePair f (E (H0 g)) = sourcePair (H0 (E f)) g := by
    rw [E_pair f (H0 g), diagonalAction_pair (E f) g]
  change sourcePair f ((1/2:ℂ) • (H0 (E g)-E (H0 g))) =
    -sourcePair ((1/2:ℂ) • (H0 (E f)-E (H0 f))) g
  rw [pair_smul_r, pair_smul_l, pair_sub_r, pair_sub_l, h1, h2]
  norm_num
  ring

private theorem electric_scalar_weight (t : ℝ) (z : SourceCoordinateSlice) :
    electricWeight (SourceScalarAffineScaleTransport.scaleEquiv t z) = electricWeight z := rfl
private theorem electric_scalar_flow (t : ℝ) (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    SourceScalarAffineScaleTransport.coreFlow t (E f) z word =
      (electricWeight z : ℂ) * SourceScalarAffineScaleTransport.coreFlow t f z word := by
  rw [SourceScalarAffineScaleTransport.coreFlow_apply, SourceScalarAffineScaleTransport.coreFlow_apply]
  change _ * ((electricWeight (SourceScalarAffineScaleTransport.scaleEquiv t z) : ℂ) *
    f (SourceScalarAffineScaleTransport.scaleEquiv t z) word) = _
  rw [electric_scalar_weight]
  ring
private theorem electric_phi_generator : Commute E SourceScalarAffineScaleTransport.generator := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have h1 := SourceScalarAffineScaleTransport.component_flow_derivative (E f) z word 0
  have h2 := (SourceScalarAffineScaleTransport.component_flow_derivative f z word 0).const_mul
    (electricWeight z : ℂ)
  have he : (fun t : ℝ => SourceScalarAffineScaleTransport.coreFlow t (E f) z word) =
      (fun t : ℝ => (electricWeight z : ℂ) * SourceScalarAffineScaleTransport.coreFlow t f z word) :=
    funext (fun t => electric_scalar_flow t f z word)
  rw [he] at h1
  have h := h1.unique h2
  simp only [SourceScalarAffineScaleTransport.coreFlow_zero] at h
  exact h.symm
private theorem electric_inverse_commute : Commute E U := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (electricWeight z : ℂ) • ((reciprocalVolume z : ℂ) • f z) =
    (reciprocalVolume z : ℂ) • ((electricWeight z : ℂ) • f z)
  exact smul_comm _ _ _
private theorem electric_radius_commute : Commute E phiRadiusAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (electricWeight z : ℂ) • ((phiRadius z : ℂ) • f z) =
    (phiRadius z : ℂ) • ((electricWeight z : ℂ) • f z)
  exact smul_comm _ _ _

/-- This CE restriction keeps the full gauge and coframe source, and fixes the original scalar radius. -/
theorem actual_electric_phi_square : bracket CE phiSquare = 0 := by
  have hphi : bracket E phiSquare = 0 := sub_eq_zero.mpr (electric_radius_commute.pow_right 2).eq
  have hUPhi : bracket E (U * SourceScalarAffineScaleTransport.generator) = 0 := by
    apply sub_eq_zero.mpr
    apply LinearMap.ext
    intro f
    have h1 := LinearMap.congr_fun electric_inverse_commute.eq (SourceScalarAffineScaleTransport.generator f)
    have h2 := LinearMap.congr_fun electric_phi_generator.eq f
    change E (U (SourceScalarAffineScaleTransport.generator f)) =
      U (SourceScalarAffineScaleTransport.generator (E f))
    change E (U (SourceScalarAffineScaleTransport.generator f)) = U (E (SourceScalarAffineScaleTransport.generator f)) at h1
    change E (SourceScalarAffineScaleTransport.generator f) = SourceScalarAffineScaleTransport.generator (E f) at h2
    rw [h1, h2]
  have hH : bracket H0 phiSquare = (n/2:ℂ) • (U * SourceScalarAffineScaleTransport.generator) :=
    original_phi_square_current
  have hj : bracket (bracket H0 E) phiSquare =
      bracket H0 (bracket E phiSquare) - bracket E (bracket H0 phiSquare) := by
    unfold bracket
    noncomm_ring
  change (CE*phiSquare-phiSquare*CE) = 0
  have he : CE*phiSquare-phiSquare*CE = (1/2:ℂ) • bracket (bracket H0 E) phiSquare := by
    unfold CE fullElectricCurrent bracket
    simp only [smul_mul_assoc, mul_smul_comm]
    module
  rw [he, hj, hphi, hH]
  have hs : bracket E ((n/2:ℂ) • (U * SourceScalarAffineScaleTransport.generator)) =
      (n/2:ℂ) • bracket E (U * SourceScalarAffineScaleTransport.generator) := by
    unfold bracket
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [hs, hUPhi]
  simp only [bracket, mul_zero, zero_mul, sub_self, smul_zero]

private theorem electric_double (F : Index) (g : diagonal.domain) :
    bracket E (bracket H0 E) = (4:ℂ) • (U*E) + wedgeAction := by
  have h := (actual_matched_electric_source 0 0 F Complex.I (by simp) g).2.2
  have hH : H0 = compressionCore F + defectAction F := by
    unfold H0 defectAction
    module
  rw [hH]
  unfold bracket at h ⊢
  linear_combination (norm := noncomm_ring) h

theorem actual_electric_field_current (F : Index) (g : diagonal.domain) :
    bracket CE E = (-2:ℂ) • (U*E) - (1/2:ℂ) • wedgeAction := by
  have he : bracket CE E = (-1/2:ℂ) • bracket E (bracket H0 E) := by
    unfold CE fullElectricCurrent bracket
    simp only [smul_sub]
    noncomm_ring
    module
  rw [he, electric_double F g]
  module

/-- The primitive in the original full-forcing word is a restriction of the same electric Lyapunov. -/
theorem actual_electric_primitive_normal_form :
    P = (2/(n:ℂ)) • phiSquare + (5/2:ℂ) • E - (2:ℂ) • L := by
  change (2/(n:ℂ)) • phiSquare - (4/(n:ℂ)) • clock + (1/2:ℂ) • E =
    (2/(n:ℂ)) • phiSquare + (5/2:ℂ) • E - (2:ℂ) • (E+(2/(n:ℂ)) • clock)
  module

/-- The matched electric primitive dissipates both the original UE slot and the complete wedge. -/
theorem actual_matched_primitive_electric_current (F : Index) (g : diagonal.domain) :
    bracket CE P = (-5:ℂ) • (U*E) - (1/4:ℂ) • wedgeAction := by
  have hL := original_electric_positive_current.2.1
  have he : bracket CE P = (2/(n:ℂ)) • bracket CE phiSquare +
      (5/2:ℂ) • bracket CE E - (2:ℂ) • bracket CE L := by
    rw [actual_electric_primitive_normal_form]
    unfold bracket
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      smul_sub]
    module
  rw [he, actual_electric_phi_square, actual_electric_field_current F g, hL]
  module

private theorem density_nonnegative (f : QuantumTest) (z : physicalChart) :
    0 ≤ (densityPair f f z.val).re := by
  have h := GaussBoundedMultiplier.weighted_square (fun N => GaussDensityCore.density N z.val)
    (fun N => (GaussDensityCore.density_pos N z).le) (f z.val)
  exact (sq_nonneg _).trans_eq h.symm
private theorem electric_weight_positive (z : physicalChart) : 0 ≤ electricWeight z.val := by
  have hn := lapse_pos
  have hs : 0 < sourceSigma :=
    SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource.legacy.sigma_pos
  have hv := volume_pos z
  have hG := SourceCornerWeight.gauge_square_nonneg z.val
  unfold electricWeight SourceGaugeRadiusMetric.electricSquare reciprocalVolume
  positivity
private theorem real_multiplier_nonnegative (a : SourceCoordinateSlice → ℝ)
    (ha : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val)
    (hpos : ∀ z : physicalChart, 0 ≤ a z.val) (f : QuantumTest) :
    0 ≤ (sourcePair f (multiply a ha f)).re := by
  have hp : (sourcePair f (multiply a ha f)).re =
      ∫ z : SourceCoordinateSlice, (densityPair f (multiply a ha f) z).re
        ∂GaussHistoryHilbert.configurationMeasure := by
    rw [sourcePair_integral]
    exact (integral_re (densityPair_integrable f (multiply a ha f))).symm
  rw [hp]
  apply integral_nonneg
  intro z
  change 0 ≤ (densityPair f (multiply a ha f) z).re
  by_cases hz : z ∈ physicalChart
  · have he : densityPair f (multiply a ha f) z = (a z : ℂ) * densityPair f f z := inner_smul_right _ _ _
    rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (hpos ⟨z,hz⟩) (density_nonnegative f ⟨z,hz⟩)
  · have hf : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair, hf, map_zero, inner_zero_left, Complex.zero_re, le_refl]

theorem actual_electric_energy_nonnegative (f : QuantumTest) : 0 ≤ (sourcePair f (E f)).re :=
  real_multiplier_nonnegative electricWeight _ electric_weight_positive f
private theorem inverse_electric_nonnegative (f : QuantumTest) : 0 ≤ (sourcePair f ((U*E) f)).re := by
  let a : SourceCoordinateSlice → ℝ := fun z => reciprocalVolume z * electricWeight z
  have ha (z : physicalChart) : ContDiffAt ℝ ∞ a z.val :=
    (reciprocal_volume_smooth z).mul (by
      change ContDiffAt ℝ ∞ (fun z => reciprocalVolume z * SourceGaugeRadiusMetric.electricSquare z) z.val
      exact (reciprocal_volume_smooth z).mul (SourceGaugeRadialCurrent.electric_square_smooth z))
  have he : U*E = multiply a ha := by
    apply LinearMap.ext
    intro q
    apply DFunLike.ext
    intro z
    change (reciprocalVolume z : ℂ) • ((electricWeight z : ℂ) • q z) =
      ((reciprocalVolume z * electricWeight z : ℝ) : ℂ) • q z
    rw [smul_smul, Complex.ofReal_mul]
  rw [he]
  apply real_multiplier_nonnegative a ha
  intro z
  exact mul_nonneg (inv_nonneg.mpr (volume_pos z).le) (electric_weight_positive z)

/-- Both endpoint restrictions are generated from the same source midpoint, with no inverse or group premise. -/
def electricEndpoint (h : ℝ) (forward : Bool) : End :=
  (1:End) + (if forward then -(h:ℂ) else (h:ℂ)) • CE

private theorem endpoint_apply (h : ℝ) (forward : Bool) (w : QuantumTest) :
    electricEndpoint h forward w = w + (if forward then -(h:ℂ) else (h:ℂ)) • CE w := rfl

private theorem midpoint_word (h : ℝ) (T : End) (w : QuantumTest) :
    sourcePair (electricEndpoint h true w) (T (electricEndpoint h true w)) -
      sourcePair (electricEndpoint h false w) (T (electricEndpoint h false w)) =
      (2*(h:ℂ)) * sourcePair w ((bracket CE T) w) := by
  simp only [endpoint_apply, Bool.false_eq_true, ite_true, ite_false, map_add, map_smul,
    pair_add_l, pair_add_r, pair_smul_l, pair_smul_r, star_neg,
    Complex.star_def, Complex.conj_ofReal]
  have hC : sourcePair w (CE (T w)) = -sourcePair (CE w) (T w) := CE_pair w (T w)
  change _ = (2*(h:ℂ)) * sourcePair w (CE (T w) - T (CE w))
  rw [pair_sub_r, hC]
  ring

/-- A finite source step preserves norm, increases volume, and spends the original electric/log-volume quantity. -/
theorem actual_electric_midpoint_update (h : ℝ) (w : QuantumTest) :
    ‖embed (electricEndpoint h true w)‖^2 = ‖embed (electricEndpoint h false w)‖^2 ∧
    (sourcePair (electricEndpoint h true w) (volumeAction (electricEndpoint h true w))).re -
      (sourcePair (electricEndpoint h false w) (volumeAction (electricEndpoint h false w))).re =
      2*h*n*(sourcePair w (E w)).re ∧
    (sourcePair (electricEndpoint h true w) (L (electricEndpoint h true w))).re -
      (sourcePair (electricEndpoint h false w) (L (electricEndpoint h false w))).re =
      -h*(sourcePair w (wedgeAction w)).re := by
  have h0 := congrArg Complex.re (midpoint_word h 1 w)
  have hV := congrArg Complex.re (midpoint_word h volumeAction w)
  have hL := congrArg Complex.re (midpoint_word h L w)
  have hzero : bracket CE (1:End) = 0 := by unfold bracket; simp
  rw [hzero] at h0
  simp only [Module.End.one_apply, LinearMap.zero_apply, sourcePair, map_zero, inner_zero_right,
    mul_zero, Complex.zero_re, Complex.sub_re] at h0
  have hs (q : QuantumTest) : (inner ℂ (embed q) (embed q)).re = ‖embed q‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) (embed q)).symm
  simp only [hs] at h0
  rw [original_electric_positive_current.1] at hV
  rw [original_electric_positive_current.2.1] at hL
  norm_num only [LinearMap.smul_apply, pair_smul_r, Complex.sub_re, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im,
    Complex.normSq_ofNat, Complex.one_re, Complex.one_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero, neg_zero] at hV hL
  refine ⟨by linarith only [h0], ?_, ?_⟩
  · linear_combination hV
  · linear_combination hL

/-- The exact matched primitive and electric energy share one generated midpoint update and geometric debit. -/
theorem actual_electric_midpoint_primitive (F : Index) (g : diagonal.domain) (h : ℝ) (w : QuantumTest) :
    (sourcePair (electricEndpoint h true w) (E (electricEndpoint h true w))).re -
      (sourcePair (electricEndpoint h false w) (E (electricEndpoint h false w))).re =
      -4*h*(sourcePair w ((U*E) w)).re - h*(sourcePair w (wedgeAction w)).re ∧
    (sourcePair (electricEndpoint h true w) (P (electricEndpoint h true w))).re -
      (sourcePair (electricEndpoint h false w) (P (electricEndpoint h false w))).re =
      -10*h*(sourcePair w ((U*E) w)).re - (h/2)*(sourcePair w (wedgeAction w)).re := by
  have hE := congrArg Complex.re (midpoint_word h E w)
  have hP := congrArg Complex.re (midpoint_word h P w)
  rw [actual_electric_field_current F g] at hE
  rw [actual_matched_primitive_electric_current F g] at hP
  norm_num only [LinearMap.sub_apply, LinearMap.smul_apply, pair_sub_r, pair_smul_r,
    Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.neg_im, Complex.div_re,
    Complex.div_im, Complex.normSq_ofNat, Complex.one_re, Complex.one_im, mul_zero, zero_mul, sub_zero, zero_add,
    add_zero, neg_zero] at hE hP
  constructor
  · linear_combination hE
  · linear_combination hP

/-- The generated nonnegative endpoint electric energy pays the complete UE/wedge output. -/
theorem actual_midpoint_electric_payment (F : Index) (g : diagonal.domain) (h : ℝ) (hh : 0 ≤ h)
    (w : QuantumTest) :
    0 ≤ 4*h*(sourcePair w ((U*E) w)).re + h*(sourcePair w (wedgeAction w)).re ∧
    4*h*(sourcePair w ((U*E) w)).re + h*(sourcePair w (wedgeAction w)).re ≤
      (sourcePair (electricEndpoint h false w) (E (electricEndpoint h false w))).re ∧
    (sourcePair (electricEndpoint h true w) (P (electricEndpoint h true w))).re ≤
      (sourcePair (electricEndpoint h false w) (P (electricEndpoint h false w))).re := by
  have he := actual_electric_midpoint_primitive F g h w
  have hu := inverse_electric_nonnegative w
  have hw := original_electric_positive_current.2.2.1 w
  have hp := actual_electric_energy_nonnegative (electricEndpoint h true w)
  have hU := mul_nonneg hh hu
  have hW := mul_nonneg hh hw
  constructor
  · nlinarith only [hU, hW]
  constructor
  · linarith only [he.1, hp]
  · nlinarith only [he.2, hU, hW]

private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell

private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (phiReciprocal x:ℂ) • ((phiRadius x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'

private theorem theta_commute (m ell:ℕ) : Commute S (T m ell) :=by
  let Q:End:=(1:End)-S
  have hQ(f:QuantumTest):S (Q f)=Q (S f):=by
    change S (f-S f)=S f-S (S f)
    rw [map_sub]
  have hp(k:ℕ)(f:QuantumTest):S ((Q^k) f)=(Q^k) (S f):=by
    induction k with
    | zero => simp only [pow_zero,Module.End.one_apply]
    | succ k ih =>
      rw [pow_succ']
      change S (Q ((Q^k) f))=Q ((Q^k) (S f))
      rw [hQ,ih]
  change S*(Q^(m+1)-Q^(ell+1))=(Q^(m+1)-Q^(ell+1))*S
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply,LinearMap.sub_apply,map_sub,hp]

private theorem source_step (F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    compressionCore F (resolventCore F z hz f)=f+z • resolventCore F z hz f := by
  have he (u:QuantumTest):embed (compressionCore F u)=GaussGradedCompression.compression F (embed u) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hr (u:QuantumTest):embed (resolventCore F z hz u)=finiteResolvent F z (embed u) := by
    unfold resolventCore SourceScalarPositiveBulkWard.state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have h:=congrArg (fun A:H  →L[ℂ] H=>A (embed f))
    (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
  apply embed_injective
  simp only [he,hr,map_add,map_smul]
  have hf:FullYSourceResolventGraphSplice.resolvent (GaussGradedCompression.compression F) z=
      finiteResolvent F z := by unfold finiteResolvent;rfl
  rw [hf] at h
  change (GaussGradedCompression.compression F-z • 1) (finiteResolvent F z (embed f))=embed f at h
  simp only [sub_apply,smul_apply,one_apply_eq_self] at h
  linear_combination (norm:=module) h


theorem actual_full_normalized_source (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    diagonalAction (normalizedState m ell F z hz g)=normalizedForcing m ell F z hz g+
      z • normalizedState m ell F z hz g := by
  let q:=resolventCore F z hz (coreEquiv.symm g)
  let h:=resolventCore F z hz (r (coreEquiv.symm g))
  have hq:diagonalAction q=coreEquiv.symm g+z • q+defectAction F q := by
    have hx:=source_step F z hz (coreEquiv.symm g)
    change compressionCore F q=coreEquiv.symm g+z • q at hx
    rw [←hx]
    simp only [defectAction,LinearMap.sub_apply]
    module
  have hh:diagonalAction h=r (coreEquiv.symm g)+z • h+defectAction F h := by
    have hx:=source_step F z hz (r (coreEquiv.symm g))
    change compressionCore F h=r (coreEquiv.symm g)+z • h at hx
    rw [←hx]
    simp only [defectAction,LinearMap.sub_apply]
    module
  have htr:(S*T m ell)*r=T m ell := by
    apply LinearMap.ext
    intro f
    have hc:=LinearMap.congr_fun (theta_commute m ell).eq (r f)
    have hr:=LinearMap.congr_fun inverse_radius f
    simp only [Module.End.mul_apply,Module.End.one_apply] at hc hr ⊢
    rw [hc,hr]

  have ht:=LinearMap.congr_fun htr (coreEquiv.symm g)
  unfold normalizedForcing normalizedState bracket
  change diagonalAction (T m ell q-(S*T m ell) h)=
    ((diagonalAction*(T m ell)-(T m ell)*diagonalAction) q-
      (diagonalAction*(S*T m ell)-(S*T m ell)*diagonalAction) h+
      T m ell (defectAction F q)-(S*T m ell) (defectAction F h))+z • (T m ell q-(S*T m ell) h)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,hq,hh,map_add,map_smul] at ht ⊢
  linear_combination (norm:=module) -ht


/-- The same midpoint step produces its complete H0 forcing, including the double electric current. -/
def electricUpdatedForcing (h : ℝ) (forward : Bool) (w f : QuantumTest) : QuantumTest :=
  electricEndpoint h forward f +
    (if forward then -(h:ℂ) else (h:ℂ)) • (bracket H0 CE w)

theorem actual_electric_updated_forcing (h : ℝ) (forward : Bool)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    let f := normalizedForcing m ell F z hz g
    H0 (electricEndpoint h forward w) = electricUpdatedForcing h forward w f +
      z • electricEndpoint h forward w := by
  dsimp only
  have hs := actual_full_normalized_source m ell F z hz g
  change H0 (normalizedState m ell F z hz g) =
    normalizedForcing m ell F z hz g + z • normalizedState m ell F z hz g at hs
  simp only [electricUpdatedForcing, endpoint_apply]
  change H0 (normalizedState m ell F z hz g +
      (if forward then -(h:ℂ) else (h:ℂ)) • CE (normalizedState m ell F z hz g)) =
    normalizedForcing m ell F z hz g +
      (if forward then -(h:ℂ) else (h:ℂ)) • CE (normalizedForcing m ell F z hz g) +
      (if forward then -(h:ℂ) else (h:ℂ)) •
        (H0 (CE (normalizedState m ell F z hz g)) - CE (H0 (normalizedState m ell F z hz g))) +
      z • (normalizedState m ell F z hz g +
        (if forward then -(h:ℂ) else (h:ℂ)) • CE (normalizedState m ell F z hz g))
  rw [map_add, map_smul, hs, map_add, map_smul]
  module

/-- The current remainder consumes the original electric forcing primitive, with the full defect unchanged. -/
theorem actual_first_current_electric_return (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    firstCurrentJointRemainder m ell F z hz g = electricForcingWord m ell F z hz g -
      ClockPhiMatchedGainFrequencyPayment.gainFrequency m ell F z hz g -
      (n/48) * comparisonEnergy w + (5*n/48) * ‖embed (U w)‖^2 := by
  have h := actual_whole_signed_joint_balance m ell F z hz g
  have he := (actual_matched_electric_source m ell F z hz g).2.1
  dsimp only at h ⊢
  unfold wholeSignedWork at h
  rw [he] at h
  linarith only [h]

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (q : ℝ) :
    (actualFrequency advanced μ q).im ≠ 0 := by
  cases advanced <;> simpa only [actualFrequency, Bool.false_eq_true, ite_false, ite_true,
    Complex.star_def, Complex.conj_im, line_im, neg_ne_zero] using hμ.ne'

/-- The midpoint update pays its original UE/wedge output on the full frequency line, before any common-tail limit. -/
theorem actual_electric_frequency_payment (μ : ℝ) (hμ : 0 < μ) (advanced : Bool)
    (h : ℝ) (hh : 0 ≤ h) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    let w : ℝ → QuantumTest := fun q => normalizedState m ell F (actualFrequency advanced μ q)
      (frequency_nonreal advanced μ hμ q) g
    Integrable (fun q : ℝ => 4*h*(sourcePair (w q) ((U*E) (w q))).re +
      h*(sourcePair (w q) (wedgeAction (w q))).re) ∧
    (∫ q : ℝ, 4*h*(sourcePair (w q) ((U*E) (w q))).re +
      h*(sourcePair (w q) (wedgeAction (w q))).re) ≤
      ∫ q : ℝ, (sourcePair (electricEndpoint h false (w q)) (E (electricEndpoint h false (w q)))).re ∧
    (∫ q : ℝ, (sourcePair (electricEndpoint h true (w q)) (P (electricEndpoint h true (w q)))).re) ≤
      ∫ q : ℝ, (sourcePair (electricEndpoint h false (w q)) (P (electricEndpoint h false (w q)))).re := by
  intro w
  have hu := (actual_normalized_pair_integrable μ hμ advanced m ell F g 1 (U*E)).re
  have hw := (actual_normalized_pair_integrable μ hμ advanced m ell F g 1 wedgeAction).re
  have he := (actual_normalized_pair_integrable μ hμ advanced m ell F g
    (electricEndpoint h false) (E*electricEndpoint h false)).re
  have hp (b : Bool) := (actual_normalized_pair_integrable μ hμ advanced m ell F g
    (electricEndpoint h b) (P*electricEndpoint h b)).re
  have hi : Integrable (fun q : ℝ => 4*h*(sourcePair (w q) ((U*E) (w q))).re +
      h*(sourcePair (w q) (wedgeAction (w q))).re) :=
    (hu.const_mul (4*h)).add (hw.const_mul h)
  refine ⟨hi, ?_, ?_⟩
  · apply integral_mono hi he
    intro q
    exact (actual_midpoint_electric_payment F g h hh (w q)).2.1
  · apply integral_mono (hp true) (hp false)
    intro q
    exact (actual_midpoint_electric_payment F g h hh (w q)).2.2

/-- The matched primitive is paid by the same source update that preserves both full forcing equations. -/
theorem actual_joint_electric_source_update (h : ℝ) (hh : 0 ≤ h)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    let f := normalizedForcing m ell F z hz g
    (∀ b : Bool, H0 (electricEndpoint h b w) = electricUpdatedForcing h b w f +
      z • electricEndpoint h b w) ∧
    ‖embed (electricEndpoint h true w)‖^2 = ‖embed (electricEndpoint h false w)‖^2 ∧
    (sourcePair (electricEndpoint h true w) (P (electricEndpoint h true w))).re ≤
      (sourcePair (electricEndpoint h false w) (P (electricEndpoint h false w))).re ∧
    firstCurrentJointRemainder m ell F z hz g = electricForcingWord m ell F z hz g -
      ClockPhiMatchedGainFrequencyPayment.gainFrequency m ell F z hz g -
      (n/48) * comparisonEnergy w + (5*n/48) * ‖embed (U w)‖^2 := by
  dsimp only
  exact ⟨fun b => actual_electric_updated_forcing h b m ell F z hz g,
    (actual_electric_midpoint_update h (normalizedState m ell F z hz g)).1,
    (actual_midpoint_electric_payment F g h hh (normalizedState m ell F z hz g)).2.2,
    actual_first_current_electric_return m ell F z hz g⟩
end LowEnergy.JointElectricSource
