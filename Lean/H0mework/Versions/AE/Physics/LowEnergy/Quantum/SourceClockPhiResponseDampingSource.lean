import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponsePositiveSource
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockSourceTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiResponseDampingSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussFockWeights
open GaussYukawaCoefficient GaussRadialDomain GaussYukawaOperator GaussRadialMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare
open SourceClockAcceleration SourceClockReflectedForm SourceClockSourceTail
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusResponseAffine SourceClockRadiusAffineCutoff
open SourceClockPhiRadiusResponsePositiveSource SourceScalarPairedTransport SourceScalarDoubleCurrent
open SourceScalarPositiveBulkWard SourceActualResolventEnergy SourceClockYukawaCubicCurrent FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem phi_one (z : SourceCoordinateSlice) : 1 ≤ phiRadius z := by
  have hs : phiRadius z^2=1+‖scalarField z‖^2/4 := Real.sq_sqrt (by positivity)
  have hn : 0 ≤ phiRadius z := Real.sqrt_nonneg _
  nlinarith only [hs,hn,sq_nonneg ‖scalarField z‖]

private def thetaValue (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  (1-(phiRadius z)⁻¹)^(m+1)-(1-(phiRadius z)⁻¹)^(ell+1)

private theorem theta_bounds (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    0 ≤ thetaValue m ell z ∧ thetaValue m ell z ≤ (1-(phiRadius z)⁻¹)^(m+1) ∧
      thetaValue m ell z ≤ 1 := by
  have hs : 0 ≤ (phiRadius z)⁻¹ := inv_nonneg.mpr (by linarith only [phi_one z])
  have hs1 : (phiRadius z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (phi_one z)
  have hq : 0 ≤ 1-(phiRadius z)⁻¹ := sub_nonneg.mpr hs1
  have hq1 : 1-(phiRadius z)⁻¹ ≤ 1 := by linarith only [hs]
  have hp := pow_le_pow_of_le_one hq hq1 (Nat.add_le_add_right hml 1)
  refine ⟨sub_nonneg.mpr hp,sub_le_self _ (pow_nonneg hq _),?_⟩
  exact (sub_le_self _ (pow_nonneg hq _)).trans (pow_le_one₀ hq hq1)

private theorem theta_square_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    thetaValue m ell z^2 ≤ phiRadius z^2/(m+2:ℝ) := by
  have hr : 0 < phiRadius z := lt_of_lt_of_le zero_lt_one (phi_one z)
  have hs : 0 ≤ (phiRadius z)⁻¹ := (inv_pos.mpr hr).le
  have hs1 : (phiRadius z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (phi_one z)
  have ht := theta_bounds m ell hml z
  have hp := SourceNativeCutoffContact.squared_geometric_peak ((phiRadius z)⁻¹) hs hs1 (m+1)
  have hd : 2/(m+3:ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (m+3:ℝ))).mpr
    have hn : 0 ≤ (m:ℝ) := by positivity
    linarith only [hn]
  have hp' : (phiRadius z)⁻¹^2*(1-(phiRadius z)⁻¹)^(m+1) ≤ 1/(m+2:ℝ) := by
    apply (le_div_iff₀ (by positivity : 0 < (m+2:ℝ))).mpr
    push_cast at hp
    have hd' : 2/((m:ℝ)+1+2) ≤ 1 := by convert hd using 1;ring
    nlinarith only [hp.trans hd']
  have ht2 : thetaValue m ell z^2 ≤ (1-(phiRadius z)⁻¹)^(m+1) := by
    nlinarith only [ht.1,ht.2.1,ht.2.2]
  have h := (mul_le_mul_of_nonneg_left ht2 (sq_nonneg ((phiRadius z)⁻¹))).trans hp'
  have h' := mul_le_mul_of_nonneg_left h (sq_nonneg (phiRadius z))
  have he : phiRadius z^2*((phiRadius z)⁻¹^2*thetaValue m ell z^2)=thetaValue m ell z^2 := by
    field_simp [hr.ne']
  rw [he] at h'
  exact h'.trans_eq (by ring)

private theorem two_difference (a : ℝ) (u v : FockFiber) :
    ‖(a:ℂ) • u-v‖^2 ≤ 2*a^2*‖u‖^2+2*‖v‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le ((a:ℂ) • u) v) 2
  have hs := sq_nonneg (‖(a:ℂ) • u‖-‖v‖)
  have hb : ‖(a:ℂ) • u-v‖^2 ≤ 2*‖(a:ℂ) • u‖^2+2*‖v‖^2 := by
    nlinarith only [h,hs]
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,mul_assoc] using hb

private def localPrice (K α : ℝ) : ℝ := scalePrice+K/α
private def normError (K α : ℝ) (m : ℕ) : ℝ := 2*K*(localPrice K α)^4/(m+2:ℝ)

private theorem near_far_price (K α : ℝ) (hK : 0 ≤ K) (hα : 0 < α)
    (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) (u v : FockFiber) :
    K*‖(thetaValue m ell z:ℂ) • ((phiRadius z:ℂ) • u-v)‖^2 ≤
      α*(4*radius z^2-1)*‖(thetaValue m ell z:ℂ) • ((phiRadius z:ℂ) • u-v)‖^2+
      normError K α m*(‖u‖^2+‖v‖^2) := by
  have hC : 0 ≤ centerPrice := by unfold centerPrice;positivity
  have hL : 2 ≤ localPrice K α := by
    have hdiv := div_nonneg hK hα.le
    unfold localPrice scalePrice
    linarith only [hC,hdiv]
  have hE : 0 ≤ normError K α m := by unfold normError;positivity
  have hrad := one_le_radius z
  have hrad' : 0 ≤ 4*radius z^2-1 := by nlinarith only [hrad]
  by_cases hfar : localPrice K α ≤ phiRadius z
  · have hb := (abs_le.mp (original_radius_center_bound z)).1
    change -centerPrice ≤ radius z-phiRadius z at hb
    have hr : 2+K/α ≤ radius z := by
      dsimp only [localPrice,scalePrice] at hfar
      linarith only [hfar,hb]
    have hk' : K ≤ α*radius z := by
      have h := mul_le_mul_of_nonneg_left hr hα.le
      rw [mul_add,mul_div_cancel₀ _ hα.ne'] at h
      linarith only [h,hα]
    have hcoeff : K ≤ α*(4*radius z^2-1) := by
      have hm := mul_nonneg hα.le (show 0 ≤ 4*radius z^2-1-radius z by nlinarith only [hrad])
      linarith only [hk',hm]
    have h := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖(thetaValue m ell z:ℂ) • ((phiRadius z:ℂ) • u-v)‖)
    exact h.trans (le_add_of_nonneg_right (mul_nonneg hE (by positivity)))
  · have hnear : phiRadius z ≤ localPrice K α := (not_le.mp hfar).le
    have hρ0 := (phi_one z).trans' (by norm_num : (0:ℝ) ≤ 1)
    have hρ2 := pow_le_pow_left₀ hρ0 hnear 2
    have ht2 := (theta_square_bound m ell hml z).trans
      (div_le_div_of_nonneg_right hρ2 (by positivity : 0 ≤ (m+2:ℝ)))
    have hL2 : 1 ≤ (localPrice K α)^2 := by nlinarith only [hL,sq_nonneg (localPrice K α-2)]
    have hu := mul_le_mul_of_nonneg_right hρ2 (sq_nonneg ‖u‖)
    have hv' := mul_le_mul_of_nonneg_right hL2 (sq_nonneg ‖v‖)
    have hv := (two_difference (phiRadius z) u v).trans
      (by nlinarith only [hu,hv'] :
        2*phiRadius z^2*‖u‖^2+2*‖v‖^2 ≤ 2*(localPrice K α)^2*(‖u‖^2+‖v‖^2))
    have hp := mul_le_mul ht2 hv (sq_nonneg ‖(phiRadius z:ℂ) • u-v‖) (by positivity)
    have h := mul_le_mul_of_nonneg_left hp hK
    have he : K*((localPrice K α)^2/(m+2:ℝ)*(2*(localPrice K α)^2*(‖u‖^2+‖v‖^2)))=
        normError K α m*(‖u‖^2+‖v‖^2) := by unfold normError;ring
    rw [he] at h
    have hx : K*‖(thetaValue m ell z:ℂ) • ((phiRadius z:ℂ) • u-v)‖^2 ≤
        normError K α m*(‖u‖^2+‖v‖^2) := by
      simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,mul_assoc] using h
    exact hx.trans (le_add_of_nonneg_left (mul_nonneg (mul_nonneg hα.le hrad') (sq_nonneg _)))

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

private def windowed (m ell : ℕ) (q h : QuantumTest) : QuantumTest :=
  phiThetaAction m ell (phiRadiusAction q-h)

private theorem phi_power_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    (((1-phiInverseAction)^n) f) x=((1-(affineRadius x)⁻¹:ℝ):ℂ)^n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (((1-phiInverseAction)^n) f) x-(phiReciprocal x:ℂ) • ((((1-phiInverseAction)^n) f) x)=_
    rw [ih,pow_succ',mul_smul]
    unfold phiReciprocal phiRadius
    push_cast
    module

private theorem windowed_point (m ell : ℕ) (q h : QuantumTest) (x : SourceCoordinateSlice) :
    windowed m ell q h x=(thetaValue m ell x:ℂ) • ((phiRadius x:ℂ) • q x-h x) := by
  change (((1-phiInverseAction)^(m+1)) (phiRadiusAction q-h)) x-
    (((1-phiInverseAction)^(ell+1)) (phiRadiusAction q-h)) x=_
  rw [phi_power_point,phi_power_point]
  change _=(thetaValue m ell x:ℂ) • ((phiRadiusAction q-h) x)
  simp only [thetaValue,←Complex.ofReal_pow,←sub_smul,←Complex.ofReal_sub]

private theorem density_square (f : QuantumTest) (z : physicalChart) :
    (densityPair f f z.val).re=
      ‖GaussBoundedMultiplier.halfWeight (fun N => GaussDensityCore.density N z.val) (f z.val)‖^2 := by
  change RCLike.re (inner ℂ (GaussFockWeights.weight
    (fun N => (GaussDensityCore.density N z.val:ℂ)) (f z.val)) (f z.val))=_
  exact GaussBoundedMultiplier.weighted_square _ (fun N => (GaussDensityCore.density_pos N z).le) _

private theorem density_point_price (K α : ℝ) (hK : 0 ≤ K) (hα : 0 < α)
    (m ell : ℕ) (hml : m ≤ ell) (q h : QuantumTest) (z : SourceCoordinateSlice) :
    K*(densityPair (windowed m ell q h) (windowed m ell q h) z).re ≤
      α*((4*radius z^2-1)*(densityPair (windowed m ell q h) (windowed m ell q h) z).re)+
      normError K α m*((densityPair q q z).re+(densityPair h h z).re) := by
  by_cases hz : z∈physicalChart
  · let x : physicalChart := ⟨z,hz⟩
    rw [density_square _ x,density_square q x,density_square h x]
    have hp := near_far_price K α hK hα m ell hml z
      (GaussBoundedMultiplier.halfWeight (fun N => GaussDensityCore.density N z) (q z))
      (GaussBoundedMultiplier.halfWeight (fun N => GaussDensityCore.density N z) (h z))
    rw [windowed_point,map_smul,map_sub,map_smul]
    simpa only [mul_assoc] using hp
  · have hq : q z=0 := image_eq_zero_of_notMem_tsupport (fun hh => hz (q.tsupport_subset hh))
    have hh : h z=0 := image_eq_zero_of_notMem_tsupport (fun hh => hz (h.tsupport_subset hh))
    have hv : windowed m ell q h z=0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hz ((windowed m ell q h).tsupport_subset hh))
    simp only [densityPair,hq,hh,hv,map_zero,inner_zero_left,Complex.zero_re,mul_zero,zero_add,le_refl]

private theorem norm_square_integral_re (f : QuantumTest) :
    ‖embed f‖^2=∫ z : SourceCoordinateSlice,(densityPair f f z).re
      ∂GaussHistoryHilbert.configurationMeasure := by
  simpa only [RCLike.re_eq_complex_re] using GaussBoundedMultiplier.norm_square_integral f

private theorem core_norm_absorption (K α : ℝ) (hK : 0 ≤ K) (hα : 0 < α)
    (m ell : ℕ) (hml : m ≤ ell) (q h : QuantumTest) :
    K*‖embed (windowed m ell q h)‖^2 ≤ α*radiusForm (windowed m ell q h)+
      normError K α m*(‖embed q‖^2+‖embed h‖^2) := by
  have hq : Integrable (fun x => (densityPair q q x).re) GaussHistoryHilbert.configurationMeasure := by
    simpa only [RCLike.re_eq_complex_re] using (densityPair_integrable q q).re
  have hh : Integrable (fun x => (densityPair h h x).re) GaussHistoryHilbert.configurationMeasure := by
    simpa only [RCLike.re_eq_complex_re] using (densityPair_integrable h h).re
  have hv : Integrable (fun x => (densityPair (windowed m ell q h) (windowed m ell q h) x).re)
      GaussHistoryHilbert.configurationMeasure := by
    simpa only [RCLike.re_eq_complex_re] using (densityPair_integrable (windowed m ell q h) (windowed m ell q h)).re
  have hr := radius_density_integrable (windowed m ell q h)
  have hi := integral_mono (hv.const_mul K)
    ((hr.const_mul α).add ((hq.add hh).const_mul (normError K α m)))
    (fun z => density_point_price K α hK hα m ell hml q h z)
  simp only [Pi.add_apply] at hi
  have hright :
      (∫ x : SourceCoordinateSlice, α*((4*radius x^2-1)*(densityPair (windowed m ell q h) (windowed m ell q h) x).re)+
        normError K α m*((densityPair q q x).re+(densityPair h h x).re)
        ∂GaussHistoryHilbert.configurationMeasure)=
      α*radiusForm (windowed m ell q h)+normError K α m*(‖embed q‖^2+‖embed h‖^2) := by
    calc
      _ = (∫ x : SourceCoordinateSlice, α*((4*radius x^2-1)*(densityPair (windowed m ell q h) (windowed m ell q h) x).re)
          ∂GaussHistoryHilbert.configurationMeasure)+
        (∫ x : SourceCoordinateSlice, normError K α m*((densityPair q q x).re+(densityPair h h x).re)
          ∂GaussHistoryHilbert.configurationMeasure) :=
        integral_add (hr.const_mul α) ((hq.add hh).const_mul (normError K α m))
      _ = _ := by
        rw [integral_const_mul,integral_const_mul]
        have hsum := integral_add hq hh
        rw [hsum,←radius_density,←norm_square_integral_re,
          ←norm_square_integral_re]
  rw [integral_const_mul] at hi
  change K*(∫ x : SourceCoordinateSlice,(densityPair (windowed m ell q h) (windowed m ell q h) x).re
    ∂GaussHistoryHilbert.configurationMeasure) ≤ _ at hi
  rw [hright,←norm_square_integral_re] at hi
  exact hi

private theorem lapse_pos : 0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem young (x y η : ℝ) (hη : 0 < η) : x*y ≤ η*x^2+y^2/(4*η) := by
  have h := sq_nonneg (2*η*x-y)
  have he : η*x^2+y^2/(4*η)=(4*η^2*x^2+y^2)/(4*η) := by field_simp
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < 4*η)).mpr
  nlinarith only [h]

private theorem coframe_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (sourceTime 0)^2/4*coframeGram (inverseVolumeAction (phiResponseCore m ell F z hz g)) ≤
      phiPositivePrice m ell F z hz g := by
  rw [actual_phi_positive_source]
  have hs : 0 ≤ scalarForm (inverseVolumeAction (phiResponseCore m ell F z hz g)) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hr : 0 ≤ radiusForm (phiResponseCore m ell F z hz g) := by
    rw [radius_density]
    apply integral_nonneg
    intro x
    change 0 ≤ (4*radius x^2-1)*(densityPair (phiResponseCore m ell F z hz g) (phiResponseCore m ell F z hz g) x).re
    have h1 := one_le_radius x
    have hc : 0 ≤ 4*radius x^2-1 := by nlinarith only [h1]
    by_cases hx : x∈physicalChart
    · have hf := density_square (phiResponseCore m ell F z hz g) ⟨x,hx⟩
      rw [hf]
      exact mul_nonneg hc (sq_nonneg _)
    · have hf : phiResponseCore m ell F z hz g x=0 :=
        image_eq_zero_of_notMem_tsupport (fun hh => hx ((phiResponseCore m ell F z hz g).tsupport_subset hh))
      simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,mul_zero,le_refl]
  have hS := mul_nonneg (by positivity : 0 ≤ (sourceTime 0)^2/2) hs
  have hR := mul_nonneg (by positivity : 0 ≤ 2*(sourceTime 0)^2) hr
  linarith only [hS,hR]

private theorem radius_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    2*(sourceTime 0)^2*radiusForm (phiResponseCore m ell F z hz g) ≤ phiPositivePrice m ell F z hz g := by
  rw [actual_phi_positive_source]
  have hc := original_coframe_gram_nonnegative (inverseVolumeAction (phiResponseCore m ell F z hz g))
  have hs : 0 ≤ scalarForm (inverseVolumeAction (phiResponseCore m ell F z hz g)) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC := mul_nonneg (by positivity : 0 ≤ (sourceTime 0)^2/4) hc
  have hS := mul_nonneg (by positivity : 0 ≤ (sourceTime 0)^2/2) hs
  linarith only [hC,hS]

def dampingError (ν α : ℝ) (m : ℕ) : ℝ := normError (3*ν^2/α) (α*(sourceTime 0)^2) m

/-- The damping spends an arbitrary source-price fraction and an internally shrinking two-input error. -/
theorem actual_phi_damping_source (ν α : ℝ) (hα : 0 < α) (m ell : ℕ) (hml : m ≤ ell)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    2*|ν| * |(sourcePair (phiResponseCore m ell F z hz g)
      (clockCurrent (phiResponseCore m ell F z hz g))).re| ≤
      α*phiPositivePrice m ell F z hz g+dampingError ν α m*
        (‖embed (resolventCore F z hz (coreEquiv.symm g))‖^2+
          ‖embed (resolventCore F z hz (phiRadiusAction (coreEquiv.symm g)))‖^2) := by
  let v := phiResponseCore m ell F z hz g
  have hJ := original_clock_current_gram v
  have hC := mul_le_mul_of_nonneg_left (coframe_price m ell F z hz g)
    (by norm_num : (0:ℝ) ≤ 3/2)
  have hJ' : ‖embed (clockCurrent v)‖^2 ≤ (3/2:ℝ)*phiPositivePrice m ell F z hz g := by
    dsimp only [v] at hJ
    nlinarith only [hJ,hC]
  have hp := (Complex.abs_re_le_norm (sourcePair v (clockCurrent v))).trans
    (norm_inner_le_norm (𝕜 := ℂ) (embed v) (embed (clockCurrent v)))
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*|ν| by positivity)
  have hy := young ‖embed (clockCurrent v)‖ (2*|ν| * ‖embed v‖) (α/3) (by positivity)
  have hpaid := mul_le_mul_of_nonneg_left hJ' (show 0 ≤ α/3 by positivity)
  have hy' : 2*|ν| * |(sourcePair v (clockCurrent v)).re| ≤
      (α/2)*phiPositivePrice m ell F z hz g+(3*ν^2/α)*‖embed v‖^2 := by
    have he : (2*|ν| * ‖embed v‖)^2/(4*(α/3))=(3*ν^2/α)*‖embed v‖^2 := by
      rw [mul_pow,mul_pow,sq_abs]
      field_simp
      ring
    rw [he] at hy
    nlinarith only [hp',hy,hpaid]
  have hn : sourceTime 0≠0 := lapse_pos.ne'
  have hβ : 0 < α*(sourceTime 0)^2 := mul_pos hα (sq_pos_of_ne_zero hn)
  have hv := core_norm_absorption (3*ν^2/α) (α*(sourceTime 0)^2) (by positivity) hβ m ell hml
    (resolventCore F z hz (coreEquiv.symm g))
    (resolventCore F z hz (phiRadiusAction (coreEquiv.symm g)))
  change (3*ν^2/α)*‖embed v‖^2 ≤ α*(sourceTime 0)^2*radiusForm v+dampingError ν α m*
    (‖embed (resolventCore F z hz (coreEquiv.symm g))‖^2+
      ‖embed (resolventCore F z hz (phiRadiusAction (coreEquiv.symm g)))‖^2) at hv
  have hr := mul_le_mul_of_nonneg_left (radius_price m ell F z hz g) (show 0 ≤ α/2 by positivity)
  dsimp only [v] at hy' hv
  nlinarith only [hy',hv,hr]

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem original_input_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g:H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)

private theorem phi_input_embed (g : diagonal.domain) :
    embed (phiRadiusAction (coreEquiv.symm g))=(phiRadiusSource g:H) := rfl

private theorem actual_square (μ : ℝ) (hμ : 0 < μ) (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2))=
      ENNReal.ofReal (Real.pi/μ*‖g‖^2) := by
  simpa only [line,mul_comm (μ:ℂ) Complex.I] using SourceActualResolventEnergy.actual_square_lintegral F μ hμ g

def dampingBudget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (2*|μ| * |(sourcePair
    (phiResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)
    (clockCurrent (phiResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g))).re|)

/-- Every finite compression spends the same freely small fraction; only the original two fixed input masses pay the error. -/
theorem actual_phi_damping_common_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (α : ℝ) (hα : 0 < α) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      dampingBudget m ell F μ hμ g ≤
        ENNReal.ofReal α*phiPositiveBudget m ell F μ hμ g+ENNReal.ofReal ε := by
  intro ε hε
  let K := 3*μ^2/α
  let β := α*(sourceTime 0)^2
  let M := Real.pi/μ*(‖(g:H)‖^2+‖(phiRadiusSource g:H)‖^2)
  let C := 2*K*(localPrice K β)^4*M
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hM : 0 ≤ M := by dsimp [M];positivity
  have hC : 0 ≤ C := by dsimp [C];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hml F => ?_⟩
  have hden : 0 < (m+2:ℝ) := by positivity
  have hN' : C/ε < (m+2:ℝ) := by
    have hm' : (N:ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hN,hm']
  have htail : C/(m+2:ℝ) ≤ ε := by
    apply (div_le_iff₀ hden).mpr
    have h := (div_lt_iff₀ hε).mp hN'
    nlinarith only [h]
  have hE : 0 ≤ dampingError μ α m := by unfold dampingError normError;positivity
  have hR := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have mg : Measurable (fun w : ℝ => ENNReal.ofReal (‖finiteResolvent F (line μ w) (g:H)‖^2)) :=
    ((hR.clm_apply continuous_const).norm.pow 2).measurable.ennreal_ofReal
  have mh : Measurable (fun w : ℝ => ENNReal.ofReal (‖finiteResolvent F (line μ w) (phiRadiusSource g:H)‖^2)) :=
    ((hR.clm_apply continuous_const).norm.pow 2).measurable.ennreal_ofReal
  have merror : Measurable (fun w : ℝ => ENNReal.ofReal (dampingError μ α m)*
      (ENNReal.ofReal (‖finiteResolvent F (line μ w) (g:H)‖^2)+
        ENNReal.ofReal (‖finiteResolvent F (line μ w) (phiRadiusSource g:H)‖^2))) :=
    (mg.add mh).const_mul (ENNReal.ofReal (dampingError μ α m))
  have hi : dampingBudget m ell F μ hμ g ≤
      ENNReal.ofReal α*phiPositiveBudget m ell F μ hμ g+
      ENNReal.ofReal (dampingError μ α m)*ENNReal.ofReal M := by
    unfold dampingBudget phiPositiveBudget
    calc
      _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal α*
          ENNReal.ofReal (phiPositivePrice m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)+
          ENNReal.ofReal (dampingError μ α m)*
            (ENNReal.ofReal (‖finiteResolvent F (line μ w) (g:H)‖^2)+
              ENNReal.ofReal (‖finiteResolvent F (line μ w) (phiRadiusSource g:H)‖^2)) := by
        apply lintegral_mono
        intro w
        dsimp only
        have hp := actual_phi_damping_source μ α hα m ell hml F (line μ w)
          (by simpa only [line_im] using hμ.ne') g
        rw [resolvent_embed,resolvent_embed,original_input_embed,phi_input_embed] at hp
        apply (ENNReal.ofReal_le_ofReal hp).trans
        calc
          _ ≤ ENNReal.ofReal (α*phiPositivePrice m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)+
              ENNReal.ofReal (dampingError μ α m*
                (‖finiteResolvent F (line μ w) (g:H)‖^2+‖finiteResolvent F (line μ w) (phiRadiusSource g:H)‖^2)) :=
            ENNReal.ofReal_add_le
          _ = _ := by
            rw [ENNReal.ofReal_mul hα.le,ENNReal.ofReal_mul hE,
              ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      _ = _ := by
        rw [lintegral_add_right _ merror,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_right _ mh,
          actual_square μ hμ F (g:H),actual_square μ hμ F (phiRadiusSource g:H),
          ←ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        dsimp only [M]
        ring
  have he : dampingError μ α m*M=C/(m+2:ℝ) := by
    dsimp only [dampingError,normError,K,β,C]
    ring
  calc
    _ ≤ ENNReal.ofReal α*phiPositiveBudget m ell F μ hμ g+
        ENNReal.ofReal (dampingError μ α m)*ENNReal.ofReal M := hi
    _ = ENNReal.ofReal α*phiPositiveBudget m ell F μ hμ g+ENNReal.ofReal (C/(m+2:ℝ)) := by
      rw [←ENNReal.ofReal_mul hE,he]
    _ ≤ _ := add_le_add le_rfl (ENNReal.ofReal_le_ofReal htail)

end LowEnergy.SourceClockPhiResponseDampingSource
