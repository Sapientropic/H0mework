import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarAffineCutoffTail
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarVacuumRadialJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.SourceScalarAffineSecondCutoffTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open GaussRadialDomain GaussYukawaCoefficient GaussUnitaryHistory SourceNativeCutoffContact
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarAffineScaleTransport SourceMixedNativeReturn SourceRelativePowerTail
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open GaussNativeForm GaussNativeMatter
open GaussFockWeights GaussRadialMomentum
open SourceScalarAffineCutoffTail SourceScalarVirialBulk
open scoped InnerProductSpace ContDiff Topology
abbrev End := SourceScalarGaugeScale.End

private theorem half_geometric (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) (hm : 1 ≤ m) :
    (m+1 : ℝ)*(1-q)*q^m  ≤  3*(q^(m/2+1)-q^(m+1)) := by
  let h := m/2+1
  let n := m-m/2
  have ht (h n : ℕ) : (∑ j ∈ Finset.range n,(q^(h+j)-q^(h+j+1)))=q^h-q^(h+n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      have he : h+(n+1)=h+n+1 := by omega
      rw [he]
      ring
  have hs : (n : ℝ)*((1-q)*q^m)  ≤  q^h-q^(h+n) := by
    calc
      _ = ∑ j ∈ Finset.range n,(1-q)*q^m := by simp
      _  ≤  ∑ j ∈ Finset.range n,(q^(h+j)-q^(h+j+1)) := by
        apply Finset.sum_le_sum
        intro j hj
        have he : h+j ≤ m := by dsimp [h,n] at *;have := Finset.mem_range.mp hj;omega
        have hp := pow_le_pow_of_le_one hq hq1 he
        have hc := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hq1)
        simpa only [pow_succ] using! (show (1-q)*q^m ≤ q^(h+j)-q^(h+j)*q from by nlinarith [hc])
      _ = _ := ht h n
  have hn : (m+1 : ℝ)  ≤  3*(n : ℝ) := by
    exact_mod_cast (show m+1 ≤ 3*n from by dsimp [n];omega)
  have hp : 0 ≤ (1-q)*q^m := mul_nonneg (sub_nonneg.mpr hq1) (pow_nonneg hq m)
  have hc := mul_le_mul_of_nonneg_right hn hp
  have he : h+n=m+1 := by dsimp [h,n];omega
  rw [he] at hs
  dsimp [h] at hs
  nlinarith

/-- Two source derivative weights pay one original quarter-index relative-tail window. -/
theorem second_geometric (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 3 ≤ m) :
    (m+1 : ℝ)*m*(1-q)^2*q^(m-1) ≤
      72*(q^(((m-1)/2)/2+1)-q^((m-1)/2+1)) := by
  let h := (m-1)/2
  have hh : 1 ≤ h := by dsimp [h];omega
  have hhalf := half_geometric q hq hq1 h hh
  let d := q^(h/2+1)-q^(h+1)
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact sub_nonneg.mpr (pow_le_pow_of_le_one hq hq1 (by omega : h/2+1 ≤ h+1))
  have hd1 : d ≤ 1 := by
    dsimp [d]
    have hp : q^(h/2+1) ≤ 1 := pow_le_one₀ hq hq1
    have hpn : 0 ≤ q^(h+1) := pow_nonneg hq _
    linarith
  have he : q^(m-1) ≤ q^(2*h) := pow_le_pow_of_le_one hq hq1 (by dsimp [h];omega)
  have hn : (m : ℝ) ≤ 2*(h+1 : ℝ) := by exact_mod_cast (show m≤2*(h+1) from by dsimp [h];omega)
  have hn2 : (m+1 : ℝ) ≤ 2*(m : ℝ) := by exact_mod_cast (show m+1≤2*m from by omega)
  have hs : 0 ≤ 1-q := sub_nonneg.mpr hq1
  have hqpow : 0 ≤ q^h := pow_nonneg hq _
  have hp : 0 ≤ (m : ℝ)*(1-q)*q^h := by positivity
  have hbound : (m : ℝ)*(1-q)*q^h ≤ 6*d := by
    dsimp [d] at hhalf ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hqpow]
  have hpow : q^(2*h)=(q^h)^2 := by rw [mul_comm 2 h,pow_mul]
  have hmain : (m+1 : ℝ)*m*(1-q)^2*q^(m-1) ≤
      2*((m : ℝ)*(1-q)*q^h)^2 := by
    calc
      _ ≤ (m+1 : ℝ)*m*(1-q)^2*q^(2*h) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = (m+1 : ℝ)*m*((1-q)*q^h)^2 := by rw [hpow];ring
      _ ≤ 2*((m : ℝ)*(1-q)*q^h)^2 := by
        nlinarith [sq_nonneg ((1-q)*q^h)]
  have hsq := pow_le_pow_left₀ hp hbound 2
  nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hd1)]

def secondGeometricCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  ((m+1 : ℝ)*m*(reciprocal z)^2*(1-reciprocal z)^(m-1)-
    (ell+1 : ℝ)*ell*(reciprocal z)^2*(1-reciprocal z)^(ell-1))

private theorem second_geometric_smooth (m ell : ℕ) :
    ContDiff ℝ ∞ (secondGeometricCoefficient m ell) :=
  (((contDiff_const.mul contDiff_const).mul (reciprocal_smooth.pow 2)).mul
    ((contDiff_const.sub reciprocal_smooth).pow _)).sub
  (((contDiff_const.mul contDiff_const).mul (reciprocal_smooth.pow 2)).mul
    ((contDiff_const.sub reciprocal_smooth).pow _))

def secondGeometricAction (m ell : ℕ) : End :=
  multiply (secondGeometricCoefficient m ell)
    (fun _ => (second_geometric_smooth m ell).contDiffAt)

private theorem second_geometric_domination (m ell : ℕ) (hm : 3 ≤ m) (hell : m ≤ ell)
    (z : SourceCoordinateSlice) :
    (secondGeometricCoefficient m ell z)^2 ≤
      10368*((theta ((((m-1)/2)/2)) ((m-1)/2) z)^2+
        (theta ((((ell-1)/2)/2)) ((ell-1)/2) z)^2) := by
  let s := reciprocal z
  let q := 1-s
  have hs : 0 ≤ s := (inv_pos.mpr (radius_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ q := sub_nonneg.mpr hs1
  have hq1 : q ≤ 1 := by dsimp [q];linarith
  have hA := second_geometric q hq hq1 m hm
  have hB := second_geometric q hq hq1 ell (hm.trans hell)
  have hpa : 0 ≤ (m+1 : ℝ)*m*s^2*q^(m-1) := by positivity
  have hpb : 0 ≤ (ell+1 : ℝ)*ell*s^2*q^(ell-1) := by positivity
  have hab := abs_sub ((m+1 : ℝ)*m*s^2*q^(m-1))
    ((ell+1 : ℝ)*ell*s^2*q^(ell-1))
  rw [abs_of_nonneg hpa,abs_of_nonneg hpb] at hab
  have he : secondGeometricCoefficient m ell z=
      (m+1 : ℝ)*m*s^2*q^(m-1)-(ell+1 : ℝ)*ell*s^2*q^(ell-1) := rfl
  have hb : |secondGeometricCoefficient m ell z| ≤
      72*(theta ((((m-1)/2)/2)) ((m-1)/2) z+
        theta ((((ell-1)/2)/2)) ((ell-1)/2) z) := by
    rw [he]
    dsimp [theta,q,s] at hA hB ⊢
    nlinarith
  have hn := sq_nonneg (theta ((((m-1)/2)/2)) ((m-1)/2) z-
    theta ((((ell-1)/2)/2)) ((ell-1)/2) z)
  have hp := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hp
  nlinarith

private theorem real_inner_scaled {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (r : ℝ) (x : E) :
    (inner ℂ (A ((r : ℂ) • x)) ((r : ℂ) • x)).re=r^2*(inner ℂ (A x) x).re := by
  rw [map_smul,inner_smul_left,inner_smul_right,starRingEnd_apply,Complex.star_def,Complex.conj_ofReal]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

private theorem scalar_density (a : SourceCoordinateSlice → ℝ)
    (ha : ∀ z : physicalChart,ContDiffAt ℝ ∞ a z.val) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (densityPair (multiply a ha f) (multiply a ha f) z).re=
      (a z)^2*(densityPair f f z).re := by
  change (inner ℂ (weight (fun N => GaussDensityCore.complexDensity N z) ((a z : ℂ) • f z))
    ((a z : ℂ) • f z)).re=_
  exact real_inner_scaled _ _ _

private theorem density_nonnegative (f : QuantumTest) (z : SourceCoordinateSlice) :
    0 ≤ (densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · change 0 ≤ RCLike.re (inner ℂ (weight (fun N => (GaussDensityCore.density N z : ℂ)) (f z)) (f z))
    rw [GaussBoundedMultiplier.weighted_square _ (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le)]
    exact sq_nonneg _
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

/-- The double-binomial source multiplier is paid by two actual quarter-index source tails. -/
theorem actual_second_geometric_norm_domination (m ell : ℕ) (hm : 3 ≤ m)
    (hell : m ≤ ell) (f : QuantumTest) :
    ‖embed (secondGeometricAction m ell f)‖^2 ≤
      10368*(‖relativeTail ((((m-1)/2)/2)) ((m-1)/2) (embed f)‖^2+
        ‖relativeTail ((((ell-1)/2)/2)) ((ell-1)/2) (embed f)‖^2) := by
  have hi := (densityPair_integrable
    (SourceNativeCutoffContact.thetaAction ((((m-1)/2)/2)) ((m-1)/2) f)
    (SourceNativeCutoffContact.thetaAction ((((m-1)/2)/2)) ((m-1)/2) f)).re
  have hj := (densityPair_integrable
    (SourceNativeCutoffContact.thetaAction ((((ell-1)/2)/2)) ((ell-1)/2) f)
    (SourceNativeCutoffContact.thetaAction ((((ell-1)/2)/2)) ((ell-1)/2) f)).re
  have ha := (densityPair_integrable (secondGeometricAction m ell f)
    (secondGeometricAction m ell f)).re
  have ht (a b : ℕ) : embed (SourceNativeCutoffContact.thetaAction a b f)=
      relativeTail a b (embed f) := SourceNativeCutoffContact.theta_core a b f
  rw [←ht,←ht]
  rw [GaussBoundedMultiplier.norm_square_integral,GaussBoundedMultiplier.norm_square_integral,
    GaussBoundedMultiplier.norm_square_integral,←integral_add hi hj,←integral_const_mul]
  apply integral_mono ha ((hi.add hj).const_mul 10368)
  intro z
  have h := mul_le_mul_of_nonneg_right
    (second_geometric_domination m ell hm hell z) (density_nonnegative f z)
  change (densityPair (secondGeometricAction m ell f) (secondGeometricAction m ell f) z).re ≤
    10368*((densityPair
      (SourceNativeCutoffContact.thetaAction ((((m-1)/2)/2)) ((m-1)/2) f)
      (SourceNativeCutoffContact.thetaAction ((((m-1)/2)/2)) ((m-1)/2) f) z).re+
      (densityPair
        (SourceNativeCutoffContact.thetaAction ((((ell-1)/2)/2)) ((ell-1)/2) f)
        (SourceNativeCutoffContact.thetaAction ((((ell-1)/2)/2)) ((ell-1)/2) f) z).re)
  simp only [secondGeometricAction,SourceNativeCutoffContact.thetaAction,scalar_density]
  nlinarith

private theorem point_energy (a b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ≤ 10368*(b+c)) :
    ENNReal.ofReal a ≤ ENNReal.ofReal 10368*(ENNReal.ofReal b+ENNReal.ofReal c) := by
  rw [←ENNReal.ofReal_add hb hc,←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10368)]
  exact ENNReal.ofReal_le_ofReal h

/-- The genuinely second-binomial source coefficient has a common full-frequency tail
for the actual varying finite-resolvent input. -/
theorem actual_second_geometric_retarded_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceRead F g (secondGeometricAction m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := SourceRetardedForcingTail.actual_theta_full_frequency_tail
    μ hμ g (ε/(2*10368)) (by positivity)
  refine ⟨4*N+8,fun m hm ell hell => ?_⟩
  have hm0 : 3 ≤ m := by omega
  have hmN : N ≤ ((m-1)/2)/2 := by omega
  have heN : N ≤ ((ell-1)/2)/2 := by omega
  have hml : ((m-1)/2)/2 ≤ (m-1)/2 := Nat.div_le_self _ 2
  have hel : ((ell-1)/2)/2 ≤ (ell-1)/2 := Nat.div_le_self _ 2
  filter_upwards [hN _ hmN _ hml,hN _ heN _ hel] with F hA hB
  have hb (w : ℝ) :
      ‖sourceRead F g (secondGeometricAction m ell) (finiteResolvent F (line μ w) (g : H))‖^2 ≤
      10368*(‖relativeTail ((((m-1)/2)/2)) ((m-1)/2)
          (finiteResolvent F (line μ w) (g : H))‖^2+
        ‖relativeTail ((((ell-1)/2)/2)) ((ell-1)/2)
          (finiteResolvent F (line μ w) (g : H))‖^2) := by
    have hz : (line μ w).im ≠ 0 := by simpa only [line_im] using hμ.ne'
    rw [source_read_resolvent F g (secondGeometricAction m ell) (line μ w) hz]
    have h := actual_second_geometric_norm_domination m ell hm0 hell
      (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (line μ w) hz g))
    have hv : embed (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (line μ w) hz g))=
        finiteResolvent F (line μ w) (g : H) :=
      congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    simpa only [hv] using! h
  have hmA : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖relativeTail ((((m-1)/2)/2)) ((m-1)/2)
        (finiteResolvent F (line μ w) (g : H))‖^2)) :=
    ((((relativeTail _ _).continuous.comp
      ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply
        continuous_const)).norm.pow 2).measurable.ennreal_ofReal)
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 10368*
        (ENNReal.ofReal (‖relativeTail ((((m-1)/2)/2)) ((m-1)/2)
          (finiteResolvent F (line μ w) (g : H))‖^2)+
         ENNReal.ofReal (‖relativeTail ((((ell-1)/2)/2)) ((ell-1)/2)
          (finiteResolvent F (line μ w) (g : H))‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      exact point_energy _ _ _ (sq_nonneg _) (sq_nonneg _) (hb w)
    _ = ENNReal.ofReal 10368*((∫⁻ w : ℝ, ENNReal.ofReal
          (‖relativeTail ((((m-1)/2)/2)) ((m-1)/2)
            (finiteResolvent F (line μ w) (g : H))‖^2))+
        ∫⁻ w : ℝ, ENNReal.ofReal
          (‖relativeTail ((((ell-1)/2)/2)) ((ell-1)/2)
            (finiteResolvent F (line μ w) (g : H))‖^2)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_left hmA]
    _ ≤ ENNReal.ofReal 10368*
        (ENNReal.ofReal (ε/(2*10368))+ENNReal.ofReal (ε/(2*10368))) :=
      mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤10368)]
      congr 1
      ring

def affineQ (z : SourceCoordinateSlice) : ℝ :=
  reciprocal z*(1-(reciprocal z)^2)-
    radialDerivative ((vacuum : Scalar),0) z

private theorem affine_q_derivative (z : SourceCoordinateSlice) :
    fderiv ℝ (fun x : SourceCoordinateSlice => 1-reciprocal x) z
      (SourceScalarVirialBulk.phiEuler z)=affineQ z := by
  have hd := (hasFDerivAt_const (1 : ℝ) z).sub
    ((reciprocal_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have h := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ => D (SourceScalarVirialBulk.phiEuler z)) hd.fderiv
  change fderiv ℝ (fun x : SourceCoordinateSlice => 1-reciprocal x) z (SourceScalarVirialBulk.phiEuler z)=_ at h
  rw [h]
  simp only [zero_sub,neg_apply]
  rw [GaussRadialMomentum.reciprocal_derivative]
  simp only [SourceScalarVirialBulk.phiEuler,neg_div,neg_neg]
  change inner ℝ (z.2.1 : Scalar) ((vacuum : Scalar)+(z.2.1 : Scalar)) /
    (4*radius z^3)=_
  rw [inner_add_right,real_inner_self_eq_norm_sq]
  have hr : radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 :=
    Real.sq_sqrt (by positivity)
  have hn : ‖(z.2.1 : Scalar)‖^2=4*(radius z^2-1) := by nlinarith
  rw [hn]
  unfold affineQ radialDerivative reciprocal
  field_simp [(radius_pos z).ne']
  ring

private theorem affine_q_bound (z : SourceCoordinateSlice) :
    |affineQ z| ≤ (1+‖(vacuum : Scalar)‖/2)*reciprocal z := by
  let s := reciprocal z
  have hs : 0 ≤ s := (inv_pos.mpr (radius_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hfactor : 0 ≤ 1-s^2 := by nlinarith
  have hfactor1 : 1-s^2 ≤ 1 := by nlinarith
  have hd := SourceNativeCutoffContact.reciprocal_native_bound ((vacuum : Scalar),0) z
  have hs2 : s^2 ≤ s := by nlinarith
  have ha : 0 ≤ s*(1-s^2) := mul_nonneg hs hfactor
  have hb : s*(1-s^2) ≤ s := mul_le_of_le_one_right hs hfactor1
  have hdn : -(‖(vacuum : Scalar)‖/2)*s^2 ≤
      radialDerivative ((vacuum : Scalar),0) z := by
    simpa only [neg_mul] using (neg_le_of_abs_le hd)
  have hdp : radialDerivative ((vacuum : Scalar),0) z ≤
      (‖(vacuum : Scalar)‖/2)*s^2 := le_of_abs_le hd
  dsimp [affineQ]
  rw [abs_le]
  constructor <;> nlinarith [norm_nonneg (vacuum : Scalar)]

private theorem affine_q_smooth : ContDiff ℝ ∞ affineQ :=
  (reciprocal_smooth.mul (contDiff_const.sub (reciprocal_smooth.pow 2))).sub
    (radialDerivative_smooth ((vacuum : Scalar),0))

def secondPeakCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  ((m+1 : ℝ)*m*(1-reciprocal z)^(m-1)-
    (ell+1 : ℝ)*ell*(1-reciprocal z)^(ell-1))*(affineQ z)^2

private theorem second_peak_smooth (m ell : ℕ) :
    ContDiff ℝ ∞ (secondPeakCoefficient m ell) :=
  (((contDiff_const.mul contDiff_const).mul
    ((contDiff_const.sub reciprocal_smooth).pow _)).sub
  ((contDiff_const.mul contDiff_const).mul
    ((contDiff_const.sub reciprocal_smooth).pow _))).mul (affine_q_smooth.pow 2)

def secondPeakAction (m ell : ℕ) : End :=
  multiply (secondPeakCoefficient m ell)
    (fun _ => (second_peak_smooth m ell).contDiffAt)

private theorem second_peak_coefficient_domination (m ell : ℕ)
    (z : SourceCoordinateSlice) :
    (secondPeakCoefficient m ell z)^2 ≤
      ((1+‖(vacuum : Scalar)‖/2)^4)*
        (secondGeometricCoefficient m ell z)^2 := by
  let K := 1+‖(vacuum : Scalar)‖/2
  let s := reciprocal z
  let D := (m+1 : ℝ)*m*(1-s)^(m-1)-(ell+1 : ℝ)*ell*(1-s)^(ell-1)
  have hA := affine_q_bound z
  change |affineQ z| ≤ K*s at hA
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hs : 0 ≤ s := (inv_pos.mpr (radius_pos z)).le
  have hA2 : (affineQ z)^2 ≤ (K*s)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hA 2
    simpa only [sq_abs] using h
  have hA4 : ((affineQ z)^2)^2 ≤ ((K*s)^2)^2 :=
    pow_le_pow_left₀ (sq_nonneg _) hA2 2
  have hgeom : secondGeometricCoefficient m ell z=D*s^2 := by
    dsimp [secondGeometricCoefficient,D,s]
    ring
  rw [hgeom]
  change (D*(affineQ z)^2)^2 ≤ (K^4)*(D*s^2)^2
  have hD : 0 ≤ D^2 := sq_nonneg D
  rw [mul_pow,mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left hA4 hD]

theorem actual_second_peak_norm_domination (m ell : ℕ) (f : QuantumTest) :
    ‖embed (secondPeakAction m ell f)‖^2 ≤
      ((1+‖(vacuum : Scalar)‖/2)^4)*
        ‖embed (secondGeometricAction m ell f)‖^2 := by
  have ha := (densityPair_integrable (secondPeakAction m ell f)
    (secondPeakAction m ell f)).re
  have hb := (densityPair_integrable (secondGeometricAction m ell f)
    (secondGeometricAction m ell f)).re
  rw [GaussBoundedMultiplier.norm_square_integral,GaussBoundedMultiplier.norm_square_integral,
    ←integral_const_mul]
  apply integral_mono ha (hb.const_mul _)
  intro z
  have h := mul_le_mul_of_nonneg_right
    (second_peak_coefficient_domination m ell z) (density_nonnegative f z)
  change (densityPair (secondPeakAction m ell f) (secondPeakAction m ell f) z).re ≤
    ((1+‖(vacuum : Scalar)‖/2)^4)*
      (densityPair (secondGeometricAction m ell f) (secondGeometricAction m ell f) z).re
  simp only [secondPeakAction,secondGeometricAction,scalar_density]
  nlinarith

/-- The actual twice-differentiated binomial peak has a common whole-frequency tail
against the same moving finite-resolvent source. -/
theorem actual_second_peak_retarded_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceRead F g (secondPeakAction m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let K := (1+‖(vacuum : Scalar)‖/2)^4
  have hK : 0 ≤ K := by dsimp [K];positivity
  obtain ⟨N,hN⟩ := actual_second_geometric_retarded_tail μ hμ g
    (ε/(K+1)) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have hb (w : ℝ) :
      ‖sourceRead F g (secondPeakAction m ell)
        (finiteResolvent F (line μ w) (g : H))‖^2 ≤
        K*‖sourceRead F g (secondGeometricAction m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2 := by
    have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
    rw [source_read_resolvent F g (secondPeakAction m ell) (line μ w) hz,
      source_read_resolvent F g (secondGeometricAction m ell) (line μ w) hz]
    have h := actual_second_peak_norm_domination m ell
      (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (line μ w) hz g))
    have hv : embed (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (line μ w) hz g))=
        finiteResolvent F (line μ w) (g : H) :=
      congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    simpa only [hv] using! h
  have hmG : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖sourceRead F g (secondGeometricAction m ell)
        (finiteResolvent F (line μ w) (g : H))‖^2)) :=
    ((((sourceRead F g (secondGeometricAction m ell)).continuous.comp
      ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply
        continuous_const)).norm.pow 2).measurable.ennreal_ofReal)
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal K*ENNReal.ofReal
        (‖sourceRead F g (secondGeometricAction m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      exact (ENNReal.ofReal_le_ofReal (hb w)).trans_eq (ENNReal.ofReal_mul hK)
    _ = ENNReal.ofReal K*(∫⁻ w : ℝ, ENNReal.ofReal
        (‖sourceRead F g (secondGeometricAction m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2)) := by
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K*ENNReal.ofReal (ε/(K+1)) :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    _ = ENNReal.ofReal (K*(ε/(K+1))) := (ENNReal.ofReal_mul hK).symm
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (K+1)*(ε/(K+1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ε := by field_simp

private theorem field_multiplier (E : End) (v : SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (v z))
    (a : SourceCoordinateSlice → ℝ) (ha : ContDiff ℝ ∞ a)
    (f : QuantumTest) (z : SourceCoordinateSlice) :
    (E* multiply a (fun _ => ha.contDiffAt)-multiply a (fun _ => ha.contDiffAt)*E) f z=
      (fderiv ℝ a z (v z) : ℂ) • f z := by
  have hf : (multiply a (fun _ => ha.contDiffAt) f : SourceCoordinateSlice → FockFiber)=
      fun x => a x • f x := by
    funext x
    apply PiLp.ext
    intro word
    exact Complex.real_smul.symm
  change E (multiply a (fun _ => ha.contDiffAt) f) z-(a z : ℂ) • E f z=_
  rw [hE,hE,hf,fderiv_fun_smul (ha.differentiable (by simp)).differentiableAt
    (f.contDiff.differentiable (by simp)).differentiableAt]
  change a z • fderiv ℝ f z (v z)+fderiv ℝ a z (v z) • f z-
    (a z : ℂ) • fderiv ℝ f z (v z)=(fderiv ℝ a z (v z) : ℂ) • f z
  apply PiLp.ext
  intro word
  simp only [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,Complex.real_smul]
  ring

def firstCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  ((m+1 : ℝ)*(1-reciprocal z)^m-
    (ell+1 : ℝ)*(1-reciprocal z)^ell)*affineQ z

private theorem first_coefficient_smooth (m ell : ℕ) :
    ContDiff ℝ ∞ (firstCoefficient m ell) :=
  (((contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow m)).sub
      (contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow ell))).mul
    affine_q_smooth)

def firstAction (m ell : ℕ) : End :=
  multiply (firstCoefficient m ell) (fun _ => (first_coefficient_smooth m ell).contDiffAt)

private theorem theta_affine_derivative (m ell : ℕ) (z : SourceCoordinateSlice) :
    fderiv ℝ (SourceNativeCutoffContact.theta m ell) z
      (SourceScalarVirialBulk.phiEuler z)=firstCoefficient m ell z := by
  have hd := (hasFDerivAt_const (1 : ℝ) z).sub
    ((reciprocal_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have h := (hd.pow (m+1)).sub (hd.pow (ell+1))
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ =>
    D (SourceScalarVirialBulk.phiEuler z)) h.fderiv
  change fderiv ℝ (SourceNativeCutoffContact.theta m ell) z
    (SourceScalarVirialBulk.phiEuler z)=_ at he
  rw [he]
  simp only [sub_apply,smul_apply,smul_eq_mul,zero_sub,neg_apply,nsmul_eq_mul,
    Pi.sub_apply,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
  have hq := affine_q_derivative z
  have hdq := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ =>
    D (SourceScalarVirialBulk.phiEuler z)) hd.fderiv
  simp only [zero_sub] at hdq
  have hv : -(fderiv ℝ reciprocal z) (SourceScalarVirialBulk.phiEuler z)=affineQ z :=
    hdq.symm.trans hq
  rw [hv]
  unfold firstCoefficient
  ring

/-- The already compiled affine cutoff is the actual multiplier generated by the
original phi field acting on the original theta. -/
theorem actual_affine_first_multiplier (m ell : ℕ) : affineCutoff m ell=firstAction m ell := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have he := field_multiplier SourceScalarVirialBulk.phiEulerAction
    SourceScalarVirialBulk.phiEuler SourceScalarVirialBulk.phi_euler_apply
    (SourceNativeCutoffContact.theta m ell)
    (SourceNativeCutoffContact.theta_smooth m ell) f z
  change (SourceScalarVirialBulk.phiEulerAction*SourceNativeCutoffContact.thetaAction m ell-
    SourceNativeCutoffContact.thetaAction m ell*SourceScalarVirialBulk.phiEulerAction) f z=_ at he
  change (SourceScalarVirialBulk.phiEulerAction*SourceNativeCutoffContact.thetaAction m ell-
    SourceNativeCutoffContact.thetaAction m ell*SourceScalarVirialBulk.phiEulerAction) f z=
      (firstCoefficient m ell z : ℂ) • f z
  rw [theta_affine_derivative] at he
  exact he

def secondCutoff (m ell : ℕ) : End := deltaPhi (affineCutoff m ell)

def firstBinomial (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  (m+1 : ℝ)*(1-reciprocal z)^m-(ell+1 : ℝ)*(1-reciprocal z)^ell

def affineQPrime (z : SourceCoordinateSlice) : ℝ :=
  fderiv ℝ affineQ z (SourceScalarVirialBulk.phiEuler z)

/-- The original second phi cutoff is exactly the second field coefficient on each
source test. No derivative of the varying finite-resolvent input is introduced. -/
theorem actual_second_source_coefficient (m ell : ℕ) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    secondCutoff m ell f z=(fderiv ℝ (firstCoefficient m ell) z
      (SourceScalarVirialBulk.phiEuler z) : ℂ) • f z := by
  have he := field_multiplier SourceScalarVirialBulk.phiEulerAction
    SourceScalarVirialBulk.phiEuler SourceScalarVirialBulk.phi_euler_apply
    (firstCoefficient m ell) (first_coefficient_smooth m ell) f z
  unfold secondCutoff
  rw [actual_affine_first_multiplier]
  change (SourceScalarVirialBulk.phiEulerAction*firstAction m ell-
    firstAction m ell*SourceScalarVirialBulk.phiEulerAction) f z=_ at he
  exact he

/-- Exact two-term source chain rule: the paid double-binomial peak plus the
first binomial multiplied by the actual second affine q jet. -/
private theorem first_coefficient_derivative (m ell : ℕ) (z : SourceCoordinateSlice) :
    fderiv ℝ (firstCoefficient m ell) z (SourceScalarVirialBulk.phiEuler z)=
      secondPeakCoefficient m ell z+firstBinomial m ell z*affineQPrime z := by
  have hq := (hasFDerivAt_const (1 : ℝ) z).sub
    ((reciprocal_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have h1 := ((hq.pow m).const_mul (m+1 : ℝ)).sub
    ((hq.pow ell).const_mul (ell+1 : ℝ))
  have h2 := ((affine_q_smooth.differentiable (by simp)).differentiableAt
    (x := z)).hasFDerivAt
  have h := h1.mul h2
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ =>
    D (SourceScalarVirialBulk.phiEuler z)) h.fderiv
  change fderiv ℝ (firstCoefficient m ell) z
    (SourceScalarVirialBulk.phiEuler z)=_ at he
  rw [he]
  simp only [add_apply,sub_apply,smul_apply,smul_eq_mul,nsmul_eq_mul,neg_apply,zero_sub]
  have hdq := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ =>
    D (SourceScalarVirialBulk.phiEuler z)) hq.fderiv
  simp only [zero_sub] at hdq
  have hv : -(fderiv ℝ reciprocal z) (SourceScalarVirialBulk.phiEuler z)=affineQ z :=
    hdq.symm.trans (affine_q_derivative z)
  rw [hv]
  unfold firstBinomial affineQPrime secondPeakCoefficient
  simp only [Pi.sub_apply]
  ring

/-- Exact actual second-phi cutoff coefficient on the source core. -/
theorem actual_second_source_return (m ell : ℕ) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    secondCutoff m ell f z=
      ((secondPeakCoefficient m ell z+
        firstBinomial m ell z*affineQPrime z : ℝ) : ℂ) • f z := by
  rw [actual_second_source_coefficient,first_coefficient_derivative]

def vacuumRadialPrime (z : SourceCoordinateSlice) : ℝ :=
  fderiv ℝ (radialDerivative ((vacuum : Scalar),0)) z
    (SourceScalarVirialBulk.phiEuler z)

private theorem affine_q_prime_return (z : SourceCoordinateSlice) :
    affineQPrime z=-(1-3*(reciprocal z)^2)*affineQ z-vacuumRadialPrime z := by
  have hs := (reciprocal_smooth.differentiable (by simp)).differentiableAt
    (x := z) |>.hasFDerivAt
  have hd := ((radialDerivative_smooth ((vacuum : Scalar),0)).differentiable
    (by simp)).differentiableAt (x := z) |>.hasFDerivAt
  have h := (hs.sub (hs.pow 3)).sub hd
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ =>
    D (SourceScalarVirialBulk.phiEuler z)) h.fderiv
  have hf : (reciprocal-(fun x : SourceCoordinateSlice => reciprocal x^3)-
      radialDerivative ((vacuum : Scalar),0))=affineQ := by
    funext x
    dsimp [affineQ]
    ring
  rw [hf] at he
  change affineQPrime z=_ at he
  rw [he]
  simp only [sub_apply,smul_apply,smul_eq_mul,nsmul_eq_mul]
  have hq := affine_q_derivative z
  have hds := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ =>
    D (SourceScalarVirialBulk.phiEuler z))
      ((hasFDerivAt_const (1 : ℝ) z).sub hs).fderiv
  simp only [zero_sub,neg_apply] at hds
  have hv : (fderiv ℝ reciprocal z) (SourceScalarVirialBulk.phiEuler z)=-affineQ z := by
    have hne := hds.symm.trans hq
    have h := congrArg (fun r : ℝ => -r) hne
    simpa only [neg_neg] using h
  rw [hv]
  unfold vacuumRadialPrime
  ring

/-- The second actual affine source jet has one reciprocal weight, paid by the
same first-cutoff source scale. -/
theorem affine_q_prime_bound (z : SourceCoordinateSlice) :
    |affineQPrime z| ≤
      (2+3*‖(vacuum : Scalar)‖+‖(vacuum : Scalar)‖^2)*reciprocal z := by
  let s := reciprocal z
  let v := ‖(vacuum : Scalar)‖
  have hs : 0 ≤ s := (inv_pos.mpr (radius_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hfac : |1-3*s^2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg s]
  have hA : |affineQ z| ≤ (1+v/2)*s := affine_q_bound z
  have hR : |vacuumRadialPrime z| ≤ (2*v+v^2)*s := by
    exact SourceScalarVacuumRadialJet.actual_vacuum_radial_phi_bound z
  rw [affine_q_prime_return]
  have hmul : |-(1-3*s^2)*affineQ z|=|1-3*s^2| * |affineQ z| := by
    rw [abs_mul,abs_neg]
  have hsum : |-(1-3*s^2)*affineQ z-vacuumRadialPrime z| ≤
      |1-3*s^2| * |affineQ z|+|vacuumRadialPrime z| := by
    exact (abs_sub (-(1-3*s^2)*affineQ z) (vacuumRadialPrime z)).trans_eq
      (congrArg (fun r : ℝ => r+|vacuumRadialPrime z|) hmul)
  calc
    _ ≤ |1-3*s^2| * |affineQ z|+|vacuumRadialPrime z| := hsum
    _ ≤ 2*((1+v/2)*s)+(2*v+v^2)*s := by
      have hp := mul_le_mul hfac hA (abs_nonneg _) (by norm_num : (0 : ℝ)≤2)
      linarith
    _ = _ := by dsimp [v,s];ring

def firstGeometricCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  firstBinomial m ell z*reciprocal z

private theorem first_geometric_smooth (m ell : ℕ) :
    ContDiff ℝ ∞ (firstGeometricCoefficient m ell) :=
  (((contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow m)).sub
      (contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow ell))).mul
    reciprocal_smooth)

def firstGeometricAction (m ell : ℕ) : End :=
  multiply (firstGeometricCoefficient m ell)
    (fun _ => (first_geometric_smooth m ell).contDiffAt)

private theorem first_geometric_domination (m ell : ℕ) (hm : 1 ≤ m)
    (hell : m ≤ ell) (z : SourceCoordinateSlice) :
    (firstGeometricCoefficient m ell z)^2 ≤
      18*((theta (m/2) m z)^2+(theta (ell/2) ell z)^2) := by
  let s := reciprocal z
  let q := 1-s
  have hs : 0 ≤ s := (inv_pos.mpr (radius_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ q := sub_nonneg.mpr hs1
  have hq1 : q ≤ 1 := by dsimp [q];linarith
  have hA := half_geometric q hq hq1 m hm
  have hB := half_geometric q hq hq1 ell (hm.trans hell)
  have hpa : 0 ≤ (m+1 : ℝ)*s*q^m := by positivity
  have hpb : 0 ≤ (ell+1 : ℝ)*s*q^ell := by positivity
  have hab := abs_sub ((m+1 : ℝ)*s*q^m) ((ell+1 : ℝ)*s*q^ell)
  rw [abs_of_nonneg hpa,abs_of_nonneg hpb] at hab
  have he : firstGeometricCoefficient m ell z=
      ((m+1 : ℝ)*s*q^m)-((ell+1 : ℝ)*s*q^ell) := by
    dsimp [firstGeometricCoefficient,firstBinomial,s,q]
    ring
  have hb : |firstGeometricCoefficient m ell z| ≤
      3*(theta (m/2) m z+theta (ell/2) ell z) := by
    rw [he]
    dsimp [theta,q,s] at hA hB ⊢
    nlinarith
  have hn := sq_nonneg (theta (m/2) m z-theta (ell/2) ell z)
  have hp := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hp
  nlinarith

theorem actual_first_geometric_norm_domination (m ell : ℕ) (hm : 1 ≤ m)
    (hell : m ≤ ell) (f : QuantumTest) :
    ‖embed (firstGeometricAction m ell f)‖^2 ≤
      18*(‖relativeTail (m/2) m (embed f)‖^2+
        ‖relativeTail (ell/2) ell (embed f)‖^2) := by
  have hi := (densityPair_integrable (SourceNativeCutoffContact.thetaAction (m/2) m f)
    (SourceNativeCutoffContact.thetaAction (m/2) m f)).re
  have hj := (densityPair_integrable (SourceNativeCutoffContact.thetaAction (ell/2) ell f)
    (SourceNativeCutoffContact.thetaAction (ell/2) ell f)).re
  have ha := (densityPair_integrable (firstGeometricAction m ell f)
    (firstGeometricAction m ell f)).re
  have ht (a b : ℕ) : embed (SourceNativeCutoffContact.thetaAction a b f)=
      relativeTail a b (embed f) := SourceNativeCutoffContact.theta_core a b f
  rw [←ht,←ht]
  rw [GaussBoundedMultiplier.norm_square_integral,GaussBoundedMultiplier.norm_square_integral,
    GaussBoundedMultiplier.norm_square_integral,←integral_add hi hj,←integral_const_mul]
  apply integral_mono ha ((hi.add hj).const_mul 18)
  intro z
  have h := mul_le_mul_of_nonneg_right
    (first_geometric_domination m ell hm hell z) (density_nonnegative f z)
  change (densityPair (firstGeometricAction m ell f)
    (firstGeometricAction m ell f) z).re ≤
    18*((densityPair (SourceNativeCutoffContact.thetaAction (m/2) m f)
      (SourceNativeCutoffContact.thetaAction (m/2) m f) z).re+
      (densityPair (SourceNativeCutoffContact.thetaAction (ell/2) ell f)
        (SourceNativeCutoffContact.thetaAction (ell/2) ell f) z).re)
  simp only [firstGeometricAction,SourceNativeCutoffContact.thetaAction,scalar_density]
  nlinarith

private theorem second_coefficient_domination (m ell : ℕ) (z : SourceCoordinateSlice) :
    (secondPeakCoefficient m ell z+firstBinomial m ell z*affineQPrime z)^2 ≤
      2*((secondPeakCoefficient m ell z)^2+
        (2+3*‖(vacuum : Scalar)‖+‖(vacuum : Scalar)‖^2)^2*
          (firstGeometricCoefficient m ell z)^2) := by
  let C := 2+3*‖(vacuum : Scalar)‖+‖(vacuum : Scalar)‖^2
  let D := firstBinomial m ell z
  let s := reciprocal z
  have hA : |affineQPrime z| ≤ C*s := affine_q_prime_bound z
  have hA2 : (affineQPrime z)^2 ≤ (C*s)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hA 2
    simpa only [sq_abs] using h
  have hD : 0 ≤ D^2 := sq_nonneg D
  have hR : (D*affineQPrime z)^2 ≤ C^2*(D*s)^2 := by
    have h := mul_le_mul_of_nonneg_left hA2 hD
    nlinarith
  have hG : firstGeometricCoefficient m ell z=D*s := rfl
  rw [hG]
  nlinarith [sq_nonneg (secondPeakCoefficient m ell z-D*affineQPrime z)]

private theorem second_scalar_density (m ell : ℕ) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    (densityPair (secondCutoff m ell f) (secondCutoff m ell f) z).re=
      (secondPeakCoefficient m ell z+firstBinomial m ell z*affineQPrime z)^2*
        (densityPair f f z).re := by
  have h := actual_second_source_return m ell f z
  change (inner ℂ (weight (fun N => GaussDensityCore.complexDensity N z)
    (secondCutoff m ell f z)) (secondCutoff m ell f z)).re=_
  rw [h]
  exact real_inner_scaled _ _ _

/-- The actual second-phi cutoff on the complete source core is controlled by
the two source-generated full-frequency channels. -/
theorem actual_second_norm_domination (m ell : ℕ) (f : QuantumTest) :
    ‖embed (secondCutoff m ell f)‖^2 ≤
      2*(‖embed (secondPeakAction m ell f)‖^2+
        (2+3*‖(vacuum : Scalar)‖+‖(vacuum : Scalar)‖^2)^2*
          ‖embed (firstGeometricAction m ell f)‖^2) := by
  have ha := (densityPair_integrable (secondCutoff m ell f) (secondCutoff m ell f)).re
  have hb := (densityPair_integrable (secondPeakAction m ell f)
    (secondPeakAction m ell f)).re
  have hc := (densityPair_integrable (firstGeometricAction m ell f)
    (firstGeometricAction m ell f)).re
  rw [GaussBoundedMultiplier.norm_square_integral,
    GaussBoundedMultiplier.norm_square_integral,
    GaussBoundedMultiplier.norm_square_integral,
    ←integral_const_mul,←integral_add hb (hc.const_mul _),←integral_const_mul]
  apply integral_mono ha ((hb.add (hc.const_mul _)).const_mul 2)
  intro z
  have h := mul_le_mul_of_nonneg_right (second_coefficient_domination m ell z)
    (density_nonnegative f z)
  change (densityPair (secondCutoff m ell f) (secondCutoff m ell f) z).re ≤
    2*((densityPair (secondPeakAction m ell f) (secondPeakAction m ell f) z).re+
      (2+3*‖(vacuum : Scalar)‖+‖(vacuum : Scalar)‖^2)^2*
        (densityPair (firstGeometricAction m ell f)
          (firstGeometricAction m ell f) z).re)
  rw [second_scalar_density]
  simp only [secondPeakAction,firstGeometricAction,scalar_density]
  nlinarith

private theorem point_energy_first (a b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ≤ 18*(b+c)) :
    ENNReal.ofReal a ≤ ENNReal.ofReal 18*(ENNReal.ofReal b+ENNReal.ofReal c) := by
  rw [←ENNReal.ofReal_add hb hc,←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)]
  exact ENNReal.ofReal_le_ofReal h

/-- The actual varying finite-resolvent scalar-Euler cutoff has the original common full-frequency tail. -/
theorem actual_first_geometric_retarded_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N  ≤  m → ∀ ell, m  ≤  ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceRead F g (firstGeometricAction m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2))  ≤  ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := SourceRetardedForcingTail.actual_theta_full_frequency_tail μ hμ g (ε/36) (by positivity)
  refine ⟨2*N+2,fun m hm ell hell => ?_⟩
  have hm0 : 1 ≤ m := by omega
  have hmN : N ≤ m/2 := by omega
  have heN : N ≤ ell/2 := by omega
  filter_upwards [hN (m/2) hmN m (Nat.div_le_self m 2),
    hN (ell/2) heN ell (Nat.div_le_self ell 2)] with F hA hB
  have hb (w : ℝ) : ‖sourceRead F g (firstGeometricAction m ell) (finiteResolvent F (line μ w) (g : H))‖^2 ≤
      18*(‖relativeTail (m/2) m (finiteResolvent F (line μ w) (g : H))‖^2+
          ‖relativeTail (ell/2) ell (finiteResolvent F (line μ w) (g : H))‖^2) := by
    have hz : (line μ w).im ≠ 0 := by simpa only [line_im] using hμ.ne'
    rw [source_read_resolvent F g (firstGeometricAction m ell) (line μ w) hz]
    have h := actual_first_geometric_norm_domination m ell hm0 hell (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (line μ w) hz g))
    have hv : embed (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (line μ w) hz g))=
        finiteResolvent F (line μ w) (g : H) :=
      congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    simpa only [hv] using! h
  have hmA : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖relativeTail (m/2) m (finiteResolvent F (line μ w) (g : H))‖^2)) :=
    ((((relativeTail (m/2) m).continuous.comp
      ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal)
  calc
    _  ≤  ∫⁻ w : ℝ, ENNReal.ofReal 18*(ENNReal.ofReal (‖relativeTail (m/2) m (finiteResolvent F (line μ w) (g : H))‖^2)+
        ENNReal.ofReal (‖relativeTail (ell/2) ell (finiteResolvent F (line μ w) (g : H))‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      exact point_energy_first _ _ _ (sq_nonneg _) (sq_nonneg _) (hb w)
    _ = ENNReal.ofReal 18*((∫⁻ w : ℝ, ENNReal.ofReal (‖relativeTail (m/2) m (finiteResolvent F (line μ w) (g : H))‖^2))+
        ∫⁻ w : ℝ, ENNReal.ofReal (‖relativeTail (ell/2) ell (finiteResolvent F (line μ w) (g : H))‖^2)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_left hmA]
    _  ≤  ENNReal.ofReal 18*(ENNReal.ofReal (ε/36)+ENNReal.ofReal (ε/36)) := mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)]
      congr 1
      ring

private theorem point_second_energy (a b c K : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hK : 0 ≤ K) (h : a ≤ 2*(b+K*c)) :
    ENNReal.ofReal a ≤ ENNReal.ofReal 2*
      (ENNReal.ofReal b+ENNReal.ofReal K*ENNReal.ofReal c) := by
  rw [←ENNReal.ofReal_mul hK,←ENNReal.ofReal_add hb (mul_nonneg hK hc),
    ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]
  exact ENNReal.ofReal_le_ofReal h

private theorem weighted_lintegral (P G : ℝ → ENNReal)
    (hP : Measurable P) (c d : ℝ) :
    (∫⁻ w : ℝ, ENNReal.ofReal c*(P w+ENNReal.ofReal d*G w))=
      ENNReal.ofReal c*((∫⁻ w : ℝ, P w)+
        ENNReal.ofReal d*(∫⁻ w : ℝ, G w)) := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left hP,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem source_read_three_norm (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) (A B C : End) (c K : ℝ)
    (hcore : ∀ f : QuantumTest,
      ‖embed (A f)‖^2 ≤ c*(‖embed (B f)‖^2+K*‖embed (C f)‖^2)) :
    ‖sourceRead F g A (finiteResolvent F z (g : H))‖^2 ≤
      c*(‖sourceRead F g B (finiteResolvent F z (g : H))‖^2+
        K*‖sourceRead F g C (finiteResolvent F z (g : H))‖^2) := by
  let f := coreEquiv.symm (SourceEscapeCurrent.sourceCore F z hz g)
  have hA := source_read_resolvent F g A z hz
  have hB := source_read_resolvent F g B z hz
  have hC := source_read_resolvent F g C z hz
  calc
    _ = ‖embed (A f)‖^2 := congrArg (fun x : H => ‖x‖^2) hA
    _ ≤ c*(‖embed (B f)‖^2+K*‖embed (C f)‖^2) := hcore f
    _ = _ := by rw [hB,hC]

/-- The original twice-differentiated affine cutoff has a common full-frequency tail
on the actual varying finite-resolvent source, without a moment or derivative-tail premise. -/
theorem actual_second_retarded_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceRead F g (secondCutoff m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := 2+3*‖(vacuum : Scalar)‖+‖(vacuum : Scalar)‖^2
  let K := C^2
  have hK : 0 ≤ K := sq_nonneg _
  obtain ⟨N₁,h₁⟩ := actual_second_peak_retarded_tail μ hμ g (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := actual_first_geometric_retarded_tail μ hμ g
    (ε/(4*(K+1))) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell,
    h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell] with F hP hG
  have hb (w : ℝ) :
      ‖sourceRead F g (secondCutoff m ell)
        (finiteResolvent F (line μ w) (g : H))‖^2 ≤
        2*(‖sourceRead F g (secondPeakAction m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2+
          K*‖sourceRead F g (firstGeometricAction m ell)
            (finiteResolvent F (line μ w) (g : H))‖^2) := by
    have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
    exact source_read_three_norm F g (line μ w) hz
      (secondCutoff m ell) (secondPeakAction m ell)
      (firstGeometricAction m ell) 2 K
      (actual_second_norm_domination m ell)
  have hmP : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖sourceRead F g (secondPeakAction m ell)
        (finiteResolvent F (line μ w) (g : H))‖^2)) :=
    ((((sourceRead F g (secondPeakAction m ell)).continuous.comp
      ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply
        continuous_const)).norm.pow 2).measurable.ennreal_ofReal)
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 2*
        (ENNReal.ofReal (‖sourceRead F g (secondPeakAction m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2)+
         ENNReal.ofReal K*ENNReal.ofReal
          (‖sourceRead F g (firstGeometricAction m ell)
            (finiteResolvent F (line μ w) (g : H))‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      exact point_second_energy _ _ _ K (sq_nonneg _) (sq_nonneg _) hK (hb w)
    _ = ENNReal.ofReal 2*((∫⁻ w : ℝ, ENNReal.ofReal
          (‖sourceRead F g (secondPeakAction m ell)
            (finiteResolvent F (line μ w) (g : H))‖^2))+
        ENNReal.ofReal K*(∫⁻ w : ℝ, ENNReal.ofReal
          (‖sourceRead F g (firstGeometricAction m ell)
            (finiteResolvent F (line μ w) (g : H))‖^2))) := by
      exact weighted_lintegral _ _ hmP 2 K
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+
        ENNReal.ofReal K*ENNReal.ofReal (ε/(4*(K+1)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add hP (mul_le_mul_of_nonneg_left hG (by positivity))
    _ = ENNReal.ofReal (2*(ε/4+K*(ε/(4*(K+1))))) := by
      rw [←ENNReal.ofReal_mul hK,
        ←ENNReal.ofReal_add (by positivity) (mul_nonneg hK (by positivity)),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      have hrat : K*(ε/(4*(K+1))) ≤ ε/4 := by
        calc
          _ ≤ (K+1)*(ε/(4*(K+1))) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = ε/4 := by field_simp
      linarith

private theorem delta_phi_product (A B : End) :
    deltaPhi (A*B)=deltaPhi A*B+A*deltaPhi B := by
  change SourceScalarVirialBulk.phiEulerAction*(A*B)-(A*B)*SourceScalarVirialBulk.phiEulerAction=
    (SourceScalarVirialBulk.phiEulerAction*A-A*SourceScalarVirialBulk.phiEulerAction)*B+A*(SourceScalarVirialBulk.phiEulerAction*B-B*SourceScalarVirialBulk.phiEulerAction)
  noncomm_ring

def squareCutoff (m ell : ℕ) : End :=
  SourceNativeCutoffContact.thetaAction m ell*SourceNativeCutoffContact.thetaAction m ell

/-- The actual first phi derivative of the squared source cutoff, with both ordered sides. -/
theorem actual_square_first_return (m ell : ℕ) :
    deltaPhi (squareCutoff m ell)=
      affineCutoff m ell*SourceNativeCutoffContact.thetaAction m ell+
        SourceNativeCutoffContact.thetaAction m ell*affineCutoff m ell := by
  exact delta_phi_product _ _

/-- The actual second phi derivative of the squared cutoff retains both second jets and
both ordered first-jet crosses. -/
theorem actual_square_second_return (m ell : ℕ) :
    deltaPhi (deltaPhi (squareCutoff m ell))=
      secondCutoff m ell*SourceNativeCutoffContact.thetaAction m ell+
        (2 : ℂ) • (affineCutoff m ell*affineCutoff m ell)+
        SourceNativeCutoffContact.thetaAction m ell*secondCutoff m ell := by
  rw [actual_square_first_return,map_add,delta_phi_product,delta_phi_product]
  change (secondCutoff m ell*SourceNativeCutoffContact.thetaAction m ell+affineCutoff m ell*affineCutoff m ell)+
    (affineCutoff m ell*affineCutoff m ell+SourceNativeCutoffContact.thetaAction m ell*secondCutoff m ell)=_
  simp only [two_smul]
  abel

private theorem theta_nonnegative_le_one (m ell : ℕ) (hell : m ≤ ell)
    (z : SourceCoordinateSlice) :
    0 ≤ SourceNativeCutoffContact.theta m ell z ∧
      SourceNativeCutoffContact.theta m ell z ≤ 1 := by
  let q := 1-reciprocal z
  have hs : 0 ≤ reciprocal z := (inv_pos.mpr (radius_pos z)).le
  have hs1 : reciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ q := sub_nonneg.mpr hs1
  have hq1 : q ≤ 1 := by dsimp [q];linarith
  have hpow := pow_le_pow_of_le_one hq hq1 (Nat.add_le_add_right hell 1)
  have hpow1 : q^(m+1) ≤ 1 := pow_le_one₀ hq hq1
  have hn : 0 ≤ q^(ell+1) := pow_nonneg hq _
  dsimp [SourceNativeCutoffContact.theta,q]
  constructor <;> linarith

private theorem first_coefficient_uniform_bound (m ell : ℕ) (hm : 1 ≤ m)
    (hell : m ≤ ell) (z : SourceCoordinateSlice) :
    |firstCoefficient m ell z| ≤
      6*(1+‖(vacuum : Scalar)‖/2) := by
  let K := 1+‖(vacuum : Scalar)‖/2
  let D := firstBinomial m ell z
  let s := reciprocal z
  have hA : |affineQ z| ≤ K*s := affine_q_bound z
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hD : |D*s| ≤ 6 := by
    have h := first_geometric_domination m ell hm hell z
    have hθm := theta_nonnegative_le_one (m/2) m (Nat.div_le_self m 2) z
    have hθe := theta_nonnegative_le_one (ell/2) ell (Nat.div_le_self ell 2) z
    have hθm2 : (theta (m/2) m z)^2 ≤ 1 := by nlinarith [sq_nonneg (theta (m/2) m z)]
    have hθe2 : (theta (ell/2) ell z)^2 ≤ 1 := by nlinarith [sq_nonneg (theta (ell/2) ell z)]
    have hG : firstGeometricCoefficient m ell z=D*s := rfl
    rw [hG] at h
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (D*s-6),sq_nonneg (D*s+6)]
  have h0 : |firstCoefficient m ell z|=|D| * |affineQ z| := by
    change |D*affineQ z|=_
    rw [abs_mul]
  have hG : |D*s|=|D| * s := by
    have hs : 0 ≤ s := (inv_pos.mpr (radius_pos z)).le
    rw [abs_mul,abs_of_nonneg hs]
  rw [h0]
  calc
    _ ≤ |D| * (K*s) := mul_le_mul_of_nonneg_left hA (abs_nonneg _)
    _ = K*(|D| * s) := by ring
    _ ≤ K*6 := mul_le_mul_of_nonneg_left (hG ▸ hD) hK
    _ = _ := by ring

theorem actual_square_first_source_return (m ell : ℕ) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    (deltaPhi (squareCutoff m ell) f) z=
      ((2*theta m ell z*firstCoefficient m ell z : ℝ) : ℂ) • f z := by
  rw [actual_square_first_return,actual_affine_first_multiplier]
  change ((firstCoefficient m ell z : ℂ) •
      ((theta m ell z : ℂ) • f z))+
    ((theta m ell z : ℂ) •
      ((firstCoefficient m ell z : ℂ) • f z))=_
  apply PiLp.ext
  intro word
  simp only [PiLp.add_apply,PiLp.smul_apply]
  push_cast
  ring

theorem actual_square_second_source_return (m ell : ℕ) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    (deltaPhi (deltaPhi (squareCutoff m ell)) f) z=
      ((2*(theta m ell z*
        (secondPeakCoefficient m ell z+firstBinomial m ell z*affineQPrime z)+
        (firstCoefficient m ell z)^2) : ℝ) : ℂ) • f z := by
  rw [actual_square_second_return,actual_affine_first_multiplier]
  have h₁ := actual_second_source_return m ell
    (SourceNativeCutoffContact.thetaAction m ell f) z
  have h₂ := actual_second_source_return m ell f z
  change secondCutoff m ell (SourceNativeCutoffContact.thetaAction m ell f) z+
    (2 : ℂ) • firstAction m ell (firstAction m ell f) z+
      (theta m ell z : ℂ) • secondCutoff m ell f z=_
  rw [h₁,h₂]
  change (((secondPeakCoefficient m ell z+
      firstBinomial m ell z*affineQPrime z : ℝ) : ℂ) •
      ((theta m ell z : ℂ) • f z))+
    (2 : ℂ) • ((firstCoefficient m ell z : ℂ) •
      ((firstCoefficient m ell z : ℂ) • f z))+
    (theta m ell z : ℂ) •
      (((secondPeakCoefficient m ell z+
        firstBinomial m ell z*affineQPrime z : ℝ) : ℂ) • f z)=_
  apply PiLp.ext
  intro word
  simp only [PiLp.add_apply,PiLp.smul_apply]
  push_cast
  ring

private theorem square_first_coefficient_domination (m ell : ℕ) (hell : m ≤ ell)
    (z : SourceCoordinateSlice) :
    (2*theta m ell z*firstCoefficient m ell z)^2 ≤
      4*(firstCoefficient m ell z)^2 := by
  have ht := theta_nonnegative_le_one m ell hell z
  have ht2 : (theta m ell z)^2 ≤ 1 := by nlinarith
  have hs := sq_nonneg (firstCoefficient m ell z)
  nlinarith [mul_le_mul_of_nonneg_right ht2 hs]

private theorem square_first_scalar_density (m ell : ℕ) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    (densityPair (deltaPhi (squareCutoff m ell) f)
      (deltaPhi (squareCutoff m ell) f) z).re=
      (2*theta m ell z*firstCoefficient m ell z)^2*
        (densityPair f f z).re := by
  have h := actual_square_first_source_return m ell f z
  change (inner ℂ (weight (fun N => GaussDensityCore.complexDensity N z)
    ((deltaPhi (squareCutoff m ell) f) z))
    ((deltaPhi (squareCutoff m ell) f) z)).re=_
  rw [h]
  exact real_inner_scaled _ _ _

theorem actual_square_first_norm_domination (m ell : ℕ) (hell : m ≤ ell)
    (f : QuantumTest) :
    ‖embed (deltaPhi (squareCutoff m ell) f)‖^2 ≤
      4*‖embed (affineCutoff m ell f)‖^2 := by
  have ha := (densityPair_integrable (deltaPhi (squareCutoff m ell) f)
    (deltaPhi (squareCutoff m ell) f)).re
  have hb := (densityPair_integrable (affineCutoff m ell f)
    (affineCutoff m ell f)).re
  rw [GaussBoundedMultiplier.norm_square_integral,
    GaussBoundedMultiplier.norm_square_integral,←integral_const_mul]
  apply integral_mono ha (hb.const_mul 4)
  intro z
  have h := mul_le_mul_of_nonneg_right
    (square_first_coefficient_domination m ell hell z) (density_nonnegative f z)
  change (densityPair (deltaPhi (squareCutoff m ell) f)
    (deltaPhi (squareCutoff m ell) f) z).re ≤
      4*(densityPair (affineCutoff m ell f) (affineCutoff m ell f) z).re
  rw [square_first_scalar_density,actual_affine_first_multiplier]
  simp only [firstAction,scalar_density]
  nlinarith

private theorem square_second_coefficient_domination (m ell : ℕ)
    (hm : 1 ≤ m) (hell : m ≤ ell) (z : SourceCoordinateSlice) :
    (2*(theta m ell z*
      (secondPeakCoefficient m ell z+firstBinomial m ell z*affineQPrime z)+
      (firstCoefficient m ell z)^2))^2 ≤
      8*((secondPeakCoefficient m ell z+firstBinomial m ell z*affineQPrime z)^2+
        (6*(1+‖(vacuum : Scalar)‖/2))^2*(firstCoefficient m ell z)^2) := by
  let T := theta m ell z
  let S := secondPeakCoefficient m ell z+firstBinomial m ell z*affineQPrime z
  let P := firstCoefficient m ell z
  let M := 6*(1+‖(vacuum : Scalar)‖/2)
  have ht := theta_nonnegative_le_one m ell hell z
  have ht2 : T^2 ≤ 1 := by dsimp [T];nlinarith
  have hp := first_coefficient_uniform_bound m ell hm hell z
  have hp2 : P^2 ≤ M^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hp 2
    simpa only [sq_abs] using h
  have hTS : (T*S)^2 ≤ S^2 := by nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg S)]
  have hP4 : (P^2)^2 ≤ M^2*P^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hp2 (sq_nonneg P)]
  change (2*(T*S+P^2))^2 ≤ 8*(S^2+M^2*P^2)
  have hsum : (T*S+P^2)^2 ≤ 2*((T*S)^2+(P^2)^2) := by
    nlinarith [sq_nonneg (T*S-P^2)]
  have hright : (T*S)^2+(P^2)^2 ≤ S^2+M^2*P^2 := by linarith
  nlinarith

private theorem square_second_scalar_density (m ell : ℕ) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    (densityPair (deltaPhi (deltaPhi (squareCutoff m ell)) f)
      (deltaPhi (deltaPhi (squareCutoff m ell)) f) z).re=
      (2*(theta m ell z*
        (secondPeakCoefficient m ell z+firstBinomial m ell z*affineQPrime z)+
        (firstCoefficient m ell z)^2))^2*(densityPair f f z).re := by
  have h := actual_square_second_source_return m ell f z
  change (inner ℂ (weight (fun N => GaussDensityCore.complexDensity N z)
    ((deltaPhi (deltaPhi (squareCutoff m ell)) f) z))
    ((deltaPhi (deltaPhi (squareCutoff m ell)) f) z)).re=_
  rw [h]
  exact real_inner_scaled _ _ _

theorem actual_square_second_norm_domination (m ell : ℕ) (hm : 1 ≤ m)
    (hell : m ≤ ell) (f : QuantumTest) :
    ‖embed (deltaPhi (deltaPhi (squareCutoff m ell)) f)‖^2 ≤
      8*(‖embed (secondCutoff m ell f)‖^2+
        (6*(1+‖(vacuum : Scalar)‖/2))^2*
          ‖embed (affineCutoff m ell f)‖^2) := by
  have ha := (densityPair_integrable (deltaPhi (deltaPhi (squareCutoff m ell)) f)
    (deltaPhi (deltaPhi (squareCutoff m ell)) f)).re
  have hb := (densityPair_integrable (secondCutoff m ell f)
    (secondCutoff m ell f)).re
  have hc := (densityPair_integrable (affineCutoff m ell f)
    (affineCutoff m ell f)).re
  rw [GaussBoundedMultiplier.norm_square_integral,
    GaussBoundedMultiplier.norm_square_integral,
    GaussBoundedMultiplier.norm_square_integral,
    ←integral_const_mul,←integral_add hb (hc.const_mul _),←integral_const_mul]
  apply integral_mono ha ((hb.add (hc.const_mul _)).const_mul 8)
  intro z
  have h := mul_le_mul_of_nonneg_right
    (square_second_coefficient_domination m ell hm hell z)
    (density_nonnegative f z)
  change (densityPair (deltaPhi (deltaPhi (squareCutoff m ell)) f)
    (deltaPhi (deltaPhi (squareCutoff m ell)) f) z).re ≤
    8*((densityPair (secondCutoff m ell f) (secondCutoff m ell f) z).re+
      (6*(1+‖(vacuum : Scalar)‖/2))^2*
        (densityPair (affineCutoff m ell f) (affineCutoff m ell f) z).re)
  rw [square_second_scalar_density,second_scalar_density,
    actual_affine_first_multiplier]
  simp only [firstAction,scalar_density]
  nlinarith

/-- The original first phi jet of theta squared has a common full-frequency tail
for the same varying finite-resolvent source. -/
theorem actual_square_first_retarded_tail (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceRead F g
          (deltaPhi (squareCutoff m ell))
          (finiteResolvent F (line μ w) (g : H))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_affine_retarded_tail μ hμ g (ε/4) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have hb (w : ℝ) :
      ‖sourceRead F g (deltaPhi (squareCutoff m ell))
        (finiteResolvent F (line μ w) (g : H))‖^2 ≤
      4*‖sourceRead F g (affineCutoff m ell)
        (finiteResolvent F (line μ w) (g : H))‖^2 := by
    have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
    have h := source_read_three_norm F g (line μ w) hz
      (deltaPhi (squareCutoff m ell)) (affineCutoff m ell)
      (affineCutoff m ell) 4 0 (fun f => by
        simpa only [zero_mul,add_zero] using
          actual_square_first_norm_domination m ell hell f)
    simpa only [zero_mul,add_zero] using h
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 4*ENNReal.ofReal
      (‖sourceRead F g (affineCutoff m ell)
        (finiteResolvent F (line μ w) (g : H))‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      exact (ENNReal.ofReal_le_ofReal (hb w)).trans_eq
        (ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤4))
    _ = ENNReal.ofReal 4*(∫⁻ w : ℝ, ENNReal.ofReal
      (‖sourceRead F g (affineCutoff m ell)
        (finiteResolvent F (line μ w) (g : H))‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal 4*ENNReal.ofReal (ε/4) :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤4)]
      congr 1
      ring

private theorem point_square_energy (a b c K : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hK : 0 ≤ K) (h : a ≤ 8*(b+K*c)) :
    ENNReal.ofReal a ≤ ENNReal.ofReal 8*
      (ENNReal.ofReal b+ENNReal.ofReal K*ENNReal.ofReal c) := by
  rw [←ENNReal.ofReal_mul hK,←ENNReal.ofReal_add hb (mul_nonneg hK hc),
    ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤8)]
  exact ENNReal.ofReal_le_ofReal h

/-- Both literal phi jets of theta squared have source-generated full-frequency
budgets. This second mouth retains theta times the actual second cutoff and the
actual first-cutoff square, with no target-tail premise. -/
theorem actual_square_second_retarded_tail (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceRead F g
          (deltaPhi (deltaPhi (squareCutoff m ell)))
          (finiteResolvent F (line μ w) (g : H))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let K := (6*(1+‖(vacuum : Scalar)‖/2))^2
  have hK : 0 ≤ K := sq_nonneg _
  obtain ⟨N₁,h₁⟩ := actual_second_retarded_tail μ hμ g (ε/16) (by positivity)
  obtain ⟨N₂,h₂⟩ := actual_affine_retarded_tail μ hμ g
    (ε/(16*(K+1))) (by positivity)
  refine ⟨max 1 (max N₁ N₂),fun m hm ell hell => ?_⟩
  have hm0 : 1 ≤ m := by omega
  have hm1 : N₁ ≤ m := by omega
  have hm2 : N₂ ≤ m := by omega
  filter_upwards [h₁ m hm1 ell hell,h₂ m hm2 ell hell] with F hS hA
  have hb (w : ℝ) :
      ‖sourceRead F g (deltaPhi (deltaPhi (squareCutoff m ell)))
        (finiteResolvent F (line μ w) (g : H))‖^2 ≤
        8*(‖sourceRead F g (secondCutoff m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2+
          K*‖sourceRead F g (affineCutoff m ell)
            (finiteResolvent F (line μ w) (g : H))‖^2) := by
    have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
    exact source_read_three_norm F g (line μ w) hz
      (deltaPhi (deltaPhi (squareCutoff m ell)))
      (secondCutoff m ell) (affineCutoff m ell) 8 K
      (actual_square_second_norm_domination m ell hm0 hell)
  have hmS : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖sourceRead F g (secondCutoff m ell)
        (finiteResolvent F (line μ w) (g : H))‖^2)) :=
    ((((sourceRead F g (secondCutoff m ell)).continuous.comp
      ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply
        continuous_const)).norm.pow 2).measurable.ennreal_ofReal)
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 8*
        (ENNReal.ofReal (‖sourceRead F g (secondCutoff m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2)+
         ENNReal.ofReal K*ENNReal.ofReal
          (‖sourceRead F g (affineCutoff m ell)
            (finiteResolvent F (line μ w) (g : H))‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      exact point_square_energy _ _ _ K (sq_nonneg _) (sq_nonneg _) hK (hb w)
    _ = ENNReal.ofReal 8*((∫⁻ w : ℝ, ENNReal.ofReal
          (‖sourceRead F g (secondCutoff m ell)
            (finiteResolvent F (line μ w) (g : H))‖^2))+
        ENNReal.ofReal K*(∫⁻ w : ℝ, ENNReal.ofReal
          (‖sourceRead F g (affineCutoff m ell)
            (finiteResolvent F (line μ w) (g : H))‖^2))) := by
      exact weighted_lintegral _ _ hmS 8 K
    _ ≤ ENNReal.ofReal 8*(ENNReal.ofReal (ε/16)+
        ENNReal.ofReal K*ENNReal.ofReal (ε/(16*(K+1)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add hS (mul_le_mul_of_nonneg_left hA (by positivity))
    _ = ENNReal.ofReal (8*(ε/16+K*(ε/(16*(K+1))))) := by
      rw [←ENNReal.ofReal_mul hK,
        ←ENNReal.ofReal_add (by positivity) (mul_nonneg hK (by positivity)),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤8)]
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      have hrat : K*(ε/(16*(K+1))) ≤ ε/16 := by
        calc
          _ ≤ (K+1)*(ε/(16*(K+1))) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = ε/16 := by field_simp
      linarith

end LowEnergy.SourceScalarAffineSecondCutoffTail
