import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.FixedEndpoints
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RefinedRate
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter Metric Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open scoped Topology InnerProductSpace

open private power_analytic power_jet from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.CoefficientJet
open private moment from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel

local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "phase" => fun c (N : Nat) => ((N+1 : Nat) : ℂ)^(-s₀ c)
local notation "clock" => fun (N : Nat) => Real.log ((N+1 : Nat) : ℝ)
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection
local notation "R₀" => fun c => burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)
local notation "m" => fun c => moment c
  (burnolQuarterZeroExtension (burnolMeanZeroTruncatedFourier (nativeSmooth c) : BurnolQuarterIntervalL2))

private def jetRadius (c : BurnolCompletedMellinCoordinate) : ℝ := (1-(s₀ c).re)/2
private def circleBudget (c : BurnolCompletedMellinCoordinate) : ℝ := 4*(‖s₀ c‖+1)*(‖s₀ c‖+2)

def cutoffJetBudget (c : BurnolCompletedMellinCoordinate) (j : Nat) : ℝ :=
  (j.factorial : ℝ)*circleBudget c/(jetRadius c)^j

private theorem strip (c : BurnolCompletedMellinCoordinate) : 1/2 < (s₀ c).re ∧ (s₀ c).re < 1 := by
  simpa only [star_def, conj_re] using And.intro c.rightHalf c.belowOne

private theorem radius_positive (c : BurnolCompletedMellinCoordinate) : 0 < jetRadius c := by
  unfold jetRadius
  linarith [(strip c).2]

private theorem disc_bounds (c : BurnolCompletedMellinCoordinate) (z : ℂ)
    (inside : z ∈ closedBall (s₀ c) (jetRadius c)) :
    0 < z.re ∧ z ≠ 1 ∧ (s₀ c).re-1/4 ≤ z.re ∧ ‖z‖ ≤ ‖s₀ c‖+1 := by
  have close : ‖z-s₀ c‖ ≤ jetRadius c := by simpa only [mem_closedBall, dist_eq_norm] using inside
  have realClose := abs_le.mp ((Complex.abs_re_le_norm (z-s₀ c)).trans close)
  simp only [Complex.sub_re, jetRadius] at realClose
  have right : 0 < z.re := by linarith [(strip c).1, realClose.1]
  have below : z.re < 1 := by linarith [(strip c).2, realClose.2]
  refine ⟨right, fun gone => ?_, by linarith [(strip c).1, realClose.1], ?_⟩
  · rw [gone, Complex.one_re] at below
    exact lt_irrefl _ below
  · calc
      ‖z‖ = ‖(z-s₀ c)+s₀ c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z-s₀ c‖+‖s₀ c‖ := norm_add_le _ _
      _ ≤ ‖s₀ c‖+1 := by unfold jetRadius at close; linarith [(strip c).1]

private def boundaryError (N : Nat) (z : ℂ) : ℂ :=
  CoefficientJet.finite N z-riemannZeta z+(1/2 : ℂ)*((N+1 : Nat) : ℂ)^(-z)

private theorem boundary_analytic (c : BurnolCompletedMellinCoordinate) (N : Nat) :
    AnalyticOnNhd ℂ (boundaryError N) (closedBall (s₀ c) (jetRadius c)) := by
  intro z inside
  have bounds := disc_bounds c z inside
  have finite := CoefficientJet.finite_analytic N z ⟨bounds.1,bounds.2.1⟩
  have infinite := analyticOn_riemannZeta z (by simpa using bounds.2.1)
  have live : ((N+1 : Nat) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  exact (finite.sub infinite).add (analyticAt_const.mul (power_analytic _ live z))

private theorem boundary_on_circle (c : BurnolCompletedMellinCoordinate) (N : Nat)
    (z : ℂ) (inside : z ∈ sphere (s₀ c) (jetRadius c)) :
    ‖boundaryError N z‖ ≤ circleBudget c * ((N+1 : Nat) : ℝ)^(-(s₀ c).re-3/4) := by
  obtain ⟨right, notOne, realBound, size⟩ := disc_bounds c z (sphere_subset_closedBall inside)
  have bound := RefinedRate.coefficient_error_bound z right notOne (N+1) (Nat.succ_pos N)
  have factor : ‖z*(z+1)‖ ≤ (‖s₀ c‖+1)*(‖s₀ c‖+2) := by
    rw [norm_mul]
    apply mul_le_mul size _ (norm_nonneg _) (by positivity)
    exact (norm_add_le z 1).trans (by rw [norm_one]; linarith)
  have inverse : 1/(z.re+1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have cost : RefinedRate.constant z ≤ circleBudget c := by
    unfold RefinedRate.constant circleBudget
    nlinarith [mul_le_mul_of_nonneg_left (show 1+1/(z.re+1) ≤ 2 by linarith) (norm_nonneg (z*(z+1)))]
  have power : ((N+1 : Nat) : ℝ)^(-z.re-1) ≤ ((N+1 : Nat) : ℝ)^(-(s₀ c).re-3/4) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos N) (by linarith)
  exact bound.trans (mul_le_mul cost power (Real.rpow_nonneg (by positivity) _) (by unfold circleBudget; positivity))

/-- The actual count retains the trapezoid boundary at every fixed derivative order. -/
theorem actual_cutoff_jet_error (c : BurnolCompletedMellinCoordinate) (j N : Nat) :
    ‖CoefficientJet.jet j N (s₀ c) - CoefficientJet.zetaJet j (s₀ c) +
      (1/2 : ℂ)*(-(clock N : ℂ))^j*phase c N‖ ≤
      cutoffJetBudget c j * ((N+1 : Nat) : ℝ)^(-(s₀ c).re-3/4) := by
  let z := s₀ c
  let r := jetRadius c
  have analytic := boundary_analytic c N
  have regular : DiffContOnCl ℂ (boundaryError N) (ball z r) :=
    (analytic.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  have estimate := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j (radius_positive c) regular (boundary_on_circle c N)
  have zInside : z ∈ closedBall z r := mem_closedBall_self (radius_positive c).le
  have bounds := disc_bounds c z zInside
  have finite := CoefficientJet.finite_analytic N z ⟨bounds.1,bounds.2.1⟩
  have infinite := analyticOn_riemannZeta z (by simpa using bounds.2.1)
  have live : ((N+1 : Nat) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  let wave := fun t : ℂ => ((N+1 : Nat) : ℂ)^(-t)
  have power : AnalyticAt ℂ wave z := power_analytic _ live z
  have logRead : Complex.log ((N+1 : Nat) : ℂ) = (clock N : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_log (by positivity)).symm
  have derived : iteratedDeriv j (boundaryError N) z =
      CoefficientJet.jet j N z-CoefficientJet.zetaJet j z+
        (1/2 : ℂ)*(-(clock N : ℂ))^j*phase c N := by
    have correction : AnalyticAt ℂ ((1/2 : ℂ) • wave) z := analyticAt_const.mul power
    change iteratedDeriv j ((CoefficientJet.finite N-riemannZeta)+((1/2 : ℂ) • wave)) z = _
    rw [iteratedDeriv_add (finite.sub infinite).contDiffAt correction.contDiffAt,
      iteratedDeriv_sub finite.contDiffAt infinite.contDiffAt, iteratedDeriv_const_smul_field]
    have jetRead : iteratedDeriv j wave z = (-Complex.log ((N+1 : Nat) : ℂ))^j*phase c N :=
      power_jet _ live z j
    rw [jetRead, logRead, smul_eq_mul, ← mul_assoc]
    rfl
  rw [derived] at estimate
  unfold cutoffJetBudget
  convert estimate using 1
  ring

local notation "A" => fun c (n : Nat) => Prod.fst (clockCoefficients c (actualClockPair c n))
local notation "expected" => fun c (n : Nat) =>
  (1/2 : ℂ)*(m c-(clock (n+1) : ℂ))*phase c (n+1)
local notation "errorBudget" => fun c => ‖m c‖*cutoffJetBudget c 0 + cutoffJetBudget c 1

theorem actual_clock_outer_price_error (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ‖A c n-expected c n‖ ≤ errorBudget c * ((n+2 : Nat) : ℝ)^(-(s₀ c).re-3/4) := by
  let z := s₀ c
  let w := phase c (n+1)
  let l := (clock (n+1) : ℂ)
  let e₀ := FiniteForcing.coefficient z (n+2)-riemannZeta z+(1/2 : ℂ)*w
  let e₁ := CoefficientJet.jet 1 (n+1) z-CoefficientJet.zetaJet 1 z+(1/2 : ℂ)*(-l)*w
  have zero := actual_cutoff_jet_error c 0 (n+1)
  have one := actual_cutoff_jet_error c 1 (n+1)
  simp only [CoefficientJet.jet, CoefficientJet.zetaJet, iteratedDeriv_zero, CoefficientJet.finite,
    pow_zero, mul_one] at zero
  simp only [pow_one] at one
  have algebra : A c n-expected c n = -(m c*e₀+e₁) := by
    change (clockCoefficients c (actualClockPair c n)).1-expected c n = _
    rw [actual_clock_coefficients]
    change m c*riemannZeta z+CoefficientJet.zetaJet 1 z-countedJetPrice c (n+1)-expected c n = _
    unfold countedJetPrice
    dsimp only [e₀, e₁, w, l, z, CoefficientJet.jet, CoefficientJet.finite, iteratedDeriv_zero]
    ring
  rw [algebra, norm_neg]
  calc
    _ ≤ ‖m c*e₀‖+‖e₁‖ := norm_add_le _ _
    _ ≤ ‖m c‖*(cutoffJetBudget c 0 * ((n+2 : Nat) : ℝ)^(-(s₀ c).re-3/4)) +
        cutoffJetBudget c 1 * ((n+2 : Nat) : ℝ)^(-(s₀ c).re-3/4) := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left zero (norm_nonneg _)) one
    _ = _ := by ring

private theorem phase_scaled_error_zero (c : BurnolCompletedMellinCoordinate)
    (error : Nat → ℂ) (budget : ℝ)
    (estimate : ∀ n : Nat, ‖error n‖ ≤ budget * ((n+2 : Nat) : ℝ)^(-(s₀ c).re-3/4)) :
    Tendsto (fun n : Nat => error n/phase c (n+1)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have indices : Tendsto (fun n : Nat => ((n+2 : Nat) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  have upper := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/4)).comp indices).const_mul budget
  simp only [mul_zero, Function.comp_def] at upper
  apply squeeze_zero (fun _ => norm_nonneg _) _ upper
  intro n
  rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega), neg_re]
  have scale : ((n+2 : Nat) : ℝ)^(-(s₀ c).re-3/4)/((n+2 : Nat) : ℝ)^(-(s₀ c).re) =
      ((n+2 : Nat) : ℝ)^(-(3/4 : ℝ)) := by
    rw [← Real.rpow_sub (by positivity)]
    congr 1
    ring
  exact (div_le_div_of_nonneg_right (estimate n)
    (Real.rpow_nonneg (by positivity) _)).trans_eq (by rw [mul_div_assoc, scale])

local notation "delta" => fun c (n : Nat) =>
  floorFromResponses c+riemannZeta (s₀ c) • elementarySource c-compensated c (n+2)
local notation "scale" => fun c (n : Nat) => (clock (n+1) : ℂ)*phase c (n+1)

private theorem phase_ne (c : BurnolCompletedMellinCoordinate) (N : Nat) :
    phase c N ≠ 0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  exact Or.inl (by exact_mod_cast Nat.succ_ne_zero N)

/-- The original fixed B count coefficient has its own phase scale. -/
theorem actual_phase_count_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => (phase c (n+1))⁻¹*(clockCoefficients c (actualClockPair c n)).2)
      atTop (𝓝 (-(1/2 : ℂ))) := by
  let error := fun n : Nat => (clockCoefficients c (actualClockPair c n)).2+(1/2 : ℂ)*phase c (n+1)
  have estimate (n : Nat) : ‖error n‖ ≤ cutoffJetBudget c 0 * ((n+2 : Nat) : ℝ)^(-(s₀ c).re-3/4) := by
    dsimp only [error]
    rw [actual_clock_coefficients]
    simpa only [CoefficientJet.jet, CoefficientJet.zetaJet, iteratedDeriv_zero, CoefficientJet.finite,
      pow_zero, mul_one] using actual_cutoff_jet_error c 0 (n+1)
  have bounded := phase_scaled_error_zero c error (cutoffJetBudget c 0) estimate
  have actual := bounded.sub (tendsto_const_nhds (x := (1/2 : ℂ)))
  simp only [zero_sub] at actual
  apply actual.congr'
  filter_upwards with n
  let w := phase c (n+1)
  let b := (clockCoefficients c (actualClockPair c n)).2
  change (b+(1/2 : ℂ)*w)/w-1/2 = w⁻¹*b
  rw [add_div, mul_div_assoc, div_self (phase_ne c (n+1)), mul_one, add_sub_cancel_right, div_eq_mul_inv]
  exact mul_comm _ _

theorem actual_scaled_outer_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => (scale c n)⁻¹*(-(2*A c n))) atTop (𝓝 (1 : ℂ)) := by
  let inverse := fun n : Nat => ((clock (n+1) : ℂ))⁻¹
  have indices : Tendsto (fun n : Nat => ((n+2 : Nat) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  have inverseLimit : Tendsto inverse atTop (𝓝 0) := by
    simpa only [inverse, Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
        (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp indices))
  have error := phase_scaled_error_zero c _ (errorBudget c) (actual_clock_outer_price_error c)
  have sum := (tendsto_const_nhds (x := m c)).add (error.const_mul (2 : ℂ))
  have limit := (tendsto_const_nhds (x := (1 : ℂ))).sub (sum.mul inverseLimit)
  simp only [mul_zero, add_zero, sub_zero] at limit
  apply limit.congr'
  filter_upwards with n
  let l := (clock (n+1) : ℂ)
  let w := phase c (n+1)
  have nonzero : w ≠ 0 := phase_ne c (n+1)
  have logLive : l ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast (by omega : 1 < n+2))).ne'
  change 1-(m c+2*((A c n-(1/2 : ℂ)*(m c-l)*w)/w))*l⁻¹ = (l*w)⁻¹ * (-(2*A c n))
  field_simp [nonzero, logLive]
  ring

/-- The phase- and log-normalized original physical return converges to the original Riesz vector. -/
theorem actual_scaled_counted_physical_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => (scale c n)⁻¹ • P (R₀ c (delta c n))) atTop (𝓝 (K c)) := by
  have field := (actual_scaled_outer_limit c).smul_const (K c)
  simp only [one_smul] at field
  apply field.congr'
  filter_upwards with n
  rw [actual_clock_physical, smul_smul]

theorem actual_scaled_counted_K_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => inner ℂ (K c) ((scale c n)⁻¹ • P (R₀ c (delta c n))))
      atTop (𝓝 (inner ℂ (K c) (K c))) :=
  ((innerSL ℂ (K c)).continuous.tendsto _).comp (actual_scaled_counted_physical_limit c)

theorem actual_late_counted_physical_ne_zero (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    ∀ᶠ n : Nat in atTop, P (R₀ c (delta c n)) ≠ 0 := by
  have live : K c ≠ 0 := by
    intro gone
    apply burnolCompletedMellinEvaluator_nonzero_at_zero c zero
    ext value
    rw [← burnolCompletedMellinRieszVector_readback c value, gone, inner_zero_left]
    rfl
  have near := (actual_scaled_counted_physical_limit c).eventually
    (compl_singleton_mem_nhds_iff.mpr live)
  filter_upwards [near] with n different gone
  exact different (by simp only [gone, smul_zero, mem_singleton_iff])

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
