import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.JointLogConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KLogVectorSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Abel.Gaussian.ClozelBurnolBoundaryGaussianHeatTest
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.Isometry
import H0mework.Arithmetic.BurnolMellin.GaussianFourierKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCounting
import H0mework.Arithmetic.MellinProjection.TailKernel

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.KappaConductor
open Complex Filter FourierTransform MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalGamma.Source.JointLogConductor
noncomputable section
local notation "q" => (1 / 4 : ℝ)

def originalFirstField (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) : BurnolL2 :=
  -PositionCounting.value c zero - burnolTateReciprocalL2 (CountingDual.value c)

def originalDualField (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) : BurnolL2 :=
  burnolTateReciprocalL2 (originalFirstField c zero)

def originalDualLogValue (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (OriginalGamma.Source.KLogVector.originalLogAValue c) +
    burnolTateReciprocalL2 (OriginalGamma.Source.KLogVector.originalLogDValue c)

private def offDiagonalHeat (time distance : ℝ) : ℂ :=
  (Real.sqrt (Real.pi / time) * Real.exp (-(Real.pi ^ 2 * distance ^ 2 / time)) : ℝ)

private def offDiagonalLog (distance : ℝ) : ℂ :=
  -(1 / 2 : ℂ) * ∫ time : ℝ in Ioi 0, (time : ℂ)⁻¹ * offDiagonalHeat time distance

private theorem off_diagonal_gaussian_payment (distance : ℝ) (nonzero : distance ≠ 0) :
    offDiagonalLog distance = -(1 / (2 * |distance|) : ℝ) := by
  let rate : ℝ := Real.pi ^ 2 * distance ^ 2
  let g : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ)) * Real.exp (-(rate * u))
  have ratePos : 0 < rate := mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_ne_zero nonzero)
  have inverse := integral_comp_rpow_Ioi g (p := (-1 : ℝ)) (by norm_num)
  have changeKernel : (fun t : ℝ => t⁻¹ * (Real.sqrt (Real.pi / t) * Real.exp (-(rate / t)))) =ᵐ[volume.restrict (Ioi 0)]
      fun t => Real.sqrt Real.pi * ((|-1| * t ^ ((-1 : ℝ) - 1)) * g (t ^ (-1 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
    have tpos : 0 < t := positive
    have sqrtNe : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr positive).ne'
    have inversePower : (t⁻¹) ^ (-(1 / 2 : ℝ)) = Real.sqrt t := by
      rw [Real.inv_rpow positive.le, Real.rpow_neg positive.le, inv_inv, ← Real.sqrt_eq_rpow]
    have doublePower : t ^ ((-1 : ℝ) - 1) = (t ^ 2)⁻¹ := by
      rw [show (-1 : ℝ) - 1 = -(2 : ℝ) by ring, Real.rpow_neg positive.le, Real.rpow_two]
    dsimp only [g]
    rw [Real.rpow_neg_one, inversePower, doublePower, Real.sqrt_div Real.pi_pos.le]
    norm_num only [abs_neg, abs_one, one_mul]
    rw [show rate / t = rate * t⁻¹ by ring]
    have shape : t⁻¹ / Real.sqrt t = (t ^ 2)⁻¹ * Real.sqrt t := by
      field_simp [tpos.ne', sqrtNe]
      nlinarith [Real.sq_sqrt positive.le]
    rw [← mul_assoc, show t⁻¹ * (Real.sqrt Real.pi / Real.sqrt t) = Real.sqrt Real.pi * (t⁻¹ / Real.sqrt t) by ring, shape]
    ring
  have kernelIntegral : (∫ t : ℝ in Ioi 0, t⁻¹ * (Real.sqrt (Real.pi / t) * Real.exp (-(rate / t)))) =
      Real.sqrt Real.pi * ((1 / rate) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2)) := by
    rw [integral_congr_ae changeKernel, integral_const_mul]
    change Real.sqrt Real.pi * (∫ t : ℝ in Ioi 0, (|-1| * t ^ ((-1 : ℝ) - 1)) • g (t ^ (-1 : ℝ))) = _
    rw [inverse]
    have read := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 / 2 : ℝ)) (by norm_num) ratePos
    simpa only [g, show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by ring] using congrArg (Real.sqrt Real.pi * ·) read
  have rootRate : Real.sqrt rate = Real.pi * |distance| := by
    rw [show rate = (Real.pi * |distance|) ^ 2 by dsimp only [rate]; rw [mul_pow, sq_abs], Real.sqrt_sq_eq_abs,
      abs_of_pos (mul_pos Real.pi_pos (abs_pos.mpr nonzero))]
  have scalar : (∫ t : ℝ in Ioi 0, t⁻¹ * (Real.sqrt (Real.pi / t) * Real.exp (-(rate / t)))) = |distance|⁻¹ := by
    rw [kernelIntegral, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
      Real.sqrt_one, rootRate]
    have sqrtPi := Real.sq_sqrt Real.pi_pos.le
    field_simp [Real.pi_ne_zero, abs_ne_zero.mpr nonzero]
    nlinarith
  unfold offDiagonalLog offDiagonalHeat
  have actual : (∫ t : ℝ in Ioi 0, (t : ℂ)⁻¹ * (Real.sqrt (Real.pi / t) * Real.exp (-(Real.pi ^ 2 * distance ^ 2 / t)) : ℝ)) =
      ((∫ t : ℝ in Ioi 0, t⁻¹ * (Real.sqrt (Real.pi / t) * Real.exp (-(rate / t)))) : ℝ) := by
    simp only [rate, ← Complex.ofReal_inv, ← Complex.ofReal_mul, integral_complex_ofReal]
  rw [actual, scalar]
  push_cast
  ring

private def heatLogCut (N : ℕ) (frequency : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t : ℝ in (1 / ((N : ℝ) + 1))..((N : ℝ) + 1),
    t⁻¹ * (Real.exp (-t) - Real.exp (-(frequency ^ 2 * t)))

private theorem heat_log_cut_limit (frequency : ℝ) (nonzero : frequency ≠ 0) :
    Tendsto (fun N : ℕ => heatLogCut N frequency) atTop (𝓝 (Real.log |frequency|)) := by
  let source : ℝ → ℝ := fun t => Real.exp (-t)
  have native : LocallyIntegrableOn source (Ioi 0) :=
    (Real.continuous_exp.comp continuous_neg).locallyIntegrable.locallyIntegrableOn (Ioi 0)
  have bottom : Tendsto source (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    simpa only [source, Function.comp_def, neg_zero, Real.exp_zero] using
      (Real.continuous_exp.comp continuous_neg).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have top : Tendsto source atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have whole := Frullani.tendsto_intervalIntegral native (a := 1) (by norm_num)
    (b := frequency ^ 2) (sq_pos_of_ne_zero nonzero) bottom top
  have lower : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall (fun N => by simp; positivity)⟩
  have upper : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have sampled := (whole.comp (lower.prodMk upper)).const_mul (1 / 2 : ℝ)
  simp only [smul_eq_mul] at sampled
  have target : (1 / 2 : ℝ) * (Real.log (frequency ^ 2 / 1) * (1 - 0)) = Real.log |frequency| := by
    rw [div_one, sub_zero, mul_one, Real.log_pow, Real.log_abs]
    ring
  rw [target] at sampled
  simpa only [heatLogCut, source, Function.comp_def, one_mul, smul_eq_mul] using sampled

private theorem exponential_log_interval_bound (a b : ℝ) (aPositive : 0 < a) (bPositive : 0 < b) :
    |∫ t : ℝ in a..b, t⁻¹ * Real.exp (-t)| ≤ |Real.log (b / a)| := by
  have native : LocallyIntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    (Real.continuous_exp.comp continuous_neg).locallyIntegrable.locallyIntegrableOn (Ioi 0)
  have bound := Frullani.norm_integral_inv_smul_sub_le native aPositive bPositive
    (V := (0 : ℝ)) (δ := 1) (by norm_num) (fun t inside => by
      have positive : 0 < t := (lt_min aPositive bPositive).trans_le (uIoc_subset_uIcc inside).1
      simp only [sub_zero, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr positive.le))
  simpa only [smul_eq_mul, sub_zero, smul_zero, mul_zero, one_mul, Real.norm_eq_abs] using bound

private theorem heat_log_cut_bound (N : ℕ) (frequency : ℝ) (nonzero : frequency ≠ 0) :
    |heatLogCut N frequency| ≤ 2 * |Real.log (|frequency|)| := by
  let epsilon := 1 / ((N : ℝ) + 1)
  let upper := (N : ℝ) + 1
  let b := frequency ^ 2
  let source : ℝ → ℝ := fun t => Real.exp (-t)
  let u : ℝ → ℝ := fun t => t⁻¹ * source t
  have ePos : 0 < epsilon := by dsimp [epsilon]; positivity
  have uPos : 0 < upper := by dsimp [upper]; positivity
  have bPos : 0 < b := sq_pos_of_ne_zero nonzero
  have native : LocallyIntegrableOn source (Ioi 0) :=
    (Real.continuous_exp.comp continuous_neg).locallyIntegrable.locallyIntegrableOn (Ioi 0)
  have interval {a z : ℝ} (aPos : 0 < a) (zPos : 0 < z) : IntervalIntegrable u volume a z :=
    Frullani.intervalIntegrable_inv_smul native aPos zPos
  have split : (∫ t : ℝ in epsilon..upper, t⁻¹ * (source t - source (b * t))) =
      (∫ t : ℝ in epsilon..(b * epsilon), u t) - ∫ t : ℝ in upper..(b * upper), u t := by
    calc
      _ = (∫ t : ℝ in epsilon..upper, t⁻¹ • source (1 * t)) -
          ∫ t : ℝ in epsilon..upper, t⁻¹ • source (b * t) := by
        simp_rw [one_mul, smul_eq_mul, mul_sub]
        exact intervalIntegral.integral_sub
          (by simpa only [smul_eq_mul, one_mul] using Frullani.intervalIntegrable_inv_smul_comp_mul native ePos uPos (by norm_num : (0 : ℝ) < 1))
          (by simpa only [smul_eq_mul] using Frullani.intervalIntegrable_inv_smul_comp_mul native ePos uPos bPos)
      _ = (∫ t : ℝ in epsilon..upper, u t) - ∫ t : ℝ in (b * epsilon)..(b * upper), u t := by
        rw [Frullani.integral_comp_mul_inv_smul (f := source) (c := 1) (by norm_num),
          Frullani.integral_comp_mul_inv_smul (f := source) (c := b) bPos.ne']
        simp only [one_mul, u, smul_eq_mul]
      _ = _ := intervalIntegral.integral_interval_sub_interval_comm
        (interval ePos uPos) (interval (mul_pos bPos ePos) (mul_pos bPos uPos))
        (interval ePos (mul_pos bPos ePos))
  have lowerBound := exponential_log_interval_bound epsilon (b * epsilon) ePos (mul_pos bPos ePos)
  have upperBound := exponential_log_interval_bound upper (b * upper) uPos (mul_pos bPos uPos)
  rw [mul_div_cancel_right₀ b ePos.ne'] at lowerBound
  rw [mul_div_cancel_right₀ b uPos.ne'] at upperBound
  have combined : |(∫ t : ℝ in epsilon..(b * epsilon), u t) - ∫ t : ℝ in upper..(b * upper), u t| ≤
      2 * |Real.log b| := (abs_sub _ _).trans (by dsimp only [u, source]; linarith)
  change |(1 / 2 : ℝ) * (∫ t : ℝ in epsilon..upper, t⁻¹ * (source t - source (b * t)))| ≤ _
  rw [split, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have reduced := mul_le_mul_of_nonneg_left combined (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have normalization : (1 / 2 : ℝ) * (2 * |Real.log b|) = 2 * |Real.log (|frequency|)| := by
    dsimp only [b]
    rw [Real.log_pow, Real.log_abs, abs_mul]
    norm_num
    ring
  exact reduced.trans_eq normalization

private theorem heat_log_cut_measurable (N : ℕ) : Measurable (heatLogCut N) := by
  have joint : StronglyMeasurable (fun p : ℝ × ℝ =>
      p.2⁻¹ * (Real.exp (-p.2) - Real.exp (-(p.1 ^ 2 * p.2)))) :=
    (by fun_prop : Measurable (fun p : ℝ × ℝ =>
      p.2⁻¹ * (Real.exp (-p.2) - Real.exp (-(p.1 ^ 2 * p.2))))).stronglyMeasurable
  have generated := joint.integral_prod_right' (ν := volume.restrict (Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1)))
  have direction : 1 / ((N : ℝ) + 1) ≤ (N : ℝ) + 1 := by
    have source : 1 ≤ (N : ℝ) + 1 := by have nonneg := Nat.cast_nonneg (α := ℝ) N; linarith
    have inv : 1 / ((N : ℝ) + 1) ≤ 1 := by simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) source
    exact inv.trans source
  change Measurable (fun frequency : ℝ => (1 / 2 : ℝ) * ∫ t : ℝ in (1 / ((N : ℝ) + 1))..((N : ℝ) + 1), t⁻¹ * (Real.exp (-t) - Real.exp (-(frequency ^ 2 * t))))
  simpa only [intervalIntegral.integral_of_le direction] using generated.measurable.const_mul (1 / 2 : ℝ)

private theorem heat_log_paired_source_limit (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    Tendsto (fun N : ℕ => ∫ x : ℝ, star (test x) * (heatLogCut N x : ℂ) * value x)
      atTop (𝓝 (inner ℂ (OriginalGamma.Source.FiniteLogCounting.logSchwartzL2 test) value)) := by
  let logged := OriginalGamma.Source.FiniteLogCounting.logSchwartzL2 test
  let bound : ℝ → ℝ := fun x => 2 * ‖logged x‖ * ‖value x‖
  have logRead := OriginalGamma.Source.FiniteLogCounting.original_log_schwartz_raw test
  have boundInt : Integrable bound := by
    have product := (L2.integrable_inner (𝕜 := ℂ) logged value).norm.const_mul 2
    apply product.congr
    filter_upwards with x
    simp only [bound, RCLike.inner_apply, starRingEnd_apply, norm_mul, norm_star]
    ring
  have measured (N : ℕ) : AEStronglyMeasurable (fun x : ℝ => star (test x) * (heatLogCut N x : ℂ) * value x) :=
    ((by fun_prop : Measurable (fun x : ℝ => star (test x))).mul ((heat_log_cut_measurable N).complex_ofReal)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable value)
  have dominate (N : ℕ) : ∀ᵐ x : ℝ ∂volume,
      ‖star (test x) * (heatLogCut N x : ℂ) * value x‖ ≤ bound x := by
    filter_upwards [logRead, volume.ae_ne (0 : ℝ)] with x logarithm nonzero
    dsimp only [bound]
    rw [logarithm, norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖test x‖ * |heatLogCut N x| * ‖value x‖ ≤ ‖test x‖ * (2 * |Real.log (|x|)|) * ‖value x‖ := by
        gcongr
        exact heat_log_cut_bound N x nonzero
      _ = _ := by ring
  have point : ∀ᵐ x : ℝ ∂volume, Tendsto
      (fun N : ℕ => star (test x) * (heatLogCut N x : ℂ) * value x) atTop
      (𝓝 (star (test x) * (Real.log (|x|) : ℂ) * value x)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
    exact (((Complex.continuous_ofReal.tendsto _).comp (heat_log_cut_limit x nonzero)).const_mul _).mul_const _
  have source := tendsto_integral_of_dominated_convergence bound measured boundInt dominate point
  have actual : (∫ x : ℝ, star (test x) * (Real.log (|x|) : ℂ) * value x) = inner ℂ logged value := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [logRead] with x logarithm
    rw [RCLike.inner_apply, logarithm, starRingEnd_apply, star_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  rw [actual] at source
  exact source

private def sourceHeat (time : ℝ) (positive : 0 < time) : SchwartzMap ℝ ℂ :=
  burnolBoundaryGaussianHeatTest (time / Real.pi) (div_pos positive Real.pi_pos)

private theorem source_heat_frequency (time : ℝ) (positive : 0 < time) (x : ℝ) :
    (𝓕 (sourceHeat time positive)) x = ((Real.exp (-(time * x ^ 2)) : ℝ) : ℂ) := by
  rw [sourceHeat, fourier_burnolBoundaryGaussianHeatTest, burnolGaussianRaw, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  congr 2
  field_simp [Real.pi_ne_zero]

private theorem source_heat_inverse_frequency (time : ℝ) (positive : 0 < time) (x : ℝ) :
    (𝓕⁻ (sourceHeat time positive)) x = ((Real.exp (-(time * x ^ 2)) : ℝ) : ℂ) := by
  change (𝓕 (sourceHeat time positive)) (-x) = _
  rw [source_heat_frequency]
  simp only [neg_sq]

private def sourceHeatCotest (time : ℝ) (positive : 0 < time) (test : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (.mul ℂ ℂ) (sourceHeat time positive) test

private theorem source_heat_cotest_inverse (time : ℝ) (positive : 0 < time) (test : SchwartzMap ℝ ℂ) :
    𝓕⁻ (sourceHeatCotest time positive test) =
      SchwartzMap.pairing (.mul ℂ ℂ) (𝓕⁻ (sourceHeat time positive)) (𝓕⁻ test) := by
  ext x
  change (𝓕 (sourceHeatCotest time positive test)) (-x) = _
  rw [sourceHeatCotest, SchwartzMap.fourier_convolution]
  rfl

private theorem source_heat_physical (time : ℝ) (positive : 0 < time) (x : ℝ) :
    sourceHeat time positive x = offDiagonalHeat time x := by
  have frequency : ((𝓕 (sourceHeat time positive) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = burnolGaussianRaw (time / Real.pi) := by
    funext y
    rw [source_heat_frequency, burnolGaussianRaw, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
    congr 2
    field_simp [Real.pi_ne_zero]
  calc
    _ = (𝓕⁻ (𝓕 (sourceHeat time positive))) x := by rw [fourierInv_fourier_eq]
    _ = offDiagonalHeat time x := by
      change (𝓕 (𝓕 (sourceHeat time positive))) (-x) = _
      rw [SchwartzMap.fourier_coe, frequency, fourier_burnolGaussianRaw (div_pos positive Real.pi_pos)]
      unfold offDiagonalHeat burnolGaussianReciprocalScale burnolGaussianRaw
      rw [Real.rpow_neg (div_pos positive Real.pi_pos).le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv, inv_div,
        ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
      congr 2
      field_simp [positive.ne', Real.pi_ne_zero]

private theorem source_heat_cotest_physical (time : ℝ) (positive : 0 < time)
    (test : SchwartzMap ℝ ℂ) (y : ℝ) :
    sourceHeatCotest time positive test y = ∫ x : ℝ, offDiagonalHeat time (y - x) * test x := by
  rw [sourceHeatCotest, SchwartzMap.convolution_apply]
  change (∫ x : ℝ, sourceHeat time positive x * test (y - x)) = _
  rw [← integral_sub_left_eq_self (fun x : ℝ => sourceHeat time positive x * test (y - x)) volume y]
  simp_rw [sub_sub_cancel, source_heat_physical]

private def tailWeight (y : ℝ) : ℝ := (1 + |y|)⁻¹

private theorem tail_weight_memLp : MemLp tailWeight 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by unfold tailWeight; fun_prop : Measurable tailWeight).aestronglyMeasurable).mpr
  apply integrable_inv_one_add_sq.mono' (by unfold tailWeight; fun_prop)
  filter_upwards with y
  have positive : 0 < 1 + |y| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), tailWeight, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive), inv_pow]
  have den : 0 < 1 + y ^ 2 := by positivity
  have bigger : 1 + y ^ 2 ≤ (1 + |y|) ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
  simpa only [one_div] using one_div_le_one_div_of_le den bigger

private theorem kernel_clock_payment (distance : ℝ) (nonzero : distance ≠ 0) :
    (∫ time : ℝ in Ioi 0, (time : ℂ)⁻¹ * offDiagonalHeat time distance) = ((|distance|⁻¹ : ℝ) : ℂ) := by
  calc
    _ = (-2 : ℂ) * offDiagonalLog distance := by unfold offDiagonalLog; ring
    _ = _ := by
      rw [off_diagonal_gaussian_payment distance nonzero]
      push_cast
      field_simp [abs_ne_zero.mpr nonzero]

private theorem kernel_clock_integrable (distance : ℝ) (nonzero : distance ≠ 0) :
    IntegrableOn (fun time : ℝ => (time : ℂ)⁻¹ * offDiagonalHeat time distance) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [kernel_clock_payment distance nonzero]
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (abs_ne_zero.mpr nonzero))

private theorem kernel_clock_norm_payment (distance : ℝ) (nonzero : distance ≠ 0) :
    (∫ time : ℝ in Ioi 0, ‖(time : ℂ)⁻¹ * offDiagonalHeat time distance‖) = |distance|⁻¹ := by
  have castNorm : Complex.ofReal (∫ time : ℝ in Ioi 0, ‖(time : ℂ)⁻¹ * offDiagonalHeat time distance‖) =
      ∫ time : ℝ in Ioi 0, (time : ℂ)⁻¹ * offDiagonalHeat time distance := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with time positive
    have tpos : 0 < time := positive
    unfold offDiagonalHeat
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos tpos, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.exp_pos _),
      Complex.ofReal_mul, Complex.ofReal_inv]
  apply Complex.ofReal_injective
  exact castNorm.trans (kernel_clock_payment distance nonzero)

end
end OriginalGamma.Source.KappaConductor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
