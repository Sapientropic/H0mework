import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Prolate.Kernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingPrimitive
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ProlateFourierTail
open Complex Filter FourierTransform MeasureTheory Set
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszSourceGreen ProlateKernel
open scoped ContDiff Topology ENNReal
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "freq" => (2 * (Real.pi : ℂ))
attribute [local instance 1100] NormedSpace.complexToReal

/-- Every tail here is absolutely integrable; the original non-L¹ Mellin tail is never split off. -/
def tail (coordinate : BurnolCompletedMellinCoordinate) (k : ℕ) (x : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi q, (t : ℂ) ^ (-(star coordinate.value + k)) * Constructor.phase x t

private theorem power_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (k : ℕ) (positive : 1 ≤ k) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(star coordinate.value + k))) (Ioi q) := by
  apply integrableOn_Ioi_cpow_of_lt _ (by norm_num : (0 : ℝ) < q)
  simp only [neg_re, add_re, star_def, conj_re, natCast_re]
  have bound : (1 : ℝ) ≤ k := by exact_mod_cast positive
  linarith [coordinate.rightHalf]

private theorem tail_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (k : ℕ) (positive : 1 ≤ k) (x : ℝ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(star coordinate.value + k)) * Constructor.phase x t) (Ioi q) := by
  apply (power_integrable coordinate k positive).mul_bdd (Constructor.phaseContinuous x).aestronglyMeasurable
  filter_upwards with t
  exact (Circle.norm_coe (𝐞 (-(x * t)))).le

/-- One source integration by parts retains its actual q phase and its next integrable tail. -/
theorem tail_step (coordinate : BurnolCompletedMellinCoordinate) (k : ℕ) (positive : 1 ≤ k) (x : ℝ) :
    (freq * I * (x : ℂ)) * tail coordinate k x =
      (q : ℂ) ^ (-(star coordinate.value + k)) * Constructor.phase x q -
        (star coordinate.value + k) * tail coordinate (k + 1) x := by
  let primitive := fun t : ℝ => (t : ℂ) ^ (-(star coordinate.value + k)) * Constructor.phase x t
  have derivative (t : ℝ) (inside : t ∈ Ici q) :
      HasDerivAt primitive
        (-(star coordinate.value + k) *
          ((t : ℂ) ^ (-(star coordinate.value + (k + 1 : ℕ))) * Constructor.phase x t) -
            (freq * I * (x : ℂ)) * ((t : ℂ) ^ (-(star coordinate.value + k)) * Constructor.phase x t)) t := by
    convert! (burnolMellinTailPower_hasDerivAt (star coordinate.value + k)
      (by linarith [inside.out] : 0 < t)).mul (Constructor.phase_derivative x t) using 1
    push_cast
    ring
  have integrable : IntegrableOn (fun t : ℝ =>
      -(star coordinate.value + k) *
        ((t : ℂ) ^ (-(star coordinate.value + (k + 1 : ℕ))) * Constructor.phase x t) -
          (freq * I * (x : ℂ)) * ((t : ℂ) ^ (-(star coordinate.value + k)) * Constructor.phase x t)) (Ioi q) :=
    ((tail_integrable coordinate (k + 1) (by omega) x).const_mul _).sub
      ((tail_integrable coordinate k positive x).const_mul _)
  have infinity : Tendsto primitive atTop (𝓝 0) := by
    apply (burnolMellinTailPower_tendsto_zero (star coordinate.value + k) ?_).zero_mul_isBoundedUnder_le
    · exact isBoundedUnder_of_eventually_le (Eventually.of_forall fun t =>
        (Circle.norm_coe (𝐞 (-(x * t)))).le)
    · simp only [add_re, star_def, conj_re, natCast_re]
      positivity [coordinate.rightHalf]
  have source := integral_Ioi_of_hasDerivAt_of_tendsto' derivative integrable infinity
  rw [integral_sub ((tail_integrable coordinate (k + 1) (by omega) x).const_mul _)
    ((tail_integrable coordinate k positive x).const_mul _), integral_const_mul,
    integral_const_mul] at source
  change -(star coordinate.value + k) * tail coordinate (k + 1) x -
    (freq * I * (x : ℂ)) * tail coordinate k x = 0 - primitive q at source
  dsimp only [primitive] at source
  linear_combination -source

private theorem original_tail_read (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolMellinTailDerivativeFourierRaw q coordinate x = tail coordinate 1 x := by
  unfold burnolMellinTailDerivativeFourierRaw VectorFourier.fourierIntegral tail
  simp only [innerₗ_apply_apply, Real.inner_apply, Circle.smul_def, smul_eq_mul]
  have source : (fun t : ℝ => (𝐞 (-(t * x)) : ℂ) * burnolRadiusMellinTailKernelRaw q (coordinate.value + 1) t) =
      (Ioi q).indicator (fun t : ℝ => (t : ℂ) ^ (-(star coordinate.value + 1)) * Constructor.phase x t) := by
    funext t
    by_cases inside : t ∈ Ioi q
    · simp only [burnolRadiusMellinTailKernelRaw, inside, if_true, indicator_of_mem inside,
        star_add, star_one, Constructor.phase]
      ring
    · simp only [burnolRadiusMellinTailKernelRaw, inside, if_false, mul_zero, indicator_of_notMem inside]
  rw [source, integral_indicator measurableSet_Ioi]
  simp only [Nat.cast_one]

private theorem phase_exp (x y : ℝ) : Constructor.phase x y =
    Complex.exp (-(freq * (x : ℂ) * (y : ℂ)) * I) := by
  unfold Constructor.phase
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

private theorem phase_cos (x : ℝ) :
    Constructor.phase x q + Constructor.phase (-x) q = 2 * Complex.cos (scale * (x : ℂ)) := by
  rw [phase_exp, phase_exp, Complex.cos]
  simp only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]
  unfold scale frequency
  ring_nf

private theorem phase_sin (x : ℝ) :
    (Constructor.phase x q - Constructor.phase (-x) q) * I = 2 * Complex.sin (scale * (x : ℂ)) := by
  rw [phase_exp, phase_exp, Complex.sin]
  simp only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]
  unfold scale frequency
  ring_nf

def sinTail (coordinate : BurnolCompletedMellinCoordinate) (k : ℕ) (x : ℝ) : ℂ :=
  (tail coordinate k x - tail coordinate k (-x)) * I / 2

def cosTail (coordinate : BurnolCompletedMellinCoordinate) (k : ℕ) (x : ℝ) : ℂ :=
  (tail coordinate k x + tail coordinate k (-x)) / 2

theorem remainder_integral (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    sinTail coordinate 3 x = ∫ t : ℝ in Ioi q,
      (t : ℂ) ^ (-(star coordinate.value + 3)) * Complex.sin (frequency * (x : ℂ) * (t : ℂ)) := by
  unfold sinTail tail
  rw [← integral_sub (tail_integrable coordinate 3 (by omega) x)
    (tail_integrable coordinate 3 (by omega) (-x)), ← integral_mul_const, ← integral_div]
  apply integral_congr_ae
  filter_upwards with t
  rw [phase_exp, phase_exp, Complex.sin]
  simp only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg, Nat.cast_ofNat]
  unfold frequency
  ring

private theorem sinTail_step (coordinate : BurnolCompletedMellinCoordinate)
    (k : ℕ) (positive : 1 ≤ k) (x : ℝ) :
    (freq * (x : ℂ)) * sinTail coordinate k x =
      (q : ℂ) ^ (-(star coordinate.value + k)) * Complex.cos (scale * (x : ℂ)) -
        (star coordinate.value + k) * cosTail coordinate (k + 1) x := by
  have first := tail_step coordinate k positive x
  have second := tail_step coordinate k positive (-x)
  have phases := phase_cos x
  simp only [Complex.ofReal_neg] at second
  unfold sinTail cosTail
  linear_combination (first + second + (q : ℂ) ^ (-(star coordinate.value + k)) * phases) / 2

private theorem cosTail_step (coordinate : BurnolCompletedMellinCoordinate)
    (k : ℕ) (positive : 1 ≤ k) (x : ℝ) :
    (freq * (x : ℂ)) * cosTail coordinate k x =
      -(q : ℂ) ^ (-(star coordinate.value + k)) * Complex.sin (scale * (x : ℂ)) +
        (star coordinate.value + k) * sinTail coordinate (k + 1) x := by
  have first := tail_step coordinate k positive x
  have second := tail_step coordinate k positive (-x)
  have phases := phase_sin x
  simp only [Complex.ofReal_neg] at second
  unfold sinTail cosTail
  linear_combination (norm := ring_nf) -I * (first - second) / 2 -
    (q : ℂ) ^ (-(star coordinate.value + k)) * phases / 2
  simp only [Complex.I_sq]
  ring

private theorem numerator_read (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolGapTailFourierNumerator q coordinate x =
      GapEuler.gapMean q coordinate * Constructor.phase (-x) q +
        ((q : ℂ) ^ (-star coordinate.value) - GapEuler.gapMean q coordinate) * Constructor.phase x q -
          star coordinate.value * tail coordinate 1 x := by
  unfold burnolGapTailFourierNumerator GapEuler.gapMean
  rw [original_tail_read]
  simp only [Constructor.phase, neg_mul, neg_neg, mul_comm]

/-- The first tail is the exact original Fourier numerator, with the original gap mean retained. -/
theorem original_numerator (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ} (nonzero : x ≠ 0) :
    (freq * (x : ℂ)) * ForcingWhole.raw coordinate x =
      (2 * GapEuler.gapMean q coordinate - (q : ℂ) ^ (-star coordinate.value)) *
        Complex.sin (scale * (x : ℂ)) + star coordinate.value * sinTail coordinate 1 x := by
  have xne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  have pne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have phases := phase_sin x
  ring_nf at phases
  unfold ForcingWhole.raw burnolEvenRaw burnolGapTailFourierRaw
  rw [numerator_read, numerator_read]
  simp only [neg_neg, Complex.ofReal_neg]
  unfold sinTail
  field_simp
  linear_combination (norm := ring_nf) (2 * GapEuler.gapMean q coordinate - (q : ℂ) ^ (-star coordinate.value)) * I * phases
  simp only [Complex.I_sq]
  ring

/-- The three endpoint terms and the full integrable remainder are computed from the original h. -/
theorem original_expansion (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ} (nonzero : x ≠ 0) :
    ForcingWhole.raw coordinate x =
      (2 * GapEuler.gapMean q coordinate - (q : ℂ) ^ (-star coordinate.value)) *
          Complex.sin (scale * (x : ℂ)) / (freq * (x : ℂ)) +
        star coordinate.value * (q : ℂ) ^ (-(star coordinate.value + 1)) *
          Complex.cos (scale * (x : ℂ)) / (freq * (x : ℂ)) ^ 2 +
        star coordinate.value * (star coordinate.value + 1) *
          (q : ℂ) ^ (-(star coordinate.value + 2)) * Complex.sin (scale * (x : ℂ)) /
            (freq * (x : ℂ)) ^ 3 -
        star coordinate.value * (star coordinate.value + 1) * (star coordinate.value + 2) *
          sinTail coordinate 3 x / (freq * (x : ℂ)) ^ 3 := by
  have source := original_numerator coordinate nonzero
  have first := sinTail_step coordinate 1 (by omega) x
  have second := cosTail_step coordinate 2 (by omega) x
  norm_num only [Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd] at first second
  have xne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  have pne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination (freq * (x : ℂ)) ^ 2 * source +
    star coordinate.value * (freq * (x : ℂ)) * first -
      star coordinate.value * (star coordinate.value + 1) * second

/-- The remaining source has every moment needed for two actual Fourier derivatives. -/
theorem remainder_moment (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ) (bound : n ≤ 2) :
    Integrable (fun t : ℝ => ‖t‖ ^ n * ‖(t : ℂ) ^ (-(star coordinate.value + 3))‖)
      (volume.restrict (Ioi q)) := by
  have exponent : (n : ℝ) - coordinate.value.re - 3 < -1 := by
    have nle : (n : ℝ) ≤ 2 := by exact_mod_cast bound
    linarith [coordinate.rightHalf]
  have source := integrableOn_Ioi_rpow_of_lt exponent (by norm_num : (0 : ℝ) < q)
  apply source.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t inside
  have positive : 0 < t := (by norm_num : (0 : ℝ) < q).trans inside
  rw [Complex.norm_cpow_eq_rpow_re_of_pos positive, Real.norm_of_nonneg positive.le,
    ← Real.rpow_natCast, ← Real.rpow_add positive]
  congr 1
  simp only [neg_re, add_re, star_def, conj_re]
  norm_num
  ring

theorem remainder_contDiff (coordinate : BurnolCompletedMellinCoordinate) :
    ContDiff ℝ 2 (sinTail coordinate 3) := by
  have moments (n : ℕ) (bound : (n : ℕ∞) ≤ 2) :
      Integrable (fun t : ℝ => ‖t‖ ^ n * ‖(t : ℂ) ^ (-(star coordinate.value + 3))‖)
        (volume.restrict (Ioi q)) :=
    remainder_moment coordinate n (by exact_mod_cast bound)
  have bilinear : (innerₗ ℝ) = (innerSL ℝ).toLinearMap₁₂ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [innerₗ_apply_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, innerSL_apply_apply]
  have original := VectorFourier.contDiff_fourierIntegral (innerSL ℝ) (N := 2) moments
  have tailRead : tail coordinate 3 = VectorFourier.fourierIntegral 𝐞
      (volume.restrict (Ioi q)) (innerSL ℝ).toLinearMap₁₂
        (fun t : ℝ => (t : ℂ) ^ (-(star coordinate.value + 3))) := by
    funext x
    rw [← bilinear]
    simp only [tail, VectorFourier.fourierIntegral, innerₗ_apply_apply, Real.inner_apply,
      Constructor.phase, Circle.smul_def, smul_eq_mul,
      mul_comm, Nat.cast_ofNat]
  have regular : ContDiff ℝ 2 (tail coordinate 3) := tailRead ▸ original
  unfold sinTail
  fun_prop

def remainderBound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  ∫ t : ℝ in Ioi q, ‖(t : ℂ) ^ (-(star coordinate.value + 3))‖

theorem remainderBound_nonnegative (coordinate : BurnolCompletedMellinCoordinate) :
    0 ≤ remainderBound coordinate := integral_nonneg fun _ => norm_nonneg _

theorem remainder_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    ‖sinTail coordinate 3 x‖ ≤ remainderBound coordinate := by
  have one (y : ℝ) : ‖tail coordinate 3 y‖ ≤ remainderBound coordinate := by
    apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    filter_upwards with t
    simp only [Constructor.phase, norm_mul, Circle.norm_coe, mul_one, Nat.cast_ofNat]
  unfold sinTail
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  exact (norm_sub_le _ _).trans ((add_le_add (one x) (one (-x))).trans_eq (by ring))

namespace EdgeTrig
private theorem phase_exp (x y : ℝ) :
    Constructor.phase x y = Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * (y : ℂ)) := by
  unfold Constructor.phase
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

private theorem phase_pair (x : ℝ) :
    Constructor.phase x q + Constructor.phase x (-q) =
      2 * Complex.cos (2 * (Real.pi : ℂ) * q * (x : ℂ)) := by
  rw [phase_exp, phase_exp, Complex.cos]
  have first : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * q =
      -(2 * (Real.pi : ℂ) * q * (x : ℂ)) * Complex.I := by ring
  have second : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * ((-q : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ) * q * (x : ℂ)) * Complex.I := by push_cast; ring
  rw [first, second]
  ring

private theorem fourier_one (x : ℝ) :
    burnolRadiusTruncatedFourierRaw q (intervalConstant q) x =
      ∫ y : ℝ in (-q)..q, Constructor.phase x y := by
  have actual := Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)
  rw [← Constructor.fourierRaw_state, congrFun actual x, Constructor.fourierRaw_integral]
  simp only [mul_one]

private theorem edge_trigonometric (x : ℝ) (nonzero : x ≠ 0) :
    Edge.raw q x = (2 * q : ℂ) *
      (Complex.cos (2 * (Real.pi : ℂ) * q * (x : ℂ)) -
        Complex.sin (2 * (Real.pi : ℂ) * q * (x : ℂ)) /
          (2 * (Real.pi : ℂ) * q * (x : ℂ))) := by
  have piNe : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have xNe : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  have slopeNe : -2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) piNe) Complex.I_ne_zero) xNe
  rw [Edge.raw_apply, phase_pair, fourier_one,
    intervalIntegral.integral_congr (fun y _ => phase_exp x y), integral_exp_mul_complex slopeNe,
    Complex.sin]
  have first : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * q =
      -(2 * (Real.pi : ℂ) * q * (x : ℂ)) * Complex.I := by ring
  have second : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * ((-q : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ) * q * (x : ℂ)) * Complex.I := by push_cast; ring
  rw [first, second]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem original_trig (x : ℝ) (nonzero : x ≠ 0) :
    Edge.raw q x = 2 * (q : ℂ) * Complex.cos (scale * (x : ℂ)) -
      2 * Complex.sin (scale * (x : ℂ)) / (frequency * (x : ℂ)) := by
  rw [edge_trigonometric x nonzero]
  unfold scale frequency
  have piNe : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have xNe : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  field_simp

theorem original_derivative (x : ℝ) (nonzero : x ≠ 0) :
    HasDerivAt (Edge.raw q)
      (-2 * (q : ℂ) * scale * Complex.sin (scale * (x : ℂ)) -
        2 * (q : ℂ) * Complex.cos (scale * (x : ℂ)) / (x : ℂ) +
          2 * Complex.sin (scale * (x : ℂ)) / (frequency * (x : ℂ) ^ 2)) x := by
  have omegaNe : frequency ≠ 0 := by
    unfold frequency
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have xNe : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  have inner := (hasDerivAt_id (x : ℂ)).const_mul scale
  have cosine := (Complex.hasDerivAt_cos (scale * (x : ℂ))).comp (x : ℂ) inner
  have sine := (Complex.hasDerivAt_sin (scale * (x : ℂ))).comp (x : ℂ) inner
  have quotient := (sine.const_mul 2).div ((hasDerivAt_id (x : ℂ)).const_mul frequency) (mul_ne_zero omegaNe xNe)
  have analytic := ((cosine.const_mul (2 * (q : ℂ))).sub quotient).comp_ofReal
  have localDerivative : HasDerivAt (fun t : ℝ =>
      2 * (q : ℂ) * Complex.cos (scale * (t : ℂ)) - 2 * Complex.sin (scale * (t : ℂ)) / (frequency * (t : ℂ)))
      (-2 * (q : ℂ) * scale * Complex.sin (scale * (x : ℂ)) -
        2 * (q : ℂ) * Complex.cos (scale * (x : ℂ)) / (x : ℂ) +
          2 * Complex.sin (scale * (x : ℂ)) / (frequency * (x : ℂ) ^ 2)) x := by
    convert! analytic using 1
    simp only [id_eq, mul_one, Function.comp_apply]
    field_simp [omegaNe, xNe]
    unfold scale
    ring
  apply localDerivative.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds nonzero] with t ht
  exact original_trig t ht

end EdgeTrig

def edgeDerivative (x : ℝ) : ℂ :=
  -2 * (q : ℂ) * scale * Complex.sin (scale * (x : ℂ)) -
    2 * (q : ℂ) * Complex.cos (scale * (x : ℂ)) / (x : ℂ) +
      2 * Complex.sin (scale * (x : ℂ)) / (frequency * (x : ℂ) ^ 2)

def first (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((star coordinate.value - 1) * ForcingWhole.raw coordinate x +
    ForcingWhole.coefficient coordinate * Edge.raw q x) / (x : ℂ)

def second (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((star coordinate.value - 1) * (star coordinate.value - 2) * ForcingWhole.raw coordinate x +
    ForcingWhole.coefficient coordinate *
      ((star coordinate.value - 2) * Edge.raw q x + (x : ℂ) * edgeDerivative x)) / (x : ℂ) ^ 2

theorem original_first_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (nonzero : x ≠ 0) : HasDerivAt (ForcingWhole.raw coordinate) (first coordinate x) x :=
  forcing_raw_hasDerivAt coordinate x nonzero

theorem original_second_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (nonzero : x ≠ 0) : HasDerivAt (first coordinate) (second coordinate x) x := by
  have castNonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  have identity : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := Complex.ofRealCLM.hasDerivAt
  have generated := (((original_first_hasDerivAt coordinate nonzero).const_mul (star coordinate.value - 1)).add
    ((EdgeTrig.original_derivative x nonzero).const_mul (ForcingWhole.coefficient coordinate))).div identity castNonzero
  convert! generated using 1
  unfold first second edgeDerivative
  simp only [Pi.add_apply]
  field_simp
  ring

private theorem second_derivative (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (nonzero : x ≠ 0) : deriv (deriv (ForcingWhole.raw coordinate)) x = second coordinate x := by
  have same : deriv (ForcingWhole.raw coordinate) =ᶠ[𝓝 x] first coordinate := by
    filter_upwards [eventually_ne_nhds nonzero] with t ht
    exact (original_first_hasDerivAt coordinate ht).deriv
  exact ((original_second_hasDerivAt coordinate nonzero).congr_of_eventuallyEq same).deriv

def remainderNumerator (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star coordinate.value * (star coordinate.value + 1) *
    ((q : ℂ) ^ (-(star coordinate.value + 2)) * Complex.sin (scale * (x : ℂ)) -
      (star coordinate.value + 2) * sinTail coordinate 3 x)

/-- The original gap primitive cancels both growing Fourier terms before any norm is taken. -/
theorem original_action_read (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (nonzero : x ≠ 0) :
    act (ForcingWhole.raw coordinate) x =
      (star coordinate.value * (star coordinate.value - 1) -
        (q : ℂ) ^ 2 * (star coordinate.value - 1) * (star coordinate.value - 2) / (x : ℂ) ^ 2) *
          ForcingWhole.raw coordinate x -
      ForcingWhole.coefficient coordinate * (q : ℂ) ^ 2 * (star coordinate.value - 2) *
        Edge.raw q x / (x : ℂ) ^ 2 -
      ForcingWhole.coefficient coordinate * (q : ℂ) ^ 2 * edgeDerivative x / (x : ℂ) +
      ((q : ℂ) ^ 2 * remainderNumerator coordinate x / frequency +
        2 * ForcingWhole.coefficient coordinate * (1 - star coordinate.value) *
          Complex.sin (scale * (x : ℂ)) / frequency) / (x : ℂ) := by
  have castNonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have primitive : (q : ℂ) ^ (-star coordinate.value) =
      2 * (1 - star coordinate.value) * GapEuler.gapMean q coordinate := by
    linear_combination -2 * GapEuler.gapMean_primitive q (by norm_num) coordinate
  have nextPower : (q : ℂ) ^ (-(star coordinate.value + 1)) =
      (q : ℂ) ^ (-star coordinate.value) / (q : ℂ) := by
    rw [show -(star coordinate.value + 1) = -star coordinate.value - 1 by ring,
      Complex.cpow_sub _ _ (by norm_num : (q : ℂ) ≠ 0), Complex.cpow_one]
  rw [act, second_derivative coordinate nonzero, (original_first_hasDerivAt coordinate nonzero).deriv]
  unfold first second
  rw [original_expansion coordinate nonzero, EdgeTrig.original_trig x nonzero]
  unfold edgeDerivative remainderNumerator ForcingWhole.coefficient scale frequency
  rw [nextPower, primitive]
  field_simp
  ring

private def ExteriorBounded (f : ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, q ≤ |x| → ‖f x‖ ≤ C

private theorem ExteriorBounded.const (z : ℂ) : ExteriorBounded (fun _ => z) :=
  ⟨‖z‖, norm_nonneg _, fun _ _ => le_rfl⟩

private theorem ExteriorBounded.add {f g : ℝ → ℂ} (hf : ExteriorBounded f) (hg : ExteriorBounded g) :
    ExteriorBounded (fun x => f x + g x) := by
  obtain ⟨A, ha, fa⟩ := hf
  obtain ⟨B, hb, gb⟩ := hg
  exact ⟨A + B, add_nonneg ha hb, fun x hx => (norm_add_le _ _).trans (add_le_add (fa x hx) (gb x hx))⟩

private theorem ExteriorBounded.sub {f g : ℝ → ℂ} (hf : ExteriorBounded f) (hg : ExteriorBounded g) :
    ExteriorBounded (fun x => f x - g x) := by
  obtain ⟨A, ha, fa⟩ := hf
  obtain ⟨B, hb, gb⟩ := hg
  exact ⟨A + B, add_nonneg ha hb, fun x hx => (norm_sub_le _ _).trans (add_le_add (fa x hx) (gb x hx))⟩

private theorem ExteriorBounded.mul {f g : ℝ → ℂ} (hf : ExteriorBounded f) (hg : ExteriorBounded g) :
    ExteriorBounded (fun x => f x * g x) := by
  obtain ⟨A, ha, fa⟩ := hf
  obtain ⟨B, hb, gb⟩ := hg
  refine ⟨A * B, mul_nonneg ha hb, fun x hx => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (fa x hx) (gb x hx) (norm_nonneg _) ha

private theorem ExteriorBounded.const_mul {f : ℝ → ℂ} (hf : ExteriorBounded f) (z : ℂ) :
    ExteriorBounded (fun x => z * f x) := (ExteriorBounded.const z).mul hf

private theorem ExteriorBounded.congr {f g : ℝ → ℂ} (hg : ExteriorBounded g)
    (same : ∀ x : ℝ, q ≤ |x| → f x = g x) : ExteriorBounded f := by
  obtain ⟨C, hc, gc⟩ := hg
  exact ⟨C, hc, fun x hx => by rw [same x hx]; exact gc x hx⟩

private theorem exterior_nonzero {x : ℝ} (outside : q ≤ |x|) : x ≠ 0 := by
  have positive : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans_le outside
  exact abs_pos.mp positive

private theorem exterior_inverse : ExteriorBounded (fun x : ℝ => (x : ℂ)⁻¹) := by
  refine ⟨4, by norm_num, fun x hx => ?_⟩
  have positive : 0 < |x| := abs_pos.mpr (exterior_nonzero hx)
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, ← one_div, div_le_iff₀ positive]
  linarith

private theorem sin_norm (x : ℝ) : ‖Complex.sin (scale * (x : ℂ))‖ ≤ 1 := by
  have realRead : scale * (x : ℂ) = (((2 * Real.pi * q) * x : ℝ) : ℂ) := by
    unfold scale frequency
    push_cast
    rfl
  rw [realRead, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

private theorem cos_norm (x : ℝ) : ‖Complex.cos (scale * (x : ℂ))‖ ≤ 1 := by
  have realRead : scale * (x : ℂ) = (((2 * Real.pi * q) * x : ℝ) : ℂ) := by
    unfold scale frequency
    push_cast
    rfl
  rw [realRead, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

private theorem bounded_sin : ExteriorBounded (fun x : ℝ => Complex.sin (scale * (x : ℂ))) :=
  ⟨1, by norm_num, fun x _ => sin_norm x⟩

private theorem bounded_cos : ExteriorBounded (fun x : ℝ => Complex.cos (scale * (x : ℂ))) :=
  ⟨1, by norm_num, fun x _ => cos_norm x⟩

private theorem bounded_sinTail (coordinate : BurnolCompletedMellinCoordinate) (k : ℕ) :
    ExteriorBounded (sinTail coordinate k) := by
  let C : ℝ := ∫ t : ℝ in Ioi q, ‖(t : ℂ) ^ (-(star coordinate.value + k))‖
  have one (y : ℝ) : ‖tail coordinate k y‖ ≤ C := by
    apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    filter_upwards with t
    simp only [Constructor.phase, norm_mul, Circle.norm_coe, mul_one]
  refine ⟨C, integral_nonneg fun _ => norm_nonneg _, fun x _ => ?_⟩
  unfold sinTail
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  exact (norm_sub_le _ _).trans ((add_le_add (one x) (one (-x))).trans_eq (by ring))

private theorem bounded_value_weighted (coordinate : BurnolCompletedMellinCoordinate) :
    ExteriorBounded (fun x : ℝ => (x : ℂ) * ForcingWhole.raw coordinate x) := by
  have bounded := ((bounded_sin.const_mul
    (2 * GapEuler.gapMean q coordinate - (q : ℂ) ^ (-star coordinate.value))).add
      ((bounded_sinTail coordinate 1).const_mul (star coordinate.value))).const_mul frequency⁻¹
  apply bounded.congr
  intro x hx
  have source := original_numerator coordinate (exterior_nonzero hx)
  have nonzero : frequency ≠ 0 := by
    unfold frequency
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  change _ = frequency⁻¹ * _
  rw [← source]
  unfold frequency at nonzero ⊢
  field_simp

private theorem bounded_value (coordinate : BurnolCompletedMellinCoordinate) :
    ExteriorBounded (ForcingWhole.raw coordinate) := by
  apply (exterior_inverse.mul (bounded_value_weighted coordinate)).congr
  intro x hx
  have nonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (exterior_nonzero hx)
  field_simp

private theorem bounded_edge : ExteriorBounded (Edge.raw q) := by
  have source := (bounded_cos.const_mul (2 * (q : ℂ))).sub
    ((bounded_sin.mul exterior_inverse).const_mul (2 / frequency))
  apply source.congr
  intro x hx
  rw [EdgeTrig.original_trig x (exterior_nonzero hx)]
  ring

private theorem bounded_edgeDerivative : ExteriorBounded edgeDerivative := by
  have source := ((bounded_sin.const_mul (-2 * (q : ℂ) * scale)).sub
    ((bounded_cos.mul exterior_inverse).const_mul (2 * (q : ℂ)))).add
      ((bounded_sin.mul (exterior_inverse.mul exterior_inverse)).const_mul (2 / frequency))
  apply source.congr
  intro x _
  unfold edgeDerivative
  ring

private theorem bounded_first_weighted (coordinate : BurnolCompletedMellinCoordinate) :
    ExteriorBounded (fun x : ℝ => (x : ℂ) * first coordinate x) := by
  have source := ((bounded_value coordinate).const_mul (star coordinate.value - 1)).add
    (bounded_edge.const_mul (ForcingWhole.coefficient coordinate))
  apply source.congr
  intro x hx
  have nonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (exterior_nonzero hx)
  unfold first
  field_simp

private theorem bounded_remainderNumerator (coordinate : BurnolCompletedMellinCoordinate) :
    ExteriorBounded (remainderNumerator coordinate) :=
  ((bounded_sin.const_mul ((q : ℂ) ^ (-(star coordinate.value + 2)))).sub
    ((bounded_sinTail coordinate 3).const_mul (star coordinate.value + 2))).const_mul
      (star coordinate.value * (star coordinate.value + 1))

private theorem bounded_action_weighted (coordinate : BurnolCompletedMellinCoordinate) :
    ExteriorBounded (fun x : ℝ => (x : ℂ) * act (ForcingWhole.raw coordinate) x) := by
  have b0 := (bounded_value_weighted coordinate).const_mul
    (star coordinate.value * (star coordinate.value - 1))
  have b1 := ((bounded_value coordinate).mul exterior_inverse).const_mul
    ((q : ℂ) ^ 2 * (star coordinate.value - 1) * (star coordinate.value - 2))
  have b2 := (bounded_edge.mul exterior_inverse).const_mul
    (ForcingWhole.coefficient coordinate * (q : ℂ) ^ 2 * (star coordinate.value - 2))
  have b3 := bounded_edgeDerivative.const_mul (ForcingWhole.coefficient coordinate * (q : ℂ) ^ 2)
  have b4 := (bounded_remainderNumerator coordinate).const_mul ((q : ℂ) ^ 2 / frequency)
  have b5 := bounded_sin.const_mul (2 * ForcingWhole.coefficient coordinate * (1 - star coordinate.value) / frequency)
  have source := ((((b0.sub b1).sub b2).sub b3).add b4).add b5
  apply source.congr
  intro x hx
  have nonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (exterior_nonzero hx)
  rw [original_action_read coordinate (exterior_nonzero hx)]
  field_simp
  ring

private theorem ExteriorBounded.unweight {f : ℝ → ℂ}
    (hf : ExteriorBounded (fun x : ℝ => (x : ℂ) * f x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, q ≤ |x| → ‖f x‖ ≤ C / |x| := by
  obtain ⟨C, hc, bound⟩ := hf
  refine ⟨C, hc, fun x hx => ?_⟩
  have source := bound x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at source
  exact (le_div_iff₀ (abs_pos.mpr (exterior_nonzero hx))).mpr (by simpa only [mul_comm] using source)

theorem original_value_bound (coordinate : BurnolCompletedMellinCoordinate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, q ≤ |x| → ‖ForcingWhole.raw coordinate x‖ ≤ C / |x| :=
  (bounded_value_weighted coordinate).unweight

theorem original_first_bound (coordinate : BurnolCompletedMellinCoordinate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, q ≤ |x| → ‖first coordinate x‖ ≤ C / |x| :=
  (bounded_first_weighted coordinate).unweight

theorem original_tail_bound (coordinate : BurnolCompletedMellinCoordinate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, q ≤ |x| → ‖act (ForcingWhole.raw coordinate) x‖ ≤ C / |x| :=
  (bounded_action_weighted coordinate).unweight

theorem original_action_aestronglyMeasurable (coordinate : BurnolCompletedMellinCoordinate) :
    AEStronglyMeasurable (act (ForcingWhole.raw coordinate)) volume := by
  have value := (ForcingWhole.raw_local coordinate).aestronglyMeasurable
  have d1 := aestronglyMeasurable_deriv (ForcingWhole.raw coordinate) volume
  have d2 := aestronglyMeasurable_deriv (deriv (ForcingWhole.raw coordinate)) volume
  unfold act
  fun_prop

private theorem outer_memLp (f : ℝ → ℂ) (measured : AEStronglyMeasurable f volume)
    {C : ℝ} (nonnegative : 0 ≤ C) (bound : ∀ x : ℝ, q ≤ |x| → ‖f x‖ ≤ C / |x|) :
    MemLp (((symmetricInterval q)ᶜ).indicator f) 2 volume := by
  have measurable := measured.indicator (measurableSet_symmetricInterval q).compl
  apply (memLp_two_iff_integrable_sq_norm measurable).2
  let g : ℝ → ℝ := (Ioi q).indicator (fun x : ℝ => C ^ 2 * x ^ (-2 : ℝ))
  have positiveTail : IntegrableOn (fun x : ℝ => C ^ 2 * x ^ (-2 : ℝ)) (Ioi q) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < q)).const_mul _
  have gi : Integrable g := (integrable_indicator_iff measurableSet_Ioi).2 positiveTail
  have sumInt : Integrable (fun x : ℝ => g x + g (-x)) := gi.add gi.comp_neg
  have gn (x : ℝ) : 0 ≤ g x := by
    unfold g
    by_cases hx : x ∈ Ioi q
    · rw [indicator_of_mem hx]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ((by norm_num : (0 : ℝ) ≤ q).trans hx.le) _)
    · rw [indicator_of_notMem hx]
  apply sumInt.mono' (measurable.norm.pow 2)
  filter_upwards with x
  change ‖‖((symmetricInterval q)ᶜ).indicator f x‖ ^ 2‖ ≤ g x + g (-x)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  by_cases outside : q < |x|
  · have mem : x ∈ (symmetricInterval q)ᶜ := by
      change ¬(-q ≤ x ∧ x ≤ q)
      exact fun h => not_lt_of_ge (abs_le.mpr h) outside
    rw [indicator_of_mem mem]
    have square : ‖f x‖ ^ 2 ≤ (C / |x|) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (div_nonneg nonnegative (abs_nonneg _)) |>.2 (bound x outside.le)
    have power : (C / |x|) ^ 2 = C ^ 2 * |x| ^ (-2 : ℝ) := by
      rw [div_pow, show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg_natCast,
        zpow_neg, zpow_natCast, div_eq_mul_inv]
    apply square.trans
    rw [power]
    rcases le_total 0 x with pos | neg
    · have hx : q < x := by simpa only [abs_of_nonneg pos] using outside
      have hn : ¬q < -x := by linarith
      simp only [g, indicator_of_mem (show x ∈ Ioi q from hx),
        indicator_of_notMem (show -x ∉ Ioi q from hn), abs_of_nonneg pos, add_zero, le_refl]
    · have hn : q < -x := by simpa only [abs_of_nonpos neg] using outside
      have hx : ¬q < x := by linarith
      simp only [g, indicator_of_notMem (show x ∉ Ioi q from hx),
        indicator_of_mem (show -x ∈ Ioi q from hn), abs_of_nonpos neg, zero_add, le_refl]
  · have mem : x ∉ (symmetricInterval q)ᶜ := by
      change ¬¬(-q ≤ x ∧ x ≤ q)
      exact not_not.mpr (abs_le.mp (le_of_not_gt outside))
    rw [indicator_of_notMem mem]
    simpa using add_nonneg (gn x) (gn (-x))


/-- The actual whole Fourier forcing generates its exterior prolate L² source. -/
theorem original_outer_memLp (coordinate : BurnolCompletedMellinCoordinate) :
    MemLp (((symmetricInterval q)ᶜ).indicator (act (ForcingWhole.raw coordinate))) 2 volume := by
  obtain ⟨C, nonnegative, bound⟩ := original_tail_bound coordinate
  exact outer_memLp (act (ForcingWhole.raw coordinate))
    (original_action_aestronglyMeasurable coordinate) nonnegative bound

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ProlateFourierTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
