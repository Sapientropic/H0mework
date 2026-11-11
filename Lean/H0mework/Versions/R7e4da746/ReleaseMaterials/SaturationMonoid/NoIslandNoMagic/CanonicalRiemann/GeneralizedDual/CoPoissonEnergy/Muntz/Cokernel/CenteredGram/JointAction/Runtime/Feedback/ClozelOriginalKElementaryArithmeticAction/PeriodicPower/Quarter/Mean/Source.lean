import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mean.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Sampling OriginalKElementaryArithmeticAction.PeriodicPower.Lattice
open OriginalKElementaryArithmeticAction.PeriodicPower.Source OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
open scoped Topology ENNReal InnerProductSpace
open private circleValue quarter_supported from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Sampling
open private box_fourier_trig from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Resolved
open private representative_preserving from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source
open private even_positive_price from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Source
local instance periodPositive : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "C" => ConstantDual.seed
local notation "circleμ" => AddCircle.haarAddCircle (T:=(1:ℝ))
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)

private theorem box_circle_raw :
    (circleMap C : AddCircle (1:ℝ) → ℂ) =ᵐ[circleμ]
      fun x => (symmetricInterval q).indicator (fun _ => (1:ℂ)) (representative x) := by
  have raw : (C:ℝ→ℂ) =ᵐ[volume] (symmetricInterval q).indicator (fun _ => (1:ℂ)) := by
    filter_upwards [ConstantDual.seed_coeFn] with x read
    rw [read, ConstantDual.seedRaw]
    by_cases inside : x ∈ symmetricInterval q
    · rw [indicator_of_mem inside, if_pos (abs_le.mpr inside)]
    · rw [indicator_of_notMem inside, if_neg (fun h => inside (abs_le.mp h))]
  have lifted := (circleMap_raw C)
  have preserve : MeasurePreserving representative circleμ
      (volume.restrict (Ioc (-(1/2):ℝ) (1/2:ℝ))) := by
    simpa only [show (-(1/2):ℝ)+1=1/2 by norm_num] using representative_preserving
  filter_upwards [lifted, preserve.quasiMeasurePreserving.ae (ae_restrict_of_ae raw)] with x read value
  exact read.trans value

/-- The actual quarter mean is read from the same original Fourier Hilbert source. -/
theorem actual_quarter_mean_pair (c : BurnolCompletedMellinCoordinate) :
    burnolQuarterMeanCoefficient (periodicQuarter c) =
      (2:ℂ) * inner ℂ (circleMap C) (periodicPower c) := by
  rw [Constructor.mean_integral, L2.inner_def]
  congr 1
  rw [integral_congr_ae (actual_periodic_quarter_raw c)]
  have raw : (fun x : AddCircle (1:ℝ) => inner ℂ (circleMap C x) (periodicPower c x)) =ᵐ[circleμ]
      AddCircle.liftIoc 1 (-(1/2):ℝ) ((symmetricInterval q).indicator (periodicRaw c)) := by
    filter_upwards [box_circle_raw, actual_periodic_raw c] with x boxRead periodicRead
    rw [boxRead, periodicRead, RCLike.inner_apply]
    change periodicRaw c (representative x) * star
      ((symmetricInterval q).indicator (fun _ => (1:ℂ)) (representative x)) = _
    change _ = (symmetricInterval q).indicator (periodicRaw c) (representative x)
    by_cases inside : representative x ∈ symmetricInterval q
    · rw [indicator_of_mem inside, indicator_of_mem inside, star_one, mul_one]
    · rw [indicator_of_notMem inside, indicator_of_notMem inside, star_zero, mul_zero]
  rw [integral_congr_ae raw, AddCircle.integral_haarAddCircle]
  norm_num only [inv_one, one_smul]
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral]
  norm_num only [show (-(1/2):ℝ)+1=1/2 by norm_num]
  have subset : symmetricInterval q ⊆ Ioc (-(1/2):ℝ) (1/2:ℝ) := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  rw [
    intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2),
    integral_indicator (measurableSet_symmetricInterval q),
    Measure.restrict_restrict (measurableSet_symmetricInterval q),Set.inter_eq_left.mpr subset]

private theorem seed_fourier_sample (n : ℤ) : fourierSample C n = box n := by
  unfold fourierSample fourierPoint burnolRadiusTruncatedFourierRaw VectorFourier.fourierIntegral
  rw [←integral_indicator (measurableSet_symmetricInterval q)]
  apply integral_congr_ae
  filter_upwards [burnolQuarterZeroExtension_coe (intervalConstant q)] with x read
  change _ * burnolQuarterZeroExtension (intervalConstant q) x = _
  rw [read]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside, Circle.smul_def, Real.fourierChar_apply]
    simp only [smul_eq_mul, innerₗ_apply_apply, Real.inner_apply]
    congr 1
    congr 1
    push_cast
    ring
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]
    simp

theorem actual_quarter_mean_hasSum (c : BurnolCompletedMellinCoordinate) :
    HasSum (fun n:ℤ => star (box n) * powerCoefficient c n)
      ((1/2:ℂ) * burnolQuarterMeanCoefficient (periodicQuarter c)) := by
  have source := actual_periodic_reverse_pair c C (quarter_supported _)
  rw [←circleMap_original] at source
  convert! source.congr_fun (fun n => by rw [seed_fourier_sample]) using 1
  rw [actual_quarter_mean_pair]
  ring

private theorem box_sine (x:ℝ) (nonzero:x≠0) :
    box x = (Real.sin (2*Real.pi*q*x):ℂ) / ((Real.pi*x:ℝ):ℂ) := by
  rw [box_fourier_trig x nonzero]
  have angle : ProlateKernel.scale*(x:ℂ) = ((2*Real.pi*q*x:ℝ):ℂ) := by
    unfold ProlateKernel.scale ProlateKernel.frequency
    push_cast
    ring
  rw [angle,←Complex.ofReal_sin]
  push_cast
  ring

private theorem box_even (x:ℝ) : box (-x)=box x := by
  by_cases zero:x=0
  · simp only [zero,neg_zero]
  · rw [box_sine (-x) (neg_ne_zero.mpr zero),box_sine x zero]
    simp only [mul_neg, Real.sin_neg, Complex.ofReal_neg, neg_div_neg_eq]

private theorem positive_mean_term (c:BurnolCompletedMellinCoordinate) (n:ℕ) :
    star (box ((n:ℤ)+1))*powerCoefficient c ((n:ℤ)+1) =
      (1/(2*(Real.pi:ℂ))) *
        ((Real.sin (2*Real.pi*q*(n+1)):ℂ)/(n+1:ℂ)^(star c.value+1)) := by
  have nonzeroR : (n:ℝ)+1≠0 := by positivity
  have nonzeroC : (n:ℂ)+1≠0 := by exact_mod_cast nonzeroR
  rw [powerCoefficient_positive]
  norm_num only [Int.cast_add,Int.cast_natCast,Int.cast_one]
  rw [box_sine _ nonzeroR]
  simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
  rw [powerSample,Complex.cpow_add _ _ nonzeroC,Complex.cpow_one,
    Complex.cpow_neg,Complex.ofReal_mul]
  push_cast
  simp only [starRingEnd_apply]
  field_simp

/-- The complete Unit mean is generated by a genuinely convergent sine-zeta value. -/
theorem actual_quarter_mean (c:BurnolCompletedMellinCoordinate) :
    burnolQuarterMeanCoefficient (periodicQuarter c) =
      (2/(Real.pi:ℂ))*HurwitzZeta.sinZeta q (star c.value+1) := by
  let pair : ℤ→ℂ := fun n=>star (box n)*powerCoefficient c n
  have whole := actual_quarter_mean_hasSum c
  change HasSum pair _ at whole
  have even : pair.Even := by
    intro n
    dsimp only [pair]
    rw [powerCoefficient_even,Int.cast_neg,box_even]
  have zero : pair 0=0 := by simp only [pair,powerCoefficient_zero,mul_zero]
  have price := even_positive_price pair even zero whole.summable
  rw [whole.tsum_eq] at price
  have domain : 1<(star c.value+1).re := by
    simp only [add_re,star_def,conj_re,one_re]
    linarith [c.rightHalf]
  have source := HurwitzZeta.hasSum_nat_sinZeta q domain
  have shifted := (hasSum_nat_add_iff' 1).mpr source
  simp only [Finset.sum_range_one,Nat.cast_zero,mul_zero,Real.sin_zero,
    Complex.ofReal_zero,zero_div,sub_zero] at shifted
  have actual := shifted.mul_left (1/(2*(Real.pi:ℂ)))
  simp only [Nat.cast_add,Nat.cast_one] at actual
  have same : (fun n:ℕ=>pair (n+1)) =
      (fun n:ℕ=>(1/(2*(Real.pi:ℂ)))*
        ((Real.sin (2*Real.pi*q*(n+1)):ℂ)/(n+1:ℂ)^(star c.value+1))) := by
    funext n
    simpa only [pair,Int.cast_add,Int.cast_natCast,Int.cast_one] using positive_mean_term c n
  rw [same,actual.tsum_eq] at price
  linear_combination -4*price

theorem actual_zeroMean_quarter_wave (c:BurnolCompletedMellinCoordinate) :
    burnolQuarterZeroExtension (Constructor.zeroMean (periodicQuarter c):Hq) =
      quarterWave c -
        ((2/(Real.pi:ℂ))*HurwitzZeta.sinZeta q (star c.value+1)) • C := by
  rw [Constructor.zeroMean_read,actual_quarter_mean,map_sub,map_smul]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mean.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
