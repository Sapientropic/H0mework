import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.HMellinPair
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReturnConstantTail
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantMean

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.HKernelRead

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "H" => ConstantDual.value
local notation "Hraw" => ConstantDual.sawtoothRaw
local notation "E" => burnolQuarterZeroExtension
local notation "K" => burnolCompletedMellinRieszVector

private def powerH (s : ℂ) (x : ℝ) : ℂ := ((|x| : ℝ) : ℂ) ^ (-s) * Hraw x

private theorem powerH_even (s : ℂ) (x : ℝ) : powerH s (-x) = powerH s x := by
  simp only [powerH, ConstantDual.sawtoothRaw, abs_neg]

private theorem powerH_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (powerH (star coordinate.value)) := by
  exact HMellin.whole_integrable (star coordinate.value)
    (by simp only [star_def, conj_re]; linarith [coordinate.rightHalf])
    (by simpa only [star_def, conj_re] using coordinate.belowOne)

private theorem positive_tail (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in Ioi q, powerH (star coordinate.value) x) =
      -(q : ℂ) ^ (1 - star coordinate.value) / star coordinate.value := by
  have decay : (-star coordinate.value - 1).re < -1 := by
    simp only [sub_re, neg_re, star_def, conj_re, one_re]
    linarith [coordinate.rightHalf]
  have source : (fun x : ℝ => powerH (star coordinate.value) x) =ᵐ[volume.restrict (Ioi q)]
      fun x => -(q : ℂ) * (x : ℂ) ^ (-star coordinate.value - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have positive : 0 < x := lt_trans (by norm_num : (0 : ℝ) < q) hx
    have nonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
    rw [powerH, ConstantDual.sawtooth_tail x (by simpa only [mem_Ioi, abs_of_pos positive] using hx),
      abs_of_pos positive, Complex.ofReal_div, Complex.cpow_sub _ _ nonzero, Complex.cpow_one]
    ring
  rw [integral_congr_ae source, integral_const_mul,
    integral_Ioi_cpow_of_lt decay (by norm_num : (0 : ℝ) < q), sub_add_cancel,
    neg_div_neg_eq]
  have power : (q : ℂ) ^ (1 - star coordinate.value) =
      (q : ℂ) * (q : ℂ) ^ (-star coordinate.value) := by
    rw [show 1 - star coordinate.value = 1 + (-star coordinate.value) by ring,
      Complex.cpow_add _ _ (by norm_num : (q : ℂ) ≠ 0), Complex.cpow_one]
  rw [power]
  ring

/-- The full Mellin zero pays the inner power/H integral after the genuine exterior tail is retained. -/
private theorem window_power (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    (∫ x : ℝ in symmetricInterval q, powerH (star coordinate.value) x) =
      (2 : ℂ) * (q : ℂ) ^ (1 - star coordinate.value) / star coordinate.value := by
  have integrable := powerH_integrable coordinate
  have negative : (∫ x : ℝ in Iio (-q), powerH (star coordinate.value) x) =
      -(q : ℂ) ^ (1 - star coordinate.value) / star coordinate.value := by
    rw [← integral_Iic_eq_integral_Iio,
      setIntegral_congr_fun measurableSet_Iic (fun x _ => (powerH_even (star coordinate.value) x).symm),
      integral_comp_neg_Iic, neg_neg, positive_tail]
  have outside : (∫ x : ℝ in (symmetricInterval q)ᶜ, powerH (star coordinate.value) x) =
      -(2 : ℂ) * (q : ℂ) ^ (1 - star coordinate.value) / star coordinate.value := by
    have region : (symmetricInterval q)ᶜ = Iio (-q) ∪ Ioi q := by
      ext x
      simp only [mem_compl_iff, symmetricInterval, mem_Icc, not_and_or, not_le,
        mem_union, mem_Iio, mem_Ioi]
    rw [region, setIntegral_union
      (Iio_disjoint_Ioi_of_le (by norm_num : -q ≤ q)) measurableSet_Ioi
      integrable.integrableOn integrable.integrableOn, negative, positive_tail]
    ring
  have full := integral_add_compl (measurableSet_symmetricInterval q) integrable
  rw [outside, show (∫ x : ℝ, powerH (star coordinate.value) x) = 0 from HMellin.whole_zero coordinate zero] at full
  linear_combination full

private theorem H_real (x : ℝ) : star (Hraw x) = Hraw x := by
  simp only [ConstantDual.sawtoothRaw, star_neg, star_def, Complex.conj_ofReal]

private theorem window_pair_raw (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    (fun x : ℝ => inner ℂ (burnolQuarterRestriction H x) (state x)) =ᵐ[μq]
      fun x => Hraw x * raw x := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) H,
    ae_restrict_of_ae ConstantDual.value_coeFn, represents] with x restricted value source
  change burnolQuarterRestriction H x = H x at restricted
  rw [restricted, value, source, RCLike.inner_apply]
  simp only [starRingEnd_apply, H_real]
  ring

private theorem window_pair (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    inner ℂ H (E state) = ∫ x : ℝ in symmetricInterval q, Hraw x * raw x := by
  have adjoint := ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction H state
  change inner ℂ H (E state) = _ at adjoint
  rw [adjoint, L2.inner_def, integral_congr_ae (window_pair_raw state raw represents)]

private theorem window_integrable (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    IntegrableOn (fun x : ℝ => Hraw x * raw x) (symmetricInterval q) :=
  (L2.integrable_inner (𝕜 := ℂ) (burnolQuarterRestriction H) state).congr
    (window_pair_raw state raw represents)

private theorem return_abs (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszReturnRaw coordinate |x| = burnolRieszReturnRaw coordinate x := by
  rcases le_or_gt 0 x with positive | negative
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg negative, return_raw_even]

/-- This split is within the true L¹ position source; its singular summand is never assigned an L² state. -/
private theorem position_pair (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ, Hraw x * PositionCounting.seedRaw coordinate x) =
      (1 / 2 : ℂ) * (∫ x : ℝ in symmetricInterval q, powerH (star coordinate.value) x) -
        GapEuler.gapMean q coordinate * inner ℂ H ConstantDual.seed -
        inner ℂ H (E (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) := by
  have constantRead := window_pair (intervalConstant q) (fun _ => (1 : ℂ)) (intervalConstant_coeFn q)
  have returnRead := window_pair (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
    (burnolRieszReturnRaw coordinate) (Constructor.returnState_read coordinate)
  have constantInt : IntegrableOn Hraw (symmetricInterval q) := by
    simpa only [mul_one] using window_integrable (intervalConstant q) (fun _ => (1 : ℂ))
      (intervalConstant_coeFn q)
  have returnInt := window_integrable (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
    (burnolRieszReturnRaw coordinate) (Constructor.returnState_read coordinate)
  have powerInt : IntegrableOn (fun x : ℝ => (1 / 2 : ℂ) * powerH (star coordinate.value) x)
      (symmetricInterval q) := (powerH_integrable coordinate).integrableOn.const_mul (1 / 2 : ℂ)
  have meanInt := constantInt.const_mul (GapEuler.gapMean q coordinate)
  have raw : (fun x : ℝ => Hraw x * PositionCounting.seedRaw coordinate x) =
      (symmetricInterval q).indicator (fun x : ℝ => (1 / 2 : ℂ) * powerH (star coordinate.value) x -
        GapEuler.gapMean q coordinate * Hraw x - Hraw x * burnolRieszReturnRaw coordinate x) := by
    funext x
    by_cases inside : x ∈ symmetricInterval q
    · rw [PositionCounting.seedRaw, if_pos (abs_le.mpr inside), indicator_of_mem inside,
        positionSource, return_abs]
      unfold powerH
      ring
    · rw [PositionCounting.seedRaw, if_neg (fun h => inside (abs_le.mp h)), indicator_of_notMem inside, mul_zero]
  rw [raw, integral_indicator (measurableSet_symmetricInterval q)]
  have split := integral_sub (powerInt.sub meanInt) returnInt
  simp only [Pi.sub_apply] at split
  rw [split, integral_sub powerInt meanInt, integral_const_mul, integral_const_mul,
    ← returnRead]
  simp only [mul_one] at constantRead
  rw [← constantRead]
  rfl

private theorem kernel_pair_left (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    inner ℂ H (K coordinate : BurnolL2) =
      -(q : ℂ) ^ (1 - star coordinate.value) / star coordinate.value +
        positionMean coordinate * inner ℂ H ConstantDual.seed -
        inner ℂ (fourierL2 ReturnConstantTail.outside)
          (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) := by
  have mean := congrArg (star : ℂ → ℂ) (ReturnConstantTail.original_mean_pair coordinate)
  simp only [star_def, map_sub, map_add, map_mul, Complex.conj_conj, inner_conj_symm] at mean
  have even : reflectL2 (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) =
      E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) := by
    change reflectL2 (burnolRadiusZeroExtension q (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) = _
    rw [burnolRadiusZeroExtension_reflect, burnolRieszSingleFourierSource_reflection_fixed]
    rfl
  have fourier := fourierL2.inner_map_map H
    (fourierL2 (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))
  rw [fourierL2_fourierL2, even] at fourier
  rw [HMellin.original_kernel_pair coordinate zero, position_pair, window_power coordinate zero, fourier]
  linear_combination mean

/-- The original zero pays the homogeneous contact. Exactly one fixed first-program exterior read remains. -/
theorem original_pair (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    inner ℂ (K coordinate : BurnolL2) H =
      -(q : ℂ) ^ (1 - coordinate.value) / coordinate.value +
        (1 / 2 : ℂ) * star (positionMean coordinate) * (Real.eulerMascheroniConstant - 1) -
        inner ℂ (E (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))
          (fourierL2 ReturnConstantTail.outside) := by
  have actual := congrArg (star : ℂ → ℂ) (kernel_pair_left coordinate zero)
  have power : star ((q : ℂ) ^ (1 - star coordinate.value)) = (q : ℂ) ^ (1 - coordinate.value) := by
    have source := Complex.conj_cpow (q : ℂ) (1 - coordinate.value) (by
      rw [Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ q)]
      exact Real.pi_ne_zero.symm)
    simpa only [Complex.conj_ofReal, map_sub, map_one, star_def] using source.symm
  rw [star_sub, star_add, star_div₀, star_neg, power, star_star, star_mul] at actual
  simp only [star_def, inner_conj_symm] at actual
  rw [ConstantMean.original_pair] at actual
  exact actual.trans (by simp only [star_def]; ring)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.HKernelRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
