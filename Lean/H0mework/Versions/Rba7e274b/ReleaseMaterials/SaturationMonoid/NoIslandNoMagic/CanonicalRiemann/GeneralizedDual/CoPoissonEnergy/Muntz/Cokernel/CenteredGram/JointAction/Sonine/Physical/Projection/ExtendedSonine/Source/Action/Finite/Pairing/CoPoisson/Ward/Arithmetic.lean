import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Energy.CountGap

/-! The original weighted co-Poisson programme generates its finite integer-channel
formula before pairing with any L² test. The whole-axis integral retains the
combined counting sum and its actual mean; no infinite tail is discarded. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.Arithmetic

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszFinitePairing.CoPoisson
open OriginalRieszFinitePairing.CoPoisson.Energy

noncomputable section

private theorem weighted_mean (lower upper : ℝ) (f f' : ℝ → ℂ)
    (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) :
    f upper * ((upper - lower : ℝ) : ℂ) -
      (∫ u : ℝ in Ioc lower upper, f' u * ((u - lower : ℝ) : ℂ)) =
        ∫ u : ℝ in Ioc lower upper, f u := by
  have continuous : ContinuousOn f (Icc lower upper) :=
    fun u hu => (derivative u hu).continuousAt.continuousWithinAt
  have linearContinuous : ContinuousOn (fun u : ℝ => ((u - lower : ℝ) : ℂ))
      (Icc lower upper) := by fun_prop
  have product : IntervalIntegrable (fun u : ℝ => f' u * ((u - lower : ℝ) : ℂ))
      volume lower upper := (regular.mul linearContinuous).intervalIntegrable_of_Icc ordered
  have original : IntervalIntegrable f volume lower upper :=
    continuous.intervalIntegrable_of_Icc ordered
  have total : (∫ u : ℝ in lower..upper, f' u * ((u - lower : ℝ) : ℂ) + f u) =
      f upper * ((upper - lower : ℝ) : ℂ) := by
    have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => f u * ((u - lower : ℝ) : ℂ))
      (f' := fun u : ℝ => f' u * ((u - lower : ℝ) : ℂ) + f u)
      (a := lower) (b := upper) (fun u hu => by
        have h := derivative u (by simpa only [uIcc_of_le ordered] using hu)
        simpa only [Complex.ofReal_sub, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using!
          h.mul (Complex.ofRealCLM.hasDerivAt.sub_const (lower : ℂ))) (product.add original)
    simpa using actual
  rw [intervalIntegral.integral_add product original,
    intervalIntegral.integral_of_le ordered, intervalIntegral.integral_of_le ordered] at total
  linear_combination -total

private theorem channel_integral (lower upper t : ℝ) (f f' : ℝ → ℂ)
    (inside : t ∈ Ico lower upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) :
    (∫ u : ℝ in Ioc lower upper, if t < u then f' u else 0) = f upper - f t := by
  have integrand : (fun u : ℝ => if t < u then f' u else 0) =
      (Ioi t).indicator f' := by rfl
  rw [integrand, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have intersection : Ioi t ∩ Ioc lower upper = Ioc t upper := by
    ext u
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨ht, _, hb⟩
      exact ⟨ht, hb⟩
    · rintro ⟨ht, hb⟩
      exact ⟨ht, inside.1.trans_lt ht, hb⟩
  rw [intersection, ← intervalIntegral.integral_of_le inside.2.le]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => derivative u (Icc_subset_Icc inside.1 le_rfl (by
      simpa only [uIcc_of_le inside.2.le] using hu)))
    ((regular.mono (Icc_subset_Icc inside.1 le_rfl)).intervalIntegrable_of_Icc inside.2.le)

private theorem count_wave_expansion (lower upper u x : ℝ)
    (_lowerPositive : 0 < lower) (upperBound : u ≤ upper) (nonzero : x ≠ 0) :
    burnolReciprocalStepWaveRaw lower u x =
      (∑ n ∈ burnolReciprocalStepChannels lower upper x,
        if (n : ℝ) / |x| < u then ((|x| : ℝ) : ℂ)⁻¹ else 0) - ((u - lower : ℝ) : ℂ) := by
  classical
  have absPositive := abs_pos.mpr nonzero
  have subset : burnolReciprocalStepChannels lower u x ⊆
      burnolReciprocalStepChannels lower upper x := by
    intro n hn
    simp only [burnolReciprocalStepChannels, Finset.mem_Ico] at hn ⊢
    exact ⟨hn.1, hn.2.trans_le (Nat.ceil_mono
      (mul_le_mul_of_nonneg_right upperBound absPositive.le))⟩
  have counts : (∑ n ∈ burnolReciprocalStepChannels lower upper x,
      if (n : ℝ) / |x| < u then ((|x| : ℝ) : ℂ)⁻¹ else 0) =
        ((burnolReciprocalStepChannels lower u x).card : ℂ) * ((|x| : ℝ) : ℂ)⁻¹ := by
    calc
      _ = ∑ n ∈ burnolReciprocalStepChannels lower u x,
          if (n : ℝ) / |x| < u then ((|x| : ℝ) : ℂ)⁻¹ else 0 := by
        symm
        apply Finset.sum_subset subset
        intro n hn hnot
        have lowerN := (Finset.mem_Ico.mp hn).1
        have outside : ¬ (n : ℝ) / |x| < u := by
          intro active
          apply hnot
          exact Finset.mem_Ico.mpr ⟨lowerN, Nat.lt_ceil.mpr
            ((div_lt_iff₀ absPositive).mp active)⟩
        exact if_neg outside
      _ = ∑ _n ∈ burnolReciprocalStepChannels lower u x, ((|x| : ℝ) : ℂ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro n hn
        exact if_pos ((div_lt_iff₀ absPositive).mpr
          (Nat.lt_ceil.mp (Finset.mem_Ico.mp hn).2))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  rw [counts]
  simp only [burnolReciprocalStepWaveRaw, burnolReciprocalStepWaveReal, if_neg nonzero]
  push_cast
  rw [div_eq_mul_inv]

def weightedCountingRaw (lower upper : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (∑ n ∈ burnolReciprocalStepChannels lower upper x, f ((n : ℝ) / |x|)) *
    ((|x| : ℝ) : ℂ)⁻¹ - ∫ u : ℝ in Ioc lower upper, f u

theorem weighted_count_raw (lower upper x : ℝ) (f f' : ℝ → ℂ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (nonzero : x ≠ 0)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) :
    f upper * burnolReciprocalStepWaveRaw lower upper x -
      (∫ u : ℝ in Ioc lower upper, f' u * burnolReciprocalStepWaveRaw lower u x) =
        weightedCountingRaw lower upper f x := by
  classical
  let channels := burnolReciprocalStepChannels lower upper x
  let inverse : ℂ := ((|x| : ℝ) : ℂ)⁻¹
  have absPositive := abs_pos.mpr nonzero
  have channelInside (n : ℕ) (hn : n ∈ channels) : (n : ℝ) / |x| ∈ Ico lower upper := by
    obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hn
    exact ⟨(le_div_iff₀ absPositive).mpr (Nat.ceil_le.mp hl),
      (div_lt_iff₀ absPositive).mpr (Nat.lt_ceil.mp hu)⟩
  have baseIntegrable : IntegrableOn f' (Ioc lower upper) :=
    regular.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have channelIntegrable (n : ℕ) : IntegrableOn
      (fun u : ℝ => if (n : ℝ) / |x| < u then f' u * inverse else 0) (Ioc lower upper) := by
    exact (baseIntegrable.mul_const inverse).indicator measurableSet_Ioi
  have meanIntegrable : IntegrableOn (fun u : ℝ => f' u * ((u - lower : ℝ) : ℂ))
      (Ioc lower upper) :=
    (regular.mul (show ContinuousOn (fun u : ℝ => ((u - lower : ℝ) : ℂ))
      (Icc lower upper) from by fun_prop)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have expanded : (∫ u : ℝ in Ioc lower upper, f' u * burnolReciprocalStepWaveRaw lower u x) =
      (∑ n ∈ channels, (f upper - f ((n : ℝ) / |x|)) * inverse) -
        ∫ u : ℝ in Ioc lower upper, f' u * ((u - lower : ℝ) : ℂ) := by
    have integrand : ∀ u ∈ Ioc lower upper,
        f' u * burnolReciprocalStepWaveRaw lower u x =
          (∑ n ∈ channels, if (n : ℝ) / |x| < u then f' u * inverse else 0) -
            f' u * ((u - lower : ℝ) : ℂ) := by
      intro u inside
      rw [count_wave_expansion lower upper u x lowerPositive inside.2 nonzero, mul_sub,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      simp only [mul_ite, mul_zero, inverse]
    rw [setIntegral_congr_fun measurableSet_Ioc integrand,
      integral_sub (integrable_finsetSum _ (fun n _ => channelIntegrable n))
        meanIntegrable,
      integral_finsetSum _ (fun n _ => channelIntegrable n)]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    have rewritten : (fun u : ℝ => if (n : ℝ) / |x| < u then f' u * inverse else 0) =
        fun u : ℝ => (if (n : ℝ) / |x| < u then f' u else 0) * inverse := by
      funext u
      split_ifs <;> simp
    rw [rewritten, integral_mul_const, channel_integral lower upper _ f f'
      (channelInside n hn) derivative regular]
  rw [expanded, count_wave_expansion lower upper upper x lowerPositive le_rfl nonzero]
  have head : (∑ n ∈ channels, if (n : ℝ) / |x| < upper then inverse else 0) =
      ∑ _n ∈ channels, inverse := by
    apply Finset.sum_congr rfl
    intro n hn
    exact if_pos (channelInside n hn).2
  change f upper * ((∑ n ∈ channels, if (n : ℝ) / |x| < upper then inverse else 0) -
      ((upper - lower : ℝ) : ℂ)) - _ = _
  rw [head]
  have mean := weighted_mean lower upper f f' ordered derivative regular
  unfold weightedCountingRaw
  rw [← mean]
  change f upper * ((∑ _n ∈ channels, inverse) - ((upper - lower : ℝ) : ℂ)) -
      ((∑ n ∈ channels, (f upper - f ((n : ℝ) / |x|)) * inverse) - _) =
        (∑ n ∈ channels, f ((n : ℝ) / |x|)) * inverse - _
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

private theorem step_wave_read (lower upper : ℝ) (positive : 0 < lower) (ordered : lower ≤ upper) :
    (burnolReciprocalStepNativeWave lower upper : ℝ → ℂ) =ᵐ[volume]
      burnolReciprocalStepWaveRaw lower upper := by
  rw [burnolReciprocalStepNativeWave_eq lower upper positive ordered]
  exact (burnolReciprocalStepWave_memLp lower upper positive ordered).coeFn_toLp

private theorem wave_raw_measurable (lower : ℝ) (f' : ℝ → ℂ) (measured : Measurable f') :
    Measurable (fun point : ℝ × ℝ => f' point.1 *
      burnolReciprocalStepWaveRaw lower point.1 point.2) := by
  apply (measured.comp measurable_fst).mul
  unfold burnolReciprocalStepWaveRaw burnolReciprocalStepWaveReal burnolReciprocalStepChannels
  simp only [Nat.card_Ico]
  apply Complex.measurable_ofReal.comp
  apply Measurable.ite (measurable_snd (measurableSet_singleton (0 : ℝ)))
  · fun_prop
  · fun_prop

/-- Every counting channel and the reciprocal mean are evaluated before
pairing with the original L² vector; the integral still ranges over all x. -/
theorem weighted_wave_arithmetic_pairing (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') (test : BurnolL2) :
    inner ℂ test (burnolWeightedReciprocalStepWave lower upper f f') =
      ∫ x : ℝ, inner ℂ (test x) (weightedCountingRaw lower upper f x) := by
  let family := fun u : ℝ => f' u • burnolReciprocalStepNativeWave lower u
  let raw := fun point : ℝ × ℝ => f' point.1 * burnolReciprocalStepWaveRaw lower point.1 point.2
  have familyRead : ∀ᵐ u ∂volume.restrict (Ioc lower upper),
      (family u : ℝ → ℂ) =ᵐ[volume] fun x => raw (u, x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    filter_upwards [Lp.coeFn_smul (f' u) (burnolReciprocalStepNativeWave lower u),
      step_wave_read lower u positive inside.1.le] with x smulAt waveAt
    change (f' u • burnolReciprocalStepNativeWave lower u : BurnolL2) x = _
    rw [smulAt]
    change f' u * burnolReciprocalStepNativeWave lower u x = _
    rw [waveAt]
  have actual := burnolL2Bochner_pairing_raw (volume.restrict (Ioc lower upper)) family
    (stepWave_integrable lower upper f' positive regular) raw
    (wave_raw_measurable lower f' measured) familyRead test
  have headRead : (f upper • burnolReciprocalStepNativeWave lower upper : BurnolL2) =ᵐ[volume]
      fun x : ℝ => f upper * burnolReciprocalStepWaveRaw lower upper x := by
    filter_upwards [Lp.coeFn_smul (f upper) (burnolReciprocalStepNativeWave lower upper),
      step_wave_read lower upper positive ordered] with x smulAt waveAt
    rw [smulAt]
    change f upper * burnolReciprocalStepNativeWave lower upper x = _
    rw [waveAt]
  have headIntegrable := (L2.integrable_inner (𝕜 := ℂ) test
    (f upper • burnolReciprocalStepNativeWave lower upper)).congr
      (headRead.mono (fun x hx => congrArg (inner ℂ (test x)) hx))
  have headPairing : inner ℂ test (f upper • burnolReciprocalStepNativeWave lower upper) =
      ∫ x : ℝ, inner ℂ (test x) (f upper * burnolReciprocalStepWaveRaw lower upper x) := by
    rw [L2.inner_def]
    exact integral_congr_ae (headRead.mono (fun x hx => congrArg (inner ℂ (test x)) hx))
  rw [burnolWeightedReciprocalStepWave, inner_sub_right, headPairing, actual.2,
    ← integral_sub headIntegrable actual.1]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  rw [← inner_sub_right]
  exact congrArg (inner ℂ (test x))
    (weighted_count_raw lower upper x f f' positive ordered nonzero derivative regular)

theorem position_wave_arithmetic_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) (positionWave coordinate shift) =
      ∫ x : ℝ, inner ℂ ((burnolCompletedMellinRieszVector coordinate : BurnolL2) x)
        (weightedCountingRaw (bandLower shift) 4 (positionWeight coordinate shift) x) :=
  weighted_wave_arithmetic_pairing _ _ _ _ (bandLower_pos shift)
    (bandLower_le_four shift nonnegative)
    (fun u inside => positionWeight_hasDerivAt coordinate shift u
      ((bandLower_pos shift).trans_le inside.1))
    ((positionWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) (measurable_deriv _) _

theorem fourier_wave_arithmetic_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
      (fourierWave coordinate shift) =
      ∫ x : ℝ, inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2) x)
        (weightedCountingRaw (bandLower shift) 4 (fourierWeight coordinate shift) x) :=
  weighted_wave_arithmetic_pairing _ _ _ _ (bandLower_pos shift)
    (bandLower_le_four shift nonnegative)
    (fun u inside => fourierWeight_hasDerivAt coordinate shift u
      ((bandLower_pos shift).trans_le inside.1))
    ((fourierWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) (measurable_deriv _) _

end
end OriginalRieszFinitePairing.CoPoisson.Ward.Arithmetic
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
