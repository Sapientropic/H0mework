import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ContactSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.Channels

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszFinitePairing.CoPoisson
open OriginalRieszFinitePairing.CoPoisson.Ward.Arithmetic
open OriginalRieszFinitePairing.CoPoisson.Ward.Correction

noncomputable section

/-- The counting action on the original L² seed, with its actual half-density. -/
def sourceChannel (n : ℕ) (seed : BurnolL2) : BurnolL2 :=
  (Real.sqrt (n : ℝ) : ℂ)⁻¹ • burnolMultiplicativeDilation (-Real.log (n : ℝ)) seed

def sourceChannelRaw (lower upper : ℝ) (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (n : ℂ)⁻¹ * (f (|x / (n : ℝ)|⁻¹) * burnolReciprocalStepSourceRaw lower upper (x / (n : ℝ)))

theorem sourceChannelRaw_count (lower upper x : ℝ) (f : ℝ → ℂ) (n : ℕ)
    (positive : 0 < n) (nonzero : x ≠ 0) :
    sourceChannelRaw lower upper f n x =
      if n ∈ burnolReciprocalStepChannels lower upper x then
        f ((n : ℝ) / |x|) * ((|x| : ℝ) : ℂ)⁻¹ else 0 := by
  have nPositive : (0 : ℝ) < n := by exact_mod_cast positive
  have reciprocal : |x / (n : ℝ)|⁻¹ = (n : ℝ) / |x| := by
    rw [abs_div, abs_of_pos nPositive, inv_div]
  unfold sourceChannelRaw
  rw [reciprocal, mul_left_comm]
  have count : (n : ℂ)⁻¹ * burnolReciprocalStepSourceRaw lower upper (x / (n : ℝ)) =
      if n ∈ burnolReciprocalStepChannels lower upper x then ((|x| : ℝ) : ℂ)⁻¹ else 0 := by
    simpa using! burnolReciprocalStep_source_term lower upper x nonzero (⟨n, positive⟩ : ℕ+)
  rw [count]
  split_ifs <;> simp

private theorem sqrt_exp (n : ℕ) (positive : 0 < n) :
    Real.sqrt (n : ℝ) = Real.exp (Real.log (n : ℝ) / 2) := by
  have nPositive : (0 : ℝ) < n := by exact_mod_cast positive
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos nPositive]
  congr 1
  ring

theorem sourceChannel_coeFn (n : ℕ) (positive : 0 < n) (seed : BurnolL2) :
    (sourceChannel n seed : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => (n : ℂ)⁻¹ * seed (x / (n : ℝ)) := by
  have nPositive : (0 : ℝ) < n := by exact_mod_cast positive
  have amplitude : (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-Real.log (n : ℝ) / 2) =
      (n : ℝ)⁻¹ := by
    rw [sqrt_exp n positive, ← Real.exp_neg, ← Real.exp_add,
      show -(Real.log (n : ℝ) / 2) + -Real.log (n : ℝ) / 2 = -Real.log (n : ℝ) by ring,
      Real.exp_neg, Real.exp_log nPositive]
  filter_upwards [Lp.coeFn_smul (Real.sqrt (n : ℝ) : ℂ)⁻¹
    (burnolMultiplicativeDilation (-Real.log (n : ℝ)) seed),
    burnolMultiplicativeDilation_coeFn (-Real.log (n : ℝ)) seed] with x smulAt dilationAt
  change ((Real.sqrt (n : ℝ) : ℂ)⁻¹ •
    burnolMultiplicativeDilation (-Real.log (n : ℝ)) seed : BurnolL2) x = _
  rw [smulAt]
  change (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
    burnolMultiplicativeDilation (-Real.log (n : ℝ)) seed x = _
  rw [dilationAt]
  unfold burnolL2RawNormalizedDilation
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, amplitude,
    Complex.ofReal_inv, Complex.ofReal_natCast, Real.exp_neg, Real.exp_log nPositive]
  simp only [div_eq_mul_inv, mul_comm]

theorem sourceChannel_pairing (n : ℕ) (seed test : BurnolL2) :
    inner ℂ (sourceChannel n seed) test =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
        inner ℂ seed (burnolMultiplicativeDilation (Real.log (n : ℝ)) test) := by
  unfold sourceChannel
  rw [inner_smul_left]
  have flipped := (burnolMultiplicativeDilation (-Real.log (n : ℝ))).inner_map_eq_flip seed test
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at flipped
  rw [flipped]
  simp

theorem sourceChannel_pairing_right (n : ℕ) (seed test : BurnolL2) :
    inner ℂ test (sourceChannel n seed) =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
        inner ℂ (burnolMultiplicativeDilation (Real.log (n : ℝ)) test) seed := by
  have actual := congrArg (starRingEnd ℂ) (sourceChannel_pairing n seed test)
  simpa only [inner_conj_symm, map_mul, map_inv₀, Complex.conj_ofReal] using actual

theorem sourceChannel_fourier (n : ℕ) (seed : BurnolL2) :
    fourierL2 (sourceChannel n seed) = (Real.sqrt (n : ℝ) : ℂ)⁻¹ •
      burnolMultiplicativeDilation (Real.log (n : ℝ)) (fourierL2 seed) := by
  simp only [sourceChannel, map_smul, fourierL2_burnolMultiplicativeDilation, neg_neg]

private theorem sourceChannel_raw_pairing (n : ℕ) (positive : 0 < n)
    (seed : BurnolL2) (raw : ℝ → ℂ)
    (represents : ∀ test : BurnolL2, inner ℂ test seed =
      ∫ x : ℝ, inner ℂ (test x) (raw x)) (test : BurnolL2) :
    inner ℂ test (sourceChannel n seed) =
      ∫ x : ℝ, inner ℂ (test x) ((n : ℂ)⁻¹ * raw (x / (n : ℝ))) := by
  have nPositive : (0 : ℝ) < n := by exact_mod_cast positive
  have rootNonzero : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr nPositive).ne'
  have integralRead : (∫ x : ℝ, inner ℂ
      (burnolMultiplicativeDilation (Real.log (n : ℝ)) test x) (raw x)) =
        (Real.sqrt (n : ℝ) : ℂ) *
          ∫ x : ℝ, inner ℂ (test ((n : ℝ) * x)) (raw x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [burnolMultiplicativeDilation_coeFn (Real.log (n : ℝ)) test] with x action
    rw [action]
    unfold burnolL2RawNormalizedDilation
    rw [Real.exp_log nPositive, ← sqrt_exp n positive]
    change inner ℂ ((Real.sqrt (n : ℝ) : ℂ) • test ((n : ℝ) * x)) (raw x) = _
    rw [inner_smul_left]
    simp
  have rawScaled : (∫ x : ℝ, inner ℂ (test x) ((n : ℂ)⁻¹ * raw (x / (n : ℝ)))) =
      (n : ℂ)⁻¹ * ∫ x : ℝ, inner ℂ (test x) (raw (x / (n : ℝ))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    exact inner_smul_right (test x) (raw (x / (n : ℝ))) ((n : ℂ)⁻¹)
  have changeVariable := Measure.integral_comp_div
    (fun x : ℝ => inner ℂ (test ((n : ℝ) * x)) (raw x)) (n : ℝ)
  have multiplier : (∫ x : ℝ, inner ℂ (test x) (raw (x / (n : ℝ)))) =
      (n : ℂ) * ∫ x : ℝ, inner ℂ (test ((n : ℝ) * x)) (raw x) := by
    simpa only [mul_div_cancel₀ _ nPositive.ne', abs_of_pos nPositive,
      Complex.real_smul, Complex.ofReal_natCast] using changeVariable
  rw [sourceChannel_pairing_right, represents, integralRead, rawScaled, multiplier,
    inv_mul_cancel_left₀ rootNonzero, inv_mul_cancel_left₀ (by exact_mod_cast positive.ne' : (n : ℂ) ≠ 0)]

/-- The original weighted programme, transported by its counting action, has
the exact raw n-channel on the whole real axis. -/
theorem weighted_sourceChannel_pairing (lower upper : ℝ) (f f' : ℝ → ℂ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f')
    (n : ℕ) (positive : 0 < n) (test : BurnolL2) :
    inner ℂ test (sourceChannel n (burnolWeightedReciprocalStepSource lower upper f f')) =
      ∫ x : ℝ, inner ℂ (test x) (sourceChannelRaw lower upper f n x) := by
  exact sourceChannel_raw_pairing n positive _ _
    (burnolWeightedReciprocalStepSource_pairing lower upper f f' lowerPositive ordered
      derivative regular measured) test

theorem weighted_sourceChannel_pairing_left (lower upper : ℝ) (f f' : ℝ → ℂ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f')
    (n : ℕ) (positive : 0 < n) (test : BurnolL2) :
    inner ℂ (sourceChannel n (burnolWeightedReciprocalStepSource lower upper f f')) test =
      ∫ x : ℝ, inner ℂ (sourceChannelRaw lower upper f n x) (test x) := by
  have actual := congrArg (starRingEnd ℂ)
    (weighted_sourceChannel_pairing lower upper f f' lowerPositive ordered
      derivative regular measured n positive test)
  rw [inner_conj_symm, ← integral_conj] at actual
  simpa only [inner_conj_symm] using actual

/-- The entire higher-counting source is retained as its actual finite channel
family at each x, together with the original programme mean. -/
theorem higherCountingRaw_channels (lower upper x : ℝ) (f : ℝ → ℂ)
    (lowerPositive : 0 < lower) (nonzero : x ≠ 0) :
    higherCountingRaw lower upper f x =
      (∑ n ∈ (burnolReciprocalStepChannels lower upper x).erase 1,
        sourceChannelRaw lower upper f n x) - ∫ u : ℝ in Ioc lower upper, f u := by
  classical
  unfold higherCountingRaw
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro n member
  have actual := Finset.mem_of_mem_erase member
  have nPositive : 0 < n := lt_of_lt_of_le
    (Nat.ceil_pos.mpr (mul_pos lowerPositive (abs_pos.mpr nonzero)))
    (Finset.mem_Ico.mp actual).1
  rw [sourceChannelRaw_count lower upper x f n nPositive nonzero, if_pos actual]

theorem position_sourceChannel_read (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (n : ℕ) (positive : 0 < n) :
    (∫ x : ℝ, star (sourceChannelRaw (bandLower shift) 4
        (positionWeight coordinate shift) n x) * burnolRieszStateRaw coordinate x) =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ * inner ℂ (positionSeed coordinate shift)
        (burnolMultiplicativeDilation (Real.log (n : ℝ))
          (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := by
  rw [← sourceChannel_pairing]
  change _ = inner ℂ (sourceChannel n
    (burnolWeightedReciprocalStepSource _ _ _ _)) _
  rw [weighted_sourceChannel_pairing_left _ _ _ _ (bandLower_pos shift)
    (bandLower_le_four shift nonnegative)
    (fun u inside => positionWeight_hasDerivAt coordinate shift u
      ((bandLower_pos shift).trans_le inside.1))
    ((positionWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) (measurable_deriv _)
    n positive]
  apply integral_congr_ae
  filter_upwards [burnolRieszState_ae_raw coordinate] with x actual
  rw [actual]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

theorem fourier_sourceChannel_read (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (n : ℕ) (positive : 0 < n) :
    (∫ x : ℝ, star (sourceChannelRaw (bandLower shift) 4
        (fourierWeight coordinate shift) n x) * burnolRieszFourierRaw coordinate x) =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ * inner ℂ (fourierSeed coordinate shift)
        (burnolMultiplicativeDilation (Real.log (n : ℝ))
          (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))) := by
  rw [← sourceChannel_pairing]
  change _ = inner ℂ (sourceChannel n
    (burnolWeightedReciprocalStepSource _ _ _ _)) _
  rw [weighted_sourceChannel_pairing_left _ _ _ _ (bandLower_pos shift)
    (bandLower_le_four shift nonnegative)
    (fun u inside => fourierWeight_hasDerivAt coordinate shift u
      ((bandLower_pos shift).trans_le inside.1))
    ((fourierWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) (measurable_deriv _)
    n positive]
  apply integral_congr_ae
  filter_upwards [burnolRieszFourier_ae_raw coordinate] with x actual
  rw [actual]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.Channels
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
