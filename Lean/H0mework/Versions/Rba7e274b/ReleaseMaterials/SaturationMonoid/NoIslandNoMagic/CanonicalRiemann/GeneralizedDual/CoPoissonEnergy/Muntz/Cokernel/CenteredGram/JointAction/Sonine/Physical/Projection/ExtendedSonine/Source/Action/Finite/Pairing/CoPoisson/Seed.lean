import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Regularity
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.Weighted

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszFinitePairing

noncomputable section

def bandLower (shift : ℝ) : ℝ := 4 * Real.exp (-shift)

theorem bandLower_pos (shift : ℝ) : 0 < bandLower shift := by
  unfold bandLower
  positivity

theorem bandLower_le_four (shift : ℝ) (nonnegative : 0 ≤ shift) : bandLower shift ≤ 4 := by
  have exponential : Real.exp (-shift) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)
  unfold bandLower
  linarith

theorem bandLower_in_annulus (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    bandLower shift ∈ Icc (1 / 4 : ℝ) 4 := by
  have exponential : 1 / 2 ≤ Real.exp (-shift) := by
    calc
      1 / 2 = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      _ ≤ Real.exp (-shift) := Real.exp_le_exp.mpr (neg_le_neg bounded)
  exact ⟨by unfold bandLower; linarith, bandLower_le_four shift nonnegative⟩

private theorem band_subset_positive (shift : ℝ) : Icc (bandLower shift) 4 ⊆ Ioi 0 :=
  fun _ inside => (bandLower_pos shift).trans_le inside.1

def positionSeed (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  burnolWeightedReciprocalStepSource (bandLower shift) 4
    (positionWeight coordinate shift) (deriv (positionWeight coordinate shift))

def fourierSeed (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  burnolWeightedReciprocalStepSource (bandLower shift) 4
    (fourierWeight coordinate shift) (deriv (fourierWeight coordinate shift))

def positionWave (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  burnolWeightedReciprocalStepWave (bandLower shift) 4
    (positionWeight coordinate shift) (deriv (positionWeight coordinate shift))

def fourierWave (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  burnolWeightedReciprocalStepWave (bandLower shift) 4
    (fourierWeight coordinate shift) (deriv (fourierWeight coordinate shift))

theorem positionWave_inPa (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    positionWave coordinate shift ∈ burnolOriginalPaInL2 :=
  burnolWeightedReciprocalStepWave_inPa _ _ _ _ (bandLower_in_annulus shift nonnegative bounded)
    (by norm_num) ((positionWeight_deriv_continuousOn coordinate shift).mono (band_subset_positive shift))

theorem fourierWave_inPa (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    fourierWave coordinate shift ∈ burnolOriginalPaInL2 :=
  burnolWeightedReciprocalStepWave_inPa _ _ _ _ (bandLower_in_annulus shift nonnegative bounded)
    (by norm_num) ((fourierWeight_deriv_continuousOn coordinate shift).mono (band_subset_positive shift))

theorem positionSeed_realizes (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (positionSeed coordinate shift) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (positionWave coordinate shift)) test :=
  burnolWeightedReciprocalStepSource_realizes _ _ _ _ (bandLower_pos shift)
    (bandLower_le_four shift nonnegative) le_rfl
    ((positionWeight_deriv_continuousOn coordinate shift).mono (band_subset_positive shift)) test

theorem fourierSeed_realizes (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (fourierSeed coordinate shift) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierWave coordinate shift)) test :=
  burnolWeightedReciprocalStepSource_realizes _ _ _ _ (bandLower_pos shift)
    (bandLower_le_four shift nonnegative) le_rfl
    ((fourierWeight_deriv_continuousOn coordinate shift).mono (band_subset_positive shift)) test

def bandRaw (shift : ℝ) (profile : ℝ → ℂ) (x : ℝ) : ℂ :=
  if (1 / 4 : ℝ) < |x| ∧ |x| ≤ (1 / 4 : ℝ) * Real.exp shift then
    -(Real.exp (-shift / 2) : ℂ) * profile (Real.exp (-shift) * |x|) else 0

private theorem reciprocal_raw_eq (shift : ℝ) (profile : ℝ → ℂ) (x : ℝ) :
    reciprocalWeight shift profile (|x|⁻¹) * burnolReciprocalStepSourceRaw (bandLower shift) 4 x =
      bandRaw shift profile x := by
  by_cases zero : x = 0
  · simp [zero, burnolReciprocalStepSourceRaw, bandRaw, (bandLower_pos shift).not_ge]
  have positive := abs_pos.mpr zero
  have radiusPositive : 0 < (1 / 4 : ℝ) * Real.exp shift := by positivity
  have lower : bandLower shift = ((1 / 4 : ℝ) * Real.exp shift)⁻¹ := by
    unfold bandLower
    rw [Real.exp_neg]
    field_simp
  have active : bandLower shift ≤ |x|⁻¹ ∧ |x|⁻¹ < 4 ↔
      (1 / 4 : ℝ) < |x| ∧ |x| ≤ (1 / 4 : ℝ) * Real.exp shift := by
    rw [lower, inv_le_inv₀ radiusPositive positive]
    have high : |x|⁻¹ < 4 ↔ (1 / 4 : ℝ) < |x| := by
      calc
        |x|⁻¹ < 4 ↔ |x|⁻¹ < (1 / 4 : ℝ)⁻¹ := by norm_num
        _ ↔ (1 / 4 : ℝ) < |x| := inv_lt_inv₀ positive (by norm_num)
    rw [high, and_comm]
  unfold burnolReciprocalStepSourceRaw bandRaw
  by_cases inside : (1 / 4 : ℝ) < |x| ∧ |x| ≤ (1 / 4 : ℝ) * Real.exp shift
  · rw [if_pos (active.mpr inside), if_pos inside]
    unfold reciprocalWeight
    rw [div_inv_eq_mul, Complex.ofReal_inv, inv_inv]
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  · rw [if_neg (fun h => inside (active.mp h)), if_neg inside, mul_zero]

theorem positionSeed_pairing (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (test : BurnolL2) :
    inner ℂ test (positionSeed coordinate shift) =
      ∫ x : ℝ, inner ℂ (test x) (bandRaw shift (positionSource coordinate) x) := by
  have actual := burnolWeightedReciprocalStepSource_pairing (bandLower shift) 4
    (positionWeight coordinate shift) (deriv (positionWeight coordinate shift))
    (bandLower_pos shift) (bandLower_le_four shift nonnegative)
    (fun t inside => positionWeight_hasDerivAt coordinate shift t (band_subset_positive shift inside))
    ((positionWeight_deriv_continuousOn coordinate shift).mono (band_subset_positive shift))
    (measurable_deriv _) test
  simpa only [positionSeed, positionWeight, reciprocal_raw_eq] using actual

theorem fourierSeed_pairing (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (test : BurnolL2) :
    inner ℂ test (fourierSeed coordinate shift) =
      ∫ x : ℝ, inner ℂ (test x) (bandRaw shift (burnolRieszSingleFourierSourceRaw coordinate) x) := by
  have actual := burnolWeightedReciprocalStepSource_pairing (bandLower shift) 4
    (fourierWeight coordinate shift) (deriv (fourierWeight coordinate shift))
    (bandLower_pos shift) (bandLower_le_four shift nonnegative)
    (fun t inside => fourierWeight_hasDerivAt coordinate shift t (band_subset_positive shift inside))
    ((fourierWeight_deriv_continuousOn coordinate shift).mono (band_subset_positive shift))
    (measurable_deriv _) test
  simpa only [fourierSeed, fourierWeight, reciprocal_raw_eq] using actual

end
end OriginalRieszFinitePairing.CoPoisson
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
