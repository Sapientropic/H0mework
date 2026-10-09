import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.PairingRaw
import H0mework.Versions.V2.Arithmetic.RieszSynthesis.Evaluator

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Classical Complex Filter MeasureTheory Set
open scoped InnerProductSpace
open OriginalRieszFiniteSource OriginalRieszFiniteColumns OriginalRieszFiniteSynthesis

noncomputable section
local notation "q" => (1 / 4 : ℝ)

def exteriorRead (column : BurnolL2) (raw : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ in (symmetricInterval q)ᶜ, star (column x) * raw x

private theorem inner_split (column value : BurnolL2) (raw tail : ℝ → ℂ) (mean : ℂ)
    (regular : Integrable (column : ℝ → ℂ)) (read : (value : ℝ → ℂ) =ᵐ[volume] raw)
    (split : ∀ x : ℝ, raw x = mean + if x ∈ symmetricInterval q then 0 else tail x) :
    inner ℂ column value = mean * star (∫ x : ℝ, column x) + exteriorRead column tail := by
  have rawIntegral : Integrable (fun x : ℝ => star (column x) * raw x) := by
    apply (L2.integrable_inner (𝕜 := ℂ) column value).congr
    filter_upwards [read] with x actual
    rw [actual]
    simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]
  have conjugateRegular : Integrable (fun x : ℝ => star (column x)) :=
    (@RCLike.conjLIE ℂ _).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp regular
  have constantIntegral := conjugateRegular.const_mul mean
  have residual : (fun x : ℝ => star (column x) * raw x - mean * star (column x)) =
      (symmetricInterval q)ᶜ.indicator (fun x : ℝ => star (column x) * tail x) := by
    funext x
    rw [split x]
    by_cases inside : x ∈ symmetricInterval q
    · rw [if_pos inside, indicator_of_notMem (show x ∉ (symmetricInterval q)ᶜ from not_not_intro inside)]
      ring
    · rw [if_neg inside, indicator_of_mem (show x ∈ (symmetricInterval q)ᶜ from inside)]
      ring
  have exterior : exteriorRead column tail =
      (∫ x : ℝ, star (column x) * raw x) - ∫ x : ℝ, mean * star (column x) := by
    unfold exteriorRead
    rw [← integral_indicator (measurableSet_symmetricInterval q).compl, ← residual,
      integral_sub rawIntegral constantIntegral]
  have whole : inner ℂ column value = ∫ x : ℝ, star (column x) * raw x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [read] with x actual
    rw [actual]
    simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]
  have meanRead : (∫ x : ℝ, mean * star (column x)) = mean * star (∫ x : ℝ, column x) := by
    rw [integral_const_mul]
    simp only [Complex.star_def, integral_conj]
  rw [whole, exterior, meanRead]
  ring

/-- All four terms are computed from the same source columns and original raw source faces. -/
def annularRead (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : ℂ :=
  positionMean coordinate * star (∫ x : ℝ, positionColumn coordinate shift x) +
    fourierMean coordinate * star (∫ x : ℝ, fourierColumn coordinate shift x) +
    exteriorRead (positionColumn coordinate shift) (positionTail coordinate) +
    exteriorRead (fourierColumn coordinate shift) (fourierTail coordinate)

theorem forcing_annularRead (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    inner ℂ (forcingIntegral coordinate shift)
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) = annularRead coordinate shift := by
  have twice : fourierL2 (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) := by
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector coordinate).property.2
  have fourierRead := fourierL2.inner_map_map (fourierColumn coordinate shift)
    (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
  rw [twice] at fourierRead
  rw [forcingIntegral_columns, inner_add_left, fourierRead,
    inner_split _ _ _ _ _ (positionColumn_integrable coordinate shift)
      (burnolRieszState_ae_raw coordinate) (position_raw coordinate),
    inner_split _ _ _ _ _ (fourierColumn_integrable coordinate shift)
      (burnolRieszFourier_ae_raw coordinate) (fourier_raw coordinate)]
  unfold annularRead
  ring

theorem wholeSourceRead_annular (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (bounded : |shift| ≤ Real.log 2) :
    wholeSourceRead coordinate shift (burnolCompletedMellinRieszVector coordinate) =
      annularRead coordinate shift := by
  rw [← forcing_wholeSourceRead coordinate shift bounded]
  exact forcing_annularRead coordinate shift

theorem annularRead_keeps_defect (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (bounded : |shift| ≤ Real.log 2) :
    annularRead coordinate shift =
      firstSourceRead coordinate shift (burnolCompletedMellinRieszVector coordinate) +
        inner ℂ (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0)
          (sourceFourierDefect (burnolCompletedMellinRieszVector coordinate)) := by
  rw [← wholeSourceRead_annular coordinate shift bounded, wholeSourceRead_keeps_defect]

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
