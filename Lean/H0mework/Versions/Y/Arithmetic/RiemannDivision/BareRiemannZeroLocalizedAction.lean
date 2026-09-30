import H0mework.Versions.Y.Arithmetic.RiemannDivision.ModifiedWeakFEZeroLocalizedAction

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction

noncomputable section

/-- Bare-zeta spectral state obtained by removing the selected Xi zero at
its full order and then removing the nonvanishing completion factor. -/
def generatedRiemannBareZeroLocalizedSpectrum
    (owner : GlobalGermOwner) (coordinate value : ℂ) : ℂ :=
  generatedRiemannXiZeroLocalization owner coordinate value /
    (value * (1 - value) * Gammaℝ value)

theorem generatedRiemannZeta_eq_completed_div_gamma
    (owner : GlobalGermOwner) (value : ℂ) (valueNeZero : value ≠ 0) :
    generatedRiemannZeta owner value =
      generatedCompletedRiemannZeta owner value / Gammaℝ value := by
  simp [generatedRiemannZeta, Function.update_of_ne valueNeZero]

/-- On the nontrivial strip the localized spectrum is exactly
`zeta(value) / (value - coordinate)^m`, stated without division by the
possibly vanishing action factor. -/
theorem generatedRiemannZeta_zero_factorization
    (owner : GlobalGermOwner) (coordinate value : ℂ)
    (valueNeZero : value ≠ 0) (valueNeOne : value ≠ 1)
    (gammaNeZero : Gammaℝ value ≠ 0) :
    generatedRiemannZeta owner value =
      (value - coordinate) ^ generatedRiemannXiZeroOrder owner coordinate *
        generatedRiemannBareZeroLocalizedSpectrum owner coordinate value := by
  have xiFactor := generatedRiemannXi_factorization owner coordinate value
  have xiCompleted := generatedRiemannXi_eq_completed owner value
    valueNeZero valueNeOne
  rw [generatedRiemannZeta_eq_completed_div_gamma owner value valueNeZero]
  unfold generatedRiemannBareZeroLocalizedSpectrum
  rw [xiCompleted] at xiFactor
  field_simp [valueNeZero, sub_ne_zero.mpr valueNeOne.symm, gammaNeZero]
    at xiFactor ⊢
  linear_combination xiFactor

/-- The full-order quotient remains occupied at the selected nontrivial
zero; no simple-zero premise is used. -/
theorem generatedRiemannBareZeroLocalizedSpectrum_at_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedRiemannBareZeroLocalizedSpectrum owner
      observation.coordinate observation.coordinate ≠ 0 := by
  unfold generatedRiemannBareZeroLocalizedSpectrum
  apply div_ne_zero
  · exact generatedRiemannXiZeroLocalization_at_ne_zero
      owner observation.coordinate
  · apply mul_ne_zero
    · exact mul_ne_zero observation.coordinate_ne_zero
        (sub_ne_zero.mpr (by
          intro coordinateOne
          have below := observation.coordinate_re_lt_one
          rw [← coordinateOne] at below
          norm_num at below))
    · exact observation.gammaReal_ne_zero_of_nontrivial nontrivial

def generatedRiemannBareZeroLocalizedMultiplicityBoundary
    (owner : GlobalGermOwner) (coordinate : ℂ)
    (scale : ℝ) (value : ℂ) : ℂ :=
  (generatedRiemannXiDilationCharacter value scale -
      generatedRiemannXiDilationCharacter coordinate scale) ^
      generatedRiemannXiZeroOrder owner coordinate *
    generatedRiemannBareZeroLocalizedSpectrum owner coordinate value

/-- Exact source factorization. After the zero order is paid by the action,
only one bare zeta factor and the displayed character-slope source remain. -/
theorem generatedRiemannBareZeroLocalizedMultiplicityBoundary_factorization
    (owner : GlobalGermOwner) (coordinate value : ℂ) (scale : ℝ)
    (valueNeZero : value ≠ 0) (valueNeOne : value ≠ 1)
    (gammaNeZero : Gammaℝ value ≠ 0) :
    generatedRiemannBareZeroLocalizedMultiplicityBoundary
        owner coordinate scale value =
      generatedRiemannZeta owner value *
        (generatedRiemannXiDilationCharacterSlope coordinate scale value) ^
          generatedRiemannXiZeroOrder owner coordinate := by
  rw [generatedRiemannBareZeroLocalizedMultiplicityBoundary,
    generatedRiemannXiDilationCharacter_sub_factorization,
    mul_pow,
    generatedRiemannZeta_zero_factorization owner coordinate value
      valueNeZero valueNeOne gammaNeZero]
  ring

theorem generatedRiemannBareZeroLocalization_directConsumer
    {owner : GlobalGermOwner}
    (selected : GeneratedRiemannZeroObservationAt owner)
    (selectedNontrivial :
      ¬ ∃ n : Nat, selected.coordinate = -2 * (n + 1))
    (scale : ℝ) :
    generatedRiemannBareZeroLocalizedSpectrum owner
        selected.coordinate selected.coordinate ≠ 0 ∧
      generatedRiemannBareZeroLocalizedMultiplicityBoundary owner
        selected.coordinate scale selected.coordinate = 0 := by
  refine ⟨generatedRiemannBareZeroLocalizedSpectrum_at_ne_zero
    selected selectedNontrivial, ?_⟩
  have orderNe :
      generatedRiemannXiZeroOrder owner selected.coordinate ≠ 0 :=
    Nat.ne_of_gt
      (generatedRiemannXiZeroOrder_pos selected selectedNontrivial)
  unfold generatedRiemannBareZeroLocalizedMultiplicityBoundary
  rw [sub_self, zero_pow orderNe, zero_mul]

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
