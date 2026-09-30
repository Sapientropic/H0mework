import H0mework.Versions.Y.Arithmetic.RiemannDivision.GeneratedRiemannXiZeroLocalization
import H0mework.Versions.Y.Arithmetic.MuntzAction.CoPoissonMuntzGraphCokernelDilationAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open ClozelGeneralizedDual

noncomputable section

/-- The modified-WeakFE coordinate with exactly the selected Xi zero removed
at its full analytic multiplicity. -/
def generatedModifiedWeakFEZeroLocalizedSpectrum
    (owner : GlobalGermOwner) (coordinate value : ℂ) : ℂ :=
  generatedCompletedRiemannZeta₀ owner value *
    generatedRiemannXiZeroLocalization owner coordinate value

theorem generatedCompletedRiemannZeta₀_ne_zero_at_observation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedCompletedRiemannZeta₀ owner observation.coordinate ≠ 0 := by
  have normalForm := generatedCompletedRiemannZeta_pole_normal_form
    owner observation.coordinate
  rw [observation.completed_eq_zero_of_nontrivial nontrivial] at normalForm
  have corrected : generatedCompletedRiemannZeta₀ owner observation.coordinate =
      1 / observation.coordinate + 1 / (1 - observation.coordinate) := by
    linear_combination -normalForm
  rw [corrected]
  have coordinateNe := observation.coordinate_ne_zero
  have oneSubNe : 1 - observation.coordinate ≠ 0 := by
    apply sub_ne_zero.mpr
    intro coordinateOne
    have below := observation.coordinate_re_lt_one
    rw [← coordinateOne] at below
    norm_num at below
  intro sumZero
  have multiplied := congrArg
    (fun value : ℂ => value *
      (observation.coordinate * (1 - observation.coordinate))) sumZero
  field_simp [coordinateNe, oneSubNe] at multiplied
  norm_num at multiplied

/-- Removing the full Xi zero leaves a genuinely occupied coordinate at the
selected spectral event. -/
theorem generatedModifiedWeakFEZeroLocalizedSpectrum_at_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedModifiedWeakFEZeroLocalizedSpectrum owner
      observation.coordinate observation.coordinate ≠ 0 := by
  unfold generatedModifiedWeakFEZeroLocalizedSpectrum
  exact mul_ne_zero
    (generatedCompletedRiemannZeta₀_ne_zero_at_observation
      observation nontrivial)
    (generatedRiemannXiZeroLocalization_at_ne_zero
      owner observation.coordinate)

def generatedRiemannXiDilationCharacter
    (coordinate : ℂ) (scale : ℝ) : ℂ :=
  quarterDilationCharacter (coordinate / 2) scale

def generatedRiemannXiDilationCharacterSlope
    (coordinate : ℂ) (scale : ℝ) : ℂ → ℂ :=
  dslope (fun value => generatedRiemannXiDilationCharacter value scale)
    coordinate

theorem generatedRiemannXiDilationCharacter_sub_factorization
    (coordinate value : ℂ) (scale : ℝ) :
    generatedRiemannXiDilationCharacter value scale -
        generatedRiemannXiDilationCharacter coordinate scale =
      (value - coordinate) *
        generatedRiemannXiDilationCharacterSlope coordinate scale value := by
  simpa [generatedRiemannXiDilationCharacterSlope, smul_eq_mul] using
    (sub_smul_dslope
      (fun point : ℂ => generatedRiemannXiDilationCharacter point scale)
      coordinate value).symm

/-- Multiplicity-safe source action boundary. Repeating the same character
difference exactly the Xi zero order is forced by the source occurrence; a
single action difference is never substituted for an unknown multiplicity. -/
def generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary
    (owner : GlobalGermOwner) (coordinate : ℂ)
    (scale : ℝ) (value : ℂ) : ℂ :=
  (generatedRiemannXiDilationCharacter value scale -
      generatedRiemannXiDilationCharacter coordinate scale) ^
      generatedRiemannXiZeroOrder owner coordinate *
    generatedModifiedWeakFEZeroLocalizedSpectrum owner coordinate value

/-- Explicit spectral preimage left after the source-generated action history
has paid the selected zero's full analytic multiplicity. -/
def generatedModifiedWeakFEZeroLocalizedMultiplicityPreimage
    (owner : GlobalGermOwner) (coordinate : ℂ)
    (scale : ℝ) (value : ℂ) : ℂ :=
  generatedCompletedRiemannZeta₀ owner value *
    (generatedRiemannXiDilationCharacterSlope coordinate scale value) ^
      generatedRiemannXiZeroOrder owner coordinate

/-- Exact producer factorization: the repeated action boundary is the
source-generated entire Xi multiplier applied to a displayed preimage. -/
theorem generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary_factorization
    (owner : GlobalGermOwner) (coordinate : ℂ)
    (scale : ℝ) (value : ℂ) :
    generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary
        owner coordinate scale value =
      generatedRiemannXi owner value *
        generatedModifiedWeakFEZeroLocalizedMultiplicityPreimage
          owner coordinate scale value := by
  rw [generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary,
    generatedModifiedWeakFEZeroLocalizedMultiplicityPreimage,
    generatedModifiedWeakFEZeroLocalizedSpectrum,
    generatedRiemannXiDilationCharacter_sub_factorization,
    generatedRiemannXi_factorization owner coordinate value]
  rw [mul_pow]
  ring

theorem generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary_eq_zero
    (owner : GlobalGermOwner) (coordinate value : ℂ) (scale : ℝ)
    (valueZero : generatedRiemannXi owner value = 0) :
    generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary
        owner coordinate scale value = 0 := by
  rw [generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary_factorization,
    valueZero, zero_mul]

theorem generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary_completed_factorization
    (owner : GlobalGermOwner) (coordinate : ℂ)
    (scale : ℝ) (value : ℂ)
    (valueNeZero : value ≠ 0) (valueNeOne : value ≠ 1) :
    generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary
        owner coordinate scale value =
      (value * (1 - value) * generatedCompletedRiemannZeta owner value) *
        generatedModifiedWeakFEZeroLocalizedMultiplicityPreimage
          owner coordinate scale value := by
  rw [generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary_factorization,
    generatedRiemannXi_eq_completed owner value valueNeZero valueNeOne]

/-- Direct same-owner source contract. The selected coordinate remains
occupied, while its full action boundary carries the global Xi divisor and
therefore vanishes at every nontrivial-zero sibling. -/
theorem generatedModifiedWeakFEZeroLocalization_directConsumer
    {owner : GlobalGermOwner}
    (selected : GeneratedRiemannZeroObservationAt owner)
    (selectedNontrivial :
      ¬ ∃ n : Nat, selected.coordinate = -2 * (n + 1))
    (scale : ℝ) :
    0 < generatedRiemannXiZeroOrder owner selected.coordinate ∧
      generatedModifiedWeakFEZeroLocalizedSpectrum owner
        selected.coordinate selected.coordinate ≠ 0 ∧
      (∀ (other : GeneratedRiemannZeroObservationAt owner)
        (_otherNontrivial :
          ¬ ∃ n : Nat, other.coordinate = -2 * (n + 1)),
        generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary owner
          selected.coordinate scale other.coordinate = 0) := by
  refine ⟨generatedRiemannXiZeroOrder_pos selected selectedNontrivial,
    generatedModifiedWeakFEZeroLocalizedSpectrum_at_ne_zero
      selected selectedNontrivial, ?_⟩
  intro other otherNontrivial
  exact generatedModifiedWeakFEZeroLocalizedMultiplicityBoundary_eq_zero
    owner selected.coordinate other.coordinate scale
      (generatedRiemannXi_observation_zero other otherNontrivial)

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
