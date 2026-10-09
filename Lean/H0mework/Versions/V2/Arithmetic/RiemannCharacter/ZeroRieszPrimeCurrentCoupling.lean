import H0mework.Versions.V2.Arithmetic.RiemannCharacter.ZeroRieszCurrentCoupling

/-!
# Prime-scale Riesz-current coupling

Evaluating the actual Riesz dilation at the squared row-prime scale removes
the half-parameter and recovers the integral group-ring prime character.
The selected/reversal difference is therefore the exact prime coupling
residual detected by the existing q-rich full row.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace Character
namespace GlobalCoPoissonCurrent

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open SourceGeneratedIntegralCharacterGroupRing
open IntegralCharacterGroupRing
open ClozelGeneralizedDual

noncomputable section

theorem positive_square_cpow_neg_half
    (scale : ℝ) (positive : 0 < scale) (coordinate : ℂ) :
    ((scale ^ 2 : ℝ) : ℂ) ^ (-(coordinate / 2)) =
      (scale : ℂ) ^ (-coordinate) := by
  rw [pow_two, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg positive.le positive.le,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
  congr 2
  ring

def rowPrimeSquareScale {stage : Nat}
    (row : FactorRow seedOccurrence.root stage) : ℝ :=
  (rowPrime row : ℝ) ^ 2

theorem rowPrimeSquareScale_pos {stage : Nat}
    (row : FactorRow seedOccurrence.root stage) :
    0 < rowPrimeSquareScale row := by
  unfold rowPrimeSquareScale
  rw [pow_two]
  exact mul_pos
    (by exact_mod_cast (rowPrime row).2.pos)
    (by exact_mod_cast (rowPrime row).2.pos)

def sourceSelectedPrimeNormalizedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ZeroOwnedCharacterMuntzCokernelPayload observation nontrivial)
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) : ℂ :=
  selectedNormalizedDilationTrace observation nontrivial
    source
    (rowPrimeSquareScale row) (rowPrimeSquareScale_pos row)

def sourceReversalPrimeNormalizedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ZeroOwnedCharacterMuntzCokernelPayload observation nontrivial)
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) : ℂ :=
  reversalNormalizedDilationTrace observation nontrivial
    source
    (rowPrimeSquareScale row) (rowPrimeSquareScale_pos row)

def selectedPrimeNormalizedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) : ℂ :=
  sourceSelectedPrimeNormalizedDilationTrace observation nontrivial
    (zeroOwnedCharacterMuntzCokernelOccurrence
      observation nontrivial).root row

def reversalPrimeNormalizedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) : ℂ :=
  sourceReversalPrimeNormalizedDilationTrace observation nontrivial
    (zeroOwnedCharacterMuntzCokernelOccurrence
      observation nontrivial).root row

theorem selectedPrimeNormalizedDilationTrace_eq_groupRingEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) :
    selectedPrimeNormalizedDilationTrace observation nontrivial row =
      (zeroOwnedIntegralCharacterOccurrence observation).root.2.1
        (delta (rowPrimeScaleUnit row)) := by
  unfold selectedPrimeNormalizedDilationTrace
    sourceSelectedPrimeNormalizedDilationTrace
  rw [occurrence_selectedNormalizedDilationTrace_eq_character]
  unfold rowPrimeScaleUnit
  rw [selected_prime_basis_readback]
  unfold rowPrimeSquareScale selectedCoPoissonMuntzParameter
    installedPrimeEigenvalue
  exact positive_square_cpow_neg_half (rowPrime row : ℝ)
    (by exact_mod_cast (rowPrime row).2.pos) observation.coordinate

theorem reversalPrimeNormalizedDilationTrace_eq_groupRingEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) :
    reversalPrimeNormalizedDilationTrace observation nontrivial row =
      (zeroOwnedIntegralCharacterOccurrence observation).root.2.2
        (delta (rowPrimeScaleUnit row)) := by
  unfold reversalPrimeNormalizedDilationTrace
    sourceReversalPrimeNormalizedDilationTrace
  rw [occurrence_reversalNormalizedDilationTrace_eq_character]
  unfold rowPrimeScaleUnit
  rw [reversal_prime_basis_readback]
  unfold rowPrimeSquareScale reversalCoPoissonMuntzParameter
    installedPrimeEigenvalue
  exact positive_square_cpow_neg_half (rowPrime row : ℝ)
    (by exact_mod_cast (rowPrime row).2.pos)
    (coordinateReversal observation.coordinate)

/-- The arithmetic current is the retained source.2 Riesz flux at the
squared prime scale. -/
def primeRieszFluxResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) : ℂ :=
  selectedPrimeNormalizedDilationTrace observation nontrivial row -
    reversalPrimeNormalizedDilationTrace observation nontrivial row

theorem groupRingPrimeCurrent_eq_primeRieszFluxResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) :
    groupRingPrimeCurrent observation row =
      primeRieszFluxResidual observation nontrivial row := by
  unfold groupRingPrimeCurrent primeRieszFluxResidual
  rw [selectedPrimeNormalizedDilationTrace_eq_groupRingEvaluation,
    reversalPrimeNormalizedDilationTrace_eq_groupRingEvaluation]

theorem primeRieszFluxResidual_fullRow_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    QRich.pointFullRowCycleCReadback
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage row
        (zeroIntegralCharacterPointFullRowCycle observation stage
          (delta (rowPrimeScaleUnit row))) =
      -(quotientCoefficient row : ℂ) *
        primeRieszFluxResidual observation nontrivial row := by
  rw [groupRingPrimeCurrent_fullRow_readback,
    groupRingPrimeCurrent_eq_primeRieszFluxResidual]

/-- The existing q-rich full row is a faithful detector of the newly exposed
Riesz-current residual. -/
theorem primeRieszFluxResidual_eq_zero_iff_fullRowReadback_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    QRich.pointFullRowCycleCReadback
          (mathlibZeroPoint observation.coordinate observation.mathlibZero)
          stage row
          (zeroIntegralCharacterPointFullRowCycle observation stage
            (delta (rowPrimeScaleUnit row))) = 0 ↔
      primeRieszFluxResidual observation nontrivial row = 0 := by
  rw [groupRingPrimeCurrent_eq_zero_iff_fullRowReadback_eq_zero,
    groupRingPrimeCurrent_eq_primeRieszFluxResidual]

end

end GlobalCoPoissonCurrent
end Character
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
