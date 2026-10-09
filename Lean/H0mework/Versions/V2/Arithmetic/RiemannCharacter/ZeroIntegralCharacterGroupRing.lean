import H0mework.Realization.Integral.CharacterGroupRing
import H0mework.Versions.V2.Arithmetic.RiemannCharacter.ZeroMultiplicativeCharacterReadouts

/-!
# Same-zero integral character group ring

The zero-owned positive-real character pair generates two evaluations of one
integral group ring `ℤ[(ℝ≥0)ˣ]`.  Its basis vector at a prime reads the already
installed Euler eigenvalue, while its basis vector at the corresponding
square-root scale reads the actual positive Mellin dilation.  Thus the finite
and Archimedean roles are literal sibling evaluations of one integral
carrier, not scalar shadows joined by a comparator.

The carrier also retains the canonical nonzero `δ₁ mod p` coordinate for
every rational prime.  No finite Euler kernel, zero conclusion, separator,
fixedness, or determinant premise enters this face.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace Character
namespace IntegralCharacterGroupRing

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open RootedAccountedUnfolding
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter

noncomputable section

abbrev PositiveScaleCarrier :=
  SourceGeneratedIntegralCharacterGroupRing.Carrier (Units NNReal)

abbrev ZeroIntegralCharacterPayload :=
  Σ _source : ZeroMultiplicativeCharacterPayload,
    (PositiveScaleCarrier →ₗ[ℤ] ℂ) ×
      (PositiveScaleCarrier →ₗ[ℤ] ℂ)

/-- Both integral character evaluations are generated directly from the
character pair carried by the same zero occurrence. -/
def zeroOwnedIntegralCharacterOccurrence
    (observation : GeneratedRiemannZeroObservation) :
    RootedAccountedUnfolding ZeroIntegralCharacterPayload :=
  (zeroOwnedMultiplicativeCharacterOccurrence observation).map fun source =>
    ⟨source,
      characterEvaluation source.2.selected,
      characterEvaluation source.2.reversal⟩

theorem zeroOwnedIntegralCharacterOccurrence_projects
    (observation : GeneratedRiemannZeroObservation) :
    (zeroOwnedIntegralCharacterOccurrence observation).map Sigma.fst =
      zeroOwnedMultiplicativeCharacterOccurrence observation := by
  rw [zeroOwnedIntegralCharacterOccurrence, RootedAccountedUnfolding.map_map]
  change (zeroOwnedMultiplicativeCharacterOccurrence observation).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem zeroOwnedIntegralCharacterOccurrence_projects_to_seed
    (observation : GeneratedRiemannZeroObservation) :
    ((((((zeroOwnedIntegralCharacterOccurrence observation).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Prod.fst) =
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence := by
  rw [zeroOwnedIntegralCharacterOccurrence_projects,
    zeroOwnedMultiplicativeCharacterOccurrence_projects_to_seed]

@[simp] theorem zeroOwnedIntegralCharacterOccurrence_root_selected
    (observation : GeneratedRiemannZeroObservation) :
    (zeroOwnedIntegralCharacterOccurrence observation).root.2.1 =
      characterEvaluation
        (zeroOwnedMultiplicativeCharacterOccurrence observation).root.2.selected := by
  rfl

@[simp] theorem zeroOwnedIntegralCharacterOccurrence_root_reversal
    (observation : GeneratedRiemannZeroObservation) :
    (zeroOwnedIntegralCharacterOccurrence observation).root.2.2 =
      characterEvaluation
        (zeroOwnedMultiplicativeCharacterOccurrence observation).root.2.reversal := by
  rfl

/-- The arithmetic prime face is a basis evaluation of the same integral
character occurrence. -/
theorem selected_prime_basis_readback
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    (zeroOwnedIntegralCharacterOccurrence observation).root.2.1
        (delta (positiveRealUnit (prime : ℝ) (by
          exact_mod_cast prime.2.pos))) =
      installedPrimeEigenvalue prime observation.coordinate := by
  rw [zeroOwnedIntegralCharacterOccurrence_root_selected,
    characterEvaluation_delta,
    zeroOwnedMultiplicativeCharacterOccurrence_root_selected]
  exact (installedPrimeEigenvalue_eq_complexPowerCharacter
    prime observation.coordinate).symm

theorem reversal_prime_basis_readback
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    (zeroOwnedIntegralCharacterOccurrence observation).root.2.2
        (delta (positiveRealUnit (prime : ℝ) (by
          exact_mod_cast prime.2.pos))) =
      installedPrimeEigenvalue prime
        (coordinateReversal observation.coordinate) := by
  rw [zeroOwnedIntegralCharacterOccurrence_root_reversal,
    characterEvaluation_delta,
    zeroOwnedMultiplicativeCharacterOccurrence_root_reversal]
  exact (installedPrimeEigenvalue_eq_complexPowerCharacter prime
    (coordinateReversal observation.coordinate)).symm

/-- The selected Archimedean square-root face is another basis evaluation of
the very same integral character occurrence. -/
theorem selected_sqrt_basis_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    (zeroOwnedIntegralCharacterOccurrence observation).root.2.1
        (delta (positiveRealUnit
          (Real.sqrt (QRich.blockQRichSuccessorScale stage : ℝ)) (by
            rw [QRich.blockQRichSuccessorScale_eq_stage_add_three]
            positivity))) =
      QRich.selectedPositiveMellinDilationReadback
        observation nontrivial stage := by
  rw [zeroOwnedIntegralCharacterOccurrence_root_selected,
    characterEvaluation_delta,
    selectedPositiveMellinDilationReadback_eq_zeroOwnedCharacter]

theorem reversal_sqrt_basis_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    (zeroOwnedIntegralCharacterOccurrence observation).root.2.2
        (delta (positiveRealUnit
          (Real.sqrt (QRich.blockQRichSuccessorScale stage : ℝ)) (by
            rw [QRich.blockQRichSuccessorScale_eq_stage_add_three]
            positivity))) =
      QRich.reversalPositiveMellinDilationReadback
        observation nontrivial stage := by
  rw [zeroOwnedIntegralCharacterOccurrence_root_reversal,
    characterEvaluation_delta,
    reversalPositiveMellinDilationReadback_eq_zeroOwnedCharacter]

/-- The same carrier retains a nonzero additive prime residual independently
of the complex character evaluation. -/
def positiveScalePrimeResidualCoordinate (prime : Nat.Primes) :
    SourceGeneratedFaithfulIntegralFace.PrimeResidualCoordinate
      (L := PositiveScaleCarrier) prime :=
  deltaOnePrimeResidualCoordinate prime

theorem positiveScalePrimeResidualClass_ne_zero (prime : Nat.Primes) :
    SourceGeneratedFaithfulIntegralFace.residualClass
        (L := PositiveScaleCarrier) prime (delta (1 : Units NNReal)) ≠ 0 :=
  deltaOne_primeResidualClass_ne_zero prime

end

end IntegralCharacterGroupRing
end Character
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
