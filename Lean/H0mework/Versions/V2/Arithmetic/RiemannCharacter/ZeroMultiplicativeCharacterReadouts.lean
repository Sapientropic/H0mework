import H0mework.Versions.R2.Arithmetic.EulerDerived.DeterminantSection
import H0mework.Versions.R2.Arithmetic.RiemannCharacter.ZeroMultiplicativeCharacterOccurrence
import H0mework.Versions.R2.Arithmetic.RiemannMellinOrbit.ZeroPositiveMellinRadialDefect

/-!
# Finite and Archimedean readouts of one zero-owned character

The installed Euler eigenvalue and the square-root Mellin/dilation readback
are literal evaluations of the same complex power character.  This file adds
no comparison scalar and no finite Euler kernel claim.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace Character

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open SourceGeneratedPositiveRealCharacter

noncomputable section

/-- Finite-prime evaluation is the installed Euler eigenvalue. -/
theorem installedPrimeEigenvalue_eq_complexPowerCharacter
    (prime : Nat.Primes) (coordinate : ℂ) :
    installedPrimeEigenvalue prime coordinate =
      complexPowerCharacter coordinate
        (positiveRealUnit (prime : ℝ) (by
          exact_mod_cast prime.2.pos)) := by
  rw [installedPrimeEigenvalue, complexPowerCharacter_prime]

/-- The cofinal generated Euler coefficients are globally summed against
the same character.  In the convergent half-plane this is literally the
already installed determinant-coordinate germ. -/
def globalCharacterDirichletReadout (coordinate : ℂ) : ℂ :=
  ∑' n : Nat,
    (globalGermOccurrence.root.2.coefficients (n + 1) : ℂ) *
      complexPowerCharacter coordinate
        (positiveRealUnit (n + 1 : ℝ) (by positivity))

theorem globalCharacterDirichletReadout_eq_globalDeterminantCoordinateGerm
    {coordinate : ℂ} (converges : 1 < coordinate.re) :
    globalCharacterDirichletReadout coordinate =
      globalDeterminantCoordinateGerm coordinate := by
  rw [globalDeterminantCoordinateGerm_eq_riemannZeta converges,
    zeta_eq_tsum_one_div_nat_add_one_cpow converges]
  apply tsum_congr
  intro n
  rw [complexPowerCharacter_apply,
    generatedGlobalCoefficients_eq_zeta]
  have nonzero : n + 1 ≠ 0 := by omega
  simp [ArithmeticFunction.zeta_apply_ne nonzero, Complex.cpow_neg]

/-- The selected quarter-Mellin readback is the square-root Archimedean face
of the same zero-owned character. -/
theorem selectedPositiveMellinDilationReadback_eq_zeroOwnedCharacter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    QRich.selectedPositiveMellinDilationReadback
        observation nontrivial stage =
      (zeroOwnedMultiplicativeCharacterOccurrence observation).root.2.selected
        (positiveRealUnit
          (Real.sqrt (QRich.blockQRichSuccessorScale stage : ℝ))
          (by
            rw [QRich.blockQRichSuccessorScale_eq_stage_add_three]
            positivity)) := by
  rw [QRich.selectedPositiveMellinDilationReadback_eq_character,
    zeroOwnedMultiplicativeCharacterOccurrence_root_selected]
  have scalePositive :
      0 < (QRich.blockQRichSuccessorScale stage : ℝ) := by
    rw [QRich.blockQRichSuccessorScale_eq_stage_add_three]
    positivity
  convert (complexPowerCharacter_sqrt observation.coordinate
    (QRich.blockQRichSuccessorScale stage : ℝ) scalePositive).symm using 1
  all_goals norm_num

/-- The reversal readback is the square-root face of the reversal character
carried by that same occurrence. -/
theorem reversalPositiveMellinDilationReadback_eq_zeroOwnedCharacter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    QRich.reversalPositiveMellinDilationReadback
        observation nontrivial stage =
      (zeroOwnedMultiplicativeCharacterOccurrence observation).root.2.reversal
        (positiveRealUnit
          (Real.sqrt (QRich.blockQRichSuccessorScale stage : ℝ))
          (by
            rw [QRich.blockQRichSuccessorScale_eq_stage_add_three]
            positivity)) := by
  rw [QRich.reversalPositiveMellinDilationReadback_eq_character,
    zeroOwnedMultiplicativeCharacterOccurrence_root_reversal]
  have scalePositive :
      0 < (QRich.blockQRichSuccessorScale stage : ℝ) := by
    rw [QRich.blockQRichSuccessorScale_eq_stage_add_three]
    positivity
  convert (complexPowerCharacter_sqrt
    (coordinateReversal observation.coordinate)
    (QRich.blockQRichSuccessorScale stage : ℝ) scalePositive).symm using 1
  all_goals norm_num

end

end Character
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
