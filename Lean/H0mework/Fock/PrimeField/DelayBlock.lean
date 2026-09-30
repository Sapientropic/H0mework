import H0mework.Fock.PrimeField.RecoveryConsumer

/-! Original factorial material generates arbitrarily long native intervals with no new prime support. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeObservationDelay

open ArithmeticGeneration CanonicalUnitArithmeticFactorizationOccurrence
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open SourcePrimeHistoryRecovery

noncomputable section

def magnitude (owner : GlobalParentOwner) (length : Nat) : Nat :=
  (factorialHistory (requestHistory owner length)).cardinalShadow

theorem magnitude_value (owner : GlobalParentOwner) (length : Nat) :
    magnitude owner length = (2 * (length + 3)).factorial := by
  have generated := argument_value owner length
  change magnitude owner length + 1 = (2 * (length + 3)).factorial + 1 at generated
  omega

def firstState (owner : GlobalParentOwner) (length : Nat) : Nat := magnitude owner length / 2

theorem twice_firstState (owner : GlobalParentOwner) (length : Nat) :
    2 * firstState owner length = magnitude owner length := by
  apply Nat.mul_div_cancel'
  rw [magnitude_value]
  exact Nat.dvd_factorial (by omega) (by omega)

theorem source_candidate_composite (owner : GlobalParentOwner) (length offset : Nat) (inside : offset ≤ length) :
    ¬ Nat.Prime (magnitude owner length + 2 * offset + 5) := by
  have divides : 2 * offset + 5 ∣ magnitude owner length := by
    rw [magnitude_value]
    exact Nat.dvd_factorial (by omega) (by omega)
  have positive : 0 < magnitude owner length := by
    rw [magnitude_value]
    exact Nat.factorial_pos _
  apply Nat.not_prime_of_dvd_of_lt (m := 2 * offset + 5)
  · rw [show magnitude owner length + 2 * offset + 5 = magnitude owner length + (2 * offset + 5) by omega]
    exact dvd_add divides (dvd_refl (2 * offset + 5))
  · omega
  · omega

end
end SourcePrimeObservationDelay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
