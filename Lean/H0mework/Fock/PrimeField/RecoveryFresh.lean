import H0mework.Fock.PrimeField.RecoveryCoefficient

/-! One exact owner's existing even calculation and factorial joint fold supply the selector prime. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open CanonicalUnitArithmeticFactorizationOccurrence

noncomputable section

def requestHistory (owner : GlobalParentOwner) (index : Nat) : UnitHistory := ownerEvenTargetHistory owner (index + 2)

def euclidHistory (owner : GlobalParentOwner) (index : Nat) : UnitHistory := (factorialHistory (requestHistory owner index)).next

theorem argument_value (owner : GlobalParentOwner) (index : Nat) :
    (euclidHistory owner index).cardinalShadow = (2 * (index + 3)).factorial + 1 := by
  change (factorialHistory (requestHistory owner index)).cardinalShadow + 1 = _
  rw [factorialHistory_cardinalShadow, requestHistory, ownerEvenTargetHistory_eq_generate,
    UnitHistory.cardinalShadow_generate]

private theorem argument_ne_one (owner : GlobalParentOwner) (index : Nat) :
    (euclidHistory owner index).cardinalShadow ≠ 1 := by
  rw [argument_value]
  have positive := Nat.factorial_pos (2 * (index + 3))
  omega

def selectedPrime (owner : GlobalParentOwner) (index : Nat) : Nat.Primes :=
  ⟨(euclidHistory owner index).cardinalShadow.minFac, Nat.minFac_prime (argument_ne_one owner index)⟩

theorem selected_divides (owner : GlobalParentOwner) (index : Nat) :
    (selectedPrime owner index).val ∣ (euclidHistory owner index).cardinalShadow := Nat.minFac_dvd _

theorem selected_above (owner : GlobalParentOwner) (index : Nat) :
    2 * (index + 3) < (selectedPrime owner index).val := by
  by_contra smaller
  have bound : (selectedPrime owner index).val ≤ 2 * (index + 3) := by omega
  have dividesOld : (selectedPrime owner index).val ∣ (2 * (index + 3)).factorial :=
    Nat.dvd_factorial (selectedPrime owner index).property.pos bound
  have dividesNew := selected_divides owner index
  rw [argument_value] at dividesNew
  exact (selectedPrime owner index).property.not_dvd_one ((Nat.dvd_add_iff_right dividesOld).mpr dividesNew)

def delay (owner : GlobalParentOwner) (index : Nat) : Nat := (selectedPrime owner index).val / 2 - index - 2

theorem selected_position (owner : GlobalParentOwner) (index : Nat) :
    (selectedPrime owner index).val = 2 * (index + delay owner index) + 5 := by
  have above := selected_above owner index
  have parity := (selectedPrime owner index).property.eq_two_or_odd
  unfold delay
  omega

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
