import H0mework.Versions.X.Fock.PrimeField.DelayBlock

/-! The original root keeps updating complete multiplicity throughout the source-generated support gap. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeObservationDelay

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery

noncomputable section

def current (owner : GlobalParentOwner) (length offset : Nat) : CanonicalUnitArithmeticRoot.Current :=
  (runtimeAt (firstState owner length + offset)).current.visit.current

theorem source_birth_zero (owner : GlobalParentOwner) (length offset : Nat) (inside : offset ≤ length) :
    SourceFactorizationAction.Fock.birth (current owner length offset) = 0 := by
  apply SourceFactorizationAction.Fock.birth_of_composite
  have actual : 2 * scanIndex (current owner length offset) + 3 = magnitude owner length + 2 * offset + 5 := by
    have original : scanIndex (current owner length offset) = firstState owner length + offset + 1 := runtimeAt_scanIndex _
    have source := twice_firstState owner length
    omega
  rw [actual]
  exact source_candidate_composite owner length offset inside

theorem field_step (owner : GlobalParentOwner) (length offset : Nat) (inside : offset ≤ length) :
    rawField (firstState owner length + offset + 1) = rawField (firstState owner length + offset) := by
  have generated := (SourceFactorizationAction.Fock.runtime_source_factorization (firstState owner length + offset)).2.1
  change rawField (firstState owner length + offset + 1) = rawField (firstState owner length + offset) +
    SourceFactorizationAction.Fock.birth (current owner length offset) at generated
  rw [source_birth_zero owner length offset inside, add_zero] at generated
  exact generated

theorem field_constant (owner : GlobalParentOwner) (length offset : Nat) (inside : offset ≤ length + 1) :
    rawField (firstState owner length + offset) = rawField (firstState owner length) := by
  induction offset with
  | zero => rw [Nat.add_zero]
  | succ offset previous =>
      exact (field_step owner length offset (by omega)).trans (previous (by omega))

private def two : Nat.Primes := ⟨2, Nat.prime_two⟩

theorem source_multiplicity_increases (owner : GlobalParentOwner) (length offset : Nat) :
    0 < SourceFactorizationAction.Fock.wholeIncrement (current owner length offset) two := by
  rw [SourceFactorizationAction.Fock.whole_increment_apply]
  change 0 < (2 * scanIndex (current owner length offset) + 3).factorization 2 +
    (2 * scanIndex (current owner length offset) + 4).factorization 2
  have positive : 0 < (2 * scanIndex (current owner length offset) + 4).factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd (by omega)
      (dvd_add (dvd_mul_right 2 _) (by decide : 2 ∣ 4))
  omega

end
end SourcePrimeObservationDelay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
