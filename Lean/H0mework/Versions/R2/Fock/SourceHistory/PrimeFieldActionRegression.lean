import H0mework.Versions.R2.Fock.PrimeField.Consumer
import H0mework.Versions.R2.Fock.PrimeField.Birth
import H0mework.Versions.R2.Fock.PrimeFieldNoGo.ActionNoGo

/-! A real prime-support gap retains changing source multiplicity; the raw field alone has no native next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFactorizationAction.Fock.Controls

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

def current (depth : Nat) : CanonicalUnitArithmeticRoot.Current := (runtimeAt depth).current.visit.current

theorem current_next (depth : Nat) : CanonicalUnitArithmeticRoot.next (current depth) = current (depth + 1) := rfl

private def three : Nat.Primes := ⟨3, Nat.prime_three⟩
private def eleven : Nat.Primes := ⟨11, by decide⟩

theorem atom_ne_zero (prime : Nat.Primes) : atom prime ≠ 0 := by
  rw [atom, ← deltaUnit_coe]
  exact Units.ne_zero _

theorem gap_birth_zero : birth (current 2) = 0 := by
  apply birth_of_composite
  change ¬ Nat.Prime 9
  decide

theorem after_gap_birth : birth (current 3) = atom eleven := by
  exact birth_of_prime (current 3) (by change Nat.Prime 11; decide)

theorem gap_increment_positive : 0 < wholeIncrement (current 2) three := by
  rw [whole_increment_apply]
  change 0 < (9 : Nat).factorization 3 + (10 : Nat).factorization 3
  have grows := Nat.prime_three.factorization_pos_of_dvd (by decide : (9 : Nat) ≠ 0) (by decide : 3 ∣ 9)
  omega

theorem gap_counts_change : primeCounts (history (current 3)) ≠ primeCounts (history (current 2)) := by
  intro unchanged
  have actual := counts_next (current 2)
  rw [current_next] at actual
  have atThree := congrArg (fun counts : Nat.Primes →₀ Nat => counts three) (actual.symm.trans unchanged)
  simp only [Finsupp.add_apply] at atThree
  have positive := gap_increment_positive
  omega

theorem same_field : sourceFieldAt (current 3) = sourceFieldAt (current 2) := by
  have generated := field_next (current 2)
  rw [gap_birth_zero, add_zero, current_next] at generated
  exact generated

theorem next_fields_differ : sourceFieldAt (current 4) ≠ sourceFieldAt (current 3) := by
  have generated := field_next (current 3)
  rw [after_gap_birth, current_next] at generated
  intro same
  have zero : atom eleven = 0 :=
    add_left_cancel (generated.symm.trans (same.trans (add_zero _).symm))
  exact atom_ne_zero _ zero

theorem no_field_only_next :
    ¬ ∃ advance : IntegralOneParticle → IntegralOneParticle,
      ∀ depth, advance (sourceFieldAt (current depth)) = sourceFieldAt (current (depth + 1)) := by
  rintro ⟨advance, generated⟩
  have same := congrArg advance same_field
  rw [generated 3, generated 2] at same
  exact next_fields_differ same

theorem original_next_target_control (depth : Nat) :
    atomicTargetAmplitude (scanIndex (current depth) + 1)
      (secondQuantizedEffect (sourceFieldAt (current depth)) (birth (current depth))) = 0 := by
  have original := ParticleWaveFockSuccessorPrimeFieldActionNoGo.nextTargetAtomicAmplitude_forcedTrace_eq_zero (current depth)
  have actual := (forced_from_source (runtimePayload depth)).symm.trans (runtimePayload depth).forcedTrace_eq
  exact (congrArg (atomicTargetAmplitude (scanIndex (current depth) + 1)) actual).trans original

end
end SourceFactorizationAction.Fock.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
