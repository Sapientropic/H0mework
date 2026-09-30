import H0mework.Fock.HistoryModel.DynamicHilbertConditional
import H0mework.Fock.PrimeField.DelayActual
import H0mework.Probability.Recovery.Collision

/-! An actual prime-support collision obstructs free recovery from the original full Fock snapshot. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic.Hilbert

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourcePrimeObservationDelay SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

def snapshot (bound : Nat) (index : Fin (bound + 1)) : ParentCarrier := sourceStateAt (actor bound index)

def clockTask (bound : Nat) (index : Fin (bound + 1)) : ℂ := index.val

abbrev collisionBound (owner : GlobalParentOwner) := firstState owner 0 + 1

def collisionLeft (owner : GlobalParentOwner) : Fin (collisionBound owner + 1) :=
  ⟨firstState owner 0, by change firstState owner 0 < firstState owner 0 + 1 + 1; omega⟩

theorem actual_snapshot_collision (owner : GlobalParentOwner) :
    snapshot (collisionBound owner) (collisionLeft owner) =
      snapshot (collisionBound owner) (Fin.last (collisionBound owner)) := by
  have generated := congrArg secondQuantizedState (field_step owner 0 0 le_rfl)
  change secondQuantizedState (rawField (firstState owner 0)) = secondQuantizedState (rawField (firstState owner 0 + 1))
  simpa only [Nat.add_zero] using generated.symm

theorem collision_indices_distinct (owner : GlobalParentOwner) :
    collisionLeft owner ≠ Fin.last (collisionBound owner) := by
  intro same
  have indices := congrArg Fin.val same
  change firstState owner 0 = firstState owner 0 + 1 at indices
  omega

theorem snapshot_clock_cost (owner : GlobalParentOwner) (decoder : ParentCarrier → ℂ) :
    (1 / (collisionBound owner + 1 : ℝ)) / 2 ≤
      error (historyPMF (collisionBound owner)) (snapshot (collisionBound owner))
        (clockTask (collisionBound owner)) decoder := by
  have paid := equal_weight_pair_lower_bound (historyPMF (collisionBound owner)) (snapshot (collisionBound owner))
    (clockTask (collisionBound owner)) decoder (collisionLeft owner) (Fin.last (collisionBound owner))
    (collision_indices_distinct owner) (actual_snapshot_collision owner) (by simp only [historyPMF_apply])
  have distance : ‖clockTask (collisionBound owner) (collisionLeft owner) -
      clockTask (collisionBound owner) (Fin.last (collisionBound owner))‖ = 1 := by
    change ‖(firstState owner 0 : ℂ) - ((firstState owner 0 + 1 : Nat) : ℂ)‖ = 1
    simp only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_one]
  have weight : (historyPMF (collisionBound owner) (collisionLeft owner)).toReal =
      ((collisionBound owner + 1 : Nat) : ℝ)⁻¹ := by
    rw [historyPMF_apply, ENNReal.toReal_inv]
    exact congrArg Inv.inv (ENNReal.toReal_natCast (collisionBound owner + 1))
  rw [weight, distance, one_pow, mul_one] at paid
  simpa only [one_div, Nat.cast_add, Nat.cast_one] using paid

theorem snapshot_clock_cost_positive (owner : GlobalParentOwner) (decoder : ParentCarrier → ℂ) :
    0 < error (historyPMF (collisionBound owner)) (snapshot (collisionBound owner))
      (clockTask (collisionBound owner)) decoder :=
  lt_of_lt_of_le (by positivity) (snapshot_clock_cost owner decoder)

end
end SourceGeneratedActionWords.Fock.Dynamic.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
