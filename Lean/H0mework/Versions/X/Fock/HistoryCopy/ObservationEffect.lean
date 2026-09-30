import H0mework.Versions.X.Fock.HistoryCopy.ObservationSnapshot
import H0mework.Versions.X.Fock.HistoryCopy.ObservationInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyObservation

open SourceConditionalInventory SourceUniformFibreVariance SourcePrimeHistoryRecovery
open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open scoped Classical
noncomputable section

local instance effectParentMeasurable : MeasurableSpace ParentCarrier := ⊤

def twoMaterial : Index 3 := ⟨1, by rw [runtime_bound]; omega⟩

theorem two_index (state : Nat) : SourceCopyProgram.indexAfter 3 twoMaterial state = 2 * state + 1 := by
  rw [SourceCopyProgram.index_source, SourceCopyProgram.scale_source]
  change (state + 1) * 2 - 1 = 2 * state + 1
  omega

theorem copy_prime_read (prime : Nat.Primes) (actor : Fin 4) :
    primeRead prime (thetaProjection (after 3 3 twoMaterial actor)) =
      if prime.val ≤ 4 * actor.val + 6 then 1 else 0 := by
  rw [after_theta, two_index, primeRead_source]
  have clock : 2 * (2 * actor.val + 1 + 2) = 4 * actor.val + 6 := by omega
  rw [clock]

theorem copy_snapshot_injective : Function.Injective (after 3 3 twoMaterial) := by
  intro left right same
  let seven : Nat.Primes := ⟨7, by decide⟩
  let eleven : Nat.Primes := ⟨11, by decide⟩
  let seventeen : Nat.Primes := ⟨17, by decide⟩
  have h7 := (copy_prime_read seven left).symm.trans
    ((congrArg (fun value => primeRead seven (thetaProjection value)) same).trans (copy_prime_read seven right))
  have h11 := (copy_prime_read eleven left).symm.trans
    ((congrArg (fun value => primeRead eleven (thetaProjection value)) same).trans (copy_prime_read eleven right))
  have h17 := (copy_prime_read seventeen left).symm.trans
    ((congrArg (fun value => primeRead seventeen (thetaProjection value)) same).trans (copy_prime_read seventeen right))
  change (if 7 ≤ 4 * left.val + 6 then (1 : ℤ) else 0) = (if 7 ≤ 4 * right.val + 6 then 1 else 0) at h7
  change (if 11 ≤ 4 * left.val + 6 then (1 : ℤ) else 0) = (if 11 ≤ 4 * right.val + 6 then 1 else 0) at h11
  change (if 17 ≤ 4 * left.val + 6 then (1 : ℤ) else 0) = (if 17 ≤ 4 * right.val + 6 then 1 else 0) at h17
  have lc := left.isLt
  have rc := right.isLt
  apply Fin.ext
  split_ifs at h7 <;> norm_num at h7
  all_goals split_ifs at h11 <;> norm_num at h11
  all_goals split_ifs at h17 <;> norm_num at h17
  all_goals omega

theorem copy_cost_zero : cost 3 (after 3 3 twoMaterial) = 0 :=
  exact_inventory 3 _ copy_snapshot_injective

theorem joint_snapshot_injective : Function.Injective (joint 3 3 twoMaterial) := by
  intro left right same
  exact copy_snapshot_injective (congrArg Prod.snd same)

theorem joint_cost_zero : cost 3 (joint 3 3 twoMaterial) = 0 :=
  exact_inventory 3 _ joint_snapshot_injective

theorem actual_copy_recovery :
    cost 3 (before 3 3) = 1 ∧ cost 3 (after 3 3 twoMaterial) = 0 ∧ cost 3 (joint 3 3 twoMaterial) = 0 :=
  ⟨before_cost_three 3, copy_cost_zero, joint_cost_zero⟩

theorem original_snapshot_collision : before 3 3 (2 : Fin 4) = before 3 3 (3 : Fin 4) := by
  rw [before_source, before_source]
  exact congrArg secondQuantizedState (SourceGeneratedConditionalInventory.unchanged_snapshot 2 (by decide)).symm

theorem no_snapshot_copy :
    ¬ ∃ simulate : ParentCarrier → ParentCarrier, ∀ actor : Fin 4,
      simulate (before 3 3 actor) = after 3 3 twoMaterial actor := by
  rintro ⟨simulate, realizes⟩
  have same := congrArg simulate original_snapshot_collision
  rw [realizes, realizes] at same
  exact (by decide : (2 : Fin 4) ≠ 3) (copy_snapshot_injective same)

end
end SourceCopyObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
