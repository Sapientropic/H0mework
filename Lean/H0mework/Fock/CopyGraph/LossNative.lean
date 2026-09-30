import H0mework.Fock.CopyGraph.LossRange
import H0mework.Fock.CopyGraph.LossUpdate
import H0mework.Fock.CopyGraph.LossField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open SourceOwnedObservationHistory SourcePrimeHistoryRecovery
open SourceCopyProgram (Index)
open SourceGraphGrowth (sourceRead oldRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open scoped Classical
noncomputable section
local instance nativeLossMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem native_prime_read (depth : Nat) (index : Index depth) (prime : Nat.Primes) (state : Nat) :
    primeRead prime (thetaProjection (sourceRead depth index state).1) = if prime.val ≤ 2 * (state + 2) then 1 else 0 := by
  have original := congrArg (fun value : ParentCarrier × ParentCarrier => primeRead prime (thetaProjection value.1))
    (SourceCopyInventory.joint_source depth state index (Fin.last state))
  change primeRead prime (thetaProjection (SourceCopyObservation.before depth state (Fin.last state))) = _ at original
  rw [SourceCopyObservation.before_theta, primeRead_source] at original
  exact original.symm

theorem native_prime_novel (depth : Nat) (index : Index depth) (prime : Nat.Prime (2 * depth + 5)) :
    sourceRead depth index (depth + 1) ∉ atoms (historyPMF depth) (oldRead depth (sourceRead depth index)) := by
  intro present
  have supported := (atoms_iff (historyPMF depth) (oldRead depth (sourceRead depth index)) _).mp present
  obtain ⟨actor, _, same⟩ := (PMF.mem_support_map_iff (oldRead depth (sourceRead depth index)) (historyPMF depth)
    (sourceRead depth index (depth + 1))).mp supported
  let witness : Nat.Primes := ⟨2 * depth + 5, prime⟩
  have read := congrArg (fun value : ParentCarrier × ParentCarrier => primeRead witness (thetaProjection value.1)) same
  change primeRead witness (thetaProjection (sourceRead depth index actor.val).1) =
    primeRead witness (thetaProjection (sourceRead depth index (depth + 1)).1) at read
  rw [native_prime_read, native_prime_read] at read
  have before : ¬ witness.val ≤ 2 * (actor.val + 2) := by change ¬ 2 * depth + 5 ≤ _; have inside := actor.isLt; omega
  have after : witness.val ≤ 2 * (depth + 1 + 2) := by change 2 * depth + 5 ≤ _; omega
  rw [if_neg before, if_pos after] at read
  exact zero_ne_one read

theorem native_prime_direction_zero (depth : Nat) (index : Index depth) (prime : Nat.Prime (2 * depth + 5)) :
    direction depth index (sourceRead depth index) = 0 :=
  (direction_zero_iff_novel depth index (sourceRead depth index)).mpr (native_prime_novel depth index prime)

theorem native_prime_update_zero (depth : Nat) (index : Index depth) (prime : Nat.Prime (2 * depth + 5)) :
    update depth index (sourceRead depth index) = 0 := by
  apply ContinuousLinearMap.ext
  intro value
  rw [update_apply, native_prime_direction_zero depth index prime, smul_zero]
  rfl

theorem native_collision_cost :
    (1 : ℝ) / 8 ≤ ‖direction 2 (0 : Index 2) (sourceRead 2 (0 : Index 2))‖ ^ 2 := by
  have paid := collision_cost 2 (0 : Index 2) (sourceRead 2 (0 : Index 2)) (2 : Fin 3) SourceGraphGrowth.native_unit_collision
  norm_num only [Nat.cast_ofNat] at paid
  with_unfolding_all exact paid

theorem native_pulse_pair_ne_zero :
    inner ℂ (direction 2 (0 : Index 2) (sourceRead 2 (0 : Index 2))) (SourceGraphGrowth.pulse 2 (0 : Index 2)) ≠ 0 := by
  intro vanished
  have zero := (loss_zero_iff 2 (0 : Index 2) (sourceRead 2 (0 : Index 2)) (SourceGraphGrowth.pulse 2 (0 : Index 2))).mpr vanished
  have empty := congrArg (fun value : SourceJointClockGraph.Carrier => ‖value‖ ^ 2) zero
  have impossible : (0 : ℝ) < ‖(0 : SourceJointClockGraph.Carrier)‖ ^ 2 := by
    with_reducible exact SourceGraphGrowth.native_forgetting_positive.trans_eq empty
  norm_num only [norm_zero, zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at impossible

theorem native_rank_increment (depth : Nat) (index : Index depth) :
    (Module.finrank ℂ (SourceGraphGrowth.forgettingLoss depth index (sourceRead depth index)).range : ℝ) =
      SourceCopyInventory.increment (NativeCopy.Fock.material depth index) depth := by
  have inventory : atoms (historyPMF depth) (oldRead depth (sourceRead depth index)) =
      outputs depth (oldRead depth (sourceRead depth index)) := by
    ext atom
    rw [atoms_iff]
    exact ⟨supported_output depth _ atom, output_supported depth _ atom⟩
  rw [rank_inventory, inventory]
  change ((if sourceRead depth index (depth + 1) ∈ outputs depth (oldRead depth (sourceRead depth index)) then 1 else 0 : Nat) : ℝ) =
    if sourceRead depth index (depth + 1) ∈ outputs depth (oldRead depth (sourceRead depth index)) then 1 else 0
  split_ifs <;> norm_num

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
