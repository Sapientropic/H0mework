import H0mework.Fock.PrimeHistoryMeasure.Recovery
import H0mework.Probability.HistoryGrowth.Conditional
import H0mework.Probability.HistoryGrowth.Retention

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionMeasure

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev next (runtime : LivingRuntimeState process) : LivingRuntimeState process :=
  (normal runtime).targetRuntime.tick.next

theorem inventory_grows (runtime : LivingRuntimeState process) :
    inventoryBound runtime < inventoryBound (next runtime) := by
  rw [next_inventory]
  unfold completionDepth
  omega

theorem retained (runtime : LivingRuntimeState process) : inventoryBound runtime ≤ inventoryBound (next runtime) :=
  (inventory_grows runtime).le

def priorMass (runtime : LivingRuntimeState process) : ℝ :=
  SourceHistoryGrowth.fraction (inventoryBound runtime) (inventoryBound (next runtime))

theorem prior_mass_original (runtime : LivingRuntimeState process) :
    priorMass runtime = (inventoryBound runtime + 1 : ℝ) /
      (inventoryBound runtime + windowBound sourceOwner (inventoryBound runtime) + 3 : ℝ) := by
  rw [priorMass, SourceHistoryGrowth.fraction, next_inventory]
  simp only [completionDepth, Nat.cast_add, Nat.cast_ofNat]
  congr 1
  ring

theorem prior_mass_pos_lt_one (runtime : LivingRuntimeState process) : 0 < priorMass runtime ∧ priorMass runtime < 1 := by
  refine ⟨SourceHistoryGrowth.fraction_pos _ _, ?_⟩
  unfold priorMass SourceHistoryGrowth.fraction
  apply (div_lt_one (by positivity)).mpr
  exact_mod_cast Nat.succ_lt_succ (inventory_grows runtime)

def preserve (runtime : LivingRuntimeState process) (depth : Nat) :
    FieldSpace depth (inventoryBound runtime) →L[ℂ] FieldSpace depth (inventoryBound (next runtime)) :=
  extend depth (retained runtime)

def recover (runtime : LivingRuntimeState process) (depth : Nat) :
    FieldSpace depth (inventoryBound (next runtime)) →L[ℂ] FieldSpace depth (inventoryBound runtime) :=
  restrict depth (retained runtime)

def newMaterial (runtime : LivingRuntimeState process) (depth : Nat) :
    FieldSpace depth (inventoryBound (next runtime)) →L[ℂ] FieldSpace depth (inventoryBound (next runtime)) :=
  remainder depth (retained runtime)

theorem recover_preserve (runtime : LivingRuntimeState process) (depth : Nat)
    (value : FieldSpace depth (inventoryBound runtime)) :
    recover runtime depth (preserve runtime depth value) = value := restrict_extend depth (retained runtime) value

theorem recovery_gain (runtime : LivingRuntimeState process) (depth : Nat) :
    ‖recover runtime depth‖ = (Real.sqrt (priorMass runtime))⁻¹ := restriction_norm depth (retained runtime)

theorem recovery_gain_gt_one (runtime : LivingRuntimeState process) (depth : Nat) : 1 < ‖recover runtime depth‖ := by
  rw [recovery_gain]
  have positive := Real.sqrt_pos.mpr (prior_mass_pos_lt_one runtime).1
  have smaller : Real.sqrt (priorMass runtime) < 1 := by
    nlinarith only [Real.sq_sqrt (prior_mass_pos_lt_one runtime).1.le, (prior_mass_pos_lt_one runtime).2,
      Real.sqrt_nonneg (priorMass runtime)]
  exact (one_lt_inv₀ positive).mpr smaller

theorem retained_query (runtime : LivingRuntimeState process) (depth : Nat)
    (value : FieldSpace depth (inventoryBound (next runtime))) (index : Fin (inventoryBound runtime + 1)) :
    SourceGeneratedAtomicObservation.Recorded.query depth (inventoryBound runtime) index (recover runtime depth value) =
      SourceGeneratedAtomicObservation.Recorded.query depth (inventoryBound (next runtime))
        (SourceHistoryGrowth.includeActor (retained runtime) index) value :=
  query_retained depth (retained runtime) value index

theorem complete_energy (runtime : LivingRuntimeState process) (depth : Nat)
    (value : FieldSpace depth (inventoryBound (next runtime))) :
    ‖value‖ ^ 2 = priorMass runtime * ‖recover runtime depth value‖ ^ 2 + ‖newMaterial runtime depth value‖ ^ 2 :=
  energy_decomposition depth (retained runtime) value

theorem new_source_read (runtime : LivingRuntimeState process) (depth : Nat) :
    Actor.originalRead depth (inventoryBound (next runtime)) (Fin.last (inventoryBound (next runtime))) =
      fieldPoint nativeStep (rawWords depth) ((next runtime).current.visit.current : Current) := by
  rw [Actor.originalRead_actual]
  have original : runtimeAt (inventoryBound (next runtime)) = next runtime := by
    rw [inventory_bound]
    exact (runtime_eq (next runtime)).symm
  exact congrArg (fun current : LivingRuntimeState process =>
    fieldPoint nativeStep (rawWords depth) (current.current.visit.current : Current)) original

end
end SourceGeneratedAcquisitionMeasure
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
