import H0mework.Fock.PrimeFieldJoint.BornLoss
import H0mework.Fock.PrimeFieldJoint.BornRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedBornDecoder

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open SourceGeneratedJointTime SourceGeneratedJointClockGraph SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def unitNewest (runtime : LivingRuntimeState process) (depth : Nat) : FieldSpace depth (inventoryBound (next runtime)) :=
  Real.sqrt (inventoryBound (next runtime) + 1 : ℝ) • newest runtime depth

def unitTarget (runtime : LivingRuntimeState process) (depth : Nat) : SourceJointClockGraph.Carrier :=
  nextFieldRead depth (inventoryBound (next runtime))
    (timeTransfer depth (inventoryBound (next runtime)) (unitNewest runtime depth))

theorem unit_newest_norm (runtime : LivingRuntimeState process) (depth : Nat) : ‖unitNewest runtime depth‖ = 1 := by
  rw [unitNewest, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), newest_norm]
  have nonzero : Real.sqrt (inventoryBound (next runtime) + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem unit_target_scale (runtime : LivingRuntimeState process) (depth : Nat) :
    unitTarget runtime depth = Real.sqrt (inventoryBound (next runtime) + 1 : ℝ) • target runtime depth := by
  change nextFieldRead _ _ (timeTransfer _ _ (Real.sqrt (inventoryBound (next runtime) + 1 : ℝ) • newest runtime depth)) = _
  rw [LinearMapClass.map_smul_of_tower, LinearMap.map_smul_of_tower]
  rfl

theorem unit_coordinate (runtime : LivingRuntimeState process) (depth : Nat) :
    coordinate (inventoryBound (next runtime) + 1) (unitTarget runtime depth) = 1 := by
  rw [unit_target_scale, LinearMapClass.map_smul_of_tower, target_coordinate,
    SourceHistoryWord.coefficient_scale]
  simp only [Complex.real_smul]
  push_cast
  have nonzero : (Real.sqrt (inventoryBound (next runtime) + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < inventoryBound (next runtime) + 1 by positivity)).ne'
  field_simp

theorem unit_prior_loss (runtime : LivingRuntimeState process) (depth : Nat)
    (proposal : SourceJointFiniteDecoder.Space (inventoryBound runtime)) :
    1 ≤ ‖unitTarget runtime depth - SourceJointFiniteDecoder.action (inventoryBound runtime) proposal‖ ^ 2 := by
  have bound := coordinate_norm_le (inventoryBound (next runtime) + 1)
    (unitTarget runtime depth - SourceJointFiniteDecoder.action (inventoryBound runtime) proposal)
  rw [map_sub, unit_coordinate, prior_coordinate, sub_zero, norm_one] at bound
  nlinarith only [bound]

theorem unit_prior_residual (runtime : LivingRuntimeState process) (depth : Nat) :
    1 ≤ ‖SourceJointFiniteDecoder.residual (inventoryBound runtime) (unitTarget runtime depth)‖ ^ 2 := by
  have source := unit_prior_loss runtime depth (SourceJointFiniteDecoder.decode (inventoryBound runtime) (unitTarget runtime depth))
  rw [SourceJointFiniteDecoder.source_minimum_cost] at source
  exact source

theorem unit_fresh_decode (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceGeneratedJointFiniteDecoder.decode depth (inventoryBound (next runtime)) (unitTarget runtime depth) = unitNewest runtime depth := by
  rw [unitTarget, SourceGeneratedJointFiniteDecoder.original_K]
  exact SourceGeneratedRecordFrame.original_time_recovery depth _ _

theorem unit_fresh_residual (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceJointFiniteDecoder.residual (inventoryBound (next runtime)) (unitTarget runtime depth) = 0 :=
  SourceGeneratedJointFiniteDecoder.next_residual_zero depth _ _

end
end SourceGeneratedBornDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
