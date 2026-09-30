import H0mework.Fock.PrimeFieldJoint.BornNormalized

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedBornDecoder

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime Filter
open scoped Topology
noncomputable section

theorem actual_cost_drop (runtime : LivingRuntimeState process) (depth : Nat) :
    ‖SourceJointFiniteDecoder.residual (inventoryBound (next runtime)) (unitTarget runtime depth)‖ ^ 2 <
      ‖SourceJointFiniteDecoder.residual (inventoryBound runtime) (unitTarget runtime depth)‖ ^ 2 := by
  rw [unit_fresh_residual, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (unit_prior_residual runtime depth)

def movingCost (round : Nat) : ℝ :=
  let runtime := roundRuntime round
  ‖SourceJointFiniteDecoder.residual (inventoryBound runtime)
    (unitTarget runtime (depth (next runtime)))‖ ^ 2

theorem moving_cost_ge_one (round : Nat) : 1 ≤ movingCost round :=
  unit_prior_residual (roundRuntime round) _

theorem moving_cost_not_tendsto_zero : ¬ Tendsto movingCost atTop (𝓝 (0 : ℝ)) := by
  intro converges
  have lower := ge_of_tendsto' converges moving_cost_ge_one
  norm_num at lower

theorem acquired_cost_zero (round : Nat) :
    let runtime := roundRuntime round
    ‖SourceJointFiniteDecoder.residual (inventoryBound (next runtime))
      (unitTarget runtime (depth (next runtime)))‖ ^ 2 = 0 := by
  dsimp only
  rw [unit_fresh_residual, norm_zero, zero_pow (by decide : 2 ≠ 0)]

end
end SourceGeneratedBornDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
