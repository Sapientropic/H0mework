import H0mework.Versions.X.Fock.CopyGraph.TimeEnergySource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeEnergy

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (Packet hilbert mass restore recoveryErrors finiteRestore time)
open SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def mergedMass (depth : Nat) (index : Index depth) (packet : Packet depth index) : ℂ :=
  (∑ phase : Fin (index.val + 1), mass (packet phase)) - (index.val : ℂ) * mass (packet 0)

def mergedClock (depth : Nat) (index : Index depth) (packet : Packet depth index) : ℂ :=
  (∑ phase : Fin (index.val + 1), ((scale depth index : ℂ) * SourceJointClockGraph.clock (packet phase) -
    (phase.val : ℂ) * mass (packet phase))) -
  (index.val : ℂ) * ((scale depth index : ℂ) * SourceJointClockGraph.clock (packet 0))

def axisCost (depth : Nat) (index : Index depth) (packet : Packet depth index) : ℝ :=
  ∑ phase : Fin (index.val + 1), (‖mass (packet phase)‖ ^ 2 +
    ‖(scale depth index : ℂ) * SourceJointClockGraph.clock (packet phase)‖ ^ 2)

def copyCost (depth : Nat) (index : Index depth) (packet : Packet depth index) : ℝ :=
  ∑ phase : Fin (index.val + 1), ‖SourceCopyGraph.action depth index (packet phase)‖ ^ 2

theorem copy_cost_source (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    copyCost depth index packet =
      (∑ phase : Fin (index.val + 1), ‖hilbert (packet phase)‖ ^ 2) + axisCost depth index packet := by
  unfold copyCost axisCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro phase _
  rw [SourceCopyGraph.action_apply, SourceCopyGraph.joint_apply,
    WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change (‖SourceCopyGraph.hilbertAction depth index (hilbert (packet phase))‖ ^ 2 +
    ‖mass (packet phase)‖ ^ 2) + ‖(scale depth index : ℂ) * SourceJointClockGraph.clock (packet phase)‖ ^ 2 = _
  rw [(SourceCopyGraph.hilbertAction depth index).norm_map, add_assoc]

theorem restore_budget (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    ‖restore depth index packet‖ ^ 2 + axisCost depth index packet =
      copyCost depth index packet + ‖mergedMass depth index packet‖ ^ 2 + ‖mergedClock depth index packet‖ ^ 2 := by
  rw [restore_energy, copy_cost_source]
  unfold mergedMass mergedClock
  ring

theorem recovery_cost (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    copyCost (inventoryBound runtime) index (recoveryErrors runtime index steps target) =
      ∑ phase : Fin (index.val + 1), SourceCopyRecoveryBudget.remainingCost runtime index steps (time phase.val target) := by
  rw [SourceCopyTimeModel.recovery_errors_source]
  unfold copyCost SourceCopyRecoveryBudget.remainingCost
  apply Finset.sum_congr rfl
  intro phase _
  simp only [Pi.sub_apply, SourceCopyTimeModel.phase_source, SourceCopyTimeModel.finitePhases]

theorem finite_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    ‖target - finiteRestore runtime index steps target‖ ^ 2 +
      axisCost (inventoryBound runtime) index (recoveryErrors runtime index steps target) =
    (∑ phase : Fin (index.val + 1), SourceCopyRecoveryBudget.remainingCost runtime index steps (time phase.val target)) +
      ‖mergedMass (inventoryBound runtime) index (recoveryErrors runtime index steps target)‖ ^ 2 +
      ‖mergedClock (inventoryBound runtime) index (recoveryErrors runtime index steps target)‖ ^ 2 := by
  rw [SourceCopyTimeModel.finite_error_source, restore_budget, recovery_cost]

theorem history_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    copyCost (inventoryBound runtime) index (recoveryErrors runtime index steps target) +
      ∑ phase : Fin (index.val + 1), ∑ stage ∈ Finset.range steps,
        ‖SourceRecordedEvolution.birth runtime index stage (time phase.val target)‖ ^ 2 =
    copyCost (inventoryBound runtime) index (recoveryErrors runtime index 0 target) := by
  rw [recovery_cost, recovery_cost, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun phase _ => SourceCopyRecoveryBudget.history_budget runtime index steps (time phase.val target)

theorem whole_residual_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    (∑ phase : Fin (index.val + 1), ‖SourceCopyTimeModel.residuals runtime index steps target phase‖ ^ 2) =
      (∑ phase : Fin (index.val + 1), ‖SourceCopyGraph.residual (inventoryBound runtime) index (time phase.val target)‖ ^ 2) +
      copyCost (inventoryBound runtime) index (recoveryErrors runtime index steps target) := by
  rw [recovery_cost, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun phase _ => SourceCopyRecoveryBudget.actual_error runtime index steps (time phase.val target)

end
end SourceCopyTimeEnergy
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
