import H0mework.Fock.CopyGraph.TimeEnergyBudget

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeEnergy

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (Packet hilbert mass restore next extend recoveryErrors finitePhases time)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical InnerProductSpace
noncomputable section

theorem next_inventory_cost (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    copyCost depth index (next depth index packet) + ‖SourceCopyGraph.action depth index (packet 0)‖ ^ 2 =
      copyCost depth index packet + ‖SourceCopyGraph.action depth index (SourceJointClockGraph.action (packet 0))‖ ^ 2 := by
  unfold copyCost
  let cost := fun phase : Fin (index.val + 1 + 1) =>
    ‖SourceCopyGraph.action depth index (extend depth index packet phase)‖ ^ 2
  have first := Fin.sum_univ_succ cost
  have last := Fin.sum_univ_castSucc cost
  have old : ∀ phase : Fin (index.val + 1),
      extend depth index packet phase.castSucc = packet phase := by
    intro phase
    simp only [extend, LinearMap.pi_apply, Fin.lastCases_castSucc, LinearMap.proj_apply]
  have new : extend depth index packet (Fin.last (index.val + 1)) = SourceJointClockGraph.action (packet 0) := by
    simp only [extend, LinearMap.pi_apply, Fin.lastCases_last, LinearMap.comp_apply, LinearMap.proj_apply]
    rfl
  have atZero : extend depth index packet 0 = packet 0 := by
    simpa only [Fin.castSucc_zero] using old 0
  have following : ∀ phase : Fin (index.val + 1),
      extend depth index packet phase.succ = next depth index packet phase := by
    intro phase
    rfl
  simp only [cost, following, atZero] at first
  simp only [cost, old, new] at last
  linarith only [first, last]

def clockWork (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) : ℝ :=
  (scale depth index : ℝ) ^ 2 * (‖mass value‖ ^ 2 + 2 * (⟪SourceJointClockGraph.clock value, mass value⟫_ℂ).re)

theorem next_source_work (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    ‖SourceCopyGraph.action depth index (SourceJointClockGraph.action value)‖ ^ 2 =
      ‖SourceCopyGraph.action depth index value‖ ^ 2 + clockWork depth index value := by
  rw [SourceCopyGraph.action_energy, SourceCopyGraph.action_energy, SourceJointClockGraph.action_energy,
    SourceCopyTimeModel.clock_next, norm_add_sq (𝕜 := ℂ)]
  change (‖value‖ ^ 2 + ‖mass value‖ ^ 2 + 2 * (⟪SourceJointClockGraph.clock value, mass value⟫_ℂ).re) +
    ((scale depth index : ℝ) ^ 2 - 1) *
      (‖SourceJointClockGraph.clock value‖ ^ 2 + 2 * (⟪SourceJointClockGraph.clock value, mass value⟫_ℂ).re + ‖mass value‖ ^ 2) =
      ‖value‖ ^ 2 + ((scale depth index : ℝ) ^ 2 - 1) * ‖SourceJointClockGraph.clock value‖ ^ 2 + clockWork depth index value
  unfold clockWork
  ring

theorem next_cost (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    copyCost depth index (next depth index packet) = copyCost depth index packet + clockWork depth index (packet 0) := by
  have inventory := next_inventory_cost depth index packet
  rw [next_source_work] at inventory
  linarith only [inventory]

theorem next_budget (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    ‖restore depth index (next depth index packet)‖ ^ 2 + axisCost depth index (next depth index packet) =
      copyCost depth index packet + clockWork depth index (packet 0) +
        ‖mergedMass depth index (next depth index packet)‖ ^ 2 +
        ‖mergedClock depth index (next depth index packet)‖ ^ 2 := by
  rw [restore_budget, next_cost]

theorem finite_next_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    ‖SourceJointClockGraph.action target -
      restore (inventoryBound runtime) index (next (inventoryBound runtime) index (finitePhases runtime index steps target))‖ ^ 2 +
      axisCost (inventoryBound runtime) index (next (inventoryBound runtime) index (recoveryErrors runtime index steps target)) =
      (∑ phase : Fin (index.val + 1), SourceCopyRecoveryBudget.remainingCost runtime index steps (time phase.val target)) +
        clockWork (inventoryBound runtime) index (recoveryErrors runtime index steps target 0) +
        ‖mergedMass (inventoryBound runtime) index (next (inventoryBound runtime) index (recoveryErrors runtime index steps target))‖ ^ 2 +
        ‖mergedClock (inventoryBound runtime) index (next (inventoryBound runtime) index (recoveryErrors runtime index steps target))‖ ^ 2 := by
  rw [SourceCopyTimeModel.finite_next_error_source, next_budget, recovery_cost]

end
end SourceCopyTimeEnergy
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
