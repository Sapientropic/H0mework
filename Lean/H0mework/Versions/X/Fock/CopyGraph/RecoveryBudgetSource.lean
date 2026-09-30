import H0mework.Versions.X.Fock.CopyGraph.Geometry
import H0mework.Versions.X.Fock.CopyGraph.CofinalObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyRecoveryBudget

open SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem original_error (depth : Nat) (index : Index depth) (target proposal : SourceJointClockGraph.Carrier) :
    ‖target - SourceCopyGraph.action depth index proposal‖ ^ 2 =
      ‖SourceCopyGraph.residual depth index target‖ ^ 2 +
        ‖SourceCopyGraph.action depth index (SourceCopyGraph.recover depth index target - proposal)‖ ^ 2 := by
  have sourceZero : SourceCopyGraph.residual depth index (SourceCopyGraph.action depth index proposal) = 0 := by
    change SourceCopyGraph.action depth index proposal - SourceCopyGraph.action depth index
      (SourceCopyGraph.recover depth index (SourceCopyGraph.action depth index proposal)) = 0
    rw [SourceCopyGraph.recover_action, sub_self]
  have residualSame : SourceCopyGraph.residual depth index (target - SourceCopyGraph.action depth index proposal) =
      SourceCopyGraph.residual depth index target := by rw [map_sub, sourceZero, sub_zero]
  have inverseSame : SourceCopyGraph.recover depth index (target - SourceCopyGraph.action depth index proposal) =
      SourceCopyGraph.recover depth index target - proposal := by rw [map_sub, SourceCopyGraph.recover_action]
  have original := SourceCopyGraph.retained_energy depth index (target - SourceCopyGraph.action depth index proposal)
  rw [inverseSame, residualSame] at original
  exact original.trans (add_comm _ _)

def remainingCost (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) : ℝ :=
  ‖SourceCopyGraph.action (inventoryBound runtime) index
    (SourceCopyGraph.recover (inventoryBound runtime) index target -
      fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps)
        (SourceRecordedEvolution.recovery runtime index steps target))‖ ^ 2

theorem actual_error (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    ‖SourceRecordedEvolution.residual runtime index steps target‖ ^ 2 =
      ‖SourceCopyGraph.residual (inventoryBound runtime) index target‖ ^ 2 + remainingCost runtime index steps target := by
  rw [SourceRecordedEvolution.residual, SourceCopyCofinal.advanced_action]
  exact original_error _ index target _

theorem history_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    remainingCost runtime index steps target +
      ∑ stage ∈ Finset.range steps, ‖SourceRecordedEvolution.birth runtime index stage target‖ ^ 2 =
        remainingCost runtime index 0 target := by
  have original := SourceRecordedEvolution.history_energy runtime index steps target
  rw [actual_error, actual_error] at original
  linarith only [original]

end
end SourceCopyRecoveryBudget
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
