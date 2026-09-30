import H0mework.Fock.CopyComplete.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompleteGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] completeUniform completeMeasurable completeBorel completeT2

def read (model : Nat) (actor : Nat) : Complete.Carrier model :=
  Complete.point model ((runtimeAt actor).current.visit.current : Current)

theorem read_injective (model : Nat) : Function.Injective (read model) :=
  Hilbert.point_runtime_injective model

theorem old_read_original (model depth : Nat) : oldRead depth (read model) = Hilbert.read model depth := rfl

theorem new_read_original (model depth : Nat) : newRead depth (read model) = Hilbert.read model (depth + 1) := rfl

theorem newest_novel (model depth : Nat) :
    read model (depth + 1) ∉ atoms (historyPMF depth) (oldRead depth (read model)) := by
  intro present
  have supported := (atoms_iff (historyPMF depth) (oldRead depth (read model)) _).mp present
  obtain ⟨actor, _, same⟩ := (PMF.mem_support_map_iff (oldRead depth (read model)) (historyPMF depth)
    (read model (depth + 1))).mp supported
  have index := read_injective model same
  have inside := actor.isLt
  change actor.val = depth + 1 at index
  omega

theorem no_forgetting (model depth : Nat) (index : Index depth) :
    SourceGraphFibreUpdate.sourceUpdate depth index (read model) = 0 := by
  rw [SourceGraphFibreUpdate.source_update_is_loss, ← SourceGraphLoss.update_is_loss,
    SourceGraphLoss.update, SourceGraphLoss.novel_direction_zero depth index (read model) (newest_novel model depth)]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero, inv_zero, zero_smul]

theorem source_growth_energy (model depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    ‖SourceGraphGrowth.newResidual depth index (read model) value‖ ^ 2 +
        ‖SourceGraphBirth.update depth index (read model) value‖ ^ 2 =
      ‖SourceGraphGrowth.oldResidual depth index (read model) value‖ ^ 2 := by
  have original := SourceGraphGrowth.growth_energy depth index (read model) value
  rw [← SourceGraphBirth.update_is_birth, ← SourceGraphFibreUpdate.source_update_is_loss, no_forgetting,
    zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at original
  exact original

end
end SourceCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
