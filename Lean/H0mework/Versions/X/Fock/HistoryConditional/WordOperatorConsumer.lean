import H0mework.Versions.X.Fock.HistoryConditional.WordOperatorRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledWordOperator

open SourceGeneratedActionWords SourceOwnedObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem model_action (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    run (Fock.letterAction depth) word (SourceCopyProgram.model depth source) =
      SourceCopyProgram.model depth (action depth word source) := by
  have generated := run_source (Fock.actions depth) (Fock.observer depth) (.inl ()) word (SourceCopyProgram.whole source)
  exact generated.trans (congrArg (projection (Fock.actions depth) (Fock.observer depth) (.inl ()))
    (whole_action depth word source).symm)

theorem complete_reconstruction (depth : Nat) (word : List (Fock.Letter depth)) (target : SourceOperationNative.Carrier process) :
    run (Fock.Complete.action depth) word (SourceCopyProgram.complete depth (recover depth word target)) +
      SourceCopyProgram.complete depth (residual depth word target) = SourceCopyProgram.complete depth target := by
  rw [complete_action, ← map_add, reconstruct]

theorem model_reconstruction (depth : Nat) (word : List (Fock.Letter depth)) (target : SourceOperationNative.Carrier process) :
    run (Fock.letterAction depth) word (SourceCopyProgram.model depth (recover depth word target)) +
      SourceCopyProgram.model depth (residual depth word target) = SourceCopyProgram.model depth target := by
  rw [model_action, ← map_add, reconstruct]

theorem reader_reconstruction (depth : Nat) (word : List (Fock.Letter depth)) (target : SourceOperationNative.Carrier process)
    (index : FamilyModel.Fock.Index depth) :
    FamilyModel.Fock.readout depth
      (Fock.restrict depth (run (Fock.letterAction depth) word (SourceCopyProgram.model depth (recover depth word target)))) index +
    FamilyModel.Fock.readout depth (Fock.restrict depth (SourceCopyProgram.model depth (residual depth word target))) index =
      FamilyModel.Fock.readout depth (Fock.restrict depth (SourceCopyProgram.model depth target)) index := by
  have generated := congrArg (fun model => FamilyModel.Fock.readout depth (Fock.restrict depth model) index)
    (model_reconstruction depth word target)
  simpa only [map_add, Pi.add_apply] using generated

end
end SourceCompiledWordOperator
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
