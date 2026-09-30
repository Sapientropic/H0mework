import H0mework.Fock.CopyGraph.GrowthTagged
import H0mework.Fock.CopyGraph.DecoderInverse

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

abbrev oldAction (depth : Nat) (index : Index depth) (read : Nat → Observed) :=
  SourceConditionalGraphDecoder.action depth depth index (oldRead depth read)

abbrev taggedAction (depth : Nat) (index : Index depth) (read : Nat → Observed) :=
  SourceConditionalGraphDecoder.action (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)

abbrev newAction (depth : Nat) (index : Index depth) (read : Nat → Observed) :=
  SourceConditionalGraphDecoder.action (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read)

theorem retained_action (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    taggedAction depth index read (retainedLift depth read value) = oldAction depth index read value := by
  change SourceConditionalGraphDecoder.action (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (taggedRead depth read) (retainedLift depth read value) =
      SourceConditionalGraphDecoder.action depth depth index (oldRead depth read) value
  rw [SourceConditionalGraphDecoder.action_source, SourceConditionalGraphDecoder.action_source, retained_lift_source, tick_copy_read]

theorem retained_image (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    (oldAction depth index read).range ≤ (taggedAction depth index read).range := by
  rintro value ⟨source, rfl⟩
  exact ⟨retainedLift depth read source, retained_action depth index read source⟩

def retainedImageLift (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    (oldAction depth index read).range →ₗᵢ[ℂ] (taggedAction depth index read).range where
  toLinearMap := Submodule.inclusion (retained_image depth index read)
  norm_map' _ := rfl

theorem retained_inclusion_comp (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    (SourceConditionalGraphDecoder.inclusion (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)).comp
      (retainedImageLift depth index read) = SourceConditionalGraphDecoder.inclusion depth depth index (oldRead depth read) := by
  apply LinearIsometry.ext
  intro value
  rfl

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
