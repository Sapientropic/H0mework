import H0mework.Versions.X.Fock.CopyGraph.CofinalSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCofinal

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceGeneratedActionWords.Fock.Dynamic
open SourceCopyProgram (Index)
open scoped InnerProductSpace
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2

theorem image_full (model depth bound : Nat) (index : Index depth) :
    image depth index bound = (SourceConditionalGraphDecoder.action depth bound index (Hilbert.read model bound)).range := by
  apply le_antisymm
  · rintro _ ⟨value, rfl⟩
    refine ⟨SourceConditionalGraphDecoder.decode depth bound index (Hilbert.read model bound)
      (SourceConditionalGraph.copyRead depth bound index value), ?_⟩
    have original := SourceConditionalGraphDecoder.reconstruction depth bound index (Hilbert.read model bound)
      (SourceConditionalGraph.copyRead depth bound index value)
    rw [SourceCompleteGraph.source_recovery, add_zero] at original
    change _ = SourceCopyGraph.action depth index (SourceJointFiniteDecoder.read bound value)
    rw [SourceJointFiniteDecoder.read_source]
    exact original
  · rintro _ ⟨value, rfl⟩
    exact ⟨pullback (historyPMF bound) (Hilbert.read model bound) value, rfl⟩

local instance finiteComplete (depth bound : Nat) (index : Index depth) : CompleteSpace (image depth index bound) := by
  rw [image_full 0]
  exact (SourceConditionalGraphDecoder.source_antilipschitz depth bound index (Hilbert.read 0 bound)).completeSpace_range_clm

local instance wholeComplete (depth : Nat) (index : Index depth) : CompleteSpace (SourceCopyGraph.action depth index).range :=
  (action_closed_range depth index).isComplete.completeSpace_coe

theorem finite_projection (model depth bound : Nat) (index : Index depth) (target : SourceJointClockGraph.Carrier) :
    (image depth index bound).starProjection target =
      SourceConditionalGraphDecoder.action depth bound index (Hilbert.read model bound)
        (SourceConditionalGraphDecoder.decode depth bound index (Hilbert.read model bound) target) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [image_full model]
    exact ⟨SourceConditionalGraphDecoder.decode depth bound index (Hilbert.read model bound) target, rfl⟩
  · intro value present
    rw [image_full model] at present
    rcases present with ⟨proposal, rfl⟩
    have reconstruction := SourceConditionalGraphDecoder.reconstruction depth bound index (Hilbert.read model bound) target
    have remaining : SourceConditionalGraphDecoder.residual depth bound index (Hilbert.read model bound) target =
        target - SourceConditionalGraphDecoder.action depth bound index (Hilbert.read model bound)
          (SourceConditionalGraphDecoder.decode depth bound index (Hilbert.read model bound) target) :=
      eq_sub_iff_add_eq.mpr ((add_comm _ _).trans reconstruction)
    rw [← remaining]
    exact inner_eq_zero_symm.mp (SourceConditionalGraphDecoder.source_orthogonal depth bound index (Hilbert.read model bound) target proposal)

theorem whole_orthogonal (depth : Nat) (index : Index depth) (target value : SourceJointClockGraph.Carrier) :
    inner ℂ (SourceCopyGraph.residual depth index target) (SourceCopyGraph.action depth index value) = 0 := by
  rw [SourceCopyGraph.residual_apply, SourceCopyGraph.action_apply, WithLp.prod_inner_apply, SourceCopyGraph.joint_apply,
    WithLp.prod_inner_apply]
  change (inner ℂ (SourceCopyGraph.hilbertResidual depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint target)))
      (SourceCopyGraph.hilbertAction depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value))) +
    inner ℂ (0 : ℂ) (SourceMassCompletion.massRead (SourceJointClockGraph.joint value))) + inner ℂ (0 : ℂ) _ = 0
  rw [inner_zero_left, inner_zero_left, add_zero, add_zero]
  exact inner_eq_zero_symm.mp (IsometricRetainedTransfer.residual_orthogonal (SourceCopyGraph.hilbertAction depth index)
    (SourceMassCompletion.firstRead (SourceJointClockGraph.joint target))
    (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value)))

theorem whole_projection (depth : Nat) (index : Index depth) (target : SourceJointClockGraph.Carrier) :
    (SourceCopyGraph.action depth index).range.starProjection target =
      SourceCopyGraph.action depth index (SourceCopyGraph.recover depth index target) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨SourceCopyGraph.recover depth index target, rfl⟩
  · rintro _ ⟨value, rfl⟩
    exact whole_orthogonal depth index target value

end
end SourceCopyCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
