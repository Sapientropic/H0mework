import H0mework.Fock.CopyComplete.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompleteGraph

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
noncomputable section
attribute [local instance] completeUniform completeMeasurable completeBorel completeT2

abbrev boundary : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.recover (SourceJointClockGraph.read (SourceClockComplex.ofNative (sourcePoint 0)))

theorem boundary_residual_nonzero (model depth bound : Nat) (index : Index depth) :
    SourceConditionalGraphDecoder.residual depth bound index (Hilbert.read model bound) boundary ≠ 0 := by
  intro zero
  have generated := SourceConditionalGraphDecoder.original_reconstruction depth bound index (Hilbert.read model bound) boundary
  rw [zero, add_zero] at generated
  apply SourceJointClockDecoder.root_recovery_not_finite
  refine ⟨SourceCopyGraph.complexAction depth index
    (word depth bound (SourceConditionalGraphDecoder.fieldDecode depth bound index (Hilbert.read model bound) boundary)), ?_⟩
  rw [← SourceCopyGraph.action_source]
  exact generated

end
end SourceCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
