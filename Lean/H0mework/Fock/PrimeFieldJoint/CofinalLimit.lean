import H0mework.Fock.PrimeFieldJoint.CofinalProjection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointDecoderCofinal

open SourceGeneratedAcquisitionContinuation
open Filter
open scoped Topology
noncomputable section

def estimate (bound : Nat) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (SourceJointFiniteDecoder.read bound).comp (SourceJointFiniteDecoder.decode bound)

theorem predictions_tendsto (round : Nat) (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun future => SourceJointFiniteDecoder.action (inventoryBound (roundRuntime (round + future)))
      (SourceJointFiniteDecoder.decode (inventoryBound (roundRuntime (round + future))) target)) atTop
        (𝓝 (SourceJointClockGraph.action (SourceJointClockGraph.recover target))) := by
  let _ : ∀ future : Nat, (images round future).HasOrthogonalProjection := by
    intro future
    let _ : CompleteSpace (images round future) :=
      (SourceJointFiniteDecoder.source_antilipschitz (inventoryBound (roundRuntime (round + future)))).completeSpace_range_clm
    infer_instance
  let _ : CompleteSpace ((⨆ future : Nat, images round future).topologicalClosure) :=
    (⨆ future : Nat, images round future).isClosed_topologicalClosure.isComplete.completeSpace_coe
  have original := Submodule.starProjection_tendsto_closure_iSup (images round) (images_mono round) target
  simpa only [whole_image, whole_projection, images, finite_projection] using original

theorem estimate_tendsto (round : Nat) (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun future => estimate (inventoryBound (roundRuntime (round + future))) target) atTop
      (𝓝 (SourceJointClockGraph.recover target)) := by
  have recovered := SourceJointClockGraph.recover.continuous.continuousAt.tendsto.comp
    (predictions_tendsto round target)
  simpa only [Function.comp_def, SourceJointFiniteDecoder.action, ContinuousLinearMap.comp_apply,
    SourceJointClockGraph.recover_action, estimate] using recovered

theorem residual_formula (bound : Nat) (target : SourceJointClockGraph.Carrier) :
    SourceJointFiniteDecoder.residual bound target =
      target - SourceJointFiniteDecoder.action bound (SourceJointFiniteDecoder.decode bound target) := by
  rw [SourceJointFiniteDecoder.encoded_decode]
  rfl

theorem residual_tendsto (round : Nat) (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun future => SourceJointFiniteDecoder.residual (inventoryBound (roundRuntime (round + future))) target) atTop
      (𝓝 (SourceJointClockGraph.residual target)) := by
  have retained := (tendsto_const_nhds (x := target)).sub (predictions_tendsto round target)
  change Tendsto _ atTop (𝓝 (target - SourceJointClockGraph.action (SourceJointClockGraph.recover target)))
  simpa only [residual_formula] using retained

theorem cost_tendsto (round : Nat) (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun future => ‖SourceJointFiniteDecoder.residual (inventoryBound (roundRuntime (round + future))) target‖ ^ 2)
      atTop (𝓝 (‖SourceJointClockGraph.residual target‖ ^ 2)) :=
  ((residual_tendsto round target).norm).pow 2

end
end SourceJointDecoderCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
