import H0mework.Versions.X.Fock.CopyGraph.TemporalBoundaryBoundary

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalBoundary

open SourceCopyProgram (Index)
open SourceCopyTimeModel (Packet finitePhases)
open SourceCopyTimeGram (analysis decode residual model finiteDecode)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem decode_add (depth : Nat) (index : Index depth) (left right : Packet depth index) :
    decode depth index (left + right) = decode depth index left + decode depth index right := by
  apply SourceCopyTimeGram.normal_injective depth index
  change (analysis depth index).adjoint (analysis depth index (decode depth index (left + right))) =
    (analysis depth index).adjoint (analysis depth index (decode depth index left + decode depth index right))
  rw [SourceCopyTimeGram.normal_equation, WithLp.toLp_add, map_add, map_add, map_add,
    SourceCopyTimeGram.normal_equation, SourceCopyTimeGram.normal_equation]

theorem model_add (depth : Nat) (index : Index depth) (left right : Packet depth index) :
    model depth index (left + right) = model depth index left + model depth index right := by
  rw [SourceCopyTimeGram.model, decode_add, map_add]
  rfl

theorem actual_decoder_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    finiteDecode runtime index steps (SourceJointClockGraph.action target) -
      SourceJointClockGraph.action (finiteDecode runtime index steps target) =
    decode (inventoryBound runtime) index (SourceCopyTimeModel.next (inventoryBound runtime) index
      (WithLp.ofLp (residual (inventoryBound runtime) index (finitePhases runtime index steps target)))) +
    decode (inventoryBound runtime) index (lastCell (inventoryBound runtime) index (boundary runtime index steps target)) := by
  unfold finiteDecode
  rw [finite_next, decode_add]
  have old := SourceCopyTimeGram.next_correction (inventoryBound runtime) index (finitePhases runtime index steps target)
  rw [← old]
  abel

theorem actual_model_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    model (inventoryBound runtime) index (finitePhases runtime index steps (SourceJointClockGraph.action target)) =
      SourceCopyTimeModel.modelStep (inventoryBound runtime) index
        (model (inventoryBound runtime) index (finitePhases runtime index steps target)) +
      SourceCopyTimeModel.modelPoint (inventoryBound runtime) index
        (decode (inventoryBound runtime) index (SourceCopyTimeModel.next (inventoryBound runtime) index
          (WithLp.ofLp (residual (inventoryBound runtime) index (finitePhases runtime index steps target))))) +
      model (inventoryBound runtime) index (lastCell (inventoryBound runtime) index (boundary runtime index steps target)) := by
  rw [finite_next, model_add, SourceCopyTimeGram.model_next_correction]

theorem native_decoder_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    finiteDecode runtime index steps (SourceJointClockGraph.read
      (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next))) -
      SourceJointClockGraph.action (finiteDecode runtime index steps (SourceJointClockGraph.read
        (SourceClockComplex.ofNative (SourceOperationNative.point runtime)))) =
    decode (inventoryBound runtime) index (SourceCopyTimeModel.next (inventoryBound runtime) index
      (WithLp.ofLp (residual (inventoryBound runtime) index (finitePhases runtime index steps
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))))))) +
    decode (inventoryBound runtime) index (lastCell (inventoryBound runtime) index (boundary runtime index steps
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))))) := by
  rw [← SourceJointClockGraph.native_next runtime]
  exact actual_decoder_next runtime index steps _

end
end SourceCopyTemporalBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
