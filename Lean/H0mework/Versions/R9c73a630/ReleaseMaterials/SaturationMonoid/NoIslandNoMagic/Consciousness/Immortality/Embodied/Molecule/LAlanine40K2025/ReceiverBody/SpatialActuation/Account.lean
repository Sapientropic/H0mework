import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Joins
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Gamma

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
noncomputable section

def wholeBodyAccount (body : ReceiverBody.Runtime.ActuationResult) : ℝ :=
  Live.freeEnergy body.resource.quantum+Live.entropyProduction body.resource.quantum+
    Extract.Port.kinetic body.resource.momentum+(body.frame.total : ℝ)

theorem generated_account : wholeBodyAccount generatedBody=wholeBodyAccount input.body :=
  FiniteContinuation.next_whole_account input input_admissible

theorem generated_positive_stock : 0 < generatedBody.resource.momentum :=
  (half_pos (FiniteContinuation.stock_positive input input_admissible)).trans
    (FiniteContinuation.next_stock input input_admissible)

theorem generated_positive_work :
    0 < SIWork.energyJoule*(input.body.resource.momentum-generatedBody.resource.momentum) :=
  SIWork.work_positive input input_admissible

theorem generated_work_from_body :
    SIWork.energyJoule*(input.body.resource.momentum-generatedBody.resource.momentum)=
      SIWork.energyJoule*((generatedBody.frame.total : ℝ)-(input.body.frame.total : ℝ)) :=
  SIWork.work_from_body input input_admissible

theorem generated_engine_residual :
    (SIWork.engineHartreeJouleQ : ℝ)*((generatedBody.frame.total : ℝ)-(input.body.frame.total : ℝ))=
      SIWork.energyJoule*(input.body.resource.momentum-generatedBody.resource.momentum)+
        SIWork.engineEnergyResidual*((generatedBody.frame.total : ℝ)-(input.body.frame.total : ℝ)) :=
  SIWork.work_engine_residual input input_admissible

theorem generated_receiver_integral :
    generatedBody.resource.momentum-input.body.resource.momentum=
      (∫ t in (0 : ℝ)..duration, receiverForce .enter t)+
      (∫ t in (0 : ℝ)..duration, receiverForce .drive t)+
      (∫ t in (0 : ℝ)..duration, receiverForce .leave t) :=
  FiniteContinuation.total_receiver_update input input_admissible

theorem generated_momentum_integral (i : Coordinate) :
    (generatedBody.frame.momentum i.1 i.2 : ℝ)-(input.body.frame.momentum i.1 i.2 : ℝ)=
      (∫ t in (0 : ℝ)..duration, force .enter t i)+
      (∫ t in (0 : ℝ)..duration, force .drive t i)+
      (∫ t in (0 : ℝ)..duration, force .leave t i) :=
  FiniteContinuation.total_momentum_update input input_admissible i

theorem generated_clocks :
    generatedBody.resource.quantum.localClock=28*Propagation.Producer.nativeClockStep ∧
    generatedBody.bodyClock=13*Propagation.Producer.nativeClockStep := by
  have source : input=FiniteContinuation.Runtime.readCurrent (FiniteContinuation.Runtime.atDepth 1) :=
    SIWork.Runtime.first_same_current
  have clocks := FiniteContinuation.Runtime.clocks_at_depth 1
  have next := FiniteContinuation.next_clocks input
  change generatedBody.resource.quantum.localClock=input.body.resource.quantum.localClock+3*Propagation.Producer.nativeClockStep ∧
    generatedBody.bodyClock=input.body.bodyClock+3*Propagation.Producer.nativeClockStep at next
  rw [source,clocks.1,clocks.2] at next
  norm_num only [Nat.cast_one] at next
  constructor <;> nlinarith only [next.1,next.2]

theorem generated_history_joule :
    SIWork.energyJoule*wholeBodyAccount generatedBody=
      SIWork.wholeAccountJoule (SIWork.Runtime.readCurrent (SIWork.Runtime.atDepth 1)) := by
  rw [generated_account]
  rfl

theorem source_position_not_reused :
    ¬ FiniteContinuation.Admissible ⟨generatedBody,(FiniteContinuation.nextMaterial input).reserve⟩ := by
  intro valid
  apply generated_nonreturning
  exact valid.position.trans input_admissible.position.symm

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
