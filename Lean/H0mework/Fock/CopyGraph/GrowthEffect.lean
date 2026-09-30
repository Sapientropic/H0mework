import H0mework.Fock.CopyGraph.GrowthNative
import H0mework.Fock.CopyGraph.GrowthField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceConditionalGraphDecoder (fieldDecode)
noncomputable section
local instance effectGrowthMeasurable : MeasurableSpace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock.ParentCarrier := ⊤

abbrev pulseField (depth : Nat) (index : Index depth) : FieldSpace depth depth :=
  SourceConditionalGraphDecoder.realizeObserved depth depth (oldRead depth (sourceRead depth index))
    (SourceConditionalCorrection.one depth (oldRead depth (sourceRead depth index)))

theorem pulse_field_read (depth : Nat) (index : Index depth) :
    SourceCopyGraph.action depth index (fieldRead depth depth (pulseField depth index)) = pulse depth index :=
  SourceConditionalGraphDecoder.realized_action depth depth index (oldRead depth (sourceRead depth index)) _

theorem pulse_field_residual (depth : Nat) (index : Index depth) :
    newResidual depth index (sourceRead depth index) (pulse depth index) =
      SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
        (fieldRead (depth + 1) (depth + 1) (normalize depth (depth + 1) (Nat.le_succ depth) (pulseField depth index) -
          fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth (sourceRead depth index)) (pulse depth index))) := by
  have original := new_original_residual depth index (sourceRead depth index) (pulseField depth index)
  dsimp only at original
  rw [pulse_field_read] at original
  exact original

theorem native_original_cost :
    (1 : ℝ) / 6 ≤ ‖SourceCopyGraph.action 3 (FamilyModel.Fock.oldIndex 2 (0 : Index 2))
      (fieldRead 3 3 (normalize 2 3 (Nat.le_succ 2) (pulseField 2 (0 : Index 2)) -
        fieldDecode 3 3 (FamilyModel.Fock.oldIndex 2 (0 : Index 2)) (newRead 2 (sourceRead 2 (0 : Index 2))) (pulse 2 (0 : Index 2))))‖ ^ 2 := by
  have same := congrArg (fun value : SourceJointClockGraph.Carrier => ‖value‖ ^ 2) (pulse_field_residual 2 (0 : Index 2))
  with_reducible exact native_forgotten_cost.trans_eq same

theorem native_tagged_field (depth : Nat) (index : Index depth) :
    fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth (sourceRead depth index)) (pulse depth index) =
      normalize depth (depth + 1) (Nat.le_succ depth) (pulseField depth index) :=
  tagged_field_recovery depth index (sourceRead depth index) _

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
