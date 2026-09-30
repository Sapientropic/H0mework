import H0mework.Versions.X.Fock.CopyGraph.ColumnForcingObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRecordedEvolution

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead)
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2

def innovation (depth : Nat) (index : Index depth)
    (previous : SourceJointClockGraph.Carrier → FieldSpace depth depth) : SourceJointClockGraph.Carrier :=
  SourceGraphBirth.fresh depth index - SourceCopyGraph.action depth index
    (fieldRead depth depth (previous (SourceGraphBirth.fresh depth index)))

def direction (depth : Nat) (index : Index depth)
    (previous : SourceJointClockGraph.Carrier → FieldSpace depth depth) : FieldSpace (depth + 1) (depth + 1) :=
  SourceGraphBirth.freshField depth - normalize depth (depth + 1) (Nat.le_succ depth)
    (previous (SourceGraphBirth.fresh depth index))

def step (depth : Nat) (index : Index depth)
    (previous : SourceJointClockGraph.Carrier → FieldSpace depth depth)
    (target : SourceJointClockGraph.Carrier) : FieldSpace (depth + 1) (depth + 1) :=
  normalize depth (depth + 1) (Nat.le_succ depth) (previous target) +
    (inner ℂ (innovation depth index previous) target / ((‖innovation depth index previous‖ ^ 2 : ℝ) : ℂ)) •
      direction depth index previous

universe u
variable {Observed : Type u} [MeasurableSpace Observed]

theorem innovation_original (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    innovation depth index (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read)) =
      SourceGraphRecurrence.innovationFromPrevious depth index read
        (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read)) := by
  unfold innovation SourceGraphRecurrence.innovationFromPrevious SourceGraphRecurrence.predictionFromPrevious
  rw [ContinuousLinearMap.comp_apply, SourceGraphRecurrence.observed_canonical]
  change SourceGraphBirth.fresh depth index - SourceCopyGraph.action depth index
    (fieldRead depth depth (SourceConditionalGraphDecoder.realizeObserved depth depth (oldRead depth read)
      (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read) (SourceGraphBirth.fresh depth index)))) = _
  rw [SourceConditionalGraphDecoder.realized_action]

omit [MeasurableSpace Observed] in
theorem step_original (model depth : Nat) (index : Index depth) (target : SourceJointClockGraph.Carrier) :
    step depth index (SourceConditionalGraphDecoder.fieldDecode depth depth index (Hilbert.read model depth)) target =
      SourceCompleteGraph.step model depth index
        (SourceConditionalGraphDecoder.fieldDecode depth depth index (Hilbert.read model depth)) target := by
  rw [← SourceCompleteGraph.old_read_original]
  simp only [step, SourceCompleteGraph.step, innovation_original, add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, InnerProductSpace.rankOne_apply, smul_smul]
  change _ + (_ / _) • _ = _ + (_ * _) • _
  rw [div_eq_mul_inv, mul_comm]
  rfl

end
end SourceRecordedEvolution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
