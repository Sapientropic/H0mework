import H0mework.Fock.CopyGraph.RecurrencePrevious

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRecurrence

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead)
open scoped Classical
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def arrival (depth : Nat) (read : Nat → Observed)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    SourceJointClockGraph.Carrier →L[ℂ] ℂ :=
  ((Real.sqrt (SourceHistoryGrowth.fraction depth (depth + 1)))⁻¹ : ℂ) •
    ((SourceGeneratedAtomicObservation.evalAtContinuous
      (observed (historyPMF depth) (oldRead depth read)) (read (depth + 1)) supported).comp
        (observedFromPrevious depth read previous))

def beta (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) : ℂ :=
  1 + arrival depth read previous supported (SourceGraphBirth.fresh depth index)

def normal (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    SourceJointClockGraph.Carrier :=
  (star (beta depth index read previous supported) /
    ((‖innovationFromPrevious depth index read previous‖ ^ 2 : ℝ) : ℂ)) •
      innovationFromPrevious depth index read previous - (arrival depth read previous supported).adjoint 1

def innovationField (depth : Nat) (index : Index depth)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth) :
    FieldSpace (depth + 1) (depth + 1) :=
  SourceGraphBirth.freshField depth - normalize depth (depth + 1) (Nat.le_succ depth)
    (previous (SourceGraphBirth.fresh depth index))

def normalField (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    FieldSpace (depth + 1) (depth + 1) :=
  (star (beta depth index read previous supported) /
    ((‖innovationFromPrevious depth index read previous‖ ^ 2 : ℝ) : ℂ)) • innovationField depth index previous -
      normalize depth (depth + 1) (Nat.le_succ depth) (previous ((arrival depth read previous supported).adjoint 1))

def step (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (previous : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth depth) :
    SourceJointClockGraph.Carrier →L[ℂ] FieldSpace (depth + 1) (depth + 1) :=
  (normalize depth (depth + 1) (Nat.le_succ depth)).comp previous +
    (((‖innovationFromPrevious depth index read previous‖ ^ 2 : ℝ) : ℂ)⁻¹) •
      InnerProductSpace.rankOne ℂ (innovationField depth index previous)
        (innovationFromPrevious depth index read previous) -
    if supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support then
      (((‖normal depth index read previous supported‖ ^ 2 : ℝ) : ℂ)⁻¹) •
        InnerProductSpace.rankOne ℂ (normalField depth index read previous supported)
          (normal depth index read previous supported) else 0

theorem arrival_canonical (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    arrival depth read (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read)) supported =
      SourceGraphFibreUpdate.arrival depth index read supported := by
  rw [arrival, observed_canonical]
  rfl

theorem beta_canonical (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    beta depth index read (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read)) supported =
      SourceGraphFibreUpdate.beta depth index read supported := by
  rw [beta, arrival_canonical]
  rfl

theorem normal_canonical (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    normal depth index read (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read)) supported =
      SourceGraphFibreUpdate.normal depth index read supported := by
  rw [normal, beta_canonical, innovation_canonical, arrival_canonical]
  rfl

omit [MeasurableSingletonClass Observed] in
theorem innovation_field_canonical (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    innovationField depth index (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read)) =
      SourceGraphBirth.innovationField depth index read := rfl

theorem normal_field_canonical (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    normalField depth index read (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read)) supported =
      SourceGraphFibreUpdate.normalField depth index read supported := by
  rw [normalField, beta_canonical, innovation_canonical, innovation_field_canonical, arrival_canonical]
  rfl

theorem step_canonical (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    step depth index read (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read)) =
      SourceConditionalGraphDecoder.fieldDecode (depth + 1) (depth + 1)
        (FamilyModel.Fock.oldIndex depth index) (newRead depth read) := by
  rw [← SourceGraphFibreUpdate.field_recovery_linear]
  simp only [step, innovation_canonical, innovation_field_canonical, normal_canonical, normal_field_canonical]
  rfl

end
end SourceGraphRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
