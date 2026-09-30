import H0mework.Fock.CopyGraph.FibreGeometry
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphFibreUpdate

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead oldAction newAction)
open scoped Classical
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def update (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)⁻¹) • InnerProductSpace.rankOne ℂ (normal depth index read supported) (normal depth index read supported)

theorem update_apply (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : SourceJointClockGraph.Carrier) :
    update depth index read supported value =
      (inner ℂ (normal depth index read supported) value / ((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)) • normal depth index read supported := by
  change (((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)⁻¹) •
    (inner ℂ (normal depth index read supported) value • normal depth index read supported) = _
  rw [smul_smul, div_eq_mul_inv, mul_comm]

theorem update_is_loss (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    update depth index read supported = SourceGraphGrowth.forgettingLoss depth index read := by
  apply ContinuousLinearMap.ext
  intro value
  rw [update_apply, normal_loss_formula depth index read supported]

def sourceUpdate (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  if supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support then update depth index read supported else 0

theorem source_update_is_loss (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    sourceUpdate depth index read = SourceGraphGrowth.forgettingLoss depth index read := by
  by_cases supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support
  · rw [sourceUpdate, dif_pos supported]
    exact update_is_loss depth index read supported
  · rw [sourceUpdate, dif_neg supported]
    have novel : read (depth + 1) ∉ atoms (historyPMF depth) (oldRead depth read) := fun present =>
      supported ((atoms_iff _ _ _).mp present)
    have vanished := SourceGraphLoss.novel_direction_zero depth index read novel
    apply ContinuousLinearMap.ext
    intro value
    rw [SourceGraphLoss.loss_direction, vanished, smul_zero]
    rfl

def prediction (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (oldAction depth index read).comp (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read)) +
    SourceGraphBirth.update depth index read - sourceUpdate depth index read

theorem prediction_source (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    prediction depth index read value = newAction depth index read
      (SourceConditionalGraphDecoder.decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value) := by
  have same : prediction depth index read = SourceGraphLoss.prediction depth index read := by
    unfold prediction SourceGraphLoss.prediction
    rw [source_update_is_loss, SourceGraphLoss.update_is_loss]
  rw [same]
  exact SourceGraphLoss.prediction_source depth index read value

end
end SourceGraphFibreUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
