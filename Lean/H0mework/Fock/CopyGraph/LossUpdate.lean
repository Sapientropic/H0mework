import H0mework.Fock.CopyGraph.LossEquation
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceCopyProgram (Index)
open SourceOwnedObservationHistory
open SourceGraphGrowth (oldRead newRead oldAction newAction)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def update (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)⁻¹) • InnerProductSpace.rankOne ℂ (direction depth index read) (direction depth index read)

omit [MeasurableSingletonClass Observed] in
theorem update_apply (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    update depth index read value =
      (inner ℂ (direction depth index read) value / ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)) • direction depth index read := by
  change (((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)⁻¹) • (inner ℂ (direction depth index read) value • direction depth index read) = _
  rw [smul_smul, div_eq_mul_inv, mul_comm]

theorem update_is_loss (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    update depth index read = SourceGraphGrowth.forgettingLoss depth index read := by
  apply ContinuousLinearMap.ext
  intro value
  rw [update_apply, loss_formula]

def prediction (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (oldAction depth index read).comp (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read)) +
    SourceGraphBirth.update depth index read - update depth index read

theorem prediction_source (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    prediction depth index read value =
      newAction depth index read
        (SourceConditionalGraphDecoder.decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value) := by
  unfold prediction
  rw [SourceGraphBirth.update_is_birth, update_is_loss]
  change oldAction depth index read (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read) value) +
    (SourceGraphGrowth.taggedAction depth index read (SourceConditionalGraphDecoder.decode (depth + 1) (depth + 1)
      (FamilyModel.Fock.oldIndex depth index) (SourceGraphGrowth.taggedRead depth read) value) -
        oldAction depth index read (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read) value)) -
    (SourceGraphGrowth.taggedAction depth index read (SourceConditionalGraphDecoder.decode (depth + 1) (depth + 1)
      (FamilyModel.Fock.oldIndex depth index) (SourceGraphGrowth.taggedRead depth read) value) -
        newAction depth index read (SourceConditionalGraphDecoder.decode (depth + 1) (depth + 1)
          (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value)) = _
  abel

theorem complete_budget (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    ‖SourceGraphGrowth.newResidual depth index read value‖ ^ 2 +
        ‖inner ℂ (SourceGraphBirth.innovation depth index read) value‖ ^ 2 / ‖SourceGraphBirth.innovation depth index read‖ ^ 2 =
      ‖SourceGraphGrowth.oldResidual depth index read value‖ ^ 2 +
        ‖inner ℂ (direction depth index read) value‖ ^ 2 / ‖direction depth index read‖ ^ 2 := by
  have original := SourceGraphBirth.growth_update_cost depth index read value
  rw [loss_cost] at original
  exact original

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
