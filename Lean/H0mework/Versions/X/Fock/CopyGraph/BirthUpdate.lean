import H0mework.Versions.X.Fock.CopyGraph.BirthField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphBirth

open SourceCopyProgram (Index)
open SourceGeneratedAcquisitionJoint (normalize)
open SourceOwnedObservationHistory
open SourceGraphGrowth (oldRead taggedRead)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def update (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  ((((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)⁻¹) • innerSL ℂ (innovation depth index read)).smulRight
    (innovation depth index read)

omit [MeasurableSingletonClass Observed] in
theorem update_apply (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    update depth index read value =
      (inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • innovation depth index read := by
  change ((((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)⁻¹) * inner ℂ (innovation depth index read) value) •
    innovation depth index read = _
  rw [div_eq_mul_inv, mul_comm]

theorem update_is_birth (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    update depth index read = SourceGraphGrowth.birthGain depth index read := by
  apply ContinuousLinearMap.ext
  intro value
  rw [update_apply, birth_formula]

theorem field_decoder_update (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    SourceConditionalGraphDecoder.fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value =
      normalize depth (depth + 1) (Nat.le_succ depth) (SourceConditionalGraphDecoder.fieldDecode depth depth index (oldRead depth read) value) +
        (inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • innovationField depth index read := by
  have generated := original_birth_formula depth index read value
  unfold SourceGraphGrowth.birthField at generated
  exact (sub_eq_iff_eq_add.mp generated).trans (add_comm _ _)

theorem growth_update_cost (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    ‖SourceGraphGrowth.newResidual depth index read value‖ ^ 2 +
        ‖inner ℂ (innovation depth index read) value‖ ^ 2 / ‖innovation depth index read‖ ^ 2 =
      ‖SourceGraphGrowth.oldResidual depth index read value‖ ^ 2 + ‖SourceGraphGrowth.forgettingLoss depth index read value‖ ^ 2 := by
  rw [← birth_cost]
  exact SourceGraphGrowth.growth_energy depth index read value

end
end SourceGraphBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
