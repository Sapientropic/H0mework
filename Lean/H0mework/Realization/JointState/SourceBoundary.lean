import H0mework.Realization.JointState.ActionOccurrence

/-!
# Source boundary of one generated joint action

The covariance incidence compares the evolved seed with the source-action
seed, so its integral face is definitionally zero.  The same input also
generates the before/after source boundary

`seed(e) - seed(Ae)`.

This second dependent face retains the actual integral update.  It is not a
section chosen from a coherent or measurement residual.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedIntegralCoherentJointAction

noncomputable section

universe i h q

variable {I : Type i} {H : Type h} {Q : Type q}
variable [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]

namespace Input

/-- Actual before/after boundary of the source event inside the same joint
carrier. -/
def sourceBoundary (input : Input I H Q) (event : I) : input.Carrier :=
  input.seedLift event - input.seedLift (input.integralAction event)

@[simp] theorem sourceBoundary_integralFace
    (input : Input I H Q) (event : I) :
    input.integralFace (input.sourceBoundary event) =
      event - input.integralAction event := by
  rfl

@[simp] theorem sourceBoundary_coherentFace
    (input : Input I H Q) (event : I) :
    input.coherentFace (input.sourceBoundary event) =
      input.coherentRead event -
        input.coherentRead (input.integralAction event) := by
  rfl

@[simp] theorem sourceBoundary_measurementFace
    (input : Input I H Q) (event : I) :
    input.measurementFace (input.sourceBoundary event) =
      input.measurementRead event -
        input.measurementRead (input.integralAction event) := by
  rfl

/-- Under an actually fixed measurement action, the source boundary and the
covariance incidence have the same measurement shadow. -/
theorem sourceBoundary_measurement_eq_incidence
    (input : Input I H Q) (event : I)
    (measurement_fixed :
      input.measurementAction (input.measurementRead event) =
        input.measurementRead event) :
    input.measurementFace (input.sourceBoundary event) =
      input.measurementFace (input.incidenceResidual event) := by
  rw [sourceBoundary_measurementFace,
    incidenceResidual_measurementFace, measurement_fixed]

theorem sourceBoundary_eq_zero_iff
    (input : Input I H Q) (event : I) :
    input.sourceBoundary event = 0 ↔
      event = input.integralAction event := by
  rw [sourceBoundary, sub_eq_zero]
  exact input.seedLift_injective.eq_iff

/-- The source boundary forms its own accounted face over the original event
tree; no new occurrence source is introduced. -/
def sourceBoundaryOccurrence (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    RootedAccountedUnfolding input.Carrier :=
  occurrence.map input.sourceBoundary

theorem sourceBoundaryOccurrence_integral_readback
    (input : Input I H Q) (occurrence : RootedAccountedUnfolding I) :
    (input.sourceBoundaryOccurrence occurrence).map input.integralFace =
      occurrence.map (fun event => event - input.integralAction event) := by
  rw [sourceBoundaryOccurrence, RootedAccountedUnfolding.map_map]
  rfl

theorem sourceBoundaryOccurrence_measurement_readback
    (input : Input I H Q) (occurrence : RootedAccountedUnfolding I) :
    (input.sourceBoundaryOccurrence occurrence).map input.measurementFace =
      occurrence.map (fun event => input.measurementRead event -
        input.measurementRead (input.integralAction event)) := by
  rw [sourceBoundaryOccurrence, RootedAccountedUnfolding.map_map]
  rfl

end Input

end

end SourceGeneratedIntegralCoherentJointAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
