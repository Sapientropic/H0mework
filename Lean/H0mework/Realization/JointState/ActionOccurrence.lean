import H0mework.Realization.JointState.ActionOrbit
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Accounted occurrence of one source-generated joint action

The actual event occurrence is mapped once into the minimal orbit carrier.
Its integral, coherent and measurement faces read back the existing event
tree, while applying the single joint action produces the three corresponding
evolved faces.  These are dependent projections of one occurrence, not three
parallel action tables.
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

def jointOccurrence (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    RootedAccountedUnfolding input.Carrier :=
  occurrence.map input.seedLift

def evolvedJointOccurrence (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    RootedAccountedUnfolding input.Carrier :=
  (input.jointOccurrence occurrence).map input.omega

theorem jointOccurrence_integral_rooted (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    (input.jointOccurrence occurrence).map input.integralFace = occurrence := by
  rw [jointOccurrence, RootedAccountedUnfolding.map_map]
  change occurrence.map id = occurrence
  exact RootedAccountedUnfolding.map_id occurrence

theorem jointOccurrence_coherent_readback (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    (input.jointOccurrence occurrence).map input.coherentFace =
      occurrence.map input.coherentRead := by
  rw [jointOccurrence, RootedAccountedUnfolding.map_map]
  rfl

theorem jointOccurrence_measurement_readback (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    (input.jointOccurrence occurrence).map input.measurementFace =
      occurrence.map input.measurementRead := by
  rw [jointOccurrence, RootedAccountedUnfolding.map_map]
  rfl

/-- Applying `Ω` once and then projecting to the integral face is exactly
the original integral action occurrence. -/
theorem evolvedJointOccurrence_integral_readback (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    (input.evolvedJointOccurrence occurrence).map input.integralFace =
      occurrence.map input.integralAction := by
  rw [evolvedJointOccurrence, RootedAccountedUnfolding.map_map,
    jointOccurrence, RootedAccountedUnfolding.map_map]
  rfl

/-- Coherent evolution is the coherent face of the same `Ω` occurrence. -/
theorem evolvedJointOccurrence_coherent_readback (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    (input.evolvedJointOccurrence occurrence).map input.coherentFace =
      occurrence.map (input.coherentAction.comp input.coherentRead) := by
  rw [evolvedJointOccurrence, RootedAccountedUnfolding.map_map,
    jointOccurrence, RootedAccountedUnfolding.map_map]
  rfl

/-- Measurement/q-rich evolution is the third face of the same occurrence. -/
theorem evolvedJointOccurrence_measurement_readback (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    (input.evolvedJointOccurrence occurrence).map input.measurementFace =
      occurrence.map (input.measurementAction.comp input.measurementRead) := by
  rw [evolvedJointOccurrence, RootedAccountedUnfolding.map_map,
    jointOccurrence, RootedAccountedUnfolding.map_map]
  rfl

/-- The generated incidence residual itself forms one accounted face. -/
def residualOccurrence (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    RootedAccountedUnfolding input.Carrier :=
  occurrence.map input.incidenceResidual

theorem residualOccurrence_integral_zero (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    (input.residualOccurrence occurrence).map input.integralFace =
      occurrence.map (0 : I → I) := by
  rw [residualOccurrence, RootedAccountedUnfolding.map_map]
  apply congrArg (fun transform : I → I => occurrence.map transform)
  funext event
  exact input.incidenceResidual_integralFace event

/-- The coherent covariance mismatch is not recomputed beside the joint
occurrence: it is the coherent projection of its one residual face. -/
theorem residualOccurrence_coherent_readback (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    (input.residualOccurrence occurrence).map input.coherentFace =
      occurrence.map (fun event =>
        input.coherentAction (input.coherentRead event) -
          input.coherentRead (input.integralAction event)) := by
  rw [residualOccurrence, RootedAccountedUnfolding.map_map]
  rfl

/-- The detector/q-rich mismatch is the measurement projection of the same
residual occurrence. -/
theorem residualOccurrence_measurement_readback (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I) :
    (input.residualOccurrence occurrence).map input.measurementFace =
      occurrence.map (fun event =>
        input.measurementAction (input.measurementRead event) -
          input.measurementRead (input.integralAction event)) := by
  rw [residualOccurrence, RootedAccountedUnfolding.map_map]
  rfl

/-- Every lawful observer of the common state tree is the unique rooted fold;
the three projections do not acquire independent observer authority. -/
theorem jointOccurrence_readout_unique
    (input : Input I H Q)
    (occurrence : RootedAccountedUnfolding I)
    {Readout : Type*}
    (atOccurrence : input.Carrier → List Readout → Readout)
    (candidate : RootedAccountedUnfolding input.Carrier → Readout)
    (commutes : ∀ origin branches,
      candidate (RootedAccountedUnfolding.occur origin branches) =
        atOccurrence origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate (input.jointOccurrence occurrence) =
      (input.jointOccurrence occurrence).fold atOccurrence :=
  RootedAccountedUnfolding.fold_unique atOccurrence candidate commutes _

end Input
end

end SourceGeneratedIntegralCoherentJointAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
