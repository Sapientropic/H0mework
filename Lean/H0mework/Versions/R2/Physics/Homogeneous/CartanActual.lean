import H0mework.Versions.R2.Physics.Homogeneous.CartanSource
import H0mework.Physics.Homogeneous.Gravity
import H0mework.Versions.R2.Physics.SpinPair.Actual

/-! The source phase products generate the actual constant Cartan connection.
Its holonomic curvature and reaction are read from the same reduced field. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeCoframeLocalVariation StageNineCartanTangentSimplicityResponse
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineBlockwiseConstitutive
open StageNineTopologicalFourFormPairing Stage9C.Dynamics.Homogeneous

noncomputable section

theorem actual_gravityConnection :
    actual.gravityConnection = fun _ => homogeneousConnection spinScale := by
  funext point
  have generated : actual.gravityConnection point =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource actual point :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
      positiveSmoothUnifiedSource _ point
  rw [generated]
  exact homogeneousConnection_generated actual point lapse spinScale lapse_pos
    (upperPhase point) (lowerPhase point) (upperDualPhase point) (lowerDualPhase point)
    actual_coframe (congrFun actual_matter point) (congrFun actual_conjugateMatter point)
    (upperDual_lower_product point) (lowerDual_upper_product point)

theorem actual_gravityCurvature (point : BasePoint) :
    holonomicGravityCurvature actual point = homogeneousCurvature spinScale :=
  homogeneousCurvature_actual actual spinScale actual_gravityConnection point

theorem actual_gravitySimplicityMultiplier :
    actual.gravitySimplicityMultiplier = fun _ => homogeneousGravityReaction lapse spinScale := by
  have generated : actual.gravitySimplicityMultiplier = formNativeGravityReactionField actual :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
      positiveSmoothUnifiedSource _
  rw [generated]
  funext point
  change gravityInternalDualEquiv (physicalIIPlusBivector (actual.coframe point)) -
    gravityInternalPairVarianceNormalization (holonomicGravityCurvature actual point) = _
  simp only [actual_coframe, actual_gravityCurvature, homogeneousGravityReaction]

theorem actual_gravityReaction_coordinates (point : BasePoint) (row column : LorentzianIndex) :
    formNativeCoframeConstraintReaction (toContinuumPointField actual point)
      (Matrix.single row column 1) =
      if row = column then if row = 0 then -3 else lapse else 0 := by
  change gravityTopologicalWedgeCoefficient (actual.gravitySimplicityMultiplier point)
    (physicalIIPlusCoframeTangent (actual.coframe point) (Matrix.single row column 1)) = _
  simp only [actual_gravitySimplicityMultiplier, actual_coframe,
    homogeneousGravityReaction_coordinates, spinScale_sq]
  split_ifs <;> ring

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
