import H0mework.Physics.ScalarJets.ActionResponseOperator
import H0mework.Physics.DualVariation.RecenteredScalarSecondJetActionResponse

/-!
# Fixed P506/L0 scalar second-jet response regression

The generic producer is defined and exported without the recentered
historical chain.  This module imports that chain only to prove exact recovery
of the established fixed P506/L0 scalar response.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineScalarActionSecondJetLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

theorem genericDiracDualScalarTemporalDemandCoordinate_fixed
    (space : StageNineSpatialPoint) :
    genericDiracDualScalarTemporalDemandCoordinate
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) =
      scalarActionRealDual
        (recenteredContactDiracDualScalarTemporalDemandDual space) := by
  rfl

theorem genericDiracDualScalarTemporalDemandDual_fixed
    (space : StageNineSpatialPoint) :
    genericDiracDualScalarTemporalDemandDual
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) =
      recenteredContactDiracDualScalarTemporalDemandDual space := by
  apply LinearMap.ext
  intro direction
  change
    scalarCoordinatePairingRe direction
        (genericDiracDualScalarTemporalDemandCoordinate
          positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space)) =
      recenteredContactDiracDualScalarTemporalDemandDual space direction
  rw [genericDiracDualScalarTemporalDemandCoordinate_fixed,
    scalarCoordinatePairingRe_actionRealDual]

theorem genericDiracDualScalarGeneratedAcceleration_fixed
    (space : StageNineSpatialPoint) :
    genericDiracDualScalarGeneratedAcceleration
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) =
      recenteredContactDiracDualScalarAcceleration space := by
  unfold genericDiracDualScalarGeneratedAcceleration
    recenteredContactDiracDualScalarAcceleration
  rw [genericDiracDualScalarTemporalDemandDual_fixed]

theorem genericDiracDualScalarSecondJetActionResponse_fixed
    (space : StageNineSpatialPoint) :
    genericDiracDualScalarSecondJetActionResponse
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) =
      installScalarQuadraticTimeCorrection
        (recenteredCartanRepairedConstitutiveCurrent space)
        (recenteredContactDiracDualScalarAcceleration space) := by
  unfold genericDiracDualScalarSecondJetActionResponse
    installScalarQuadraticTimeCorrection
  rw [genericDiracDualScalarGeneratedAcceleration_fixed]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
