import H0mework.Physics.SynchronizedJoint.Response
import H0mework.Physics.Exterior.FullSynchronizedActionResponseOperatorReadout

/-!
# Field readouts of the full-synchronized Lorentz first-jet lift

These projection lemmas keep downstream matter calculations from unfolding
the full coframe/P286/matter/Lorentz producer graph.  The Lorentz first-jet
installer changes only the gravity auxiliary field; the canonical P286 and
primal-matter response legs leave the synchronized gravity connection,
base auxiliary, and already generated adjoint field unchanged.

This module is a readout boundary only.  It generates no response, residual
value, equation certificate, or fixed-point claim.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentFullSynchronizedLorentzMatterReadout

open StageNineCanonicalLocalFullActionResponseOperator
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedLorentzResponse
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineFullSynchronizedCompleteP286ActionResponseOperator
open StageNineHolonomicField
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterActionTimeVelocity

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

@[simp] theorem currentFullSynchronizedLorentzActualFirstJetLift_matter
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentFullSynchronizedLorentzActualFirstJetLift source current
      space).matter =
      (currentCanonicalFullActionActual source current space).matter :=
  rfl

@[simp] theorem
    currentFullSynchronizedLorentzActualFirstJetLift_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentFullSynchronizedLorentzActualFirstJetLift source current
      space).conjugateMatter =
      (currentCanonicalFullActionActual source current
        space).conjugateMatter :=
  rfl

theorem currentCanonicalFullActionActual_matter_eq_complete
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionActual source current space).matter =
      (actionGeneratedMatterCompleteFirstGermActual source
        (actionGeneratedMatterTemporalFirstGermActual source
          (currentP286CompleteActionResponseOperator source
            (fullSynchronizedActionResponseOperator source
              (currentCanonicalFullActionBaseActual source current space))))
        ).matter := by
  rfl

theorem fullSynchronizedActionResponseOperator_matter_eq_localField
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionResponseOperator source current).matter =
      actionGeneratedMatterLocalField
        (fullSynchronizedActionMatterCauchyState source current) 0 := by
  rfl

theorem currentCanonicalFullActionActual_conjugateMatter_eq_synchronized
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionActual source current space).conjugateMatter =
      (fullSynchronizedActionResponseOperator source
        (currentCanonicalFullActionBaseActual source current space)
        ).conjugateMatter := by
  unfold currentCanonicalFullActionActual
    canonicalLocalFullActionResponseOperator
    actionGeneratedMatterCompleteFirstGermActual
  rw [installMatterCompleteFirstGermResponse_conjugateMatter]
  unfold canonicalLocalFullActionTemporalMatterActual
    actionGeneratedMatterTemporalFirstGermActual
  rw [installMatterTemporalFirstGermResponse_conjugateMatter]
  unfold canonicalLocalFullActionP286Actual
    fullSynchronizedCompleteP286ActionResponseOperator
  rw [currentP286CompleteActionResponseOperator_conjugateMatter]

theorem currentCanonicalFullActionActual_conjugateMatter_eq_localField
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionActual source current space).conjugateMatter =
      actionGeneratedConjugateMatterLocalField
        (fullSynchronizedActionMatterCauchyState source
          (currentCanonicalFullActionBaseActual source current space))
        0 := by
  rw [
    currentCanonicalFullActionActual_conjugateMatter_eq_synchronized]
  rfl

@[simp] theorem
    currentCanonicalFullActionActual_gravityConnection_eq_synchronized
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionActual source current space).gravityConnection =
      (fullSynchronizedActionResponseOperator source
        (currentCanonicalFullActionBaseActual source current space)
        ).gravityConnection := by
  rfl

@[simp] theorem
    currentCanonicalFullActionActual_gravityAuxiliary_eq_base
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionActual source current space).gravityAuxiliary =
      (currentCanonicalFullActionBaseActual source current
        space).gravityAuxiliary := by
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentFullSynchronizedLorentzMatterReadout
