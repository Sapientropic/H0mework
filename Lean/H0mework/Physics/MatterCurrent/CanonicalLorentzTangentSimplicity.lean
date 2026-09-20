import H0mework.Physics.Cartan.CartanTangentSimplicityResponse
import H0mework.Physics.MatterCurrent.CanonicalLorentzOriginProvenance

/-!
# C3h190: same-actual Lorentz tangent-simplicity closure

C3h189 installed the complete finite Lorentz momentum response in the same
local actual that carries the action-generated connection response.  C3h190's
exact provenance theorem proves that this momentum response is zero on the
generated P506/L0 current.  Consequently the installer leaves the already
simple auxiliary field fixed, without changing or rebuilding the actual:

```text
exact P506/L0 current
→ complete 18-coordinate Lorentz momentum velocity = 0
→ C3h189 auxiliary velocity = 0
→ B(x) = II⁺(1) and e(x) = 1 on the same actual
→ Ḃ = D II⁺(e)[ė].
```

The pointwise gravity-simplicity equation and its tangent law are independent
acceptance results: neither is stored in the source or supplied to the C3h189
constructor.  The connection leg remains the previously generated
linear-Plebanski response.  This module does not assert temporal Lorentz Gauss,
all-direction stationarity, an event transition, a branch, or a global
source-time evolution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzTangentSimplicity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNinePlebanskiMultiplierVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalGravityPreservingLorentzDualResponse
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzActualFirstJetLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzOriginProvenance
open StageNineSourceActionGeneratedP506MatterCurrentCompleteFirstGermCanonicalPrimitiveCauchyUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-- The exact 18-coordinate zero response makes the C3h189 auxiliary
embedding itself zero at every contact. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzAuxiliaryVelocity_eq_zero
    (space : StageNineSpatialPoint) :
    currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        space =
      0 := by
  unfold currentCanonicalFullActionLorentzAuxiliaryVelocity
  rw [positiveP506MatterCurrentCanonicalGravityPreservingLorentzSpatialBFMomentumActionCoordinates_eq_zero]
  funext internalPair spacetimePair
  fin_cases spacetimePair <;>
    simp [lorentzSpatialAuxiliaryVelocityEmbedding]

/-- The coframe of the same C3h189 actual is the exact identity coframe on its
whole local germ. -/
theorem positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift space).coframe
        point =
      1 :=
  currentCanonicalFullActionLorentzActualFirstJetLift_coframe_one
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
    space
    (positiveP506MatterCurrentCompleteFirstGermCanonicalGeneratedZeroResponseState_coframe_one
      space)
    point

/-- The same actual's gravity auxiliary remains the simple `II⁺(1)` field at
every local point. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gravityAuxiliary_simple
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
      space).gravityAuxiliary point =
      physicalIIPlusBivector 1 := by
  change
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
      space).gravityAuxiliary point +
        localBaseCoordinate canonicalLorentzianTimeDirection point •
          currentCanonicalFullActionLorentzAuxiliaryVelocity
            positiveSmoothUnifiedSource
            positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
            space =
      physicalIIPlusBivector 1
  rw [currentCanonicalGravityPreservingActual_gravityAuxiliary_point,
    positiveP506MatterCurrentCanonicalLorentzAuxiliaryVelocity_eq_zero]
  simp only [smul_zero, add_zero]
  unfold actionGeneratedGravityAuxiliary
  rw [positiveP506MatterCurrentCompleteFirstGermCanonicalGeneratedZeroResponseState_coframe_one]

/-- Full pointwise simplicity on the same C3h189 actual.  This is stronger
than merely checking the tangent equation at the contact origin. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gravitySimplicity
    (space : StageNineSpatialPoint) :
    GravitySimplicityEquation
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift space) := by
  intro point
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gravityAuxiliary_simple,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one]

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframeTimeTangent_eq_zero
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    coframeFieldDirectionalTangent
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
          space).coframe
        point canonicalLorentzianTimeDirection =
      0 := by
  funext internal coordinate
  unfold coframeFieldDirectionalTangent
  rw [show
    (fun candidate =>
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
        space).coframe candidate internal coordinate) =
      fun _ => (1 : LorentzianCoframe) internal coordinate by
    funext candidate
    rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one]]
  simp [fieldDirectionalDerivative]

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gravityAuxiliaryTimeDerivative_eq_zero
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (internalPair spacetimePair : Fin 6) :
    fieldDirectionalDerivative
        (fun candidate =>
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
            space).gravityAuxiliary candidate internalPair spacetimePair)
        point canonicalLorentzianTimeDirection =
      0 := by
  rw [show
    (fun candidate =>
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
        space).gravityAuxiliary candidate internalPair spacetimePair) =
      fun _ => physicalIIPlusBivector 1 internalPair spacetimePair by
    funext candidate
    rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gravityAuxiliary_simple]]
  simp [fieldDirectionalDerivative]

/-- Independent same-actual acceptance: the generated auxiliary and coframe
time tangents obey the full 36-coordinate tangent-simplicity law. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_tangentSimplicity
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (internalPair spacetimePair : Fin 6) :
    fieldDirectionalDerivative
        (fun candidate =>
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
            space).gravityAuxiliary candidate internalPair spacetimePair)
        point canonicalLorentzianTimeDirection =
      physicalIIPlusCoframeTangent
        ((positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
          space).coframe point)
        (coframeFieldDirectionalTangent
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
            space).coframe
          point canonicalLorentzianTimeDirection)
        internalPair spacetimePair := by
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gravityAuxiliaryTimeDerivative_eq_zero,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframeTimeTangent_eq_zero]
  fin_cases internalPair <;>
    simp [physicalIIPlusCoframeTangent, coframeWedgeTangent,
      internalBivectorDual, lorentzianCoframeHodge]

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzTangentSimplicity
