import H0mework.Physics.MatterCurrent.CanonicalLorentzActualFirstJetLift
import H0mework.Physics.MatterCurrent.EinsteinCartanLocalActualLift
import H0mework.Physics.MatterCurrent.P286PrincipalFirstGermP286ConnectionSpatialCauchyClosure

/-!
# C3h190: exact P506/L0 Lorentz origin provenance and zero momentum response

The C3h189 finite Lorentz dual is a genuine action operator for an arbitrary
primitive Cauchy state.  On the exact P506/L0 current generated in C3h187, its
momentum leg is more rigid: the contact-local full-synchronized producer has
already generated the Einstein--Cartan contorsion of the same matter spin,
while the coframe and gravity auxiliary are the contact-constant pair
`(1, II⁺(1))`.

This module proves the resulting action normal form in the forward direction:

```text
exact C3h187 current
→ same-contact coframe / B / matter / adjoint / contorsion provenance
→ Lorentz algebraic balance of the C3h188 final actual
→ contact-family BF momentum is spatially constant
→ all 18 C3h188 momentum action coordinates vanish.
```

The last statement is producer soundness for this exact current, not an
independent Euler--Lagrange closure.  It is not assumed by the constructor and
is not obtained from the C3h189 faithful-zero-fiber theorem.  No response,
residual, branch, event, scheduler, source-time law, endpoint, or numerical
normalization is supplied.  In particular, the coordinate support of the P286
current is not inspected and cannot select a branch or generate an M0 event.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzOriginProvenance

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCanonicalLocalFullActionResponseOperator
open StageNineCoframeTwoFormPairing
open StageNineConnectionSectorSourceBalance
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalGravityPreservingLorentzDualResponse
open StageNineSourceActionGeneratedP506MatterCurrentCompleteFirstGermCanonicalPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermResponse
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermP286ConnectionSpatialCauchyClosure

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-! ## Exact C3h187 current projections -/

/-- The canonical input slice has the same primal matter probe at every
contact. -/
theorem
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_matter_probe
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.matter
        space =
      diracSpinTwoMatterProbe := by
  change
    positiveP506MatterCurrentCompleteFirstGermResponseActual.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact
    positiveP506MatterCurrentCompleteFirstGermResponseActual_matter_canonicalZeroSlice
      space

/-- The same canonical input slice retains the exact adjoint matter probe. -/
theorem
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_conjugateMatter_probe
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.conjugateMatter
        space =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    positiveP506MatterCurrentCompleteFirstGermResponseActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact
    positiveP506MatterCurrentCompleteFirstGermResponseActual_conjugateMatter_canonicalZeroSlice
      space

/-- The freshly generated C3h187 zero-response current carries the simple
gravity auxiliary at every spatial contact. -/
theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gravityAuxiliary_simple
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.gravityAuxiliary
        space =
      physicalIIPlusBivector 1 := by
  change
    (currentCanonicalFullActionActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).gravityAuxiliary (canonicalCauchySlicePoint 0 0) =
      physicalIIPlusBivector 1
  rw [canonicalCauchySlicePoint_zero_zero]
  change
    (canonicalLocalFullActionP286Actual positiveSmoothUnifiedSource
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
        space)).gravityAuxiliary 0 =
      physicalIIPlusBivector 1
  rw [canonicalLocalFullActionP286Actual_apply]
  change
    (StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator
      positiveSmoothUnifiedSource
      (fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
          space))).gravityAuxiliary 0 =
      physicalIIPlusBivector 1
  rw [StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator_gravityAuxiliary,
    fullSynchronizedActionResponseOperator_gravityAuxiliary]
  change
    (StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift.sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).gravityAuxiliary 0 =
      physicalIIPlusBivector 1
  rw [StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift.sourceActionGeneratedLinearPlebanskiJointLocalActualLift_auxiliary]
  unfold actionGeneratedGravityAuxiliary
  rw [positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_coframe_one]

/-- Primal matter also survives the C3h187 contact-local action graph at its
common origin. -/
theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_matter_probe
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.matter
        space =
      diracSpinTwoMatterProbe := by
  change
    (currentCanonicalFullActionActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).matter (canonicalCauchySlicePoint 0 0) =
      diracSpinTwoMatterProbe
  rw [canonicalCauchySlicePoint_zero_zero]
  change
    (actionGeneratedMatterCompleteFirstGermActual positiveSmoothUnifiedSource
      (actionGeneratedMatterTemporalFirstGermActual positiveSmoothUnifiedSource
        (canonicalLocalFullActionP286Actual positiveSmoothUnifiedSource
          (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
            positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
            space)))).matter 0 =
      diracSpinTwoMatterProbe
  rw [actionGeneratedMatterCompleteFirstGermActual_matter_origin,
    actionGeneratedMatterTemporalFirstGermActual_matter_origin,
    canonicalLocalFullActionP286Actual_apply]
  change
    (StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator
      positiveSmoothUnifiedSource
      (fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
          space))).matter 0 =
      diracSpinTwoMatterProbe
  rw [StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator_matter,
    fullSynchronizedActionResponseOperator_preserves_matter_origin]
  change
    (currentFullSynchronizedCompleteP286BaseActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).matter 0 =
      diracSpinTwoMatterProbe
  rw [currentFullSynchronizedCompleteP286BaseActual_matter_origin,
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_matter_probe]

/-- Adjoint matter is retained by the same action graph and contact. -/
theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_conjugateMatter_probe
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.conjugateMatter
        space =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    (currentCanonicalFullActionActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).conjugateMatter (canonicalCauchySlicePoint 0 0) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [canonicalCauchySlicePoint_zero_zero]
  change
    (canonicalLocalFullActionP286Actual positiveSmoothUnifiedSource
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
        space)).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [canonicalLocalFullActionP286Actual_apply]
  change
    (StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator
      positiveSmoothUnifiedSource
      (fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
          space))).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator_conjugateMatter,
    fullSynchronizedActionResponseOperator_preserves_conjugateMatter_origin]
  change
    (currentFullSynchronizedCompleteP286BaseActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [currentFullSynchronizedCompleteP286BaseActual_conjugateMatter_origin,
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_conjugateMatter_probe]

/-! ## Same-contact contorsion provenance -/

private def c3h187ContactBaseActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState space

private theorem c3h187ContactBaseActual_coframe_one
    (space : StageNineSpatialPoint) :
    (c3h187ContactBaseActual space).coframe 0 = 1 := by
  unfold c3h187ContactBaseActual currentCanonicalFullActionBaseActual
    currentFullSynchronizedCompleteP286BaseActual
  rw [StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift.sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe,
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_coframe_one]

private theorem c3h187ContactBaseActual_matter_probe
    (space : StageNineSpatialPoint) :
    (c3h187ContactBaseActual space).matter 0 =
      diracSpinTwoMatterProbe := by
  unfold c3h187ContactBaseActual currentCanonicalFullActionBaseActual
  rw [currentFullSynchronizedCompleteP286BaseActual_matter_origin,
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_matter_probe]

private theorem c3h187ContactBaseActual_conjugateMatter_probe
    (space : StageNineSpatialPoint) :
    (c3h187ContactBaseActual space).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  unfold c3h187ContactBaseActual currentCanonicalFullActionBaseActual
  rw [currentFullSynchronizedCompleteP286BaseActual_conjugateMatter_origin,
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_conjugateMatter_probe]

private theorem c3h187ContactBaseActual_spinCoordinates
    (space : StageNineSpatialPoint) :
    actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
        (c3h187ContactBaseActual space) 0 =
      positiveP506MatterCurrentEinsteinCartanSpinCoordinates := by
  calc
    actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          (c3h187ContactBaseActual space) 0 =
        actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          positiveP506MatterCurrentEinsteinCartanLocalActualLift 0 := by
      exact actualMatterSpinActionCoordinates_eq_of_origin_fields
        positiveSmoothUnifiedSource
        (c3h187ContactBaseActual space)
        positiveP506MatterCurrentEinsteinCartanLocalActualLift
        ((c3h187ContactBaseActual_coframe_one space).trans
          (positiveP506MatterCurrentEinsteinCartanLocalActualLift_coframe 0).symm)
        ((c3h187ContactBaseActual_matter_probe space).trans
          positiveP506MatterCurrentEinsteinCartanLocalActualLift_matter_origin.symm)
        ((c3h187ContactBaseActual_conjugateMatter_probe space).trans
          positiveP506MatterCurrentEinsteinCartanLocalActualLift_conjugate_origin.symm)
    _ = positiveP506MatterCurrentEinsteinCartanSpinCoordinates :=
      positiveP506MatterCurrentEinsteinCartanLocalActualLift_spinCoordinates

/-- The C3h187 generated current carries the Einstein--Cartan contorsion of
the same contact matter spin; it is not a supplied connection witness. -/
theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gravityConnection_contorsion
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.gravityConnection
        space =
      lorentzSkewConnectionOfBivectorOneForm
        positiveP506MatterCurrentEinsteinCartanContorsionCoordinates := by
  change
    (currentCanonicalFullActionActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).gravityConnection (canonicalCauchySlicePoint 0 0) =
      lorentzSkewConnectionOfBivectorOneForm
        positiveP506MatterCurrentEinsteinCartanContorsionCoordinates
  rw [canonicalCauchySlicePoint_zero_zero]
  change
    (canonicalLocalFullActionP286Actual positiveSmoothUnifiedSource
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
        space)).gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveP506MatterCurrentEinsteinCartanContorsionCoordinates
  rw [canonicalLocalFullActionP286Actual_apply]
  change
    (StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator
      positiveSmoothUnifiedSource
      (fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
        (c3h187ContactBaseActual space))).gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveP506MatterCurrentEinsteinCartanContorsionCoordinates
  rw [StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator_gravityConnection,
    fullSynchronizedActionResponseOperator_connection_origin]
  unfold fullSynchronizedActionLorentzOrigin
    fullSynchronizedActionContorsion fullSynchronizedActionSpin
  rw [c3h187ContactBaseActual_spinCoordinates]
  rfl

/-! ## C3h188 final-actual balance -/

theorem
    positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_coframe_one
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual
      space).coframe 0 =
      1 := by
  change
    (StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift.sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
      space).coframe 0 =
      1
  rw [StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift.sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe,
    positiveP506MatterCurrentCompleteFirstGermCanonicalGeneratedZeroResponseState_coframe_one]

theorem
    positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_gravityAuxiliary_simple
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual
      space).gravityAuxiliary 0 =
      physicalIIPlusBivector 1 := by
  change
    actionGeneratedGravityAuxiliary
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        space =
      physicalIIPlusBivector 1
  unfold actionGeneratedGravityAuxiliary
  rw [positiveP506MatterCurrentCompleteFirstGermCanonicalGeneratedZeroResponseState_coframe_one]

theorem
    positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_gravityConnection_contorsion
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual
      space).gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveP506MatterCurrentEinsteinCartanContorsionCoordinates := by
  rw [positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_gravityConnection_origin,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gravityConnection_contorsion]

theorem
    positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_matter_probe
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual
      space).matter 0 =
      diracSpinTwoMatterProbe := by
  change
    (actionGeneratedMatterCompleteFirstGermActual positiveSmoothUnifiedSource
      (actionGeneratedMatterTemporalFirstGermActual positiveSmoothUnifiedSource
        (StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator
          positiveSmoothUnifiedSource
          (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
            positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
            space)))).matter 0 =
      diracSpinTwoMatterProbe
  rw [actionGeneratedMatterCompleteFirstGermActual_matter_origin,
    actionGeneratedMatterTemporalFirstGermActual_matter_origin,
    StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator_matter]
  change
    (currentFullSynchronizedCompleteP286BaseActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
      space).matter 0 =
      diracSpinTwoMatterProbe
  rw [currentFullSynchronizedCompleteP286BaseActual_matter_origin,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_matter_probe]

theorem
    positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_conjugateMatter_probe
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual
      space).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    (StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator
      positiveSmoothUnifiedSource
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        space)).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [StageNineCurrentP286CompleteActionResponseOperator.currentP286CompleteActionResponseOperator_conjugateMatter]
  change
    (currentFullSynchronizedCompleteP286BaseActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
      space).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [currentFullSynchronizedCompleteP286BaseActual_conjugateMatter_origin,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_conjugateMatter_probe]

theorem
    positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_spinCoordinates
    (space : StageNineSpatialPoint) :
    actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual space)
        0 =
      positiveP506MatterCurrentEinsteinCartanSpinCoordinates := by
  calc
    actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual space)
          0 =
        actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          positiveP506MatterCurrentEinsteinCartanLocalActualLift 0 := by
      exact actualMatterSpinActionCoordinates_eq_of_origin_fields
        positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual space)
        positiveP506MatterCurrentEinsteinCartanLocalActualLift
        ((positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_coframe_one
          space).trans
          (positiveP506MatterCurrentEinsteinCartanLocalActualLift_coframe 0).symm)
        ((positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_matter_probe
          space).trans
          positiveP506MatterCurrentEinsteinCartanLocalActualLift_matter_origin.symm)
        ((positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_conjugateMatter_probe
          space).trans
          positiveP506MatterCurrentEinsteinCartanLocalActualLift_conjugate_origin.symm)
    _ = positiveP506MatterCurrentEinsteinCartanSpinCoordinates :=
      positiveP506MatterCurrentEinsteinCartanLocalActualLift_spinCoordinates

/-- Re-substitution of the generated contorsion gives the algebraic Lorentz
balance of the same C3h188 final actual.  This is explicitly producer
consistency, not the later independent Gauss constraint. -/
theorem
    positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_lorentzAlgebraic_producerConsistency
    (space : StageNineSpatialPoint)
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionAlgebraicSpinCurrentCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual space)
        direction 0 =
      0 := by
  rw [lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors]
  exact actualSimpleBContorsion_algebraicBalance
    positiveSmoothUnifiedSource
    (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual space)
    positiveP506MatterCurrentEinsteinCartanSpinCoordinates
    (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_coframe_one
      space)
    (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_gravityAuxiliary_simple
      space)
    (by
      rw [positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_gravityConnection_contorsion]
      rfl)
    (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_spinCoordinates
      space)
    direction

/-! ## Complete exact momentum response -/

/-- For every derivative and Lorentz test direction, the contact family of BF
momenta is a literal constant function of the spatial contact. -/
theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzBFMomentumEvaluation_constant
    (derivativeDirection : LorentzianIndex)
    (direction : LorentzSpatialBivectorDirection) :
    (fun space =>
      currentCanonicalFullActionLorentzBFMomentumEvaluation
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
          derivativeDirection space direction) =
      fun _ =>
        gravityAuxiliaryHodgePairingPolynomial 1
          (physicalIIPlusBivector 1)
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            (canonicalLorentzSpatialBivectorOneForm direction)) := by
  funext space
  change
    lorentzConnectionBFDifferentialMomentum
        (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual space)
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          (canonicalLorentzSpatialBivectorOneForm direction))
        0 =
      gravityAuxiliaryHodgePairingPolynomial 1
        (physicalIIPlusBivector 1)
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          (canonicalLorentzSpatialBivectorOneForm direction))
  unfold lorentzConnectionBFDifferentialMomentum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_coframe_one,
    positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_gravityAuxiliary_simple]
  simp

/-- The spatial divergence term of the complete C3h188 Lorentz action dual
vanishes at every contact and on every test direction. -/
theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzSpatialBFMomentumDivergence_zero
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        space direction =
      0 := by
  unfold currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
  apply Finset.sum_eq_zero
  intro derivativeDirection _
  unfold currentCanonicalFullActionLorentzSpatialBFMomentumDerivative
  rw [positiveP506MatterCurrentCanonicalGravityPreservingLorentzBFMomentumEvaluation_constant]
  simp

theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzSpatialBFMomentumRawActionReadout_zero
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        space direction =
      0 := by
  unfold currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
  dsimp only
  change
    lorentzConnectionAlgebraicSpinCurrentCoefficient positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalGravityPreservingFinalActual space)
          (canonicalLorentzSpatialBivectorOneForm direction) 0 -
        currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
          space direction =
      0
  rw [positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_lorentzAlgebraic_producerConsistency,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzSpatialBFMomentumDivergence_zero]
  ring

/-- Every one of the 18 action-owned finite coordinates vanishes. -/
theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzSpatialBFMomentumActionCoordinates_eq_zero
    (space : StageNineSpatialPoint) :
    currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        space =
      0 := by
  funext spatialDirection internalPair
  exact
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzSpatialBFMomentumRawActionReadout_zero
      space
      (canonicalLorentzSpatialBivectorCoordinateDirection spatialDirection
        internalPair)

/-- Exact no-premise result: the complete finite Lorentz BF-momentum velocity
is zero on the source-generated P506/L0 current.  The connection velocity is
not asserted to vanish. -/
theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzBFMomentumVelocity_eq_zero :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzBFMomentumVelocity =
      0 := by
  apply
    (currentCanonicalFullActionLorentzSpatialBFMomentumVelocity_eq_zero_iff
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState).2
  intro space spatialDirection internalPair
  exact
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzSpatialBFMomentumRawActionReadout_zero
      space
      (canonicalLorentzSpatialBivectorCoordinateDirection spatialDirection
        internalPair)

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzOriginProvenance
