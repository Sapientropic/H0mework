import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorMatterAdjointZeroSlice

/-!
# Matter/adjoint closure of the action-selected successor

The coupled temporal leg already realizes the primal and adjoint velocities
generated from the exact carry occurrence.  This module transports the full
spatial action data to the matching Cartan restart, proves both action laws on
the one final successor, and reads the two Euler coordinates there.

No residual coordinate, support branch, target derivative, or equation
receipt enters any constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointClosure

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicRegularity
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointZeroSlice
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorStructuralReduction
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev Coupled : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
    Source Carry

private abbrev Successor : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
    Source Coupled

private abbrev Cartan : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source Coupled

private abbrev Point (space : StageNineSpatialPoint) : BasePoint :=
  canonicalCauchySlicePoint 0 space

private abbrev ProfileRestart
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  completeJointGeneratedProfileRestartCurrent Source Carry (Point space)

private abbrev ProfilePrimal
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    (ProfileRestart space)

private theorem coupled_coframe_eq_carry :
    Coupled.coframe = Carry.coframe :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe
    Source Carry

private theorem coupled_gaugeConnection_eq_carry :
    Coupled.gaugeConnection = Carry.gaugeConnection :=
  rfl

private theorem coupled_scalar_zeroSlice_eq_carry
    (space : StageNineSpatialPoint) :
    Coupled.scalar (Point space) = Carry.scalar (Point space) :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
    Source Carry space

private theorem coupled_matter_zeroSlice_eq_carry
    (space : StageNineSpatialPoint) :
    Coupled.matter (Point space) = Carry.matter (Point space) :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
    Source Carry space

private theorem coupled_conjugateMatter_zeroSlice_eq_carry
    (space : StageNineSpatialPoint) :
    Coupled.conjugateMatter (Point space) = Carry.conjugateMatter (Point space) := by
  simpa only [Coupled, Point] using
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      Source Carry space

private theorem recenteredCarry_coframeFirstJet_origin
    (point : BasePoint) :
    holonomicCoframeFirstJetAt
        (fullyRecenterHolonomicConfiguration Carry point).coframe 0 =
      holonomicCoframeFirstJetAt Carry.coframe point := by
  apply coframeJet_eq_of_fields_eq
  · change
      (fullyRecenterHolonomicConfiguration Carry point).coframe 0 =
        Carry.coframe point
    exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · funext derivativeDirection internal coordinate
    change
      fieldDirectionalDerivative
          ((fun candidate => Carry.coframe candidate internal coordinate) ∘
            canonicalSpacetimeContactTranslation point)
          0 derivativeDirection =
        fieldDirectionalDerivative
          (fun candidate => Carry.coframe candidate internal coordinate)
          point derivativeDirection
    simpa only [canonicalSpacetimeContactTranslation_zero] using
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (fun candidate => Carry.coframe candidate internal coordinate)
        point 0 derivativeDirection

private theorem coupled_coframe_zeroSlice_eq_recenteredCarry_origin
    (space : StageNineSpatialPoint) :
    Coupled.coframe (Point space) =
      (fullyRecenterHolonomicConfiguration Carry (Point space)).coframe 0 := by
  calc
    Coupled.coframe (Point space) = Carry.coframe (Point space) :=
      congrFun coupled_coframe_eq_carry _
    _ = _ := (fullyRecenterHolonomicConfiguration_coframe_origin _ _).symm

private theorem coupled_matter_zeroSlice_eq_recenteredCarry_origin
    (space : StageNineSpatialPoint) :
    Coupled.matter (Point space) =
      (fullyRecenterHolonomicConfiguration Carry (Point space)).matter 0 := by
  calc
    Coupled.matter (Point space) = Carry.matter (Point space) :=
      coupled_matter_zeroSlice_eq_carry space
    _ = _ := (fullyRecenterHolonomicConfiguration_matter_origin _ _).symm

private theorem coupled_conjugateMatter_zeroSlice_eq_recenteredCarry_origin
    (space : StageNineSpatialPoint) :
    Coupled.conjugateMatter (Point space) =
      (fullyRecenterHolonomicConfiguration Carry
        (Point space)).conjugateMatter 0 := by
  calc
    Coupled.conjugateMatter (Point space) = Carry.conjugateMatter (Point space) :=
      coupled_conjugateMatter_zeroSlice_eq_carry space
    _ = _ :=
      (fullyRecenterHolonomicConfiguration_conjugateMatter_origin _ _).symm

private theorem coupled_spinResponse_zeroSlice_eq_recenteredCarry_origin
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionSpinResponseAt Source Coupled (Point space) =
      diracDualFormNativeActionSpinResponseAt Source
        (fullyRecenterHolonomicConfiguration Carry (Point space)) 0 := by
  exact
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
      Source Coupled
      (fullyRecenterHolonomicConfiguration Carry (Point space))
      (Point space) 0
      (coupled_coframe_zeroSlice_eq_recenteredCarry_origin space)
      (coupled_matter_zeroSlice_eq_recenteredCarry_origin space)
      (coupled_conjugateMatter_zeroSlice_eq_recenteredCarry_origin space)

private theorem coupled_actionCartanConnection_zeroSlice_eq_recenteredCarry
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionCartanConnectionAt Source Coupled (Point space) =
      diracDualFormNativeActionCartanConnectionAt Source
        (fullyRecenterHolonomicConfiguration Carry (Point space)) 0 := by
  have coframeJetEq :
      holonomicCoframeFirstJetAt Coupled.coframe (Point space) =
        holonomicCoframeFirstJetAt
          (fullyRecenterHolonomicConfiguration Carry
            (Point space)).coframe 0 := by
    rw [coupled_coframe_eq_carry]
    exact (recenteredCarry_coframeFirstJet_origin (Point space)).symm
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [coframeJetEq,
    coupled_coframe_zeroSlice_eq_recenteredCarry_origin,
    coupled_spinResponse_zeroSlice_eq_recenteredCarry_origin]

private theorem cartan_gravityConnection_zeroSlice_eq_profileRestart
    (space : StageNineSpatialPoint) :
    Cartan.gravityConnection (Point space) =
      (ProfileRestart space).gravityConnection 0 := by
  change
    diracDualFormNativeActionCartanConnectionAt Source Coupled (Point space) =
      diracDualFormNativeActionCartanConnectionAt Source
        (fullyRecenterHolonomicConfiguration Carry (Point space)) 0
  exact coupled_actionCartanConnection_zeroSlice_eq_recenteredCarry space

private theorem cartan_coframe_zeroSlice_eq_profileRestart
    (space : StageNineSpatialPoint) :
    Cartan.coframe (Point space) = (ProfileRestart space).coframe 0 := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  exact coupled_coframe_zeroSlice_eq_recenteredCarry_origin space

private theorem cartan_coframeFirstJet_zeroSlice_eq_profileRestart
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt Cartan.coframe (Point space) =
      holonomicCoframeFirstJetAt (ProfileRestart space).coframe 0 := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    coupled_coframe_eq_carry]
  exact (recenteredCarry_coframeFirstJet_origin (Point space)).symm

private theorem cartan_scalar_zeroSlice_eq_profileRestart
    (space : StageNineSpatialPoint) :
    Cartan.scalar (Point space) = (ProfileRestart space).scalar 0 := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar]
  calc
    Coupled.scalar (Point space) = Carry.scalar (Point space) :=
      coupled_scalar_zeroSlice_eq_carry space
    _ = _ := (fullyRecenterHolonomicConfiguration_scalar_origin _ _).symm

private theorem cartan_matter_zeroSlice_eq_profileRestart
    (space : StageNineSpatialPoint) :
    Cartan.matter (Point space) = (ProfileRestart space).matter 0 := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  exact coupled_matter_zeroSlice_eq_recenteredCarry_origin space

private theorem cartan_conjugateMatter_zeroSlice_eq_profileRestart
    (space : StageNineSpatialPoint) :
    Cartan.conjugateMatter (Point space) =
      (ProfileRestart space).conjugateMatter 0 := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
  exact coupled_conjugateMatter_zeroSlice_eq_recenteredCarry_origin space

private theorem cartan_gaugeConnection_zeroSlice_eq_profileRestart
    (space : StageNineSpatialPoint) :
    Cartan.gaugeConnection (Point space) =
      (ProfileRestart space).gaugeConnection 0 := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    coupled_gaugeConnection_eq_carry,
    fullyRecenterHolonomicConfiguration_gaugeConnection_origin]

private theorem coupled_matterDerivative_spatial_zeroSlice_eq_recenteredCarry
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv (Coupled.matter candidate))
        (Point space) direction.succ =
      fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Carry
            (Point space)).matter localPoint))
        0 direction.succ := by
  calc
    fieldDirectionalDerivative
          (fun candidate => matterCoordinateEquiv (Coupled.matter candidate))
          (Point space) direction.succ =
        fieldDirectionalDerivative
          (fun candidate => matterCoordinateEquiv (Carry.matter candidate))
          (Point space) direction.succ := by
      simpa [Source, Current, Carry, Coupled, Point,
        completeJointActionSelectedCoupledTemporalActual] using
        actionSelectedCoupled_matterSpatialDerivative_zeroSlice_eq_carry
          space direction
    _ = fieldDirectionalDerivative
          (fun localPoint => matterCoordinateEquiv
            ((fullyRecenterHolonomicConfiguration Carry
              (Point space)).matter localPoint))
          0 direction.succ := by
      change
        fieldDirectionalDerivative
            (fun candidate => matterCoordinateEquiv (Carry.matter candidate))
            (Point space) direction.succ =
          fieldDirectionalDerivative
            ((fun candidate => matterCoordinateEquiv (Carry.matter candidate)) ∘
              canonicalSpacetimeContactTranslation (Point space))
            0 direction.succ
      simpa only [canonicalSpacetimeContactTranslation_zero] using
        (fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
          (fun candidate => matterCoordinateEquiv (Carry.matter candidate))
          (Point space) 0 direction.succ).symm

private theorem cartan_matterCovariantDerivative_spatial_eq_profileRestart
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    holonomicMatterCovariantDerivative Cartan (Point space) direction.succ =
      holonomicMatterCovariantDerivative (ProfileRestart space) 0
        direction.succ := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
    holonomicMatterCovariantDerivative
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    coupled_matterDerivative_spatial_zeroSlice_eq_recenteredCarry,
    cartan_gravityConnection_zeroSlice_eq_profileRestart,
    cartan_gaugeConnection_zeroSlice_eq_profileRestart,
    coupled_matter_zeroSlice_eq_recenteredCarry_origin]
  rfl

private theorem knownVector_eq_of_actionFields
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (coframeEq : first.coframe firstPoint = second.coframe secondPoint)
    (scalarEq : first.scalar firstPoint = second.scalar secondPoint)
    (matterEq : first.matter firstPoint = second.matter secondPoint)
    (spatialCovariantEq : ∀ direction : Fin 3,
      holonomicMatterCovariantDerivative first firstPoint direction.succ =
        holonomicMatterCovariantDerivative second secondPoint direction.succ) :
    holonomicDiracDualCurrentCoframeMatterKnownVector first firstPoint =
      holonomicDiracDualCurrentCoframeMatterKnownVector second secondPoint := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [coframeEq, scalarEq, matterEq]
  congr 1
  apply congrArg
    (fun value : DiracExteriorMatterCarrier => Complex.I • value)
  apply Finset.sum_congr rfl
  intro direction _
  rw [spatialCovariantEq direction]

private theorem cartan_knownVector_zeroSlice_eq_profileRestart
    (space : StageNineSpatialPoint) :
    holonomicDiracDualCurrentCoframeMatterKnownVector Cartan (Point space) =
      holonomicDiracDualCurrentCoframeMatterKnownVector
        (ProfileRestart space) 0 := by
  exact knownVector_eq_of_actionFields Cartan (ProfileRestart space)
    (Point space) 0
    (cartan_coframe_zeroSlice_eq_profileRestart space)
    (cartan_scalar_zeroSlice_eq_profileRestart space)
    (cartan_matter_zeroSlice_eq_profileRestart space)
    (cartan_matterCovariantDerivative_spatial_eq_profileRestart space)

private theorem cartan_matterCovariantDerivative_time_eq_generated
    (space : StageNineSpatialPoint) :
    holonomicMatterCovariantDerivative Cartan (Point space)
        canonicalLorentzianTimeDirection =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        (ProfileRestart space) 0 := by
  have matterEq : Coupled.matter (Point space) =
      (ProfileRestart space).matter 0 := by
    simpa [Cartan] using cartan_matter_zeroSlice_eq_profileRestart space
  unfold holonomicMatterCovariantDerivative
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  rw [show
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Coupled.matter point))
        (Point space) canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          Source Carry (Point space)).matterVelocity by
    simpa [Source, Current, Carry, Coupled, Point,
      completeJointActionSelectedCoupledTemporalActual] using
      actionSelectedCoupled_matterTemporalDerivative_zeroSlice space]
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    matterCoordinateEquiv.symm_apply_apply,
    cartan_gravityConnection_zeroSlice_eq_profileRestart,
    cartan_gaugeConnection_zeroSlice_eq_profileRestart,
    matterEq]
  unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    holonomicMatterConnectionAction
  module

private theorem cartan_primalActionLaw_zeroSlice
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw Cartan (Point space)
      (holonomicMatterCovariantDerivative Cartan (Point space)
        canonicalLorentzianTimeDirection) := by
  have noncharacteristic :
      coframeTemporalPrincipalScalar
          ((ProfileRestart space).coframe 0) ≠ 0 := by
    unfold ProfileRestart completeJointGeneratedProfileRestartCurrent
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
      fullyRecenterHolonomicConfiguration_coframe_origin,
      actionSelectedCarry_coframe_eq_one,
      coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  have generated :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      (ProfileRestart space) 0 noncharacteristic
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at generated ⊢
  rw [cartan_coframe_zeroSlice_eq_profileRestart,
    cartan_knownVector_zeroSlice_eq_profileRestart,
    cartan_matterCovariantDerivative_time_eq_generated]
  exact generated

/-- Re-running the complete-joint temporal compiler on the already generated
coupled current has zero primal correction on the canonical zero slice.  The
existing coupled first jet and the fresh action response satisfy the same
noncharacteristic Dirac time law, so uniqueness identifies them before the
correction is read. -/
theorem actionSelectedCoupled_matterTemporalCoordinateCorrection_zeroSlice
    (space : StageNineSpatialPoint) :
    completeJointMatterTemporalCoordinateCorrection
        positiveSmoothUnifiedSource
        (completeJointActionSelectedCoupledTemporalActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
        (canonicalCauchySlicePoint 0 space) = 0 := by
  have noncharacteristic :
      coframeTemporalPrincipalScalar (Cartan.coframe (Point space)) ≠ 0 := by
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
      coupled_coframe_eq_carry, actionSelectedCarry_coframe_eq_one,
      coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  have generatedLaw :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      Cartan (Point space) noncharacteristic
  have unique :=
    holonomicDiracDualCurrentCoframeMatterTimeActionLaw_unique
      Cartan (Point space) noncharacteristic
      (holonomicMatterCovariantDerivative Cartan (Point space)
        canonicalLorentzianTimeDirection)
      (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        Cartan (Point space))
      (cartan_primalActionLaw_zeroSlice space) generatedLaw
  have rawEq :
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
          Cartan (Point space) =
        matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun point => matterCoordinateEquiv (Coupled.matter point))
            (Point space) canonicalLorentzianTimeDirection) := by
    unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    unfold holonomicMatterCovariantDerivative at unique
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
      at unique
    unfold holonomicMatterConnectionAction
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
    exact sub_eq_iff_eq_add.mpr (by simpa [add_assoc] using unique.symm)
  rw [completeJointMatterTemporalCoordinateCorrection_normalForm]
  change
    matterCoordinateEquiv
        (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
          Cartan (Point space)) -
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Coupled.matter point))
        (Point space) canonicalLorentzianTimeDirection = 0
  rw [rawEq, matterCoordinateEquiv.apply_symm_apply, sub_self]

private theorem successor_coframe_eq_cartan :
    Successor.coframe = Cartan.coframe := by
  calc
    Successor.coframe = Coupled.coframe :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
        Source Coupled
    _ = Cartan.coframe :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        Source Coupled).symm

private theorem successor_scalar_eq_cartan :
    Successor.scalar = Cartan.scalar := by
  calc
    Successor.scalar = Coupled.scalar :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
        Source Coupled
    _ = Cartan.scalar :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar
        Source Coupled).symm

private theorem successor_matter_eq_cartan :
    Successor.matter = Cartan.matter := by
  calc
    Successor.matter = Coupled.matter :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
        Source Coupled
    _ = Cartan.matter :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter
        Source Coupled).symm

private theorem successor_conjugateMatter_eq_cartan :
    Successor.conjugateMatter = Cartan.conjugateMatter := by
  calc
    Successor.conjugateMatter = Coupled.conjugateMatter :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
        Source Coupled
    _ = Cartan.conjugateMatter :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter
        Source Coupled).symm

private theorem successor_gravityConnection_eq_cartan :
    Successor.gravityConnection = Cartan.gravityConnection :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
    Source Coupled

private theorem successor_gaugeConnection_eq_cartan :
    Successor.gaugeConnection = Cartan.gaugeConnection := by
  calc
    Successor.gaugeConnection = Coupled.gaugeConnection :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection
        Source Coupled
    _ = Cartan.gaugeConnection :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
        Source Coupled).symm

private theorem successor_matterCovariantDerivative_eq_cartan
    (point : BasePoint) :
    holonomicMatterCovariantDerivative Successor point =
      holonomicMatterCovariantDerivative Cartan point := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [successor_matter_eq_cartan, successor_gravityConnection_eq_cartan,
    successor_gaugeConnection_eq_cartan]

private theorem successor_knownVector_eq_cartan
    (point : BasePoint) :
    holonomicDiracDualCurrentCoframeMatterKnownVector Successor point =
      holonomicDiracDualCurrentCoframeMatterKnownVector Cartan point := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [successor_coframe_eq_cartan, successor_scalar_eq_cartan,
    successor_matter_eq_cartan]
  simp_rw [successor_matterCovariantDerivative_eq_cartan]

/-- The one action-selected successor satisfies the primal Dirac action law
at every fixed P506/L0 zero-slice occurrence. -/
theorem successor_primalActionLaw_zeroSlice
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      fixedP506L0LorentzPathActionSelectedJointSuccessor (Point space)
      (holonomicMatterCovariantDerivative
        fixedP506L0LorentzPathActionSelectedJointSuccessor (Point space)
        canonicalLorentzianTimeDirection) := by
  change
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw Successor (Point space)
      (holonomicMatterCovariantDerivative Successor (Point space)
        canonicalLorentzianTimeDirection)
  have generated := cartan_primalActionLaw_zeroSlice space
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at generated ⊢
  rw [congrFun successor_coframe_eq_cartan (Point space),
    successor_knownVector_eq_cartan,
    congrFun (successor_matterCovariantDerivative_eq_cartan (Point space))
      canonicalLorentzianTimeDirection]
  simpa only [Successor] using generated

/-- The primal law reads as the exact conjugate-matter Euler zero of the
same final successor. -/
theorem successor_conjugateMatterResidual_zeroSlice
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0LorentzPathActionSelectedJointSuccessor
      (Point space)).conjugateMatter = 0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient Source Successor direction
        (Point space) = 0
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
    Source Successor (Point space) (successor_primalActionLaw_zeroSlice space)]
  simp

private theorem carry_coframeFirstJet
    (point : BasePoint) :
    holonomicCoframeFirstJetAt Carry.coframe point =
      identityCoframeMatterGeometry := by
  rw [actionSelectedCarry_coframe_eq_one]
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]

private theorem profileRestart_coframeFirstJet_origin
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt (ProfileRestart space).coframe 0 =
      identityCoframeMatterGeometry := by
  unfold ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    recenteredCarry_coframeFirstJet_origin]
  exact carry_coframeFirstJet (Point space)

private theorem profilePrimal_coframeFirstJet_origin
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt (ProfilePrimal space).coframe 0 =
      identityCoframeMatterGeometry := by
  unfold ProfilePrimal
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe]
  exact profileRestart_coframeFirstJet_origin space

private theorem cartan_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt Cartan.coframe (Point space) =
      identityCoframeMatterGeometry := by
  calc
    holonomicCoframeFirstJetAt Cartan.coframe (Point space) =
        holonomicCoframeFirstJetAt (ProfileRestart space).coframe 0 :=
      cartan_coframeFirstJet_zeroSlice_eq_profileRestart space
    _ = identityCoframeMatterGeometry :=
      profileRestart_coframeFirstJet_origin space

private theorem
    cartan_conjugateMatterSpatialDerivative_zeroSlice_eq_profilePrimal
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    holonomicConjugateMatterDerivativeDual Cartan
        (Point space) direction.succ =
      holonomicConjugateMatterDerivativeDual (ProfilePrimal space) 0
        direction.succ := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
  apply congrArg matterDualOfCoordinates
  calc
    fieldDirectionalDerivative (holonomicConjugateMatterCoordinates Coupled)
          (Point space) direction.succ =
        fieldDirectionalDerivative (holonomicConjugateMatterCoordinates Carry)
          (Point space) direction.succ := by
      simpa [Source, Current, Carry, Coupled, Point,
        completeJointActionSelectedCoupledTemporalActual] using
        actionSelectedCoupled_conjugateMatterSpatialDerivative_zeroSlice_eq_carry
          space direction
    _ = fieldDirectionalDerivative
          (holonomicConjugateMatterCoordinates
            (fullyRecenterHolonomicConfiguration Carry (Point space)))
          0 direction.succ := by
      change
        fieldDirectionalDerivative (holonomicConjugateMatterCoordinates Carry)
            (Point space) direction.succ =
          fieldDirectionalDerivative
            (holonomicConjugateMatterCoordinates Carry ∘
              canonicalSpacetimeContactTranslation (Point space))
            0 direction.succ
      simpa only [canonicalSpacetimeContactTranslation_zero] using
        (fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
          (holonomicConjugateMatterCoordinates Carry)
          (Point space) 0 direction.succ).symm
    _ = fieldDirectionalDerivative
          (holonomicConjugateMatterCoordinates (ProfilePrimal space))
          0 direction.succ := by rfl

private theorem cartan_adjointActionVelocity_zeroSlice_eq_profile
    (space : StageNineSpatialPoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Cartan
        (Point space) =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (ProfilePrimal space) 0 := by
  calc
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Cartan
          (Point space) =
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          Cartan (Point space) :=
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ (cartan_coframeFirstJet_zeroSlice space)
    _ =
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          (ProfilePrimal space) 0 := by
      apply
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity_eq_of_pointData
      · exact cartan_gravityConnection_zeroSlice_eq_profileRestart space
      · exact cartan_gaugeConnection_zeroSlice_eq_profileRestart space
      · exact cartan_scalar_zeroSlice_eq_profileRestart space
      · exact cartan_conjugateMatter_zeroSlice_eq_profileRestart space
      · exact
          cartan_conjugateMatterSpatialDerivative_zeroSlice_eq_profilePrimal
            space
    _ = holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (ProfilePrimal space) 0 :=
      (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ (profilePrimal_coframeFirstJet_origin space)).symm

private theorem
    cartan_conjugateMatterTimeDerivative_zeroSlice_eq_actionVelocity
    (space : StageNineSpatialPoint) :
    holonomicConjugateMatterDerivativeDual Cartan (Point space)
        canonicalLorentzianTimeDirection =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Cartan
        (Point space) := by
  calc
    holonomicConjugateMatterDerivativeDual Cartan (Point space)
          canonicalLorentzianTimeDirection =
        matterDualOfCoordinates
          (fieldDirectionalDerivative
            (holonomicConjugateMatterCoordinates Coupled)
            (Point space) canonicalLorentzianTimeDirection) := by
      unfold holonomicConjugateMatterDerivativeDual
        holonomicConjugateMatterDerivativeCoordinates
        holonomicConjugateMatterCoordinates Cartan
      rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
    _ = matterDualOfCoordinates
          (matterDualCoordinates
            (sourceActionGeneratedDiracDualCompleteJointProfiles
              Source Carry (Point space)).adjointVelocity) := by
      rw [show
        fieldDirectionalDerivative
            (holonomicConjugateMatterCoordinates Coupled)
            (Point space) canonicalLorentzianTimeDirection =
          matterDualCoordinates
            (sourceActionGeneratedDiracDualCompleteJointProfiles
              Source Carry (Point space)).adjointVelocity by
        simpa [Source, Current, Carry, Coupled, Point,
          completeJointActionSelectedCoupledTemporalActual] using
          actionSelectedCoupled_conjugateMatterTemporalDerivative_zeroSlice
            space]
    _ = (sourceActionGeneratedDiracDualCompleteJointProfiles
          Source Carry (Point space)).adjointVelocity :=
      matterDualOfCoordinates_surjective _
    _ = holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (ProfilePrimal space) 0 := by
      rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]
    _ = holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Cartan
          (Point space) :=
      (cartan_adjointActionVelocity_zeroSlice_eq_profile space).symm

private theorem cartan_adjointActionLaw_zeroSlice
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw Cartan
      (Point space)
      (holonomicConjugateMatterDerivativeDual Cartan (Point space)
        canonicalLorentzianTimeDirection) := by
  have coframeOne : Cartan.coframe (Point space) = 1 :=
    coframe_eq_one_of_identity_firstJet Cartan (Point space)
      (cartan_coframeFirstJet_zeroSlice space)
  have nondegenerate : Matrix.det (Cartan.coframe (Point space)) ≠ 0 := by
    rw [coframeOne]
    simp
  have noncharacteristic :
      coframeTemporalPrincipalScalar (Cartan.coframe (Point space)) ≠ 0 := by
    rw [coframeOne, coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  rw [cartan_conjugateMatterTimeDerivative_zeroSlice_eq_actionVelocity]
  exact
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_satisfies
      Cartan (Point space) nondegenerate noncharacteristic

private theorem successor_conjugateMatterDerivative_eq_cartan
    (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual Successor point direction =
      holonomicConjugateMatterDerivativeDual Cartan point direction := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [successor_conjugateMatter_eq_cartan]

private theorem successor_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt Successor.coframe (Point space) =
      identityCoframeMatterGeometry := by
  rw [successor_coframe_eq_cartan]
  exact cartan_coframeFirstJet_zeroSlice space

private theorem successor_adjointActionVelocity_eq_cartan_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Successor
        (Point space) =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Cartan
        (Point space) := by
  apply
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
  · rw [successor_coframe_eq_cartan]
  · exact congrFun successor_gravityConnection_eq_cartan _
  · exact congrFun successor_gaugeConnection_eq_cartan _
  · exact congrFun successor_scalar_eq_cartan _
  · exact congrFun successor_conjugateMatter_eq_cartan _
  · exact fun direction =>
      successor_conjugateMatterDerivative_eq_cartan (Point space) direction

/-- The same action-selected successor satisfies the independently generated
adjoint Dirac action law on the complete fixed P506/L0 zero slice. -/
theorem successor_adjointActionLaw_zeroSlice
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      fixedP506L0LorentzPathActionSelectedJointSuccessor (Point space)
      (holonomicConjugateMatterDerivativeDual
        fixedP506L0LorentzPathActionSelectedJointSuccessor (Point space)
        canonicalLorentzianTimeDirection) := by
  change
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw Successor
      (Point space)
      (holonomicConjugateMatterDerivativeDual Successor (Point space)
        canonicalLorentzianTimeDirection)
  have cartanLaw := cartan_adjointActionLaw_zeroSlice space
  have cartanCoframeOne : Cartan.coframe (Point space) = 1 :=
    coframe_eq_one_of_identity_firstJet Cartan (Point space)
      (cartan_coframeFirstJet_zeroSlice space)
  have cartanNondegenerate :
      Matrix.det (Cartan.coframe (Point space)) ≠ 0 := by
    rw [cartanCoframeOne]
    simp
  have cartanNoncharacteristic :
      coframeTemporalPrincipalScalar (Cartan.coframe (Point space)) ≠ 0 := by
    rw [cartanCoframeOne, coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  have cartanDerivativeEqVelocity :
      holonomicConjugateMatterDerivativeDual Cartan (Point space)
          canonicalLorentzianTimeDirection =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Cartan
          (Point space) :=
    (holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_iff
      Cartan (Point space) cartanNondegenerate cartanNoncharacteristic _).1
      cartanLaw
  have successorDerivativeEqVelocity :
      holonomicConjugateMatterDerivativeDual Successor (Point space)
          canonicalLorentzianTimeDirection =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Successor
          (Point space) :=
    (successor_conjugateMatterDerivative_eq_cartan (Point space)
        canonicalLorentzianTimeDirection).trans
      (cartanDerivativeEqVelocity.trans
        (successor_adjointActionVelocity_eq_cartan_zeroSlice space).symm)
  have successorCoframeOne : Successor.coframe (Point space) = 1 :=
    coframe_eq_one_of_identity_firstJet Successor (Point space)
      (successor_coframeFirstJet_zeroSlice space)
  have successorNondegenerate :
      Matrix.det (Successor.coframe (Point space)) ≠ 0 := by
    rw [successorCoframeOne]
    simp
  have successorNoncharacteristic :
      coframeTemporalPrincipalScalar (Successor.coframe (Point space)) ≠ 0 := by
    rw [successorCoframeOne, coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  exact
    (holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_iff
      Successor (Point space) successorNondegenerate
        successorNoncharacteristic _).2 successorDerivativeEqVelocity

private theorem successor_conjugateMatterCoordinates_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ (holonomicConjugateMatterCoordinates Successor)
      (Point space) := by
  have coordinateEquality :
      holonomicConjugateMatterCoordinates Successor =
        holonomicConjugateMatterCoordinates Coupled := by
    unfold holonomicConjugateMatterCoordinates
    rw [successor_conjugateMatter_eq_cartan,
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
  rw [coordinateEquality]
  simpa [Source, Current, Carry, Coupled, Point,
    completeJointActionSelectedCoupledTemporalActual] using
    actionSelectedCoupled_conjugateMatterCoordinates_differentiableAt_zeroSlice
      space

private theorem successor_coframe_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ Successor.coframe (Point space) := by
  rw [successor_coframe_eq_cartan,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    coupled_coframe_eq_carry, actionSelectedCarry_coframe_eq_one]
  fun_prop

/-- The generated adjoint action law reads out as the exact matter Euler zero
of the same action-selected successor. -/
theorem successor_matterEuler_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient Source Successor
        direction (Point space) = 0 := by
  exact
    holonomicDiracDualMatterEulerLagrange_eq_zero_of_liveActionLaw_identity_firstJet
      Source Successor (Point space)
      (successor_coframe_differentiableAt_zeroSlice space)
      (successor_conjugateMatterCoordinates_differentiableAt_zeroSlice space)
      (successor_coframeFirstJet_zeroSlice space)
      (successor_adjointActionLaw_zeroSlice space)
      direction

/-- The `.matter` coordinate of the same successor joint residual is zero on
the complete fixed P506/L0 zero slice. -/
theorem successor_matterResidual_zeroSlice
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0LorentzPathActionSelectedJointSuccessor
      (Point space)).matter = 0 := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient Source Successor
      direction (Point space) = 0
  exact successor_matterEuler_zeroSlice space direction

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointClosure
