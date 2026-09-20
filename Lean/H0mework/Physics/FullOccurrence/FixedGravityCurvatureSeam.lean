import H0mework.Physics.ElectricJoint.ElectricECOccurrenceNaturality
import H0mework.Physics.ElectricEC.FixedFullOccurrenceOriginSettlement

/-!
# Fixed P506/L0 full-occurrence global gravity-curvature seam

The source/current-only full-occurrence operator assembles one global
configuration from the local origins of the same ordered five-leg action.
This module identifies its primitive Lorentz connection before reading the
derived curvature seam.

Generically, the diagonal connection is exactly the Cartan restart of the
supplied whole current.  On the fixed P506/L0 lineage, the Einstein--Cartan
suffix of `U5` is invisible to that Cartan producer, so the diagonal
connection is the already generated `PreEC` whole connection.  Consequently
the gravity-curvature assembly seam is exactly

```text
curvature(PreEC, point)
  - EC-target(live action on fullyRecenter(U5, point)).
```

Both terms are generated before the subtraction is read.  No seam,
residual coordinate, target field, branch, or zero-fiber receipt enters a
writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalNaturality
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private theorem canonical_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
      (0 : BasePoint) := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem recentered_coframeFirstJet_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicCoframeFirstJetAt
        (fullyRecenterHolonomicConfiguration current contact).coframe 0 =
      holonomicCoframeFirstJetAt current.coframe contact := by
  apply coframeJet_eq_of_fields_eq
  · exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · funext derivativeDirection internal coordinate
    change
      fieldDirectionalDerivative
          ((fun point => current.coframe point internal coordinate) ∘
            canonicalSpacetimeContactTranslation contact)
          0 derivativeDirection =
        fieldDirectionalDerivative
          (fun point => current.coframe point internal coordinate)
          contact derivativeDirection
    simpa [canonicalSpacetimeContactTranslation] using
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (fun point => current.coframe point internal coordinate)
        contact 0 derivativeDirection

private theorem liveElectric_coframe_eq_recentered
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (completeJointLiveElectricGlobalP286Current source
        (fullyRecenterHolonomicConfiguration current contact)).coframe =
      (fullyRecenterHolonomicConfiguration current contact).coframe := by
  change
    (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator source
      (completeJointGlobalP286AlgebraicCurrent source
        (fullyRecenterHolonomicConfiguration current contact))).coframe =
      _
  rfl

private theorem liveElectric_matter_origin_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (completeJointLiveElectricGlobalP286Current source
        (fullyRecenterHolonomicConfiguration current contact)).matter 0 =
      current.matter contact := by
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source (fullyRecenterHolonomicConfiguration current contact)).matter 0 =
      current.matter contact
  calc
    _ = (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          source (fullyRecenterHolonomicConfiguration current contact)).matter
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
      rw [canonical_zero]
    _ = (fullyRecenterHolonomicConfiguration current contact).matter
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
        source (fullyRecenterHolonomicConfiguration current contact) 0
    _ = current.matter contact := by
      rw [canonical_zero,
        fullyRecenterHolonomicConfiguration_matter_origin]

private theorem liveElectric_conjugateMatter_origin_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (completeJointLiveElectricGlobalP286Current source
        (fullyRecenterHolonomicConfiguration current contact)
      ).conjugateMatter 0 =
      current.conjugateMatter contact := by
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source
      (fullyRecenterHolonomicConfiguration current contact)
      ).conjugateMatter 0 =
      current.conjugateMatter contact
  calc
    _ = (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          source
          (fullyRecenterHolonomicConfiguration current contact)
          ).conjugateMatter
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
      rw [canonical_zero]
    _ = (fullyRecenterHolonomicConfiguration current contact).conjugateMatter
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
        source (fullyRecenterHolonomicConfiguration current contact) 0
    _ = current.conjugateMatter contact := by
      rw [canonical_zero,
        fullyRecenterHolonomicConfiguration_conjugateMatter_origin]

private theorem liveElectric_spinResponse_origin_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    diracDualFormNativeActionSpinResponseAt source
        (completeJointLiveElectricGlobalP286Current source
          (fullyRecenterHolonomicConfiguration current contact)) 0 =
      diracDualFormNativeActionSpinResponseAt source current contact := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
  · rw [liveElectric_coframe_eq_recentered]
    exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · exact liveElectric_matter_origin_eq_current source current contact
  · exact
      liveElectric_conjugateMatter_origin_eq_current source current contact

private theorem liveElectric_actionCartanConnection_origin_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    diracDualFormNativeActionCartanConnectionAt source
        (completeJointLiveElectricGlobalP286Current source
          (fullyRecenterHolonomicConfiguration current contact)) 0 =
      diracDualFormNativeActionCartanConnectionAt source current contact := by
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [liveElectric_coframe_eq_recentered,
    recentered_coframeFirstJet_origin,
    fullyRecenterHolonomicConfiguration_coframe_origin,
    liveElectric_spinResponse_origin_eq_current]

theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).gravityConnection =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current).gravityConnection := by
  funext point
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_at]
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero]
  change
    diracDualFormNativeActionCartanConnectionAt source
        (completeJointLiveElectricGlobalP286Current source
          (fullyRecenterHolonomicConfiguration current point)) 0 =
      diracDualFormNativeActionCartanConnectionAt source current point
  exact liveElectric_actionCartanConnection_origin_eq_current
    source current point

/-- The gravity-curvature coordinate of the exhaustive occurrence seam is
the exact difference between the curvature of the action-generated Cartan
whole field and the EC Full-Cauchy curvature target generated at the matching
recentered occurrence.  Both sides are produced before this readout; the
seam is not used to choose either connection jet. -/
theorem
    completeJointLiveElectricECFullOccurrenceAssemblySeam_gravityCurvature_eq_cartan_sub_target
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (completeJointLiveElectricECFullOccurrenceAssemblySeam
      source current point).gravityCurvature =
      holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) point -
        sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget source
          (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
            source (fullyRecenterHolonomicConfiguration current point)) := by
  change
    holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
            source current) point -
        holonomicGravityCurvature
          (completeJointLiveElectricECFullOccurrenceContact
            source current point) 0 =
      _
  have connectionEq :=
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
      source current
  have globalCurvatureEq :
      holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
            source current) point =
        holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) point := by
    funext internalPair spacetimePair
    unfold holonomicGravityCurvature gravityConnectionDerivative
    rw [connectionEq]
  rw [globalCurvatureEq]
  change
    holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) point -
        holonomicGravityCurvature
          (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source
            (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
              source (fullyRecenterHolonomicConfiguration current point))) 0 =
      _
  rw [←
    sourceActionGeneratedDiracDualECFullCauchyConnectionJetCurvature_eq_holonomic,
    sourceActionGeneratedDiracDualECFullCauchyConnectionJetCurvature_eq_target]

private theorem fixedCurrent_actionCartanConnection_eq_preEC
    (point : BasePoint) :
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual point =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual point := by
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC]
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual
      point
      (congrFun
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC
        point)
      (congrFun
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC
        point)
      (congrFun
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC
        point)
  rw [spinEq]

private theorem preEC_connection_selfGenerated
    (point : BasePoint) :
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gravityConnection
        point =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual point := by
  change
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      positiveSmoothUnifiedSource
      (completeJointLiveElectricGlobalP286Current
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor)).gravityConnection
        point =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          positiveSmoothUnifiedSource
          (completeJointLiveElectricGlobalP286Current
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor))
        point
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
      positiveSmoothUnifiedSource
      (completeJointLiveElectricGlobalP286Current
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor)
      point

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gravityConnection_eq_preEC :
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gravityConnection =
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gravityConnection := by
  rw [show
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gravityConnection =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
      ).gravityConnection by
    exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual]
  funext point
  change
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual point =
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gravityConnection
        point
  rw [fixedCurrent_actionCartanConnection_eq_preEC,
    preEC_connection_selfGenerated]

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam_gravityCurvature_eq_cartan_sub_contact
    (point : BasePoint) :
    (completeJointLiveElectricECFullOccurrenceAssemblySeam
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
      point).gravityCurvature =
      holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual)
          point -
        holonomicGravityCurvature
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact point)
          0 := by
  change
    holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual)
          point -
        holonomicGravityCurvature
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact point)
          0 =
      _
  have connectionEq :=
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
  have curvatureEq :
      holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual)
          point =
        holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual)
          point := by
    funext internalPair spacetimePair
    unfold holonomicGravityCurvature gravityConnectionDerivative
    rw [connectionEq]
  rw [curvatureEq]

private theorem fullOccurrenceContact_gravityCurvature_origin_eq_target
    (point : BasePoint) :
    holonomicGravityCurvature
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact point) 0 =
      sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
        positiveSmoothUnifiedSource
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
          positiveSmoothUnifiedSource
          (fullyRecenterHolonomicConfiguration
            fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
            point)) := by
  change
    holonomicGravityCurvature
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          positiveSmoothUnifiedSource
          (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
            positiveSmoothUnifiedSource
            (fullyRecenterHolonomicConfiguration
              fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
              point))) 0 =
      _
  exact
    (sourceActionGeneratedDiracDualECFullCauchyConnectionJetCurvature_eq_holonomic
      positiveSmoothUnifiedSource
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        positiveSmoothUnifiedSource
        (fullyRecenterHolonomicConfiguration
          fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
          point))).symm.trans
      (sourceActionGeneratedDiracDualECFullCauchyConnectionJetCurvature_eq_target
        positiveSmoothUnifiedSource
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
          positiveSmoothUnifiedSource
          (fullyRecenterHolonomicConfiguration
            fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
            point)))

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam_gravityCurvature_eq_preEC_sub_target
    (point : BasePoint) :
    (completeJointLiveElectricECFullOccurrenceAssemblySeam
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
      point).gravityCurvature =
      holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual
          point -
        sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
          positiveSmoothUnifiedSource
          (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
            positiveSmoothUnifiedSource
            (fullyRecenterHolonomicConfiguration
              fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
              point)) := by
  change
    holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual
          point -
        holonomicGravityCurvature
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact point)
          0 =
      _
  have globalCurvatureEq :
      holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual
          point =
        holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual
          point := by
    funext internalPair spacetimePair
    unfold holonomicGravityCurvature gravityConnectionDerivative
    rw [
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gravityConnection_eq_preEC]
  rw [globalCurvatureEq,
    fullOccurrenceContact_gravityCurvature_origin_eq_target]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
