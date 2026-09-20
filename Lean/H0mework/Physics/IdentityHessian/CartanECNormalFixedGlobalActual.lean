import H0mework.Physics.IdentityHessian.CartanECNormalFixedGlobalRegularity

/-!
# Fixed P506/L0 KIN-16 global actual

The fixed contact-family calculus is compiled in the preceding regularity
module.  This module performs only the faithful diagonal readout and packages
the resulting nine primitive fields as one globally smooth actual.

The split is operational as well as conceptual: it prevents elaboration of
the diagonal aliases from repeatedly unfolding the full action-generated
contact producer.  No atlas, generic-current regularity theory, smoothness
receipt, branch, target, or residual inverse is introduced.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineTopologicalLorentzThreeFormDuality

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

local instance fixedGlobalActualMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance fixedGlobalActualP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity.fixedP286CoordinateIndexFintype

local instance fixedGlobalActualP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity.fixedP286CoordinateIsTopologicalAddGroup

private theorem fixedPrimitiveDiagonal_eq_generated :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual =
      sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState :=
  rfl

private theorem fixedWholeSlice_eq_generated :
    positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent =
      sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState :=
  rfl

/-! ## Opaque value seams from the producer to its diagonal readout -/

private theorem fixedPrimitiveDiagonal_coframe_eq
    (point : BasePoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
        point =
      (fixedIdentityECHessianCartanECNormalContactActual
        (canonicalSpatialProjection point)).coframe
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
  calc
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point)
              (canonicalSpatialProjection point)) := by
          rw [canonicalCauchySlicePoint_projections]
    _ = _ := by
      simpa only [fixedPrimitiveDiagonal_eq_generated,
        ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] using
        primitiveDiagonalActual_coframe_slice
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        (canonicalTimeProjection point)
        (canonicalSpatialProjection point)

private theorem fixedPrimitiveDiagonal_connection_eq
    (point : BasePoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
        point =
      (fixedIdentityECHessianCartanECNormalContactActual
        (canonicalSpatialProjection point)).gravityConnection
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
  calc
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point)
              (canonicalSpatialProjection point)) := by
          rw [canonicalCauchySlicePoint_projections]
    _ = _ := by
      simpa only [fixedPrimitiveDiagonal_eq_generated,
        ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] using
        primitiveDiagonalActual_gravityConnection_slice
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        (canonicalTimeProjection point)
        (canonicalSpatialProjection point)

private theorem fixedPrimitiveDiagonal_auxiliary_eq
    (point : BasePoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityAuxiliary
        point =
      (fixedIdentityECHessianCartanECNormalContactActual
        (canonicalSpatialProjection point)).gravityAuxiliary
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
  calc
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityAuxiliary
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point)
              (canonicalSpatialProjection point)) := by
          rw [canonicalCauchySlicePoint_projections]
    _ = _ := by
      simpa only [fixedPrimitiveDiagonal_eq_generated,
        ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] using
        primitiveDiagonalActual_gravityAuxiliary_slice
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        (canonicalTimeProjection point)
        (canonicalSpatialProjection point)

private theorem fixedPrimitiveDiagonal_multiplier_eq
    (point : BasePoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravitySimplicityMultiplier
        point =
      (fixedIdentityECHessianCartanECNormalContactActual
        (canonicalSpatialProjection point)).gravitySimplicityMultiplier
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
  calc
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravitySimplicityMultiplier
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point)
              (canonicalSpatialProjection point)) := by
          rw [canonicalCauchySlicePoint_projections]
    _ = _ := by
      simpa only [fixedPrimitiveDiagonal_eq_generated,
        ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] using
        primitiveDiagonalActual_multiplier_slice
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        (canonicalTimeProjection point)
        (canonicalSpatialProjection point)

private theorem fixedPrimitiveDiagonal_gaugeConnection_eq
    (point : BasePoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeConnection
        point =
      (fixedIdentityECHessianCartanECNormalContactActual
        (canonicalSpatialProjection point)).gaugeConnection
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
  calc
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeConnection
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point)
              (canonicalSpatialProjection point)) := by
          rw [canonicalCauchySlicePoint_projections]
    _ = _ := by
      simpa only [fixedPrimitiveDiagonal_eq_generated,
        ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] using
        primitiveDiagonalActual_gaugeConnection_slice
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        (canonicalTimeProjection point)
        (canonicalSpatialProjection point)

private theorem fixedPrimitiveDiagonal_gaugeAuxiliary_eq
    (point : BasePoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeAuxiliary
        point =
      (fixedIdentityECHessianCartanECNormalContactActual
        (canonicalSpatialProjection point)).gaugeAuxiliary
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
  calc
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeAuxiliary
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point)
              (canonicalSpatialProjection point)) := by
          rw [canonicalCauchySlicePoint_projections]
    _ = _ := by
      simpa only [fixedPrimitiveDiagonal_eq_generated,
        ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] using
        primitiveDiagonalActual_gaugeAuxiliary_slice
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        (canonicalTimeProjection point)
        (canonicalSpatialProjection point)

private theorem fixedPrimitiveDiagonal_scalar_eq
    (point : BasePoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar
        point =
      (fixedIdentityECHessianCartanECNormalContactActual
        (canonicalSpatialProjection point)).scalar
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
  calc
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point)
              (canonicalSpatialProjection point)) := by
          rw [canonicalCauchySlicePoint_projections]
    _ = _ := by
      simpa only [fixedPrimitiveDiagonal_eq_generated,
        ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] using
        primitiveDiagonalActual_scalar_slice
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        (canonicalTimeProjection point)
        (canonicalSpatialProjection point)

private theorem fixedPrimitiveDiagonal_matter_eq
    (point : BasePoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.matter
        point =
      (fixedIdentityECHessianCartanECNormalContactActual
        (canonicalSpatialProjection point)).matter
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
  calc
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.matter
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point)
              (canonicalSpatialProjection point)) := by
          rw [canonicalCauchySlicePoint_projections]
    _ = _ := by
      simpa only [fixedPrimitiveDiagonal_eq_generated,
        ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] using
        primitiveDiagonalActual_matter_slice
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        (canonicalTimeProjection point)
        (canonicalSpatialProjection point)

private theorem fixedPrimitiveDiagonal_conjugateMatter_eq
    (point : BasePoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.conjugateMatter
        point =
      (fixedIdentityECHessianCartanECNormalContactActual
        (canonicalSpatialProjection point)).conjugateMatter
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
  calc
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.conjugateMatter
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point)
              (canonicalSpatialProjection point)) := by
          rw [canonicalCauchySlicePoint_projections]
    _ = _ := by
      simpa only [fixedPrimitiveDiagonal_eq_generated,
        ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] using
        primitiveDiagonalActual_conjugateMatter_slice
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        (canonicalTimeProjection point)
        (canonicalSpatialProjection point)

/-! ## Globally smooth fixed diagonal -/

private def fixedPrimitiveTimeAxisProjection : BasePoint →L[ℝ] BasePoint :=
  canonicalTimeProjection.smulRight
    (coordinateDirection canonicalLorentzianTimeDirection)

@[simp] private theorem fixedPrimitiveTimeAxisProjection_apply
    (point : BasePoint) :
    fixedPrimitiveTimeAxisProjection point =
      canonicalCauchySlicePoint (canonicalTimeProjection point) 0 := by
  ext direction
  fin_cases direction <;>
    simp [fixedPrimitiveTimeAxisProjection, canonicalCauchySlicePoint,
      canonicalTimeProjection, canonicalLorentzianTimeDirection,
      coordinateDirection, localBaseCoordinate_apply, Fin.sum_univ_three]

private def fixedPrimitiveDiagonalJointPoint
    (point : BasePoint) : StageNineSpatialPoint × BasePoint :=
  (canonicalSpatialProjection point,
    canonicalCauchySlicePoint (canonicalTimeProjection point) 0)

private theorem fixedPrimitiveDiagonalJointPoint_contDiff :
    ContDiff ℝ ∞ fixedPrimitiveDiagonalJointPoint := by
  rw [show fixedPrimitiveDiagonalJointPoint =
      fun point =>
        (canonicalSpatialProjection point,
          fixedPrimitiveTimeAxisProjection point) by
    funext point
    simp [fixedPrimitiveDiagonalJointPoint]]
  exact canonicalSpatialProjection.contDiff.prodMk
    fixedPrimitiveTimeAxisProjection.contDiff

/-- The KIN-16 fixed P506/L0 diagonal is one explicit globally smooth
nine-field actual.  This is the regularity readout of the source/action
producer, not a smoothness premise accepted by that producer. -/
theorem
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.Smooth := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro internal coordinate
    rw [show
      (fun point =>
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
          |>.coframe point internal coordinate) =
      fun point =>
        (fixedIdentityECHessianCartanECNormalContactActual
          (canonicalSpatialProjection point)).coframe
            (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
            internal coordinate by
      funext point
      rw [fixedPrimitiveDiagonal_coframe_eq]]
    simpa only [Function.comp_def, fixedPrimitiveDiagonalJointPoint] using
      (fixedIdentityECHessianCartanECNormalContactActual_coframe_component_contDiff
        internal coordinate).comp fixedPrimitiveDiagonalJointPoint_contDiff
  · intro formDirection internalOut internalIn
    rw [show
      (fun point =>
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
          |>.gravityConnection point formDirection internalOut internalIn) =
      fun point =>
        (fixedIdentityECHessianCartanECNormalContactActual
          (canonicalSpatialProjection point)).gravityConnection
            (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
            formDirection internalOut internalIn by
      funext point
      rw [fixedPrimitiveDiagonal_connection_eq]]
    simpa only [Function.comp_def, fixedPrimitiveDiagonalJointPoint] using
      (fixedIdentityECHessianCartanECNormalContactActual_connection_component_contDiff
        formDirection internalOut internalIn
        ).comp fixedPrimitiveDiagonalJointPoint_contDiff
  · intro internal spacetime
    rw [show
      (fun point =>
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
          |>.gravityAuxiliary point internal spacetime) =
      fun point =>
        (fixedIdentityECHessianCartanECNormalContactActual
          (canonicalSpatialProjection point)).gravityAuxiliary
            (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
            internal spacetime by
      funext point
      rw [fixedPrimitiveDiagonal_auxiliary_eq]]
    simpa only [Function.comp_def, fixedPrimitiveDiagonalJointPoint] using
      ((contDiff_pi.mp
        (contDiff_pi.mp
          fixedIdentityECHessianCartanECNormalContactActual_auxiliary_contDiff
          internal)
        spacetime).comp fixedPrimitiveDiagonalJointPoint_contDiff)
  · intro internal spacetime
    rw [show
      (fun point =>
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
          |>.gravitySimplicityMultiplier point internal spacetime) =
      fun point =>
        (fixedIdentityECHessianCartanECNormalContactActual
          (canonicalSpatialProjection point)).gravitySimplicityMultiplier
            (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
            internal spacetime by
      funext point
      rw [fixedPrimitiveDiagonal_multiplier_eq]]
    simpa only [Function.comp_def, fixedPrimitiveDiagonalJointPoint] using
      (fixedIdentityECHessianCartanECNormalContactActual_multiplier_component_contDiff
        internal spacetime).comp fixedPrimitiveDiagonalJointPoint_contDiff
  · intro formDirection
    rw [show
      (fun point =>
        p286CoordinateEquiv
          (positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            |>.gaugeConnection point formDirection)) =
      fun point =>
        p286CoordinateEquiv
          ((fixedIdentityECHessianCartanECNormalContactActual
            (canonicalSpatialProjection point)).gaugeConnection
              (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
              formDirection) by
      funext point
      rw [fixedPrimitiveDiagonal_gaugeConnection_eq]]
    simpa only [Function.comp_def, fixedPrimitiveDiagonalJointPoint] using
      (fixedIdentityECHessianCartanECNormalContactActual_gaugeConnection_contDiff
        formDirection).comp fixedPrimitiveDiagonalJointPoint_contDiff
  · intro pair
    rw [show
      (fun point =>
        p286CoordinateEquiv
          (positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            |>.gaugeAuxiliary point pair)) =
      fun point =>
        p286CoordinateEquiv
          ((fixedIdentityECHessianCartanECNormalContactActual
            (canonicalSpatialProjection point)).gaugeAuxiliary
              (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
              pair) by
      funext point
      rw [fixedPrimitiveDiagonal_gaugeAuxiliary_eq]]
    simpa only [Function.comp_def, fixedPrimitiveDiagonalJointPoint] using
      (fixedIdentityECHessianCartanECNormalContactActual_gaugeAuxiliary_contDiff
        pair).comp fixedPrimitiveDiagonalJointPoint_contDiff
  · rw [show
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar =
      fun point =>
        (fixedIdentityECHessianCartanECNormalContactActual
          (canonicalSpatialProjection point)).scalar
            (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) by
      funext point
      rw [fixedPrimitiveDiagonal_scalar_eq]]
    simpa only [Function.comp_def, fixedPrimitiveDiagonalJointPoint] using
      fixedIdentityECHessianCartanECNormalContactActual_scalar_contDiff.comp
        fixedPrimitiveDiagonalJointPoint_contDiff
  · rw [show
      (fun point =>
        matterCoordinateEquiv
          (positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            |>.matter point)) =
      fun point =>
        matterCoordinateEquiv
          ((fixedIdentityECHessianCartanECNormalContactActual
            (canonicalSpatialProjection point)).matter
              (canonicalCauchySlicePoint
                (canonicalTimeProjection point) 0)) by
      funext point
      rw [fixedPrimitiveDiagonal_matter_eq]]
    simpa only [Function.comp_def, fixedPrimitiveDiagonalJointPoint] using
      fixedIdentityECHessianCartanECNormalContactActual_matter_contDiff.comp
        fixedPrimitiveDiagonalJointPoint_contDiff
  · intro index
    let matter :=
      matterCoordinateEquiv.symm (EuclideanSpace.single index 1)
    rw [show
      (fun point =>
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
          |>.conjugateMatter point matter) =
      fun point =>
        (fixedIdentityECHessianCartanECNormalContactActual
          (canonicalSpatialProjection point)).conjugateMatter
            (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
            matter by
      funext point
      rw [fixedPrimitiveDiagonal_conjugateMatter_eq]]
    simpa only [Function.comp_def, fixedPrimitiveDiagonalJointPoint] using
      (fixedIdentityECHessianCartanECNormalContactActual_conjugateMatter_contDiff
        matter).comp fixedPrimitiveDiagonalJointPoint_contDiff

/-! ## Complete time-zero Cauchy fidelity -/

private theorem fixedPrimitiveDiagonal_scalar_vacuum :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  funext point
  rw [fixedPrimitiveDiagonal_scalar_eq]
  exact congrFun
    (fixedIdentityECHessianCartanECNormalContactActual_scalar_vacuum
      (canonicalSpatialProjection point))
    (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)

private theorem fixedWholeSlice_scalarVelocity_zero
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.scalarVelocity
        space = 0 := by
  rw [fixedWholeSlice_eq_generated]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState
      space
  rw [reads.2.2.2.2.2.2.2.1]
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  rw [fixedIdentityECHessianCartanECNormalContactActual_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply]

/-- Full KIN-16/KIN-15 time-zero equality.  Unlike the earlier primitive
fidelity record, this theorem includes the derived scalar velocity, computed
from the same globally smooth diagonal scalar field. -/
theorem fixedPrimitiveDiagonal_zeroSlice :
    canonicalCauchyRestriction 0
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent := by
  have fidelity :=
    primitiveDiagonalActual_initialPrimitiveFidelity
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState
  apply StageNineCauchyState.ext
  · funext space
    exact fidelity.coframe space
  · funext space
    exact fidelity.gravityConnection space
  · funext space
    exact fidelity.gravityAuxiliary space
  · funext space
    exact fidelity.multiplier space
  · funext space
    exact fidelity.gaugeConnection space
  · funext space
    exact fidelity.gaugeAuxiliary space
  · funext space
    exact fidelity.scalar space
  · funext space
    change
      fieldDirectionalDerivative
          positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection =
        positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.scalarVelocity
          space
    rw [fixedPrimitiveDiagonal_scalar_vacuum,
      fixedWholeSlice_scalarVelocity_zero]
    simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply]
  · funext space
    exact fidelity.matter space
  · funext space
    exact fidelity.conjugateMatter space

/-! ## Same-global-actual gravity closure -/

/-- Simplicity holds pointwise on the single KIN-16 global actual.  The proof
reads both primitive fields from the same source-generated contact at the
same point; it does not transport any derivative claim across the diagonal. -/
theorem fixedPrimitiveDiagonal_simplicity :
    FormNativeGravitySimplicityEquation
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual := by
  intro point
  rw [fixedPrimitiveDiagonal_auxiliary_eq, fixedPrimitiveDiagonal_coframe_eq]
  have contactSimplicity :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_simplicity
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState
      (canonicalSpatialProjection point)
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] at contactSimplicity
  exact
    contactSimplicity
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)

private theorem fixedCanonicalSlice_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem deriv_along_fixedCanonicalSlice
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → V)
    (space : StageNineSpatialPoint)
    (differentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint 0 space)) :
    deriv (fun time : ℝ => field (canonicalCauchySlicePoint time space)) 0 =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection := by
  let line := fun time : ℝ =>
    time • coordinateDirection canonicalLorentzianTimeDirection +
      canonicalCauchySlicePoint 0 space
  have lineDerivative :
      HasDerivAt line
        (coordinateDirection canonicalLorentzianTimeDirection) 0 := by
    simpa [line] using
      ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const
        (coordinateDirection canonicalLorentzianTimeDirection)).add_const
          (canonicalCauchySlicePoint 0 space)
  have outerDerivative :
      HasFDerivAt field (fderiv ℝ field
        (canonicalCauchySlicePoint 0 space)) (line 0) := by
    simpa [line] using differentiable.hasFDerivAt
  have composed :=
    outerDerivative.comp_hasDerivAt 0 lineDerivative
  unfold fieldDirectionalDerivative
  rw [show
    (fun time : ℝ => field (canonicalCauchySlicePoint time space)) =
      field ∘ line by
        funext time
        congr 1
        ext direction
        fin_cases direction <;>
          simp [line, canonicalCauchySlicePoint,
            canonicalLorentzianTimeDirection, coordinateDirection,
            Fin.sum_univ_three]]
  exact composed.deriv

private theorem fixedPrimitiveDiagonal_coframe_spatialDerivative_zero
    (space : StageNineSpatialPoint)
    (axis : Fin 3)
    (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
            point internal coordinate)
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  let component := fun point : BasePoint =>
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
      point internal coordinate
  have componentDifferentiable :
      DifferentiableAt ℝ component (canonicalCauchySlicePoint 0 space) :=
    ((positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth
      |>.1 internal coordinate).differentiable (by simp)).differentiableAt
  have composed :=
    componentDifferentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  let identityComponent : ℝ :=
    (1 : LorentzianCoframe) internal coordinate
  have composedEquality :
      component ∘ canonicalCauchySlicePoint 0 =
        Function.const StageNineSpatialPoint identityComponent := by
    funext candidate
    change
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
          (canonicalCauchySlicePoint 0 candidate)
            internal coordinate =
        identityComponent
    have zeroSliceValue :=
      congrArg (fun state => state.coframe candidate)
        fixedPrimitiveDiagonal_zeroSlice
    change
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
          (canonicalCauchySlicePoint 0 candidate) =
        positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.coframe
          candidate at zeroSliceValue
    rw [zeroSliceValue,
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_coframe_one]
  have derivativeEquality := composed.fderiv
  rw [composedEquality, fderiv_const] at derivativeEquality
  have atAxis :=
    congrArg
      (fun derivative =>
        derivative (canonicalSpatialCoordinateDirection axis))
      derivativeEquality
  unfold fieldDirectionalDerivative
  simpa [ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection] using atAxis.symm

private theorem fixedPrimitiveDiagonal_coframe_temporalDerivative_zero
    (space : StageNineSpatialPoint)
    (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
            point internal coordinate)
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection = 0 := by
  let globalComponent := fun point : BasePoint =>
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
      point internal coordinate
  let contactComponent := fun point : BasePoint =>
    (fixedIdentityECHessianCartanECNormalContactActual space).coframe
      point internal coordinate
  have globalDifferentiable :
      DifferentiableAt ℝ globalComponent
        (canonicalCauchySlicePoint 0 space) :=
    ((positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth
      |>.1 internal coordinate).differentiable (by simp)).differentiableAt
  have contactContDiff : ContDiff ℝ ∞ contactComponent := by
    simpa [contactComponent, Function.comp_def] using
      (fixedIdentityECHessianCartanECNormalContactActual_coframe_component_contDiff
        internal coordinate).comp
          ((contDiff_const : ContDiff ℝ ∞
            (fun _ : BasePoint => space)).prodMk contDiff_id)
  have contactDifferentiable : DifferentiableAt ℝ contactComponent 0 :=
    (contactContDiff.differentiable (by simp)).differentiableAt
  have curveEquality :
      (fun time : ℝ =>
        globalComponent (canonicalCauchySlicePoint time space)) =
      (fun time =>
        contactComponent (canonicalCauchySlicePoint time 0)) := by
    funext time
    change
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
          (canonicalCauchySlicePoint time space)
            internal coordinate =
        (fixedIdentityECHessianCartanECNormalContactActual space).coframe
          (canonicalCauchySlicePoint time 0) internal coordinate
    rw [fixedPrimitiveDiagonal_coframe_eq]
    simp only [canonicalSpatialProjection_slice, canonicalTimeProjection_slice]
  have contactJet :=
    congrArg
      (fun jet =>
        jet.derivative canonicalLorentzianTimeDirection internal coordinate)
      (fixedIdentityECHessianCartanECNormalContactActual_coframeFirstJet_origin
        space)
  have contactDerivativeZero :
      fieldDirectionalDerivative contactComponent 0
        canonicalLorentzianTimeDirection = 0 := by
    simpa [contactComponent, holonomicCoframeFirstJetAt,
      fieldDirectionalDerivative] using contactJet
  calc
    fieldDirectionalDerivative globalComponent
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      deriv
        (fun time : ℝ =>
          globalComponent (canonicalCauchySlicePoint time space)) 0 :=
      (deriv_along_fixedCanonicalSlice
        globalComponent space globalDifferentiable).symm
    _ = deriv
        (fun time : ℝ =>
          contactComponent (canonicalCauchySlicePoint time 0)) 0 := by
      rw [curveEquality]
    _ = fieldDirectionalDerivative contactComponent 0
        canonicalLorentzianTimeDirection := by
      simpa only [fixedCanonicalSlice_zero_zero] using
        deriv_along_fixedCanonicalSlice contactComponent 0
          (by simpa only [fixedCanonicalSlice_zero_zero] using
            contactDifferentiable)
    _ = 0 := contactDerivativeZero

/-- The explicit KIN-16 diagonal has the complete identity/zero coframe first
jet on its generated time-zero slice.  Spatial derivatives are recomputed
from the whole-slice field, while the temporal derivative is recomputed from
the Hessian contact normal form. -/
theorem fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  apply coframeJet_eq_of_fields_eq
  · have zeroSliceValue :=
      congrArg (fun state => state.coframe space)
        fixedPrimitiveDiagonal_zeroSlice
    change
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
          (canonicalCauchySlicePoint 0 space) = 1
    change
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
          (canonicalCauchySlicePoint 0 space) =
        positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.coframe
          space at zeroSliceValue
    rw [zeroSliceValue,
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_coframe_one]
  · funext derivativeDirection internal coordinate
    fin_cases derivativeDirection
    · exact
        fixedPrimitiveDiagonal_coframe_temporalDerivative_zero
          space internal coordinate
    · exact
        fixedPrimitiveDiagonal_coframe_spatialDerivative_zero
          space 0 internal coordinate
    · exact
        fixedPrimitiveDiagonal_coframe_spatialDerivative_zero
          space 1 internal coordinate
    · exact
        fixedPrimitiveDiagonal_coframe_spatialDerivative_zero
          space 2 internal coordinate

private theorem fixedPrimitiveDiagonal_connection_spatialDerivative_zero
    (space : StageNineSpatialPoint)
    (axis : Fin 3)
    (formDirection internalOut internalIn : LorentzianIndex) :
    gravityConnectionDerivative
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        (canonicalCauchySlicePoint 0 space) axis.succ
        formDirection internalOut internalIn = 0 := by
  let component := fun point : BasePoint =>
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
      point formDirection internalOut internalIn
  have componentDifferentiable :
      DifferentiableAt ℝ component (canonicalCauchySlicePoint 0 space) :=
    ((positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth
      |>.2.1 formDirection internalOut internalIn).differentiable (by simp))
      |>.differentiableAt
  have composed :=
    componentDifferentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  let originComponent : ℝ :=
    (fixedIdentityECHessianCartanECNormalContactActual 0).gravityConnection
      0 formDirection internalOut internalIn
  have composedEquality :
      component ∘ canonicalCauchySlicePoint 0 =
        Function.const StageNineSpatialPoint originComponent := by
    funext candidate
    change
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
          (canonicalCauchySlicePoint 0 candidate)
          formDirection internalOut internalIn =
        originComponent
    rw [fixedPrimitiveDiagonal_connection_eq]
    simp only [canonicalSpatialProjection_slice,
      canonicalTimeProjection_slice, fixedCanonicalSlice_zero_zero]
    exact congrFun
      (congrFun
        (congrFun
          (fixedIdentityECHessianCartanECNormalContactActual_connection_origin_eq
            candidate)
          formDirection)
        internalOut)
      internalIn
  have derivativeEquality := composed.fderiv
  rw [composedEquality, fderiv_const] at derivativeEquality
  have atAxis :=
    congrArg
      (fun derivative =>
        derivative (canonicalSpatialCoordinateDirection axis))
      derivativeEquality
  unfold gravityConnectionDerivative
  simpa [ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection] using atAxis.symm

private theorem
    fixedPrimitiveDiagonal_connection_temporalDerivative_eq_contact
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    gravityConnectionDerivative
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection formDirection internalOut internalIn =
      gravityConnectionDerivative
        (fixedIdentityECHessianCartanECNormalContactActual space) 0
        canonicalLorentzianTimeDirection formDirection internalOut internalIn := by
  let globalComponent := fun point : BasePoint =>
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
      point formDirection internalOut internalIn
  let contactComponent := fun point : BasePoint =>
    (fixedIdentityECHessianCartanECNormalContactActual space).gravityConnection
      point formDirection internalOut internalIn
  have globalDifferentiable :
      DifferentiableAt ℝ globalComponent
        (canonicalCauchySlicePoint 0 space) :=
    ((positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth
      |>.2.1 formDirection internalOut internalIn).differentiable (by simp))
      |>.differentiableAt
  have contactContDiff : ContDiff ℝ ∞ contactComponent := by
    simpa [contactComponent, Function.comp_def] using
      (fixedIdentityECHessianCartanECNormalContactActual_connection_component_contDiff
        formDirection internalOut internalIn).comp
          ((contDiff_const : ContDiff ℝ ∞
            (fun _ : BasePoint => space)).prodMk contDiff_id)
  have contactDifferentiable : DifferentiableAt ℝ contactComponent 0 :=
    (contactContDiff.differentiable (by simp)).differentiableAt
  have curveEquality :
      (fun time : ℝ =>
        globalComponent (canonicalCauchySlicePoint time space)) =
      (fun time =>
        contactComponent (canonicalCauchySlicePoint time 0)) := by
    funext time
    change
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
          (canonicalCauchySlicePoint time space)
          formDirection internalOut internalIn =
        (fixedIdentityECHessianCartanECNormalContactActual space).gravityConnection
          (canonicalCauchySlicePoint time 0)
          formDirection internalOut internalIn
    rw [fixedPrimitiveDiagonal_connection_eq]
    simp only [canonicalSpatialProjection_slice,
      canonicalTimeProjection_slice]
  unfold gravityConnectionDerivative
  calc
    fieldDirectionalDerivative globalComponent
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      deriv
        (fun time : ℝ =>
          globalComponent (canonicalCauchySlicePoint time space)) 0 :=
      (deriv_along_fixedCanonicalSlice
        globalComponent space globalDifferentiable).symm
    _ = deriv
        (fun time : ℝ =>
          contactComponent (canonicalCauchySlicePoint time 0)) 0 := by
      rw [curveEquality]
    _ = fieldDirectionalDerivative contactComponent 0
        canonicalLorentzianTimeDirection := by
      simpa only [fixedCanonicalSlice_zero_zero] using
        deriv_along_fixedCanonicalSlice contactComponent 0
          (by simpa only [fixedCanonicalSlice_zero_zero] using
            contactDifferentiable)

private theorem fixedPrimitiveDiagonal_coframe_zeroSlice_eq_contact
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      (fixedIdentityECHessianCartanECNormalContactActual space).coframe 0 := by
  simpa only [canonicalSpatialProjection_slice, canonicalTimeProjection_slice,
    fixedCanonicalSlice_zero_zero] using
    fixedPrimitiveDiagonal_coframe_eq (canonicalCauchySlicePoint 0 space)

private theorem fixedPrimitiveDiagonal_connection_zeroSlice_eq_contact
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
        (canonicalCauchySlicePoint 0 space) =
      (fixedIdentityECHessianCartanECNormalContactActual
        space).gravityConnection 0 := by
  simpa only [canonicalSpatialProjection_slice, canonicalTimeProjection_slice,
    fixedCanonicalSlice_zero_zero] using
    fixedPrimitiveDiagonal_connection_eq (canonicalCauchySlicePoint 0 space)

/-- Direct mixed-jet adjudication for the spatial `(1,3)` curvature leg.
The KIN-16 global actual has no spatial first derivative in either oriented
connection slot, so this component is exactly the bracket of the common
Cartan origin.  This theorem computes the global field itself; it does not
transport the corresponding KIN-14 contact curvature receipt. -/
theorem fixedPrimitiveDiagonal_curvature_spatialPair_four_zeroSlice
    (space : StageNineSpatialPoint)
    (internalPair : Fin 6) :
    holonomicGravityCurvature
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        (canonicalCauchySlicePoint 0 space) internalPair 4 =
      originLorentzBracketCurvature
        ((fixedIdentityECHessianCartanECNormalContactActual space).gravityConnection
          0) internalPair 4 := by
  unfold holonomicGravityCurvature originLorentzBracketCurvature
  dsimp only
  have pairFirstFour : pairFirst (4 : Fin 6) = 3 := by
    rfl
  have pairSecondFour : pairSecond (4 : Fin 6) = 1 := by
    rfl
  rw [pairFirstFour, pairSecondFour]
  have derivativeThreeOne :
      gravityConnectionDerivative
          positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
          (canonicalCauchySlicePoint 0 space) 3 1
          (pairFirst internalPair) (pairSecond internalPair) = 0 := by
    simpa using
      fixedPrimitiveDiagonal_connection_spatialDerivative_zero
        space 2 1 (pairFirst internalPair) (pairSecond internalPair)
  have derivativeOneThree :
      gravityConnectionDerivative
          positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
          (canonicalCauchySlicePoint 0 space) 1 3
          (pairFirst internalPair) (pairSecond internalPair) = 0 := by
    simpa using
      fixedPrimitiveDiagonal_connection_spatialDerivative_zero
        space 0 3 (pairFirst internalPair) (pairSecond internalPair)
  rw [derivativeThreeOne, derivativeOneThree,
    fixedPrimitiveDiagonal_connection_zeroSlice_eq_contact]
  ring

/-- On the same zero slice, the global `delta B` residual is exactly the
curvature seam against the matched KIN-14 contact.  Auxiliary and reaction
values are read from that contact, while both curvature terms are recomputed
on their respective actuals. -/
theorem fixedPrimitiveDiagonal_auxiliaryResidual_eq_curvatureSeam_zeroSlice
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    holonomicFormNativeGravityAuxiliaryEulerResidual
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        (canonicalCauchySlicePoint 0 space) internalPair spacetimePair =
      holonomicContravariantGravityCurvature
          positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
          (canonicalCauchySlicePoint 0 space) internalPair spacetimePair -
        holonomicContravariantGravityCurvature
          (fixedIdentityECHessianCartanECNormalContactActual space) 0
          internalPair spacetimePair := by
  have contactEquation :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_auxiliaryEquation
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState
      space
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
    at contactEquation
  have contactCoordinate :=
    congrFun
      (congrFun
        (congrFun contactEquation 0)
        internalPair)
      spacetimePair
  have contactCoordinate' :
      holonomicContravariantGravityCurvature
            (fixedIdentityECHessianCartanECNormalContactActual space) 0
            internalPair spacetimePair -
          StageNineBlockwiseConstitutive.gravityInternalDualEquiv
              ((fixedIdentityECHessianCartanECNormalContactActual
                space).gravityAuxiliary 0)
              internalPair spacetimePair +
          (fixedIdentityECHessianCartanECNormalContactActual
              space).gravitySimplicityMultiplier 0
              internalPair spacetimePair =
        0 := by
    simpa only [holonomicFormNativeGravityAuxiliaryEulerResidual_eq,
      Pi.sub_apply, Pi.add_apply, Pi.zero_apply] using contactCoordinate
  simp only [holonomicFormNativeGravityAuxiliaryEulerResidual_eq,
    Pi.sub_apply, Pi.add_apply]
  rw [fixedPrimitiveDiagonal_auxiliary_eq,
    fixedPrimitiveDiagonal_multiplier_eq]
  simp only [canonicalSpatialProjection_slice,
    canonicalTimeProjection_slice, fixedCanonicalSlice_zero_zero]
  linarith [contactCoordinate']

private theorem fixedPrimitiveDiagonal_matter_zeroSlice_eq_contact
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.matter
        (canonicalCauchySlicePoint 0 space) =
      (fixedIdentityECHessianCartanECNormalContactActual space).matter 0 := by
  simpa only [canonicalSpatialProjection_slice, canonicalTimeProjection_slice,
    fixedCanonicalSlice_zero_zero] using
    fixedPrimitiveDiagonal_matter_eq (canonicalCauchySlicePoint 0 space)

private theorem fixedPrimitiveDiagonal_conjugateMatter_zeroSlice_eq_contact
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (fixedIdentityECHessianCartanECNormalContactActual
        space).conjugateMatter 0 := by
  simpa only [canonicalSpatialProjection_slice, canonicalTimeProjection_slice,
    fixedCanonicalSlice_zero_zero] using
    fixedPrimitiveDiagonal_conjugateMatter_eq
      (canonicalCauchySlicePoint 0 space)

/-- On the generated time-zero slice, the single global KIN-16 actual
recomputes the Cartan torsion--spin balance.  The coframe jet is the global
jet proved above; only the algebraic chart-zero spin readout is identified
with the corresponding contact readout. -/
theorem fixedPrimitiveDiagonal_torsionSpin_zeroSlice
    (space : StageNineSpatialPoint) :
    let actual :=
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
    let point := canonicalCauchySlicePoint 0 space
    internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (actual.coframe point)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt actual.coframe point)
              (actual.gravityConnection point))) =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0
          point
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus actual) point) := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let globalActual :=
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
  let contactActual :=
    fixedIdentityECHessianCartanECNormalContactActual space
  let globalField :=
    toContinuumPointField
      (restrictHolonomicConfigurationToIIPlus globalActual) point
  let contactField :=
    toContinuumPointField
      (restrictHolonomicConfigurationToIIPlus contactActual) 0
  have currentCoframeOne :
      positiveP506MatterCurrentFullSynchronizedCauchyState.coframe space =
        1 := by
    change
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe
          (canonicalCauchySlicePoint 0 space) = 1
    exact
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
        (canonicalCauchySlicePoint 0 space)
  have contactClosure :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_torsionSpin_zero
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState
      space currentCoframeOne
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] at contactClosure
  dsimp only at contactClosure
  have coframeEq : globalActual.coframe point = contactActual.coframe 0 := by
    exact fixedPrimitiveDiagonal_coframe_zeroSlice_eq_contact space
  have connectionEq :
      globalActual.gravityConnection point =
        contactActual.gravityConnection 0 := by
    exact fixedPrimitiveDiagonal_connection_zeroSlice_eq_contact space
  have jetEq :
      holonomicCoframeFirstJetAt globalActual.coframe point =
        holonomicCoframeFirstJetAt contactActual.coframe 0 := by
    rw [fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice,
      fixedIdentityECHessianCartanECNormalContactActual_coframeFirstJet_origin]
  have fieldCoframeEq : globalField.coframe = contactField.coframe := by
    change globalActual.coframe point = contactActual.coframe 0
    exact coframeEq
  have fieldMatterEq : globalField.matter = contactField.matter := by
    change globalActual.matter point = contactActual.matter 0
    exact fixedPrimitiveDiagonal_matter_zeroSlice_eq_contact space
  have fieldConjugateMatterEq :
      globalField.conjugateMatter = contactField.conjugateMatter := by
    change
      globalActual.conjugateMatter point =
        contactActual.conjugateMatter 0
    exact fixedPrimitiveDiagonal_conjugateMatter_zeroSlice_eq_contact space
  have spinEq :
      formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0
          point globalField =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0
          0 contactField := by
    change
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
          globalActual point =
        diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
          contactActual 0
    exact
      diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
        positiveSmoothUnifiedSource globalActual contactActual point 0
        fieldCoframeEq fieldMatterEq fieldConjugateMatterEq
  change
    internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (globalActual.coframe point)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt globalActual.coframe point)
              (globalActual.gravityConnection point))) =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0
          point globalField
  rw [coframeEq, jetEq, connectionEq, spinEq]
  exact contactClosure

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
