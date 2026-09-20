import H0mework.Physics.CartanAction.CartanReactionCurrentRestart
import H0mework.Physics.JointVariation.P286TemporalDevelopmentOperator
import H0mework.Physics.JointVariation.TemporalDevelopmentOperator
import H0mework.Physics.FixedJoint.FixedSectionResponse
import H0mework.Physics.DualVariation.P286CanonicalJointActionProducerCore
import H0mework.Physics.Holonomic.HolonomicGaugeCurvatureTransport

/-!
# Global development operator for the complete joint action

This module combines the strongest existing whole-field producers into one
source/current-only write:

```text
current
  -> canonical temporal matter/adjoint/scalar development
  -> canonical P286 connection write and live constitutive auxiliary
  -> source/action P286 temporal exterior development
  -> current-native Cartan connection, computed II+, and live reaction
```

The dependency order is fixed by the mother action.  The constructor accepts
no residual, support coordinate, target field, branch, equation receipt, or
zero-fiber witness.  In particular, the P286 auxiliary is recomputed from the
post-connection curvature before the gravity reaction is generated.

The resulting configuration is one four-dimensional actual, not a family of
contact germs.  The theorems below record the algebraic and Cartan sectors
that this write closes globally.  Matter, scalar, and the remaining P286
connection/coframe equations stay downstream readouts of this same actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineGlobalIntegratedAction
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance completeJointGlobalDevelopmentP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance completeJointGlobalDevelopmentP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## One source/current-only whole-field write -/

/-- The temporal matter/scalar leg of the common global development. -/
def completeJointGlobalTemporalCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
    source current

@[simp] theorem completeJointGlobalTemporalCurrent_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointGlobalTemporalCurrent source current).conjugateMatter =
      fun point =>
        current.conjugateMatter point +
          matterDualOfCoordinates
            (canonicalTimePrimitive
              (completeJointAdjointTemporalCoordinateCorrection source current)
              point) :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter
    source current

/-- The algebraic P286 leg writes the canonical action-principal connection
and recomputes the live constitutive auxiliary on the full temporal actual. -/
def completeJointGlobalP286AlgebraicCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalGeneratedActual source
    (completeJointGlobalTemporalCurrent source current)

/-- The algebraic P286 leg is definitionally the live constitutive image of
its own generated coframe and connection at every occurrence.  This is
producer soundness for the action-owned write, not a supplied equation
receipt. -/
@[simp] theorem completeJointGlobalP286AlgebraicCurrent_constitutiveAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    diracDualFormNativeConstitutiveAuxiliaryField source
        (completeJointGlobalP286AlgebraicCurrent source current) point =
      (completeJointGlobalP286AlgebraicCurrent source current
        ).gaugeAuxiliary point :=
  rfl

/-- The temporal P286 writer is anchored by the literal zero-slice value of
the same algebraic action current produced by the preceding leg. -/
@[simp] theorem completeJointGlobalP286AlgebraicCurrent_zeroSliceAnchor
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    completeJointP286ZeroSliceAnchor source
        (completeJointGlobalP286AlgebraicCurrent source current) space =
      holonomicP286GaugeAuxiliaryCoordinate
        (completeJointGlobalP286AlgebraicCurrent source current)
        (canonicalCauchySlicePoint 0 space) := by
  simp [completeJointGlobalP286AlgebraicCurrent,
    diracDualFormNativeP286CanonicalGeneratedActual,
    diracDualFormNativeP286CanonicalJointCandidate]

/-- The differential P286 leg keeps that connection and advances the same
auxiliary from its action-generated zero slice so the three temporal exterior
coordinates are realized by one global field. -/
def completeJointGlobalP286Current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
    source (completeJointGlobalP286AlgebraicCurrent source current)

/-- One branch-free global complete-joint development.

The final Cartan/reaction restart reads the already developed matter, scalar,
and P286 fields.  No diagnostic carrier is an input at any stage. -/
def sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
    (completeJointGlobalP286Current source current)

/-- The complete global write preserves the algebraic P286 producer's exact
zero-slice value through both the temporal and final Cartan legs. -/
@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate
        (completeJointGlobalP286AlgebraicCurrent source current)
        (canonicalCauchySlicePoint 0 space) := by
  funext pair
  change
    p286CoordinateEquiv
        ((sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
          (completeJointGlobalP286Current source current)).gaugeAuxiliary
          (canonicalCauchySlicePoint 0 space) pair) =
      _
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeAuxiliary]
  change
    holonomicP286GaugeAuxiliaryCoordinate
        (completeJointGlobalP286Current source current)
        (canonicalCauchySlicePoint 0 space) pair =
      _
  rw [completeJointGlobalP286Current,
    congrFun
      (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_gaugeAuxiliary_zeroSlice
        source (completeJointGlobalP286AlgebraicCurrent source current) space)
      pair,
    congrFun
      (completeJointGlobalP286AlgebraicCurrent_zeroSliceAnchor
        source current space)
      pair]

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
      source current).coframe =
      current.coframe := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    completeJointGlobalP286Current,
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_coframe,
    completeJointGlobalP286AlgebraicCurrent,
    diracDualFormNativeP286CanonicalGeneratedActual_coframe,
    completeJointGlobalTemporalCurrent,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe]

/-! ## Global action-generated zero fibers -/

/-- The gravity simplicity field is generated pointwise on the same final
actual. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current) := by
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
      source (completeJointGlobalP286Current source current)

/-- The live gravity reaction closes the auxiliary equation globally. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gravityAuxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravityAuxiliaryEquation
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current) := by
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliaryEquation
      source (completeJointGlobalP286Current source current)

/-- The temporal P286 and final Cartan legs preserve the coframe generated
by the algebraic P286 current. -/
@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe_eq_p286Algebraic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
      source current).coframe =
      (completeJointGlobalP286AlgebraicCurrent source current).coframe :=
  rfl

/-- The same legs preserve the P286 connection, hence its actual curvature. -/
@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gaugeConnection_eq_p286Algebraic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
      source current).gaugeConnection =
      (completeJointGlobalP286AlgebraicCurrent source current
        ).gaugeConnection :=
  rfl

theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gaugeCurvature_eq_p286Algebraic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicGaugeCurvature
        (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
          source current) point =
      holonomicGaugeCurvature
        (completeJointGlobalP286AlgebraicCurrent source current) point := by
  exact
    holonomicGaugeCurvature_eq_of_connection_eq
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current)
      (completeJointGlobalP286AlgebraicCurrent source current)
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gaugeConnection_eq_p286Algebraic
        source current)
      point

theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_pointCoframe_eq_p286Algebraic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (toContinuumPointField
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current) point).coframe =
      (toContinuumPointField
        (completeJointGlobalP286AlgebraicCurrent source current) point
        ).coframe := by
  exact congrFun
    (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe_eq_p286Algebraic
      source current) point

theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_pointGaugeCurvature_eq_p286Algebraic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (toContinuumPointField
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current) point).gaugeCurvature =
      (toContinuumPointField
        (completeJointGlobalP286AlgebraicCurrent source current) point
        ).gaugeCurvature :=
  sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gaugeCurvature_eq_p286Algebraic
    source current point

/-- Exact algebraic/differential compatibility boundary of the joint P286
write.  The algebraic auxiliary equation on the final actual is equivalent
to retaining the unique constitutive value generated immediately before the
temporal exterior homotopy.  This is a readout of one produced actual, not a
constructor premise. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_p286AuxiliaryEquation_iff_algebraicValue
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate :
      Matrix.det
          ((sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
            source current).coframe point) ≠
        0) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField
        (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
          source current) point) ↔
      (toContinuumPointField
        (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
          source current) point).gaugeAuxiliary =
        (toContinuumPointField
          (completeJointGlobalP286AlgebraicCurrent source current) point
          ).gaugeAuxiliary := by
  rw [
    formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField
        (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
          source current) point)
      nondegenerate]
  rw [
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_pointCoframe_eq_p286Algebraic,
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_pointGaugeCurvature_eq_p286Algebraic]
  rfl

/-- The shared zero-slice anchor closes the algebraic P286 auxiliary equation
on every nondegenerate point of the generated Cauchy slice. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_p286AuxiliaryEquation_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (nondegenerate :
      Matrix.det
          ((sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
            source current).coframe
            (canonicalCauchySlicePoint 0 space)) ≠
        0) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField
        (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint 0 space)) := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_p286AuxiliaryEquation_iff_algebraicValue
      source current (canonicalCauchySlicePoint 0 space) nondegenerate]
  funext pair
  apply p286CoordinateEquiv.injective
  exact congrFun
    (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
      source current space)
    pair

private theorem
    holonomicP286GaugeAuxiliaryExteriorDerivative_eq_of_auxiliary_eq
    (first second : StageNineHolonomicConfiguration)
    (auxiliaryEq : first.gaugeAuxiliary = second.gaugeAuxiliary)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative first point =
      holonomicP286GaugeAuxiliaryExteriorDerivative second point := by
  have coordinateEq :
      holonomicP286GaugeAuxiliaryCoordinate first =
        holonomicP286GaugeAuxiliaryCoordinate second := by
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [auxiliaryEq]
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
    p286GaugeAuxiliaryDirectionalDerivative
  rw [coordinateEq]

/-- On the generated zero slice, the final Cartan restart also preserves the
purely spatial `123` coordinate inherited from the algebraic anchor. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_p286ExteriorDerivative_spatial_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (finalP286CoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointGlobalP286Current source current))
        (canonicalCauchySlicePoint 0 space))
    (anchorCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286ZeroSliceAnchoredCurrent source
            (completeJointGlobalP286AlgebraicCurrent source current)))
        (canonicalCauchySlicePoint 0 space)) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint 0 space) 3 =
      holonomicP286GaugeAuxiliaryExteriorDerivative
        (completeJointP286ZeroSliceAnchoredCurrent source
          (completeJointGlobalP286AlgebraicCurrent source current))
        (canonicalCauchySlicePoint 0 space) 3 := by
  have generated :=
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_exteriorDerivative_spatial_zeroSlice
      source (completeJointGlobalP286AlgebraicCurrent source current) space
      (by
        simpa [completeJointGlobalP286Current] using
          finalP286CoordinateDifferentiableAt)
      anchorCoordinateDifferentiableAt
  have preserved :=
    holonomicP286GaugeAuxiliaryExteriorDerivative_eq_of_auxiliary_eq
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current)
      (completeJointGlobalP286Current source current)
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeAuxiliary
        source (completeJointGlobalP286Current source current))
      (canonicalCauchySlicePoint 0 space)
  rw [congrFun preserved 3]
  exact generated

/-- The final Cartan restart preserves the P286 temporal producer.  Thus the
same final common actual realizes all three time-containing pure-exterior
coordinates generated from the post-connection algebraic current. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_p286ExteriorDerivative_temporal
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (triple : Fin 4)
    (temporal : triple ≠ 3)
    (finalP286CoordinateSmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointGlobalP286Current source current)))
    (anchorCoordinateSmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286ZeroSliceAnchoredCurrent source
            (completeJointGlobalP286AlgebraicCurrent source current))))
    (correctionIntervalIntegrable :
      ∀ pair : Fin 6,
        IntervalIntegrable
          (fun candidateTime =>
            completeJointP286TemporalCorrectionProfile source
              (completeJointGlobalP286AlgebraicCurrent source current)
              (canonicalCauchySlicePoint candidateTime space) pair)
          MeasureTheory.volume 0 time)
    (correctionMeasurableAt :
      ∀ pair : Fin 6,
        StronglyMeasurableAtFilter
          (fun candidateTime =>
            completeJointP286TemporalCorrectionProfile source
              (completeJointGlobalP286AlgebraicCurrent source current)
              (canonicalCauchySlicePoint candidateTime space) pair)
          (nhds time) MeasureTheory.volume)
    (correctionContinuousAt :
      ∀ pair : Fin 6,
        ContinuousAt
          (fun candidateTime =>
            completeJointP286TemporalCorrectionProfile source
              (completeJointGlobalP286AlgebraicCurrent source current)
              (canonicalCauchySlicePoint candidateTime space) pair)
          time) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint time space) triple =
      completeJointP286RequiredExteriorProfile source
        (completeJointGlobalP286AlgebraicCurrent source current)
        (canonicalCauchySlicePoint time space) triple := by
  have generated :=
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_exteriorDerivative_temporal
      source (completeJointGlobalP286AlgebraicCurrent source current)
      space time triple temporal finalP286CoordinateSmooth
      anchorCoordinateSmooth correctionIntervalIntegrable
      correctionMeasurableAt correctionContinuousAt
  have preserved :=
    holonomicP286GaugeAuxiliaryExteriorDerivative_eq_of_auxiliary_eq
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current)
      (completeJointGlobalP286Current source current)
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeAuxiliary
        source (completeJointGlobalP286Current source current))
      (canonicalCauchySlicePoint time space)
  rw [congrFun preserved triple]
  exact generated

/-- Wherever the pre-Cartan global current is nondegenerate, the same final
actual satisfies the complete Cartan torsion--spin equation. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_torsionSpin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate :
      (completeJointGlobalP286Current source current).Nondegenerate) :
    FormNativeIIPlusTorsionSpinEquation source
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current) := by
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_torsionSpinEquation
      source (completeJointGlobalP286Current source current) nondegenerate

/-- Under the same regularity hypotheses, the Lorentz Euler three-form
vanishes globally on the one generated actual. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_lorentzZero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : (completeJointGlobalP286Current source current).Smooth)
    (nondegenerate :
      (completeJointGlobalP286Current source current).Nondegenerate) :
    holonomicFormNativeLorentzEulerThreeForm source 0
        (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
          source current) =
      0 := by
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero
      source (completeJointGlobalP286Current source current) smooth
      nondegenerate

/-! ## Fixed P506/L0 specialization -/

/-- The authoritative fixed source and solved current select one global
complete-joint development without adding any source datum or branch. -/
def fixedP506L0CompleteJointGlobalDevelopmentActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
    positiveSmoothUnifiedSource FixedP506FormNativeJointActionSolvedSuccessor

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
