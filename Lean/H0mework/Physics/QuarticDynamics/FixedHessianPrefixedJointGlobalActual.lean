import H0mework.Physics.ElectricJoint.ElectricECResidualTelescoping
import H0mework.Physics.QuarticDynamics.FixedCoupledTemporalOccurrence
import H0mework.Physics.QuarticDynamics.FixedScalarMomentumIdentityECLoadTransport
import H0mework.Physics.IdentityGerms.CoframeHessianLocalActualLift

/-!
# Fixed P506/L0 Hessian-prefixed complete-joint global actual

This module composes two existing action-owned producers on the fixed
P506/L0 source/current occurrence:

```text
radial-plus-scalar current
  -> identity-EC holonomic coframe Hessian write
  -> M/S/A -> P286 algebraic -> P286 live -> Cartan -> EC compiler.
```

Neither constructor consumes a residual, support coordinate, target field,
branch, or free coefficient.  The final theorem isolates the zero-slice
`e1`, Lorentz/EC `(0,3)` read into its Cartan-native value and the final EC
changed-read.  Computing those two generated terms is the remaining
coordinate seam; no observed value is fed back into this candidate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianPrefixedCompleteJointGlobalActual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineDiracDualFormNativeCompleteJointLiveElectricECResidualTelescoping
open StageNineDiracDualFormNativeCompleteJointLiveElectricECSpacetimeOccurrence
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECGravityCurvatureTargetCoordinate
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumIdentityECLoadTransport
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianUpdate
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionCauchySplit
open StageNineResidualLinearPlebanskiTorsionReduction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev HessianIncrement : CoframeHolonomicSecondJet :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    Source Current

private abbrev HessianRows : IdentityECEtaCompatibleRows :=
  sourceActionGeneratedIdentityECCoframeAccelerationRows Source Current

private abbrev LowerOrderRows : LorentzianCoframe :=
  sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates Source Current

/-- The first action-owned leg of the candidate. -/
def fixedP506L0HessianPreparedRadialCoupledCurrent :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
    Source Current

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0HessianPreparedRadialCoupledCurrent

/-- The complete candidate is the existing five-leg compiler restarted on
the Hessian-produced current. -/
def fixedP506L0HessianThenCompleteJointCandidate :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
    Source Prepared

/-- Exact dependent occurrence of the same source/current-only compiler. -/
def fixedP506L0HessianThenCompleteJointOccurrence
    (point : BasePoint) :
    CompleteJointLiveElectricECSpacetimeOccurrence Source Prepared :=
  sourceActionGeneratedCompleteJointLiveElectricECSpacetimeOccurrence
    Source Prepared point

@[simp] theorem occurrence_point
    (point : BasePoint) :
    (fixedP506L0HessianThenCompleteJointOccurrence point).point = point :=
  rfl

/-! ## Canonical zero-slice spatial-one occurrence -/

/-- The unique zero-slice `e₁` point used by the Hessian candidate's
Lorentz/Einstein--Cartan critical pair. -/
abbrev fixedP506L0HessianThenCompleteJointSpatialOnePoint : BasePoint :=
  canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 0)

/-- The dependent occurrence at the canonical zero-slice `e₁` point. -/
abbrev fixedP506L0HessianThenCompleteJointSpatialOneOccurrence :
    CompleteJointLiveElectricECSpacetimeOccurrence Source Prepared :=
  fixedP506L0HessianThenCompleteJointOccurrence
    fixedP506L0HessianThenCompleteJointSpatialOnePoint

/-- The one Cartan output actual shared by every spatial-one readout. -/
abbrev fixedP506L0HessianThenCompleteJointSpatialOneCartanActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0HessianThenCompleteJointSpatialOneOccurrence.after .cartan

/-! ## Exact Hessian field write set -/

@[simp] theorem prepared_coframe :
    Prepared.coframe = fun point =>
      Current.coframe point +
        coframeHolonomicSecondJetQuadraticRealization HessianIncrement point :=
  rfl

@[simp] theorem prepared_gravityConnection :
    Prepared.gravityConnection = fun point =>
      Current.gravityConnection point +
        identityECLeviCivitaAffineConnectionIncrement HessianIncrement point :=
  rfl

@[simp] theorem prepared_gravityAuxiliary :
    Prepared.gravityAuxiliary = fun point =>
      physicalIIPlusBivector
        (Current.coframe point +
          coframeHolonomicSecondJetQuadraticRealization HessianIncrement point) :=
  rfl

@[simp] theorem prepared_gravitySimplicityMultiplier :
    Prepared.gravitySimplicityMultiplier =
      Current.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem prepared_gaugeConnection :
    Prepared.gaugeConnection = Current.gaugeConnection :=
  rfl

@[simp] theorem prepared_gaugeAuxiliary :
    Prepared.gaugeAuxiliary = Current.gaugeAuxiliary :=
  rfl

@[simp] theorem prepared_scalar :
    Prepared.scalar = Current.scalar :=
  rfl

@[simp] theorem prepared_matter :
    Prepared.matter = Current.matter :=
  rfl

@[simp] theorem prepared_conjugateMatter :
    Prepared.conjugateMatter = Current.conjugateMatter :=
  rfl

/-! ## Current-specific generated row normal form -/

/-- The generated ten-row carrier is the eta-compatible projection of the
negative lower-order current rows.  Both sides consume the same fixed
source/current occurrence. -/
theorem hessianRows_coordinate_normalForm
    (row column : LorentzianIndex) :
    HessianRows.1 row column =
      -(LowerOrderRows row column +
          minkowskiInternalSign row * minkowskiInternalSign column *
            LowerOrderRows column row) / 2 := by
  change
    (1 / 2 : ℝ) *
        (-LowerOrderRows row column +
          minkowskiInternalSign row * minkowskiInternalSign column *
            (-LowerOrderRows column row)) =
      _
  ring

/-- Every lower-order row is the literal sum of the current origin gravity
curvature observation and the live identity-EC load on the same coframe
basis direction. -/
theorem lowerOrderRows_coordinate_normalForm
    (row column : LorentzianIndex) :
    LowerOrderRows row column =
      identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0)
          (coframeCoordinateDirection row column) +
        diracDualFormNativeIdentityECLoad Source Current
          (coframeCoordinateDirection row column) := by
  rfl

private theorem current_gravityConnection_eq_globalPreEC :
    Current.gravityConnection =
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gravityConnection := by
  change
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gravityConnection =
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gravityConnection
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gravityConnection_eq_preEC

private theorem current_gravityCurvature_origin_eq_globalPreEC :
    holonomicGravityCurvature Current 0 =
      holonomicGravityCurvature
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 := by
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [current_gravityConnection_eq_globalPreEC]

/-- The Hessian input current retains the generated pre-EC curvature
observation in the temporal--spatial row. -/
theorem current_curvatureObservation_temporalSpatial03 :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Current 0)
        (coframeCoordinateDirection 0 3) =
      (1 / 8 : ℝ) := by
  rw [current_gravityCurvature_origin_eq_globalPreEC]
  exact globalPreEC_curvatureObservation_temporalSpatial03

/-- The opposite row is read from the same generated current curvature. -/
theorem current_curvatureObservation_spatialTemporal30 :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Current 0)
        (coframeCoordinateDirection 3 0) =
      -(1 / 8 : ℝ) := by
  rw [current_gravityCurvature_origin_eq_globalPreEC]
  exact globalPreEC_curvatureObservation_spatialTemporal30

/-- Curvature and the transported live action load cancel exactly in the
`(0,3)` lower row consumed by the Hessian producer. -/
theorem lowerOrderRows_temporalSpatial03_zero :
    LowerOrderRows 0 3 = 0 := by
  rw [lowerOrderRows_coordinate_normalForm,
    current_curvatureObservation_temporalSpatial03,
    current_identityECLoad_temporalSpatial03]
  norm_num

/-- The opposite generated curvature and action-load reads cancel on the
same current as well. -/
theorem lowerOrderRows_spatialTemporal30_zero :
    LowerOrderRows 3 0 = 0 := by
  rw [lowerOrderRows_coordinate_normalForm,
    current_curvatureObservation_spatialTemporal30,
    current_identityECLoad_spatialTemporal30]
  norm_num

/-- The only row needed by the first `(0,3)` Hessian coordinate is the
oriented difference of the two live lower-order reads, not an equality with
the historical contact rows. -/
theorem hessianRows_zero_three_eq_lowerOrderRows :
    HessianRows.1 0 3 =
      (LowerOrderRows 3 0 - LowerOrderRows 0 3) / 2 := by
  rw [hessianRows_coordinate_normalForm]
  have three_ne_zero : (3 : LorentzianIndex) ≠ 0 := by decide
  simp [minkowskiInternalSign, three_ne_zero]
  ring

/-- Both oriented lower rows vanish, so the action-generated Hessian carries
no `(0,3)` component. -/
theorem hessianRows_zero_three_zero :
    HessianRows.1 0 3 = 0 := by
  rw [hessianRows_zero_three_eq_lowerOrderRows,
    lowerOrderRows_temporalSpatial03_zero,
    lowerOrderRows_spatialTemporal30_zero]
  norm_num

/-! ## Exact finite normal form at zero-slice e1 -/

private abbrev SpatialOnePoint : BasePoint :=
  fixedP506L0HessianThenCompleteJointSpatialOnePoint

private theorem spatialOnePoint_eq_coordinateDirection_one :
    SpatialOnePoint = coordinateDirection 1 := by
  ext direction
  fin_cases direction <;>
    simp [SpatialOnePoint, canonicalCauchySlicePoint,
      canonicalSpatialCoordinateDirection, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem current_coframe_spatialOne :
    Current.coframe SpatialOnePoint = 1 := by
  unfold SpatialOnePoint
  exact
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_zeroSlice
      (canonicalSpatialCoordinateDirection 0)

/-- The fixed Hessian itself at `e1` is the finite normal-section coordinate
selected by the source/current-generated ten-row carrier. -/
theorem hessianIncrement_spatialOne_coordinate
    (internal column : LorentzianIndex) :
    HessianIncrement.1 SpatialOnePoint SpatialOnePoint internal column =
      identityECNormalCoframeHessianCoordinate HessianRows.1
        1 1 internal column := by
  rw [spatialOnePoint_eq_coordinateDirection_one]
  change
    (identityECTypedHolonomicCoframeHessianSection HessianRows).1
        (coordinateDirection 1) (coordinateDirection 1) internal column = _
  rw [identityECTypedHolonomicCoframeHessianSection,
    identityECHolonomicCoframeHessianSection_coordinate]

/-- The first off-diagonal coordinate needed by the `(0,3)` Lorentz/EC
read is already fixed by the generated compatible row carrier. -/
theorem hessianIncrement_spatialOne_zero_three :
    HessianIncrement.1 SpatialOnePoint SpatialOnePoint 0 3 =
      HessianRows.1 0 3 / 6 := by
  rw [hessianIncrement_spatialOne_coordinate]
  have compatible := HessianRows.2 (3 : LorentzianIndex) (0 : LorentzianIndex)
  simp [minkowskiInternalSign] at compatible
  simp [identityECNormalCoframeHessianCoordinate,
    identityECNormalMetricHessianCoordinate,
    identityECWeylZeroRiemannCoordinate,
    identityECRicciTensorCoordinate,
    identityECEinsteinTensorCoordinate,
    identityECEinsteinTrace,
    identityECScalarCurvature,
    identityECMinkowskiMetricCoordinate,
    identityECEtaSymmetricPart_typed,
    minkowskiInternalSign, Fin.sum_univ_four]
  linarith

/-- Explicit `4 x 4` normal form of the Hessian-prepared coframe at `e1`.
The only data are the already generated finite action rows. -/
def preparedSpatialOneCoframeNormalForm : LorentzianCoframe :=
  fun internal column =>
    (1 : LorentzianCoframe) internal column +
      (1 / 2 : ℝ) *
        identityECNormalCoframeHessianCoordinate HessianRows.1
          1 1 internal column

theorem prepared_coframe_spatialOne_eq_normalForm :
    Prepared.coframe SpatialOnePoint = preparedSpatialOneCoframeNormalForm := by
  funext internal column
  rw [congrFun prepared_coframe SpatialOnePoint]
  change
    Current.coframe SpatialOnePoint internal column +
        (coframeHolonomicSecondJetQuadraticRealization HessianIncrement
          SpatialOnePoint) internal column =
      _
  rw [congrFun (congrFun current_coframe_spatialOne internal) column]
  change
    (1 : LorentzianCoframe) internal column +
        (1 / 2 : ℝ) *
          HessianIncrement.1 SpatialOnePoint SpatialOnePoint internal column =
      _
  rw [hessianIncrement_spatialOne_coordinate]
  rfl

theorem prepared_coframe_spatialOne_zero_three :
    Prepared.coframe SpatialOnePoint 0 3 = HessianRows.1 0 3 / 12 := by
  rw [congrFun (congrFun prepared_coframe_spatialOne_eq_normalForm 0) 3]
  unfold preparedSpatialOneCoframeNormalForm
  have generated := hessianIncrement_spatialOne_zero_three
  rw [hessianIncrement_spatialOne_coordinate] at generated
  rw [generated]
  have zero_ne_three : (0 : LorentzianIndex) ≠ 3 := by decide
  simp only [Matrix.one_apply, if_neg zero_ne_three]
  ring

/-- The generated e1 coframe therefore retains a zero `(0,3)` entry. -/
theorem prepared_coframe_spatialOne_zero_three_zero :
    Prepared.coframe SpatialOnePoint 0 3 = 0 := by
  rw [prepared_coframe_spatialOne_zero_three,
    hessianRows_zero_three_zero]
  norm_num

/-- The finite lowered LC one-form installed at `e1`; the affine evaluation
selects exactly derivative direction `1`. -/
def preparedSpatialOneLCBivectorOneFormNormalForm :
    LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    identityECLeviCivitaLoweredConnectionFirstJet HessianIncrement
      1 formDirection internalPair

theorem hessianAffineBivectorOneForm_spatialOne_eq_normalForm :
    identityECLeviCivitaAffineBivectorOneForm HessianIncrement SpatialOnePoint =
      preparedSpatialOneLCBivectorOneFormNormalForm := by
  rw [spatialOnePoint_eq_coordinateDirection_one]
  funext formDirection internalPair
  simp [preparedSpatialOneLCBivectorOneFormNormalForm,
    identityECLeviCivitaAffineBivectorOneForm,
    identityECLeviCivitaAffineBivectorComponentLinear,
    coframeBaseCoordinate, coordinateDirection, Fin.sum_univ_four]

/-- Exact finite connection normal form at `e1`: retained radial gravity
connection plus the source/action-generated LC one-form. -/
theorem prepared_gravityConnection_spatialOne_eq_normalForm :
    Prepared.gravityConnection SpatialOnePoint =
      Current.gravityConnection SpatialOnePoint +
        lorentzSkewConnectionOfBivectorOneForm
          preparedSpatialOneLCBivectorOneFormNormalForm := by
  rw [congrFun prepared_gravityConnection SpatialOnePoint]
  unfold identityECLeviCivitaAffineConnectionIncrement
  rw [hessianAffineBivectorOneForm_spatialOne_eq_normalForm]

/-- Exact finite auxiliary normal form at `e1`, recomputed from the same
Hessian-prepared coframe rather than transported from the old current. -/
theorem prepared_gravityAuxiliary_spatialOne_eq_normalForm :
    Prepared.gravityAuxiliary SpatialOnePoint =
      physicalIIPlusBivector preparedSpatialOneCoframeNormalForm := by
  change
    physicalIIPlusBivector (Prepared.coframe SpatialOnePoint) = _
  rw [prepared_coframe_spatialOne_eq_normalForm]

/-! ## Exact five-leg compiler custody -/

/-- The candidate mouth contains only the fixed source/current and the two
existing action-owned operators. -/
theorem candidate_eq_sourceCurrentOnly :
    fixedP506L0HessianThenCompleteJointCandidate =
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
        Source
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
          Source Current) :=
  rfl

@[simp] theorem occurrence_before_matterScalar
    (point : BasePoint) :
    (fixedP506L0HessianThenCompleteJointOccurrence point
      ).before .matterScalar = Prepared :=
  rfl

@[simp] theorem occurrence_finalActual
    (point : BasePoint) :
    (fixedP506L0HessianThenCompleteJointOccurrence point).finalActual =
      fixedP506L0HessianThenCompleteJointCandidate :=
  rfl

/-- Public-source whole-carrier telescope for this exact dependent
occurrence.  Keeping this seam beside the private source abbreviation avoids
exposing an implementation-only index while preserving the literal five
action writes. -/
theorem occurrence_pointwiseJointResidual_telescope
    (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        fixedP506L0HessianThenCompleteJointCandidate point =
      diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
          Prepared point +
        completeJointLiveElectricECReadDelta
          (fun actual =>
            diracDualFormNativePointwiseJointResidual
              positiveSmoothUnifiedSource actual point)
          Prepared
          ((fixedP506L0HessianThenCompleteJointOccurrence point
            ).after .matterScalar) +
        completeJointLiveElectricECReadDelta
          (fun actual =>
            diracDualFormNativePointwiseJointResidual
              positiveSmoothUnifiedSource actual point)
          ((fixedP506L0HessianThenCompleteJointOccurrence point
            ).after .matterScalar)
          ((fixedP506L0HessianThenCompleteJointOccurrence point
            ).after .p286Algebraic) +
        completeJointLiveElectricECReadDelta
          (fun actual =>
            diracDualFormNativePointwiseJointResidual
              positiveSmoothUnifiedSource actual point)
          ((fixedP506L0HessianThenCompleteJointOccurrence point
            ).after .p286Algebraic)
          ((fixedP506L0HessianThenCompleteJointOccurrence point
            ).after .p286LiveElectric) +
        completeJointLiveElectricECReadDelta
          (fun actual =>
            diracDualFormNativePointwiseJointResidual
              positiveSmoothUnifiedSource actual point)
          ((fixedP506L0HessianThenCompleteJointOccurrence point
            ).after .p286LiveElectric)
          ((fixedP506L0HessianThenCompleteJointOccurrence point
            ).after .cartan) +
        completeJointLiveElectricECReadDelta
          (fun actual =>
            diracDualFormNativePointwiseJointResidual
              positiveSmoothUnifiedSource actual point)
          ((fixedP506L0HessianThenCompleteJointOccurrence point
            ).after .cartan)
          fixedP506L0HessianThenCompleteJointCandidate := by
  simpa only [Source, occurrence_point, occurrence_finalActual] using
    CompleteJointLiveElectricECSpacetimeOccurrence.pointwiseJointResidual_final_eq_current_add_allActionDeltas
      (fixedP506L0HessianThenCompleteJointOccurrence point)

/-- Public-source whole-carrier recentering seam on the same generated
Candidate. -/
theorem occurrence_pointwiseJointResidual_eq_recenteredOrigin
    (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        fixedP506L0HessianThenCompleteJointCandidate point =
      diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        ((fixedP506L0HessianThenCompleteJointOccurrence point
          ).recenteredFinalActual) 0 := by
  simpa only [Source, occurrence_point, occurrence_finalActual] using
    (fixedP506L0HessianThenCompleteJointOccurrence point
      ).pointwiseJointResidual_eq_recenteredOrigin

/-- Every compiler edge is the pre-existing native action writer on the
exact preceding actual of this same dependent occurrence. -/
theorem occurrence_after_eq_nativeActionWrite
    (point : BasePoint)
    (leg : CompleteJointLiveElectricECWriteLeg) :
    (fixedP506L0HessianThenCompleteJointOccurrence point).after leg =
      completeJointLiveElectricECActionWrite Source leg
        ((fixedP506L0HessianThenCompleteJointOccurrence point).before leg) :=
  (fixedP506L0HessianThenCompleteJointOccurrence point
    ).after_eq_actionWrite leg

/-- The five action legs form one literal handoff chain, not five unrelated
candidate worlds. -/
theorem occurrence_handoffs
    (point : BasePoint) :
    (fixedP506L0HessianThenCompleteJointOccurrence point
        ).after .matterScalar =
        (fixedP506L0HessianThenCompleteJointOccurrence point
          ).before .p286Algebraic /\
      (fixedP506L0HessianThenCompleteJointOccurrence point
        ).after .p286Algebraic =
        (fixedP506L0HessianThenCompleteJointOccurrence point
          ).before .p286LiveElectric /\
      (fixedP506L0HessianThenCompleteJointOccurrence point
        ).after .p286LiveElectric =
        (fixedP506L0HessianThenCompleteJointOccurrence point
          ).before .cartan /\
      (fixedP506L0HessianThenCompleteJointOccurrence point
        ).after .cartan =
        (fixedP506L0HessianThenCompleteJointOccurrence point
          ).before .einsteinCartan :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## First exact e1 Lorentz/EC reduction -/

/-- The final EC changed-read of the generated candidate occurrence.  It is
a readout only and is not consumed by either writer. -/
def fixedP506L0HessianThenCompleteJointLorentzECDelta :
    PhysicalBivectorThreeForm :=
  completeJointLiveElectricECReadDelta
    (fun actual =>
      (diracDualFormNativePointwiseJointResidual Source actual SpatialOnePoint
        ).lorentzConnection)
    ((fixedP506L0HessianThenCompleteJointOccurrence SpatialOnePoint
      ).after .cartan)
    (fixedP506L0HessianThenCompleteJointOccurrence SpatialOnePoint).finalActual

/-- At the requested zero-slice `e1`, `(0,3)` coordinate, the candidate's
final read is exactly the Cartan-native read plus the single downstream EC
changed-read.  This is the smallest executable seam before finite coordinate
evaluation. -/
theorem fixedP506L0HessianThenCompleteJoint_lorentz003_telescope :
    (diracDualFormNativePointwiseJointResidual Source
        fixedP506L0HessianThenCompleteJointCandidate SpatialOnePoint
      ).lorentzConnection 0 3 =
      (diracDualFormNativePointwiseJointResidual Source
          ((fixedP506L0HessianThenCompleteJointOccurrence SpatialOnePoint
            ).after .cartan)
          SpatialOnePoint).lorentzConnection 0 3 +
        fixedP506L0HessianThenCompleteJointLorentzECDelta 0 3 := by
  have telescoping :=
    CompleteJointLiveElectricECSpacetimeOccurrence.read_final_eq_cartan_native_add_einsteinCartanDelta
      (fixedP506L0HessianThenCompleteJointOccurrence SpatialOnePoint)
      (fun actual =>
        (diracDualFormNativePointwiseJointResidual Source actual SpatialOnePoint
          ).lorentzConnection)
  exact congrFun (congrFun telescoping (0 : Fin 6)) (3 : Fin 4)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianPrefixedCompleteJointGlobalActual
