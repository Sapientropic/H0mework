import H0mework.Physics.Holonomic.HolonomicField
import H0mework.Physics.GaugeAction.P286Bianchi

/-!
# S9-C3h0: source-generated normalized affine P286 connection germ

This module converts the existing proof-free P286 source value and exterior
derivative into an actual primitive `P286ConnectionField`.  The so-called
source target is not a curvature slot: `sourceP286TargetCurvature` is derived
from the primitive `sourceGaugeCurvature` and the canonical P286 generator.
The source exterior derivative is then generated as that derived curvature
minus the live non-Abelian `[A,A]` bracket.

The only affine normalization is `1/2`, forced because the two oriented
first-jet terms double an antisymmetric component.  Actual Fréchet
differentiation and `dA+[A,A]` recover the derived source curvature at the
origin; neither curvature nor a realization, branch, coefficient, Bianchi, or
stationarity receipt is stored in the connection.

The installer accepts an arbitrary prior configuration and changes only its
primitive gauge connection.  It definitionally preserves the other eight
primitive fields, nondegeneracy, and smoothness, and therefore inherits the
actual off-shell P286 Bianchi identity on smooth templates.  It never fills a
full configuration with zero or arbitrary fields.

The affine function is used only as an origin local germ.  No global
extension, raw-action integrability, joint-shell stationarity, or terminal
zero-fiber claim is made.  Exact P506/L0 lineage and endpoint 11 remain source
admission readouts; Factor atomhood is not a physical source premise.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceGeneratedP286AffineConnectionGerm

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286Bianchi
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-- Continuous projection onto one coordinate of the canonical Euclidean
base.  This P286-local definition avoids importing the gravity germ merely
for a generic coordinate map. -/
def p286BaseCoordinate (direction : LorentzianIndex) : BasePoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj direction).comp
    (EuclideanSpace.equiv LorentzianIndex ℝ).toContinuousLinearMap

@[simp] theorem p286BaseCoordinate_apply
    (direction : LorentzianIndex) (point : BasePoint) :
    p286BaseCoordinate direction point = point direction :=
  rfl

/-! ## Canonical antisymmetric source jet -/

/-- Antisymmetric extension of the six actual source P286 exterior-derivative
coordinates, ordered `(01,02,03,23,31,12)`. -/
def sourceP286ExteriorDerivativeComponent
    (source : ProofFreeRicherAnholonomicSource.Source)
    (first second : LorentzianIndex) : P286LieBlockData :=
  if first = 0 ∧ second = 1 then sourceP286ExteriorDerivative source 0
  else if first = 1 ∧ second = 0 then -sourceP286ExteriorDerivative source 0
  else if first = 0 ∧ second = 2 then sourceP286ExteriorDerivative source 1
  else if first = 2 ∧ second = 0 then -sourceP286ExteriorDerivative source 1
  else if first = 0 ∧ second = 3 then sourceP286ExteriorDerivative source 2
  else if first = 3 ∧ second = 0 then -sourceP286ExteriorDerivative source 2
  else if first = 2 ∧ second = 3 then sourceP286ExteriorDerivative source 3
  else if first = 3 ∧ second = 2 then -sourceP286ExteriorDerivative source 3
  else if first = 3 ∧ second = 1 then sourceP286ExteriorDerivative source 4
  else if first = 1 ∧ second = 3 then -sourceP286ExteriorDerivative source 4
  else if first = 1 ∧ second = 2 then sourceP286ExteriorDerivative source 5
  else if first = 2 ∧ second = 1 then -sourceP286ExteriorDerivative source 5
  else 0

theorem sourceP286ExteriorDerivativeComponent_antisymm
    (source : ProofFreeRicherAnholonomicSource.Source)
    (first second : LorentzianIndex) :
    sourceP286ExteriorDerivativeComponent source first second =
      -sourceP286ExteriorDerivativeComponent source second first := by
  fin_cases first <;> fin_cases second <;>
    simp [sourceP286ExteriorDerivativeComponent]

@[simp] theorem sourceP286ExteriorDerivativeComponent_pair
    (source : ProofFreeRicherAnholonomicSource.Source) (pair : Fin 6) :
    sourceP286ExteriorDerivativeComponent source
        (pairFirst pair) (pairSecond pair) =
      sourceP286ExteriorDerivative source pair := by
  fin_cases pair <;>
    simp [sourceP286ExteriorDerivativeComponent, pairFirst, pairSecond]

/-- The affine increment as a genuine continuous linear map in the existing
finite P286 coordinates. -/
def sourceP286AffineIncrementLinear
    (source : ProofFreeRicherAnholonomicSource.Source)
    (formDirection : LorentzianIndex) :
    BasePoint →L[ℝ] P286CoordinateCarrier :=
  (1 / 2 : ℝ) •
    ∑ derivativeDirection : LorentzianIndex,
      (p286BaseCoordinate derivativeDirection).smulRight
        (p286CoordinateEquiv
          (sourceP286ExteriorDerivativeComponent source
            derivativeDirection formDirection))

/-- Source-only affine coordinate field.  Its constructor accepts no target
curvature, branch witness, coefficient, or stationarity receipt. -/
def sourceP286AffineConnectionCoordinate
    (source : ProofFreeRicherAnholonomicSource.Source) (point : BasePoint)
    (formDirection : LorentzianIndex) : P286CoordinateCarrier :=
  p286CoordinateEquiv (sourceP286Potential source formDirection) +
    sourceP286AffineIncrementLinear source formDirection point

/-- Actual primitive P286 connection field obtained by returning from the
finite coordinate chart. -/
def sourceP286AffineConnectionField
    (source : ProofFreeRicherAnholonomicSource.Source) : P286ConnectionField :=
  fun point formDirection =>
    p286CoordinateEquiv.symm
      (sourceP286AffineConnectionCoordinate source point formDirection)

@[simp] theorem sourceP286AffineIncrementLinear_zero
    (source : ProofFreeRicherAnholonomicSource.Source)
    (formDirection : LorentzianIndex) :
    sourceP286AffineIncrementLinear source formDirection 0 = 0 :=
  map_zero _

@[simp] theorem sourceP286AffineConnectionField_origin
    (source : ProofFreeRicherAnholonomicSource.Source)
    (formDirection : LorentzianIndex) :
    sourceP286AffineConnectionField source 0 formDirection =
      sourceP286Potential source formDirection := by
  simp [sourceP286AffineConnectionField,
    sourceP286AffineConnectionCoordinate]

/-- The actual connection coordinate field is componentwise smooth. -/
theorem sourceP286AffineConnectionField_smooth
    (source : ProofFreeRicherAnholonomicSource.Source)
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        (sourceP286AffineConnectionField source point formDirection) := by
  simpa [sourceP286AffineConnectionField,
    sourceP286AffineConnectionCoordinate] using
      (contDiff_const.add
        (sourceP286AffineIncrementLinear source formDirection).contDiff)

/-! ## Actual holonomic curvature readout -/

/-- Directional differentiation reads precisely half of the antisymmetric
source exterior-derivative component. -/
theorem sourceP286AffineConnectionCoordinate_directionalDerivative_origin
    (source : ProofFreeRicherAnholonomicSource.Source)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          sourceP286AffineConnectionCoordinate source point formDirection)
        0 derivativeDirection =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv
          (sourceP286ExteriorDerivativeComponent source
            derivativeDirection formDirection) := by
  unfold fieldDirectionalDerivative sourceP286AffineConnectionCoordinate
  let increment := sourceP286AffineIncrementLinear source formDirection
  rw [fderiv_const_add]
  rw [increment.hasFDerivAt.fderiv]
  change
    sourceP286AffineIncrementLinear source formDirection
        (coordinateDirection derivativeDirection) = _
  simp only [sourceP286AffineIncrementLinear]
  fin_cases derivativeDirection <;> fin_cases formDirection <;>
    simp [coordinateDirection, Fin.sum_univ_four]

/-- Antisymmetrizing the canonical affine first jet recovers the exact
source P286 exterior derivative, with no compatibility condition left over. -/
theorem sourceP286AffineConnectionCoordinate_antisymmetrizedDerivative_pair
    (source : ProofFreeRicherAnholonomicSource.Source) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          sourceP286AffineConnectionCoordinate source point
            (pairSecond pair))
        0 (pairFirst pair) -
      fieldDirectionalDerivative
        (fun point =>
          sourceP286AffineConnectionCoordinate source point
            (pairFirst pair))
        0 (pairSecond pair) =
      p286CoordinateEquiv (sourceP286ExteriorDerivative source pair) := by
  rw [sourceP286AffineConnectionCoordinate_directionalDerivative_origin,
    sourceP286AffineConnectionCoordinate_directionalDerivative_origin,
    sourceP286ExteriorDerivativeComponent_antisymm source
      (pairSecond pair) (pairFirst pair),
    sourceP286ExteriorDerivativeComponent_pair]
  simp only [map_neg]
  module

/-- Install the source-generated primitive P286 connection into an arbitrary
prior configuration.  This is a one-field installer, not a producer of the
other eight primitive fields and not a zero-filled full configuration. -/
def installSourceP286AffineConnection
    (source : ProofFreeRicherAnholonomicSource.Source)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gaugeConnection := sourceP286AffineConnectionField source }

@[simp] theorem installSourceP286AffineConnection_gaugeConnection
    (source : ProofFreeRicherAnholonomicSource.Source)
    (configuration : StageNineHolonomicConfiguration) :
    (installSourceP286AffineConnection source configuration).gaugeConnection =
      sourceP286AffineConnectionField source :=
  rfl

/-- The installer definitionally preserves every primitive field outside the
P286 connection sector. -/
theorem installSourceP286AffineConnection_preserves_otherFields
    (source : ProofFreeRicherAnholonomicSource.Source)
    (configuration : StageNineHolonomicConfiguration) :
    (installSourceP286AffineConnection source configuration).coframe =
        configuration.coframe ∧
      (installSourceP286AffineConnection source
          configuration).gravityConnection = configuration.gravityConnection ∧
      (installSourceP286AffineConnection source
          configuration).gravityAuxiliary = configuration.gravityAuxiliary ∧
      (installSourceP286AffineConnection source
          configuration).gravitySimplicityMultiplier =
        configuration.gravitySimplicityMultiplier ∧
      (installSourceP286AffineConnection source
          configuration).gaugeAuxiliary = configuration.gaugeAuxiliary ∧
      (installSourceP286AffineConnection source configuration).scalar =
        configuration.scalar ∧
      (installSourceP286AffineConnection source configuration).matter =
        configuration.matter ∧
      (installSourceP286AffineConnection source
          configuration).conjugateMatter = configuration.conjugateMatter := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem installSourceP286AffineConnection_nondegenerate_iff
    (source : ProofFreeRicherAnholonomicSource.Source)
    (configuration : StageNineHolonomicConfiguration) :
    (installSourceP286AffineConnection source configuration).Nondegenerate ↔
      configuration.Nondegenerate :=
  Iff.rfl

/-- A smooth prior template remains smooth because the replacement P286
connection has affine smooth coordinates. -/
theorem installSourceP286AffineConnection_smooth
    (source : ProofFreeRicherAnholonomicSource.Source)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (installSourceP286AffineConnection source configuration).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, _oldGaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    gravityMultiplierSmooth, sourceP286AffineConnectionField_smooth source,
    gaugeAuxiliarySmooth, scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

/-- Kinematic compatibility checkpoint: installing the source-generated
connection into any smooth template inherits the actual off-shell P286
differential Bianchi identity.  This is not a stationarity theorem. -/
theorem installSourceP286AffineConnection_offShellBianchi
    (source : ProofFreeRicherAnholonomicSource.Source)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantCurvatureDerivative
          (installSourceP286AffineConnection source configuration)
          point first second third +
        covariantCurvatureDerivative
          (installSourceP286AffineConnection source configuration)
          point second third first +
        covariantCurvatureDerivative
          (installSourceP286AffineConnection source configuration)
          point third first second = 0 := by
  exact holonomicP286GaugeCurvature_bianchi
    (installSourceP286AffineConnection source configuration)
    (installSourceP286AffineConnection_smooth source configuration smooth)
    point first second third

theorem installSourceP286AffineConnection_connectionDerivative_antisymm
    (source : ProofFreeRicherAnholonomicSource.Source)
    (configuration : StageNineHolonomicConfiguration) (pair : Fin 6) :
    p286ConnectionDerivative
        (installSourceP286AffineConnection source configuration) 0
        (pairFirst pair) (pairSecond pair) -
      p286ConnectionDerivative
        (installSourceP286AffineConnection source configuration) 0
        (pairSecond pair) (pairFirst pair) =
      sourceP286ExteriorDerivative source pair := by
  apply p286CoordinateEquiv.injective
  simp only [map_sub, p286ConnectionDerivative,
    p286CoordinateEquiv.apply_symm_apply]
  simp only [installSourceP286AffineConnection,
    sourceP286AffineConnectionField, p286CoordinateEquiv.apply_symm_apply]
  change
    fieldDirectionalDerivative
        (fun point =>
          sourceP286AffineConnectionCoordinate source point
            (pairSecond pair))
        0 (pairFirst pair) -
      fieldDirectionalDerivative
        (fun point =>
          sourceP286AffineConnectionCoordinate source point
            (pairFirst pair))
        0 (pairSecond pair) =
      p286CoordinateEquiv (sourceP286ExteriorDerivative source pair)
  exact
    sourceP286AffineConnectionCoordinate_antisymmetrizedDerivative_pair
      source pair

/-- Generic source-generated producer theorem: the actual primitive
`dA + [A,A]` curvature at the origin equals the existing source target. -/
theorem holonomicGaugeCurvature_installSourceP286AffineConnection_origin
    (source : ProofFreeRicherAnholonomicSource.Source)
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGaugeCurvature
        (installSourceP286AffineConnection source configuration) 0 =
      sourceP286TargetCurvature source := by
  funext pair
  unfold holonomicGaugeCurvature
  rw [installSourceP286AffineConnection_connectionDerivative_antisymm]
  change
    sourceP286ExteriorDerivative source pair +
        p286LieBracket
          (sourceP286AffineConnectionField source 0 (pairFirst pair))
          (sourceP286AffineConnectionField source 0 (pairSecond pair)) =
      sourceP286TargetCurvature source pair
  rw [sourceP286AffineConnectionField_origin,
    sourceP286AffineConnectionField_origin]
  simp [sourceP286ExteriorDerivative]

/-! ## Exact-lineage positive specialization -/

def positiveSourceP286AffineConnectionField : P286ConnectionField :=
  sourceP286AffineConnectionField positiveSmoothUnifiedSource.legacy

theorem positiveSourceP286AffineConnection_origin
    (formDirection : LorentzianIndex) :
    positiveSourceP286AffineConnectionField 0 formDirection =
      sourceP286Potential positiveSmoothUnifiedSource.legacy formDirection :=
  sourceP286AffineConnectionField_origin _ _

theorem positiveSourceP286AffineConnection_actualCurvature
    (template : StageNineHolonomicConfiguration) :
    holonomicGaugeCurvature
        (installSourceP286AffineConnection
          positiveSmoothUnifiedSource.legacy template) 0 =
      sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy :=
  holonomicGaugeCurvature_installSourceP286AffineConnection_origin _ _

/-- The producer is tied to the same exact P506/L0 source and endpoint 11;
lineage remains an admission theorem rather than a field of the connection. -/
theorem positiveExactLineage_generates_P286AffineConnectionGerm
    (template : StageNineHolonomicConfiguration) :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
          canonicalSource_generatedLineage_height_pos = 11 ∧
      (∀ formDirection,
        positiveSourceP286AffineConnectionField 0 formDirection =
          sourceP286Potential positiveSmoothUnifiedSource.legacy
            formDirection) ∧
      holonomicGaugeCurvature
          (installSourceP286AffineConnection
            positiveSmoothUnifiedSource.legacy template) 0 =
        sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy := by
  exact ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
    positiveSmoothUnifiedSource_generates_endpoint_eleven,
    positiveSourceP286AffineConnection_origin,
    positiveSourceP286AffineConnection_actualCurvature template⟩

end

end SaturationMonoid.PhysicsCore.StageNineSourceGeneratedP286AffineConnectionGerm
