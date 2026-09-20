import H0mework.Physics.SafeCauchy.FixedP286TemporalExactification
import H0mework.Physics.Cauchy.P286RelativeScalarConstraintOperator

/-!
# SafeFinal P286 normal-scalar initial constraint

This file specializes the connection-relative scalar normal-constraint
writer to the exact SafeFinal constitutive occurrence.  The writer computes
its scalar time jet from the supplied coframe, spatial scalar jet, and P286
connection; it accepts no velocity, residual, target zero, or stationarity
premise.

Killing the scalar temporal current is not by itself the spatial Gauss law.
The second half therefore computes the remaining `123` row and generates its
canonical equal-axis auxiliary first-jet correction.  This is exact Cauchy
constraint data.  It deliberately does not pretend that a global covariant
development realizing that pointwise jet has already been constructed.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeP286NormalScalarInitialConstraint

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConnectionSectorSourceBalance
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalECJetRegularity
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeP286TemporalExactification
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalFourFormPairing
open StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance safeNormalConstraintP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance safeNormalConstraintP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev Current : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source Prepared

private abbrev GlobalConstitutive : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalConstitutiveCurrent Source Current

/-- The exact SafeFinal constitutive occurrence with only its scalar Cauchy
time jet recomputed by the normal-momentum evaluator. -/
def fixedP506L0CartanECConstraintCauchySafeP286NormalScalarActual :
    StageNineHolonomicConfiguration :=
  p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
    GlobalConstitutive

private abbrev NormalScalar : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeP286NormalScalarActual

private theorem globalConstitutive_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (GlobalConstitutive.coframe point) ≠ 0 := by
  change coframeTemporalPrincipalScalar (Prepared.coframe point) ≠ 0
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_noncharacteristic
      point

/-- Smoothness is derived from the total current-computed formula. -/
theorem fixedP506L0CartanECConstraintCauchySafeP286NormalScalarActual_smooth :
    NormalScalar.Smooth :=
  normalConstraint_smooth GlobalConstitutive
    fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_smooth
    fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_nondegenerate
    globalConstitutive_noncharacteristic

private theorem globalConstitutive_scalar_differentiable
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ GlobalConstitutive.scalar
      (canonicalCauchySlicePoint 0 space) :=
  (fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_smooth
      |>.2.2.2.2.2.2.1 |>.differentiable (by simp)).differentiableAt

private theorem normalScalar_scalar_differentiable
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ NormalScalar.scalar
      (canonicalCauchySlicePoint 0 space) :=
  (fixedP506L0CartanECConstraintCauchySafeP286NormalScalarActual_smooth
      |>.2.2.2.2.2.2.1 |>.differentiable (by simp)).differentiableAt

/-- The scalar temporal P286 current is identically settled on the complete
SafeFinal initial slice, for every Lie-algebra coordinate. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286NormalScalarActual_scalarCurrent_temporal_zeroSlice
    (space : StageNineSpatialPoint) (component : P286CoordinateCarrier) :
    p286ScalarCurrentCoefficient Source NormalScalar
        (p286TemporalGaugeOneForm component)
        (canonicalCauchySlicePoint 0 space) = 0 := by
  apply normalConstraint_p286ScalarCurrent_temporal_zeroSlice
  · exact globalConstitutive_noncharacteristic _
  · exact globalConstitutive_scalar_differentiable space
  · exact normalScalar_scalar_differentiable space

/-! ## Honest spatial-row readout -/

private theorem p286TemporalGaugeOneForm_wedge_reads_spatial123
    (coordinate : P286CoordinateCarrier)
    (threeForm : P286GaugeThreeForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient
        (p286TemporalGaugeOneForm coordinate) threeForm =
      p286CoordinateLiePairing coordinate (threeForm 3) := by
  classical
  unfold p286GaugeOneFormThreeFormWedgeCoefficient
    p286TemporalGaugeOneForm canonicalLorentzianTimeDirection
    oneWedgeThreeSign missingTripleOfOneForm
  simp [Fin.sum_univ_four]

private theorem formNativeChargedGaugeFirstCoefficient_eq_currentSectors
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    formNativeChargedGaugeFirstCoefficient Source 0 point
        (toContinuumPointField configuration point) direction =
      p286ScalarCurrentCoefficient Source configuration direction point +
        p286MatterCurrentCoefficient Source configuration direction point := by
  unfold formNativeChargedGaugeFirstCoefficient
    p286ScalarCurrentCoefficient p286MatterCurrentCoefficient
  rw [pointwiseScalarP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point,
    pointwiseMatterP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point, mul_add]

private theorem p286Euler_spatial123_coordinate_eq_sectors
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint)
    (component : P286CoordinateCarrier) :
    p286CoordinateLiePairing component
        ((holonomicFormNativeP286GaugeEulerThreeForm Source 0 configuration
          point) 3) =
      p286CoordinateLiePairing component
          ((holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
            configuration point) 3) +
        p286ScalarCurrentCoefficient Source configuration
          (p286TemporalGaugeOneForm component) point +
        p286MatterCurrentCoefficient Source configuration
          (p286TemporalGaugeOneForm component) point := by
  rw [← p286TemporalGaugeOneForm_wedge_reads_spatial123]
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
    formNativeChargedGaugeThreeForm_evaluation,
    formNativeChargedGaugeFirstCoefficient_eq_currentSectors,
    p286TemporalGaugeOneForm_wedge_reads_spatial123]
  ring

/-- The exact current-specific remainder after the scalar normal constraint:
only the inherited covariant auxiliary exterior row and the actual matter
current remain. -/
def fixedP506L0CartanECConstraintCauchySafeP286NormalScalarGaussRemainder
    (space : StageNineSpatialPoint) (component : P286CoordinateCarrier) : ℝ :=
  let point := canonicalCauchySlicePoint 0 space
  p286CoordinateLiePairing component
      ((holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        NormalScalar point) 3) +
    p286MatterCurrentCoefficient Source NormalScalar
      (p286TemporalGaugeOneForm component) point

/-- Direct residual consumer.  This theorem prevents the scalar settlement
from being mistaken for the complete Gauss law. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286NormalScalarActual_euler_spatial123_eq_gaussRemainder
    (space : StageNineSpatialPoint) (component : P286CoordinateCarrier) :
    p286CoordinateLiePairing component
        ((holonomicFormNativeP286GaugeEulerThreeForm Source 0 NormalScalar
          (canonicalCauchySlicePoint 0 space)) 3) =
      fixedP506L0CartanECConstraintCauchySafeP286NormalScalarGaussRemainder
        space component := by
  rw [p286Euler_spatial123_coordinate_eq_sectors]
  rw [fixedP506L0CartanECConstraintCauchySafeP286NormalScalarActual_scalarCurrent_temporal_zeroSlice]
  simp [fixedP506L0CartanECConstraintCauchySafeP286NormalScalarGaussRemainder]

/-! ## Current-computed canonical Gauss first jet -/

/-- The single spatial `123` exterior correction computed from the current's
own action read.  No caller can supply a target residual. -/
def fixedP506L0CartanECConstraintCauchySafeP286GaussExteriorCorrection
    (space : StageNineSpatialPoint) : P286GaugeThreeForm :=
  let point := canonicalCauchySlicePoint 0 space
  fun triple =>
    if triple = 3 then
      pointwiseDirectP286RequiredExteriorDerivative Source NormalScalar point 3 -
        holonomicP286GaugeAuxiliaryExteriorDerivative NormalScalar point 3
    else 0

/-- Canonical equal-axis first jet.  It preserves the supplied auxiliary
value and adds only the right-inverse image of the computed `123` defect. -/
def fixedP506L0CartanECConstraintCauchySafeP286CanonicalGaussFirstJet
    (space : StageNineSpatialPoint) (direction : LorentzianIndex) :
    P286GaugeTwoForm :=
  let point := canonicalCauchySlicePoint 0 space
  p286GaugeAuxiliaryDirectionalDerivative NormalScalar point direction +
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
      (fixedP506L0CartanECConstraintCauchySafeP286GaussExteriorCorrection
        space) direction

private theorem exteriorDerivative_add
    (first second : LorentzianIndex → P286GaugeTwoForm) :
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
        (first + second) =
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative first +
        pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative second := by
  funext triple
  simp [pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
    orderedP286GaugeTwoFormComponent_add]
  abel

/-- The generated first jet settles the spatial exterior responsibility
exactly at every point of the initial slice. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286CanonicalGaussFirstJet_exterior_spatial123
    (space : StageNineSpatialPoint) :
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
        (fixedP506L0CartanECConstraintCauchySafeP286CanonicalGaussFirstJet
          space) 3 =
    pointwiseDirectP286RequiredExteriorDerivative Source NormalScalar
        (canonicalCauchySlicePoint 0 space) 3 := by
  rw [show
    fixedP506L0CartanECConstraintCauchySafeP286CanonicalGaussFirstJet space =
      p286GaugeAuxiliaryDirectionalDerivative NormalScalar
          (canonicalCauchySlicePoint 0 space) +
        formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
          (fixedP506L0CartanECConstraintCauchySafeP286GaussExteriorCorrection
            space) by rfl]
  rw [exteriorDerivative_add,
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative_canonical]
  simp only [Pi.add_apply]
  change
    holonomicP286GaugeAuxiliaryExteriorDerivative NormalScalar
          (canonicalCauchySlicePoint 0 space) 3 +
        fixedP506L0CartanECConstraintCauchySafeP286GaussExteriorCorrection
          space 3 = _
  simp [fixedP506L0CartanECConstraintCauchySafeP286GaussExteriorCorrection]

/-- Standard covariant Gauss equation evaluated on the generated first jet.
The value-level connection action and charged current remain those of the
same exact SafeFinal occurrence. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286CanonicalGaussFirstJet_covariant_spatial123
    (space : StageNineSpatialPoint) :
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
          (fixedP506L0CartanECConstraintCauchySafeP286CanonicalGaussFirstJet
            space) 3 +
        pointwiseP286GaugeTwoFormConnectionExteriorAction
          (holonomicP286GaugeConnectionCoordinate NormalScalar
            (canonicalCauchySlicePoint 0 space))
          (holonomicP286GaugeAuxiliaryCoordinate NormalScalar
            (canonicalCauchySlicePoint 0 space)) 3 =
      formNativePhysicalChargedGaugeCurrentThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField NormalScalar
          (canonicalCauchySlicePoint 0 space)) 3 := by
  rw [fixedP506L0CartanECConstraintCauchySafeP286CanonicalGaussFirstJet_exterior_spatial123]
  unfold pointwiseDirectP286RequiredExteriorDerivative
  simp only [Pi.sub_apply]
  abel

/-- The actual, not-yet-rewritten Safe current's spatial Euler row is exactly
the gap between its realized first jet and the generated canonical Gauss
first jet.  This is the direct mouth for a covariant Cauchy development. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286NormalScalarActual_euler_spatial123_eq_firstJetRealizationGap
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 NormalScalar
        (canonicalCauchySlicePoint 0 space) 3 =
      holonomicP286GaugeAuxiliaryExteriorDerivative NormalScalar
          (canonicalCauchySlicePoint 0 space) 3 -
        pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
          (fixedP506L0CartanECConstraintCauchySafeP286CanonicalGaussFirstJet
            space) 3 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts]
  have generated :=
    fixedP506L0CartanECConstraintCauchySafeP286CanonicalGaussFirstJet_covariant_spatial123
      space
  unfold formNativePhysicalChargedGaugeCurrentThreeForm at generated
  simp only [Pi.add_apply, Pi.neg_apply] at generated ⊢
  have actionEq :
      pointwiseP286GaugeTwoFormConnectionExteriorAction
          (holonomicP286GaugeConnectionCoordinate NormalScalar
            (canonicalCauchySlicePoint 0 space))
          (holonomicP286GaugeAuxiliaryCoordinate NormalScalar
            (canonicalCauchySlicePoint 0 space)) 3 =
        -formNativeChargedGaugeThreeForm Source 0
            (canonicalCauchySlicePoint 0 space)
            (toContinuumPointField NormalScalar
              (canonicalCauchySlicePoint 0 space)) 3 -
          pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
            (fixedP506L0CartanECConstraintCauchySafeP286CanonicalGaussFirstJet
              space) 3 :=
    eq_sub_of_add_eq (by simpa [add_comm] using generated)
  rw [actionEq]
  abel

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeP286NormalScalarInitialConstraint
end PhysicsCore
end SaturationMonoid
