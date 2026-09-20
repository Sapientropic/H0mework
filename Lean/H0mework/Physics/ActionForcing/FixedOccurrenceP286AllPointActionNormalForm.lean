import H0mework.Physics.ActualGerms.FixedP286AuxiliaryFirstJet
import H0mework.Physics.ActualGerms.FixedZeroSliceCoframe
import H0mework.Physics.ActionForcing.FixedOccurrenceP286ActionForcingBridge

/-!
# Fixed U6 occurrence P286 all-point action normal form

This module expands the authoritative fixed P506/L0 Algebraic Euler field in
four explicit three-form coordinates.  The canonical `D_A B` row is assembled
from the generated connection, auxiliary value, and auxiliary first jet.  The
charged row is reconstructed from the scalar-plus-Dirac mother-action covector
through the faithful P286 pairing.

The final theorems connect that finite primitive normal form to the temporal
correction and occurrence forcing already certified by the action-forcing
bridge.  No residual, target jet, support branch, successor, or zero receipt
is accepted by any definition.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6OccurrenceP286AllPointActionNormalForm

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCompleteJointP286CanonicalOccurrenceWriteProfile
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicConnectionChangedRead
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualP286AuxiliaryFirstJet
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualZeroSliceCoframe
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ActionForcingBridge
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286RadialQuarticActionPrincipal
open StageNineP286SpatialVolumeTemporalActionDuality
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance allPointActionNormalFormP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source Input

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source Input

private abbrev Canonical : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

/-! ## Faithful charged three-form coordinates -/

/-- Linear inclusion of one P286 coordinate into one connection direction. -/
def p286SingleGaugeOneFormLinear (direction : LorentzianIndex) :
    P286CoordinateCarrier →ₗ[ℝ] P286GaugeOneForm where
  toFun := singleP286GaugeOneForm direction
  map_add' := by
    intro first second
    classical
    funext formDirection
    by_cases same : formDirection = direction
    · subst formDirection
      simp [singleP286GaugeOneForm]
    · simp [singleP286GaugeOneForm, same]
  map_smul' := by
    intro parameter coordinate
    classical
    funext formDirection
    by_cases same : formDirection = direction
    · subst formDirection
      simp [singleP286GaugeOneForm]
    · simp [singleP286GaugeOneForm, same]

/-- Action covector dual to one charged three-form coordinate, including the
fixed W13 orientation sign. -/
def p286ChargedGaugeThreeFormComponentActionDual
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (triple : Fin 4) : Module.Dual ℝ P286CoordinateCarrier :=
  let direction := missingTripleOfOneForm triple
  oneWedgeThreeSign direction •
    ((formNativeChargedGaugeFirstLinearMap source chart point field).comp
      (p286SingleGaugeOneFormLinear direction))

/-- Faithful internal coordinate of one charged W13 three-form component. -/
def p286ChargedGaugeThreeFormComponentNormalForm
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (triple : Fin 4) : P286CoordinateCarrier :=
  p286CoordinateLiePairingEquiv.symm
    (p286ChargedGaugeThreeFormComponentActionDual
      source chart point field triple)

theorem formNativeChargedGaugeThreeForm_apply_eq_componentNormalForm
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (triple : Fin 4) :
    formNativeChargedGaugeThreeForm source chart point field triple =
      p286ChargedGaugeThreeFormComponentNormalForm
        source chart point field triple := by
  apply p286CoordinateLiePairingEquiv.injective
  unfold p286ChargedGaugeThreeFormComponentNormalForm
  rw [p286CoordinateLiePairingEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro coordinate
  change
    p286CoordinateLiePairing
        (formNativeChargedGaugeThreeForm source chart point field triple)
        coordinate =
      oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeChargedGaugeFirstCoefficient source chart point field
          (singleP286GaugeOneForm (missingTripleOfOneForm triple) coordinate)
  rw [← formNativeChargedGaugeThreeForm_evaluation]
  change
    p286CoordinateLiePairing
        (formNativeChargedGaugeThreeForm source chart point field triple)
        coordinate =
      oneWedgeThreeSign (missingTripleOfOneForm triple) *
        p286GaugeThreeFormWedgeLinearDual
            (formNativeChargedGaugeThreeForm source chart point field)
          (singleP286GaugeOneForm (missingTripleOfOneForm triple) coordinate)
  rw [p286GaugeThreeFormWedgeLinearDual_single_apply]
  fin_cases triple <;>
    simp [missingTripleOfOneForm, oneWedgeThreeSign,
      p286CoordinateLiePairing_symmetric]

/-! ## Temporal primitive action data -/

def fixedP506L0TemporalScalarActionNormalForm
    (point : BasePoint) : ScalarCoordinateCarrier :=
  Input.scalar point +
    canonicalTimeSecondPrimitive
      (completeJointScalarAccelerationProfile Source Input) point

def fixedP506L0TemporalMatterActionNormalForm
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  Input.matter point +
    matterCoordinateEquiv.symm
      (canonicalTimePrimitive
        (completeJointMatterTemporalCoordinateCorrection Source Input) point)

def fixedP506L0TemporalConjugateMatterActionNormalForm
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  Input.conjugateMatter point +
    matterDualOfCoordinates
      (canonicalTimePrimitive
        (completeJointAdjointTemporalCoordinateCorrection Source Input) point)

def fixedP506L0TemporalScalarCovariantActionNormalForm
    (point : BasePoint) : LorentzianIndex → ScalarCoordinateCarrier :=
  fun direction =>
    fieldDirectionalDerivative fixedP506L0TemporalScalarActionNormalForm
        point direction +
      scalarMotherLieAction
        (p286LieBlockEmbed (Input.gaugeConnection point direction))
        (fixedP506L0TemporalScalarActionNormalForm point)

/-- Exactly the primitive fields consumed by the charged P286 action. -/
def fixedP506L0TemporalChargedActionPointNormalForm
    (point : BasePoint) : StageNineContinuumPointField :=
  { toContinuumPointField Temporal point with
    coframe := Input.coframe point
    scalar := fixedP506L0TemporalScalarActionNormalForm point
    scalarCovariantDerivative :=
      fixedP506L0TemporalScalarCovariantActionNormalForm point
    matter := fixedP506L0TemporalMatterActionNormalForm point
    conjugateMatter :=
      fixedP506L0TemporalConjugateMatterActionNormalForm point }

theorem fixedP506L0Temporal_pointField_eq_chargedActionNormalForm
    (point : BasePoint) :
    toContinuumPointField Temporal point =
      fixedP506L0TemporalChargedActionPointNormalForm point := by
  apply StageNineContinuumPointField.ext <;> rfl

def fixedP506L0TemporalChargedThreeFormComponentNormalForm
    (point : BasePoint) (triple : Fin 4) : P286CoordinateCarrier :=
  p286ChargedGaugeThreeFormComponentNormalForm Source 0 point
    (fixedP506L0TemporalChargedActionPointNormalForm point) triple

theorem fixedP506L0Temporal_chargedGaugeThreeForm_apply_actionNormalForm
    (point : BasePoint) (triple : Fin 4) :
    formNativeChargedGaugeThreeForm Source 0 point
          (toContinuumPointField Temporal point) triple =
      fixedP506L0TemporalChargedThreeFormComponentNormalForm point triple := by
  rw [formNativeChargedGaugeThreeForm_apply_eq_componentNormalForm]
  unfold fixedP506L0TemporalChargedThreeFormComponentNormalForm
    p286ChargedGaugeThreeFormComponentNormalForm
  apply congrArg p286CoordinateLiePairingEquiv.symm
  apply LinearMap.ext
  intro coordinate
  unfold p286ChargedGaugeThreeFormComponentActionDual
  simp only [LinearMap.smul_apply, LinearMap.coe_comp,
    Function.comp_apply, p286SingleGaugeOneFormLinear,
    formNativeChargedGaugeFirstLinearMap_apply]
  rw [fixedP506L0Temporal_pointField_eq_chargedActionNormalForm]

/-! ## Canonical `D_A B` and Algebraic Euler four-row normal forms -/

def fixedP506L0CanonicalP286CovariantAuxiliaryJetNormalForm
    (point : BasePoint) (direction : LorentzianIndex) : P286GaugeTwoForm :=
  fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryFirstJetNormalForm
        point direction +
    p286GaugeTwoFormAdjoint
      (fixedP506L0P286CanonicalGeneratedGaugeConnectionCoordinateNormalForm
        point direction)
      (fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryCoordinateNormalForm
        point)

/-- Explicit `(012,013,023,123)` coordinate row for canonical `D_A B`. -/
def fixedP506L0CanonicalP286ExteriorFourTripleNormalForm
    (point : BasePoint) : P286GaugeThreeForm :=
  let row := fixedP506L0CanonicalP286CovariantAuxiliaryJetNormalForm point
  ![row 0 5 - row 1 1 + row 2 0,
    -row 0 4 - row 1 2 + row 3 0,
    row 0 3 - row 2 2 + row 3 1,
    row 1 3 + row 2 4 + row 3 5]

theorem
    fixedP506L0CanonicalP286ExteriorFourTripleNormalForm_eq_generatedNormalForm
    (point : BasePoint) :
    fixedP506L0CanonicalP286ExteriorFourTripleNormalForm point =
      fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryExteriorCovariantDerivativeNormalForm
        point := by
  funext triple
  fin_cases triple <;>
    simp [fixedP506L0CanonicalP286ExteriorFourTripleNormalForm,
      fixedP506L0CanonicalP286CovariantAuxiliaryJetNormalForm,
      fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryExteriorCovariantDerivativeNormalForm,
      pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
      pointwiseP286GaugeTwoFormCovariantDerivative,
      threeFormFirst, threeFormSecond, threeFormThird] <;>
    abel

def fixedP506L0AlgebraicP286EulerTripleActionNormalForm
    (point : BasePoint) (triple : Fin 4) : P286CoordinateCarrier :=
  fixedP506L0CanonicalP286ExteriorFourTripleNormalForm point triple +
    fixedP506L0TemporalChargedThreeFormComponentNormalForm point triple

theorem fixedP506L0_Algebraic_p286Euler_apply_actionNormalForm
    (point : BasePoint)
    (nondegenerate :
      Matrix.det (fixedP506L0P286CanonicalActionInput.coframe point) ≠ 0)
    (triple : Fin 4) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic point triple =
      fixedP506L0AlgebraicP286EulerTripleActionNormalForm point triple := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_eq_canonicalExterior_add_temporalCharged]
  simp only [Pi.add_apply]
  rw [
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryExteriorCovariantDerivative_normalForm
      point nondegenerate,
    ← fixedP506L0CanonicalP286ExteriorFourTripleNormalForm_eq_generatedNormalForm,
    fixedP506L0Temporal_chargedGaugeThreeForm_apply_actionNormalForm]
  rfl

def fixedP506L0AlgebraicP286EulerFourTripleActionNormalForm
    (point : BasePoint) : P286GaugeThreeForm :=
  ![fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 0,
    fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 1,
    fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 2,
    fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 3]

theorem fixedP506L0_Algebraic_p286Euler_fourTripleActionNormalForm
    (point : BasePoint)
    (nondegenerate :
      Matrix.det (fixedP506L0P286CanonicalActionInput.coframe point) ≠ 0) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic point =
      fixedP506L0AlgebraicP286EulerFourTripleActionNormalForm point := by
  funext triple
  fin_cases triple <;>
    exact fixedP506L0_Algebraic_p286Euler_apply_actionNormalForm
      point nondegenerate _

/-- Faithful occurrence one-form coordinates
`(A₀,A₁,A₂,A₃) = (E₁₂₃,−E₀₂₃,E₀₁₃,−E₀₁₂)`. -/
def fixedP506L0AlgebraicP286EulerOccurrenceOneFormActionNormalForm
    (point : BasePoint) : P286GaugeOneForm :=
  ![fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 3,
    -fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 2,
    fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 1,
    -fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 0]

theorem fixedP506L0AlgebraicP286Euler_occurrenceOneForm_actionNormalForm
    (point : BasePoint) :
    p286GaugeThreeFormOccurrenceOneFormNormalForm
        (fixedP506L0AlgebraicP286EulerFourTripleActionNormalForm point) =
      fixedP506L0AlgebraicP286EulerOccurrenceOneFormActionNormalForm point := by
  funext direction
  fin_cases direction <;>
    simp [fixedP506L0AlgebraicP286EulerFourTripleActionNormalForm,
      fixedP506L0AlgebraicP286EulerOccurrenceOneFormActionNormalForm,
      p286GaugeThreeFormOccurrenceOneFormNormalForm,
      missingTripleOfOneForm, oneWedgeThreeSign]

/-! ## Connection to the authoritative temporal-support carrier -/

theorem fixedP506L0AlgebraicActionEulerTimeCorrection_apply_actionNormalForm
    (point : BasePoint)
    (nondegenerate :
      Matrix.det (fixedP506L0P286CanonicalActionInput.coframe point) ≠ 0)
    (triple : Fin 4) :
    fixedP506L0AlgebraicActionEulerTimeCorrection point triple =
      fixedP506L0AlgebraicP286EulerTripleActionNormalForm point triple -
        (fixedP506L0RadialActionEulerField point) triple := by
  have whole := congrFun
    (fixedP506L0_Algebraic_p286Euler_eq_radial_add_timeCorrection point)
    triple
  simp only [Pi.add_apply] at whole
  calc
    fixedP506L0AlgebraicActionEulerTimeCorrection point triple =
        ((fixedP506L0RadialActionEulerField point) triple +
          fixedP506L0AlgebraicActionEulerTimeCorrection point triple) -
            (fixedP506L0RadialActionEulerField point) triple := by
      abel
    _ = holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          point triple -
        (fixedP506L0RadialActionEulerField point) triple := by
      rw [← whole]
    _ = _ := by
      rw [fixedP506L0_Algebraic_p286Euler_apply_actionNormalForm
        point nondegenerate triple]

private theorem fixedP506L0AlgebraicActionEulerTimeCorrection_012
    (point : BasePoint)
    (nondegenerate :
      Matrix.det (fixedP506L0P286CanonicalActionInput.coframe point) ≠ 0) :
    fixedP506L0AlgebraicActionEulerTimeCorrection point 0 =
      fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 0 := by
  rw [fixedP506L0AlgebraicActionEulerTimeCorrection_apply_actionNormalForm
    point nondegenerate 0]
  simp [fixedP506L0RadialActionEulerField,
    p286SpatialVolumeGaugeThreeForm]

private theorem fixedP506L0AlgebraicActionEulerTimeCorrection_013
    (point : BasePoint)
    (nondegenerate :
      Matrix.det (fixedP506L0P286CanonicalActionInput.coframe point) ≠ 0) :
    fixedP506L0AlgebraicActionEulerTimeCorrection point 1 =
      fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 1 := by
  rw [fixedP506L0AlgebraicActionEulerTimeCorrection_apply_actionNormalForm
    point nondegenerate 1]
  simp [fixedP506L0RadialActionEulerField,
    p286SpatialVolumeGaugeThreeForm]

private theorem fixedP506L0AlgebraicActionEulerTimeCorrection_023
    (point : BasePoint)
    (nondegenerate :
      Matrix.det (fixedP506L0P286CanonicalActionInput.coframe point) ≠ 0) :
    fixedP506L0AlgebraicActionEulerTimeCorrection point 2 =
      fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 2 := by
  rw [fixedP506L0AlgebraicActionEulerTimeCorrection_apply_actionNormalForm
    point nondegenerate 2]
  simp [fixedP506L0RadialActionEulerField,
    p286SpatialVolumeGaugeThreeForm]

private theorem fixedP506L0AlgebraicActionEulerTimeCorrection_123
    (point : BasePoint)
    (nondegenerate :
      Matrix.det (fixedP506L0P286CanonicalActionInput.coframe point) ≠ 0) :
    fixedP506L0AlgebraicActionEulerTimeCorrection point 3 =
      fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 3 -
        p286SpatialRadiusSquared point •
          fixedP506L0U6OccurrenceP286MotherActionCharge := by
  rw [fixedP506L0AlgebraicActionEulerTimeCorrection_apply_actionNormalForm
    point nondegenerate 3]
  simp [fixedP506L0RadialActionEulerField,
    p286SpatialVolumeGaugeThreeForm]

/-- Complete finite four-coordinate form of the all-point temporal support.
The first three entries are the time-bearing Euler rows; the `123` entry has
the generated radial zero-time contribution removed. -/
theorem fixedP506L0AlgebraicActionEulerTimeCorrection_fourTripleActionNormalForm
    (point : BasePoint)
    (nondegenerate :
      Matrix.det (fixedP506L0P286CanonicalActionInput.coframe point) ≠ 0) :
    fixedP506L0AlgebraicActionEulerTimeCorrection point =
      ![fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 0,
        fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 1,
        fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 2,
        fixedP506L0AlgebraicP286EulerTripleActionNormalForm point 3 -
          p286SpatialRadiusSquared point •
            fixedP506L0U6OccurrenceP286MotherActionCharge] := by
  funext triple
  fin_cases triple
  · exact fixedP506L0AlgebraicActionEulerTimeCorrection_012
      point nondegenerate
  · exact fixedP506L0AlgebraicActionEulerTimeCorrection_013
      point nondegenerate
  · exact fixedP506L0AlgebraicActionEulerTimeCorrection_023
      point nondegenerate
  · exact fixedP506L0AlgebraicActionEulerTimeCorrection_123
      point nondegenerate

/-- The pairing inverse of the authoritative U6 occurrence forcing is the
explicit occurrence one-form normal form on every nondegenerate authoritative
contact. -/
theorem fixedP506L0_U6_occurrenceForcing_pairingInverse_actionNormalForm_inDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space)
    (nondegenerate :
      Matrix.det
          (fixedP506L0P286CanonicalActionInput.coframe
            (canonicalCauchySlicePoint time space)) ≠ 0) :
    let contact := canonicalCauchySlicePoint time space
    p286GaugeOneFormPairingEquiv.symm
        (diracDualFormNativeP286CanonicalOriginActionForcing Source
          (completeJointGlobalTemporalCurrent Source
            (fullyRecenterHolonomicConfiguration U6 contact))) =
      fixedP506L0AlgebraicP286EulerOccurrenceOneFormActionNormalForm
        contact := by
  dsimp only
  let contact := canonicalCauchySlicePoint time space
  rw [
    fixedP506L0_U6_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_inDomain
      time space inDomain,
    p286PairingInverse_wedgeDual_allComponents,
    fixedP506L0_Algebraic_p286Euler_fourTripleActionNormalForm
      contact nondegenerate,
    fixedP506L0AlgebraicP286Euler_occurrenceOneForm_actionNormalForm]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6OccurrenceP286AllPointActionNormalForm
