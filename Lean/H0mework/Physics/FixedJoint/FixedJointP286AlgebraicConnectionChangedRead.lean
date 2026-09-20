import H0mework.Physics.FullOccurrence.FixedP286Verdict
import H0mework.Physics.ScalarJets.FixedJointP286AlgebraicMatterScalarDelta

/-!
# Fixed P506/L0 algebraic P286 connection changed read

The fixed canonical P286 action write is already proved to be zero.  Hence
the algebraic leg carries the temporal matter/scalar fields without a new
connection increment, while its complete `D_A B` field is the established
canonical one.  This module combines those two facts into one all-point
P286 Euler normal form and lets the final full-occurrence actual inherit it.

The remaining changed read is exactly the charged-current difference.  No
residual coordinate, support branch, target field, regularity certificate,
or supplied profile enters a producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicConnectionChangedRead

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance changedReadP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance changedReadP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source FixedInput

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev Canonical : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private theorem algebraic_eq_zeroCandidate :
    Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source Temporal 0 := by
  exact
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate

private theorem algebraic_coframe_eq_temporal :
    Algebraic.coframe = Temporal.coframe := by
  rw [algebraic_eq_zeroCandidate]
  rfl

private theorem algebraic_gaugeConnection_eq_temporal :
    Algebraic.gaugeConnection = Temporal.gaugeConnection := by
  rw [algebraic_eq_zeroCandidate,
    diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

private theorem algebraic_scalar_eq_temporal :
    Algebraic.scalar = Temporal.scalar := by
  rw [algebraic_eq_zeroCandidate]
  rfl

private theorem algebraic_matter_eq_temporal :
    Algebraic.matter = Temporal.matter := by
  rw [algebraic_eq_zeroCandidate]
  rfl

private theorem algebraic_conjugateMatter_eq_temporal :
    Algebraic.conjugateMatter = Temporal.conjugateMatter := by
  rw [algebraic_eq_zeroCandidate]
  rfl

private theorem algebraic_scalarCovariantDerivative_eq_temporal
    (point : BasePoint) :
    holonomicScalarCovariantDerivative Algebraic point =
      holonomicScalarCovariantDerivative Temporal point := by
  unfold holonomicScalarCovariantDerivative
  rw [algebraic_scalar_eq_temporal, algebraic_gaugeConnection_eq_temporal]

private theorem algebraic_exteriorCovariantDerivative_eq_canonical :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Algebraic =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical := by
  exact
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorCovariantDerivative_eq_canonical

private theorem u6_p286Connection_eq_algebraic
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point
      ).p286GaugeConnection =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic point := by
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286Connection_eq_algebraic
      point

/-- Because the fixed action-generated P286 write is zero, the charged read
of the algebraic stage is literally the charged read of the temporal stage
at every point. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_chargedGaugeThreeForm_eq_temporal
    (point : BasePoint) :
    formNativeChargedGaugeThreeForm Source 0 point
        (toContinuumPointField Algebraic point) =
      formNativeChargedGaugeThreeForm Source 0 point
        (toContinuumPointField Temporal point) := by
  apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
  · exact congrFun algebraic_coframe_eq_temporal point
  · exact congrFun algebraic_scalar_eq_temporal point
  · exact algebraic_scalarCovariantDerivative_eq_temporal point
  · exact congrFun algebraic_matter_eq_temporal point
  · exact congrFun algebraic_conjugateMatter_eq_temporal point

/-- All-point normal form of the fixed algebraic P286 Euler read.  The first
summand is the already generated canonical `D_A B` field; the second is the
same-source temporal charged current. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_eq_canonicalExterior_add_temporalCharged
    (point : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical point +
        formNativeChargedGaugeThreeForm Source 0 point
          (toContinuumPointField Temporal point) := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [congrFun
      algebraic_exteriorCovariantDerivative_eq_canonical
      point,
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_chargedGaugeThreeForm_eq_temporal]

/-- Subtracting the canonical action read cancels the complete BF derivative
field.  Thus the only all-point P286 changed read is the joint temporal
charged-current change. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_sub_canonical
    (point : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic point -
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 Canonical point =
      formNativeChargedGaugeThreeForm Source 0 point
          (toContinuumPointField Temporal point) -
        formNativeChargedGaugeThreeForm Source 0 point
          (toContinuumPointField Canonical point) := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [congrFun
      algebraic_exteriorCovariantDerivative_eq_canonical
      point,
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_chargedGaugeThreeForm_eq_temporal]
  abel

/-- The source/current-only full-occurrence actual inherits the same exact
P286 normal form. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286Connection_eq_canonicalExterior_add_temporalCharged
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point
      ).p286GaugeConnection =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical point +
        formNativeChargedGaugeThreeForm Source 0 point
          (toContinuumPointField Temporal point) := by
  rw [u6_p286Connection_eq_algebraic]
  exact
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_eq_canonicalExterior_add_temporalCharged
      point

/-- Exact all-point changed-read identity on U6. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286Connection_sub_canonical
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point
      ).p286GaugeConnection -
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 Canonical point =
      formNativeChargedGaugeThreeForm Source 0 point
          (toContinuumPointField Temporal point) -
        formNativeChargedGaugeThreeForm Source 0 point
          (toContinuumPointField Canonical point) := by
  rw [u6_p286Connection_eq_algebraic]
  exact
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_sub_canonical
      point

/-- The complete first germ of the U6-minus-canonical P286 read is therefore
exactly the first germ of the same-source joint charged-current change.  This
is an unconditional derivative identity because the underlying fields agree
as functions; it introduces no smoothness premise. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286ConnectionFirstGerm_sub_canonical
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          (diracDualFormNativePointwiseJointResidual Source U6 point
            ).p286GaugeConnection -
            holonomicFormNativeP286GaugeEulerThreeForm Source 0 Canonical point)
        0 direction =
      fieldDirectionalDerivative
        (fun point =>
          formNativeChargedGaugeThreeForm Source 0 point
              (toContinuumPointField Temporal point) -
            formNativeChargedGaugeThreeForm Source 0 point
              (toContinuumPointField Canonical point))
        0 direction := by
  have fieldEq :
      (fun point =>
          (diracDualFormNativePointwiseJointResidual Source U6 point
            ).p286GaugeConnection -
            holonomicFormNativeP286GaugeEulerThreeForm Source 0 Canonical point) =
        fun point =>
          formNativeChargedGaugeThreeForm Source 0 point
              (toContinuumPointField Temporal point) -
            formNativeChargedGaugeThreeForm Source 0 point
              (toContinuumPointField Canonical point) := by
    funext point
    exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286Connection_sub_canonical
        point
  rw [fieldEq]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicConnectionChangedRead
