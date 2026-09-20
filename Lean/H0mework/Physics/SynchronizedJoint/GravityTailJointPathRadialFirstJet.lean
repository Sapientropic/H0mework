import H0mework.Physics.SynchronizedJoint.GravityTailJointPathOperator
import H0mework.Physics.Jets.RadialCurveIntegralFirstJet

/-!
# Coframe first jet of the joint gravity-tail path

The joint occurrence has already emitted its primitive coframe through
sixteen canonical scalar radial integrals.  This module differentiates that
exact output componentwise.  It accepts no target jet, residual, support,
closedness law, branch, or completed field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator

open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineRadialCurveIntegralFirstJet

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-- Unconditional derivative of one emitted coframe coordinate. -/
def cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (internal coordinate : LorentzianIndex) : BasePoint →L[ℝ] ℝ :=
  ∫ parameter in (0 : ℝ)..1,
    radialCurveIntegralDerivativeIntegrand
      (fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current contact internal coordinate)
      point parameter

@[simp] theorem
    cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internal coordinate : LorentzianIndex) :
    cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
        source current 0 internal coordinate =
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current 0 internal coordinate := by
  simp [cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate,
    radialCurveIntegralDerivativeIntegrand]

/-- Complete pointwise first jet of the already emitted coframe path. -/
def cartanECSynchronizedGravityTailCoframeRadialFirstJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : PointwiseLorentzianCoframeJet where
  coframe := cartanECSynchronizedGravityTailCoframePathField
    source current point
  derivative := fun derivativeDirection internal coordinate =>
    cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
      source current point internal coordinate
      (coordinateDirection derivativeDirection)

/-- Exactification defect of one emitted coframe coordinate against the
source one-form at the same endpoint.  Both terms come from the same radial
path; no target jet is supplied. -/
def cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (internal coordinate : LorentzianIndex) : BasePoint →L[ℝ] ℝ :=
  radialCurveIntegralFirstJetDefect
    (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current contact internal coordinate)
    point

/-- The emitted coordinate first jet is the endpoint profile plus its
source-generated exactification defect. -/
theorem
    cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate_eq_endpoint_add_defect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (internal coordinate : LorentzianIndex) :
    cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
        source current point internal coordinate =
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current point internal coordinate +
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          source current point internal coordinate := by
  simpa [cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate,
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate] using
    radialCurveIntegralFirstJet_eq_endpoint_add_defect
      (fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current contact internal coordinate)
      point

/-- The exactification defect vanishes on the actual radial source
direction; any remaining defect is transverse. -/
theorem
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate_apply_radial
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internal coordinate : LorentzianIndex)
    (regular :
      ContDiff ℝ 1 fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current contact internal coordinate)
    (point : BasePoint) :
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
        source current point internal coordinate point = 0 := by
  exact radialCurveIntegralFirstJetDefect_apply_radial
    (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current contact internal coordinate)
    regular point

/-- Coordinate presentation of the generated derivative defect. -/
def cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection internal coordinate : LorentzianIndex) : ℝ :=
  cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
    source current point internal coordinate
    (coordinateDirection derivativeDirection)

/-- Full componentwise derivative normal form for the emitted coframe jet. -/
theorem
    cartanECSynchronizedGravityTailCoframeRadialFirstJet_derivative_eq_profile_add_defect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    (cartanECSynchronizedGravityTailCoframeRadialFirstJet
        source current point).derivative
        derivativeDirection internal coordinate =
      (cartanECSynchronizedGravityTailProfileCoframeFirstJet
          source current point).derivative
          derivativeDirection internal coordinate +
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
          source current point derivativeDirection internal coordinate := by
  change
    cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
        source current point internal coordinate
        (coordinateDirection derivativeDirection) = _
  rw [
    cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate_eq_endpoint_add_defect,
    add_apply,
    cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_coordinate]
  rfl

@[simp] theorem
    cartanECSynchronizedGravityTailCoframeRadialFirstJet_zero_eq_profile :
    ∀ (source : SmoothUnifiedSource)
      (current : StageNineHolonomicConfiguration),
      cartanECSynchronizedGravityTailCoframeRadialFirstJet
          source current 0 =
        cartanECSynchronizedGravityTailProfileCoframeFirstJet
          source current 0 := by
  intro source current
  apply coframeJet_eq_of_fields_eq
  · change
      cartanECSynchronizedGravityTailCoframePathField source current 0 =
        (cartanECSynchronizedGravityTailProfileCoframeFirstJet
          source current 0).coframe
    rw [cartanECSynchronizedGravityTailCoframePathField_zero,
      cartanECSynchronizedGravityTailProfileCoframeFirstJet_coframe_eq_base]
    rfl
  · funext derivativeDirection internal coordinate
    change
      cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
          source current 0 internal coordinate
          (coordinateDirection derivativeDirection) =
        (cartanECSynchronizedGravityTailProfileCoframeFirstJet
          source current 0).derivative
          derivativeDirection internal coordinate
    rw [cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate_zero,
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_coordinate]
    rfl

theorem
    cartanECSynchronizedGravityTailCoframeRadialIncrement_coordinate_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internal coordinate : LorentzianIndex)
    (regular :
      ContDiff ℝ 1 fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current contact internal coordinate)
    (point : BasePoint) :
    HasFDerivAt
      (fun endpoint =>
        cartanECSynchronizedGravityTailCoframeRadialIncrement
          source current endpoint internal coordinate)
      (cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
        source current point internal coordinate)
      point := by
  exact radialCurveIntegral_hasFDerivAt_of_contDiff
    (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current contact internal coordinate)
    regular point

theorem
    cartanECSynchronizedGravityTailCoframeRadialIncrement_coordinate_hasFDerivAt_zero_of_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internal coordinate : LorentzianIndex)
    (regular : ContDiffAt ℝ 0 (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current contact internal coordinate) 0) :
    HasFDerivAt
      (fun endpoint =>
        cartanECSynchronizedGravityTailCoframeRadialIncrement
          source current endpoint internal coordinate)
      (cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current 0 internal coordinate) 0 := by
  simpa [cartanECSynchronizedGravityTailCoframeRadialIncrement] using
    radialCurveIntegral_hasFDerivAt_zero_of_contDiffAt
      (fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current contact internal coordinate)
      regular

theorem
    cartanECSynchronizedGravityTailCoframePathField_coordinate_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internal coordinate : LorentzianIndex)
    (regular :
      ContDiff ℝ 1 fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current contact internal coordinate)
    (point : BasePoint) :
    HasFDerivAt
      (fun endpoint =>
        cartanECSynchronizedGravityTailCoframePathField
          source current endpoint internal coordinate)
      (cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
        source current point internal coordinate)
      point := by
  change HasFDerivAt
    (fun endpoint =>
      cartanECSynchronizedGravityTailCoframePathAnchor source current
          internal coordinate +
        cartanECSynchronizedGravityTailCoframeRadialIncrement
          source current endpoint internal coordinate) _ point
  exact
    (cartanECSynchronizedGravityTailCoframeRadialIncrement_coordinate_hasFDerivAt_of_contDiff
      source current internal coordinate regular point).const_add
    (cartanECSynchronizedGravityTailCoframePathAnchor source current
      internal coordinate)

theorem
    cartanECSynchronizedGravityTailCoframePathField_coordinate_hasFDerivAt_zero_of_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internal coordinate : LorentzianIndex)
    (regular : ContDiffAt ℝ 0 (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current contact internal coordinate) 0) :
    HasFDerivAt
      (fun endpoint =>
        cartanECSynchronizedGravityTailCoframePathField
          source current endpoint internal coordinate)
      (cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current 0 internal coordinate) 0 := by
  change HasFDerivAt
    (fun endpoint =>
      cartanECSynchronizedGravityTailCoframePathAnchor source current
          internal coordinate +
        cartanECSynchronizedGravityTailCoframeRadialIncrement
          source current endpoint internal coordinate) _ 0
  exact
    (cartanECSynchronizedGravityTailCoframeRadialIncrement_coordinate_hasFDerivAt_zero_of_contDiffAt
      source current internal coordinate regular).const_add
      (cartanECSynchronizedGravityTailCoframePathAnchor source current
        internal coordinate)

/-- The primitive coframe path reads back the complete radial first jet at
every point where its occurrence-native coordinate one-forms are `C¹`. -/
theorem
    holonomicCoframeFirstJetAt_cartanECSynchronizedGravityTailCoframePathField
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular : ∀ internal coordinate,
      ContDiff ℝ 1 fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current contact internal coordinate)
    (point : BasePoint) :
    holonomicCoframeFirstJetAt
        (cartanECSynchronizedGravityTailCoframePathField source current)
        point =
      cartanECSynchronizedGravityTailCoframeRadialFirstJet
        source current point := by
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    change
      fderiv ℝ
          (fun endpoint =>
            cartanECSynchronizedGravityTailCoframePathField
              source current endpoint internal coordinate)
          point (coordinateDirection derivativeDirection) =
        cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
          source current point internal coordinate
          (coordinateDirection derivativeDirection)
    rw [(cartanECSynchronizedGravityTailCoframePathField_coordinate_hasFDerivAt_of_contDiff
      source current internal coordinate (regular internal coordinate)
      point).fderiv]

/-- Local source form of the complete coframe first-jet readback. -/
theorem
    holonomicCoframeFirstJetAt_cartanECSynchronizedGravityTailCoframePathField_zero_of_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular : ∀ internal coordinate,
      ContDiffAt ℝ 0 (fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current contact internal coordinate) 0) :
    holonomicCoframeFirstJetAt
        (cartanECSynchronizedGravityTailCoframePathField source current) 0 =
      cartanECSynchronizedGravityTailCoframeRadialFirstJet
        source current 0 := by
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    change
      fderiv ℝ
          (fun endpoint =>
            cartanECSynchronizedGravityTailCoframePathField
              source current endpoint internal coordinate)
          0 (coordinateDirection derivativeDirection) =
        cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
          source current 0 internal coordinate
          (coordinateDirection derivativeDirection)
    rw [(cartanECSynchronizedGravityTailCoframePathField_coordinate_hasFDerivAt_zero_of_contDiffAt
      source current internal coordinate (regular internal coordinate)).fderiv]
    rw [cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate_zero]

/-- Whole-emitter form of the primitive coframe first-jet readback. -/
theorem
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframeFirstJet_eq_radialFirstJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular : ∀ internal coordinate,
      ContDiff ℝ 1 fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current contact internal coordinate)
    (point : BasePoint) :
    holonomicCoframeFirstJetAt
        (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
          source current).coframe point =
      cartanECSynchronizedGravityTailCoframeRadialFirstJet
        source current point := by
  rw [
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframe]
  exact
    holonomicCoframeFirstJetAt_cartanECSynchronizedGravityTailCoframePathField
      source current regular point

/-- Exact-occurrence form: no sibling completion payload can alter the
generated coframe first jet. -/
theorem
    CartanECSynchronizedGravityTailJointOccurrence.coframeFirstJet_eq_radialFirstJet
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CartanECSynchronizedGravityTailJointOccurrence source current)
    (regular : ∀ internal coordinate,
      ContDiff ℝ 1 fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          source current contact internal coordinate)
    (point : BasePoint) :
    holonomicCoframeFirstJetAt occurrence.finalActual.coframe point =
      cartanECSynchronizedGravityTailCoframeRadialFirstJet
        source current point := by
  cases occurrence
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframeFirstJet_eq_radialFirstJet
      source current regular point

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
