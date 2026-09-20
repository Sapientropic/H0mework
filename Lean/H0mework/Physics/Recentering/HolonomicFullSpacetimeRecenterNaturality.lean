import H0mework.Physics.JointVariation.FullOccurrenceContactOperator
import H0mework.Physics.CoframeJets.CoframeFirstJet

/-!
# Full-spacetime recentering naturality

The full-occurrence action leg first translates one already-generated
holonomic current to a common local origin.  This module proves, in one
whole-point-field theorem, that the translation faithfully carries every
primitive value and every derived first-jet coordinate.  The statement does
not require smoothness: affine translation preserves differentiability, and
also preserves Lean's canonical-zero `fderiv` branch when a field is not
differentiable.

The theorem is independent of an action density and therefore does not claim
that source-relative coefficients at the global point and at the local origin
are equal.  That remaining source/action covariance is a separate seam.  No
residual, support, target jet, or zero-fiber witness enters the recentering.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineHolonomicFullSpacetimeRecenterNaturality

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 1000000

local instance fullRecenterP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

private theorem fieldDirectionalDerivative_comp_fullSpacetimeTranslation
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field : BasePoint → E)
    (contact point : BasePoint)
    (direction : LorentzianIndex)
    (differentiable : DifferentiableAt ℝ field
      (canonicalSpacetimeContactTranslation contact point)) :
    fieldDirectionalDerivative
        (field ∘ canonicalSpacetimeContactTranslation contact) point direction =
      fieldDirectionalDerivative field
        (canonicalSpacetimeContactTranslation contact point) direction := by
  have translation :
      HasFDerivAt (canonicalSpacetimeContactTranslation contact)
        (ContinuousLinearMap.id ℝ BasePoint) point := by
    unfold canonicalSpacetimeContactTranslation
    fun_prop
  have composed := differentiable.hasFDerivAt.comp point translation
  unfold fieldDirectionalDerivative
  rw [composed.fderiv]
  rfl

/-- Directional derivatives commute with canonical spacetime translation
even when the field is not differentiable: affine translation is a local
diffeomorphism, so nondifferentiability is preserved and both `fderiv`
values use Lean's canonical zero. -/
theorem fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field : BasePoint → E)
    (contact point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (field ∘ canonicalSpacetimeContactTranslation contact) point direction =
      fieldDirectionalDerivative field
        (canonicalSpacetimeContactTranslation contact point) direction := by
  by_cases differentiable : DifferentiableAt ℝ field
      (canonicalSpacetimeContactTranslation contact point)
  · exact
      fieldDirectionalDerivative_comp_fullSpacetimeTranslation
        field contact point direction differentiable
  · have composedNotDifferentiable :
        ¬ DifferentiableAt ℝ
            (field ∘ canonicalSpacetimeContactTranslation contact) point := by
      intro composedDifferentiable
      have inverseDifferentiable :
          DifferentiableAt ℝ
            (canonicalSpacetimeContactTranslation (-contact))
            (canonicalSpacetimeContactTranslation contact point) := by
        unfold canonicalSpacetimeContactTranslation
        fun_prop
      have outerDifferentiable :
          DifferentiableAt ℝ
            (field ∘ canonicalSpacetimeContactTranslation contact)
            (canonicalSpacetimeContactTranslation (-contact)
              (canonicalSpacetimeContactTranslation contact point)) := by
        simpa [canonicalSpacetimeContactTranslation, add_assoc] using
          composedDifferentiable
      have recovered :=
        outerDifferentiable.comp
          (canonicalSpacetimeContactTranslation contact point)
          inverseDifferentiable
      have recoveredFunction :
          (field ∘ canonicalSpacetimeContactTranslation contact) ∘
              canonicalSpacetimeContactTranslation (-contact) =
            field := by
        funext candidate
        simp [canonicalSpacetimeContactTranslation]
      rw [recoveredFunction] at recovered
      exact differentiable recovered
    unfold fieldDirectionalDerivative
    rw [fderiv_zero_of_not_differentiableAt composedNotDifferentiable,
      fderiv_zero_of_not_differentiableAt differentiable]

/-- Gravity-connection derivatives commute with the affine recentering even
without a smoothness premise.  In the nondifferentiable branch both `fderiv`
reads use Lean's canonical zero. -/
theorem
    fullyRecenterHolonomicConfiguration_gravityConnectionDerivative_origin_unconditional
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    gravityConnectionDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0
        derivativeDirection formDirection internalOut internalIn =
      gravityConnectionDerivative current contact derivativeDirection
        formDirection internalOut internalIn := by
  change
    fieldDirectionalDerivative
        ((fun point =>
          current.gravityConnection point formDirection internalOut
            internalIn) ∘ canonicalSpacetimeContactTranslation contact)
        0 derivativeDirection =
      fieldDirectionalDerivative
        (fun point =>
          current.gravityConnection point formDirection internalOut internalIn)
        contact derivativeDirection
  simpa using
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      (fun point =>
        current.gravityConnection point formDirection internalOut internalIn)
      contact 0 derivativeDirection

/-- Backward-compatible smooth-current mouth. -/
theorem fullyRecenterHolonomicConfiguration_gravityConnectionDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    gravityConnectionDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0
        derivativeDirection formDirection internalOut internalIn =
      gravityConnectionDerivative current contact derivativeDirection
        formDirection internalOut internalIn :=
  fullyRecenterHolonomicConfiguration_gravityConnectionDerivative_origin_unconditional
    current contact derivativeDirection formDirection internalOut internalIn

theorem fullyRecenterHolonomicConfiguration_gravityCurvature_origin_unconditional
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicGravityCurvature
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicGravityCurvature current contact := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
  simp_rw [
    fullyRecenterHolonomicConfiguration_gravityConnectionDerivative_origin_unconditional
      current contact]
  simp [fullyRecenterHolonomicConfiguration]

theorem fullyRecenterHolonomicConfiguration_gravityCurvature_origin
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint) :
    holonomicGravityCurvature
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicGravityCurvature current contact := by
  exact
    fullyRecenterHolonomicConfiguration_gravityCurvature_origin_unconditional
      current contact

theorem
    fullyRecenterHolonomicConfiguration_p286ConnectionDerivative_origin_unconditional
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286ConnectionDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0
        derivativeDirection formDirection =
      p286ConnectionDerivative current contact derivativeDirection
        formDirection := by
  unfold p286ConnectionDerivative
  apply congrArg p286CoordinateEquiv.symm
  change
    fieldDirectionalDerivative
        ((fun point =>
          p286CoordinateEquiv
            (current.gaugeConnection point formDirection)) ∘
          canonicalSpacetimeContactTranslation contact)
        0 derivativeDirection =
      fieldDirectionalDerivative
        (fun point =>
          p286CoordinateEquiv (current.gaugeConnection point formDirection))
        contact derivativeDirection
  simpa using
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      (fun point =>
        p286CoordinateEquiv (current.gaugeConnection point formDirection))
      contact 0 derivativeDirection

theorem fullyRecenterHolonomicConfiguration_p286ConnectionDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286ConnectionDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0
        derivativeDirection formDirection =
      p286ConnectionDerivative current contact derivativeDirection
        formDirection :=
  fullyRecenterHolonomicConfiguration_p286ConnectionDerivative_origin_unconditional
    current contact derivativeDirection formDirection

theorem fullyRecenterHolonomicConfiguration_gaugeCurvature_origin_unconditional
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicGaugeCurvature
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicGaugeCurvature current contact := by
  funext pair
  unfold holonomicGaugeCurvature
  rw [
    fullyRecenterHolonomicConfiguration_p286ConnectionDerivative_origin_unconditional
      current contact,
    fullyRecenterHolonomicConfiguration_p286ConnectionDerivative_origin_unconditional
      current contact]
  simp [fullyRecenterHolonomicConfiguration]

theorem fullyRecenterHolonomicConfiguration_gaugeCurvature_origin
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint) :
    holonomicGaugeCurvature
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicGaugeCurvature current contact := by
  exact
    fullyRecenterHolonomicConfiguration_gaugeCurvature_origin_unconditional
      current contact

theorem
    fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicScalarCovariantDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicScalarCovariantDerivative current contact := by
  funext direction
  have derivativeEq :=
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      current.scalar contact 0 direction
  unfold holonomicScalarCovariantDerivative
  change
    fieldDirectionalDerivative
          (current.scalar ∘ canonicalSpacetimeContactTranslation contact)
          0 direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            (current.gaugeConnection
              (canonicalSpacetimeContactTranslation contact 0) direction))
          (current.scalar
            (canonicalSpacetimeContactTranslation contact 0)) =
      fieldDirectionalDerivative current.scalar contact direction +
        scalarMotherLieAction
          (p286LieBlockEmbed (current.gaugeConnection contact direction))
          (current.scalar contact)
  rw [derivativeEq]
  simp

theorem fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint) :
    holonomicScalarCovariantDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicScalarCovariantDerivative current contact :=
  fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
    current contact

theorem
    fullyRecenterHolonomicConfiguration_matterCovariantDerivative_origin_unconditional
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicMatterCovariantDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicMatterCovariantDerivative current contact := by
  funext direction
  let coordinateField : BasePoint → MatterCoordinateCarrier :=
    fun point => matterCoordinateEquiv (current.matter point)
  have derivativeEq :=
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      coordinateField contact 0 direction
  unfold holonomicMatterCovariantDerivative
  change
    matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (coordinateField ∘ canonicalSpacetimeContactTranslation contact)
            0 direction) +
        diracMatrixMatterAction
            (diracSpinConnectionLift
              (current.gravityConnection
                (canonicalSpacetimeContactTranslation contact 0)) direction)
          (current.matter
            (canonicalSpacetimeContactTranslation contact 0)) +
      diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (current.gaugeConnection
              (canonicalSpacetimeContactTranslation contact 0) direction))
        (current.matter
          (canonicalSpacetimeContactTranslation contact 0)) =
      matterCoordinateEquiv.symm
          (fieldDirectionalDerivative coordinateField contact direction) +
        diracMatrixMatterAction
            (diracSpinConnectionLift
              (current.gravityConnection contact) direction)
          (current.matter contact) +
      diracExteriorMotherLieAction
          (p286LieBlockEmbed (current.gaugeConnection contact direction))
        (current.matter contact)
  rw [derivativeEq]
  simp

theorem fullyRecenterHolonomicConfiguration_matterCovariantDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint) :
    holonomicMatterCovariantDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicMatterCovariantDerivative current contact :=
  fullyRecenterHolonomicConfiguration_matterCovariantDerivative_origin_unconditional
    current contact

/-- Canonical recentering preserves the complete primitive coframe first jet,
not only its value.  This is unconditional for the same affine-translation
reason as the other first-jet naturality readouts in this module. -/
theorem fullyRecenterHolonomicConfiguration_coframeFirstJet_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicCoframeFirstJetAt
        (fullyRecenterHolonomicConfiguration current contact).coframe 0 =
      holonomicCoframeFirstJetAt current.coframe contact := by
  apply coframeJet_eq_of_fields_eq
  · exact fullyRecenterHolonomicConfiguration_coframe_origin current contact
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

/-- Every coordinate of the generated continuum point field is faithfully
transported from the selected global occurrence to the local origin.  The
claim is valid for arbitrary fields because affine recentering preserves both
the differentiable and canonical-zero `fderiv` branches. -/
theorem fullyRecenterHolonomicConfiguration_pointField_origin_unconditional
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    toContinuumPointField
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      toContinuumPointField current contact := by
  apply StageNineContinuumPointField.ext
  · exact fullyRecenterHolonomicConfiguration_coframe_origin current contact
  · exact
      fullyRecenterHolonomicConfiguration_gravityCurvature_origin_unconditional
        current contact
  · exact
      fullyRecenterHolonomicConfiguration_gravityAuxiliary_origin
        current contact
  · exact
      fullyRecenterHolonomicConfiguration_gravitySimplicityMultiplier_origin
        current contact
  · exact
      fullyRecenterHolonomicConfiguration_gaugeCurvature_origin_unconditional
        current contact
  · exact
      fullyRecenterHolonomicConfiguration_gaugeAuxiliary_origin current contact
  · exact fullyRecenterHolonomicConfiguration_scalar_origin current contact
  · exact
      fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
        current contact
  · exact fullyRecenterHolonomicConfiguration_matter_origin current contact
  · exact
      fullyRecenterHolonomicConfiguration_matterCovariantDerivative_origin_unconditional
        current contact
  · exact
      fullyRecenterHolonomicConfiguration_conjugateMatter_origin
        current contact

/-- Backward-compatible smooth-current mouth. -/
theorem fullyRecenterHolonomicConfiguration_pointField_origin
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint) :
    toContinuumPointField
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      toContinuumPointField current contact :=
  fullyRecenterHolonomicConfiguration_pointField_origin_unconditional
    current contact

/-- Recentring twice is the same source-preserving translation as recentering
once at the composed spacetime occurrence. -/
theorem fullyRecenterHolonomicConfiguration_recenter
    (current : StageNineHolonomicConfiguration)
    (first second : BasePoint) :
    fullyRecenterHolonomicConfiguration
        (fullyRecenterHolonomicConfiguration current first) second =
      fullyRecenterHolonomicConfiguration current
        (canonicalSpacetimeContactTranslation first second) := by
  apply StageNineHolonomicConfiguration.ext <;>
    simp [fullyRecenterHolonomicConfiguration,
      canonicalSpacetimeContactTranslation, add_assoc]

/-- Whole-point-field naturality at an arbitrary local coordinate of the
recentered current, without a regularity premise. -/
theorem fullyRecenterHolonomicConfiguration_pointField_unconditional
    (current : StageNineHolonomicConfiguration)
    (contact point : BasePoint) :
    toContinuumPointField
        (fullyRecenterHolonomicConfiguration current contact) point =
      toContinuumPointField current
        (canonicalSpacetimeContactTranslation contact point) := by
  calc
    toContinuumPointField
          (fullyRecenterHolonomicConfiguration current contact) point =
        toContinuumPointField
          (fullyRecenterHolonomicConfiguration
            (fullyRecenterHolonomicConfiguration current contact) point) 0 :=
      (fullyRecenterHolonomicConfiguration_pointField_origin_unconditional
        (fullyRecenterHolonomicConfiguration current contact)
        point).symm
    _ = toContinuumPointField
          (fullyRecenterHolonomicConfiguration current
            (canonicalSpacetimeContactTranslation contact point)) 0 := by
      rw [fullyRecenterHolonomicConfiguration_recenter]
    _ = toContinuumPointField current
          (canonicalSpacetimeContactTranslation contact point) :=
      fullyRecenterHolonomicConfiguration_pointField_origin_unconditional
        current
        (canonicalSpacetimeContactTranslation contact point)

/-- Backward-compatible smooth-current mouth. -/
theorem fullyRecenterHolonomicConfiguration_pointField
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact point : BasePoint) :
    toContinuumPointField
        (fullyRecenterHolonomicConfiguration current contact) point =
      toContinuumPointField current
        (canonicalSpacetimeContactTranslation contact point) :=
  fullyRecenterHolonomicConfiguration_pointField_unconditional
    current contact point

end

end
  SaturationMonoid.PhysicsCore.StageNineHolonomicFullSpacetimeRecenterNaturality
