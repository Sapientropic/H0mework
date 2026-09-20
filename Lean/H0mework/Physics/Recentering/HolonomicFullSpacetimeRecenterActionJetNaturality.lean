import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality

/-!
# Full-spacetime recentering of the complete action jet

Canonical spacetime translation transports not only the generated continuum
point field but every derivative slot used by the authoritative nine-channel
mother-action readout.  This module proves that statement as one equality of
`DiracDualFormNativePointwiseActionJetCarrier`s.

The result is a naturality theorem for an already-generated current.  It
creates neither a global successor nor a residual-derived correction.  The
whole-carrier identity remains valid without a smoothness premise because
affine translation preserves both the differentiable and canonical-zero
`fderiv` branches.  This does not assert that an arbitrary current is smooth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineHolonomicFullSpacetimeRecenterActionJetNaturality

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineMatterPointwiseEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarPointwiseEquation
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 1000000

local instance fullActionJetRecenterP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

/-! ## Auxiliary-field derivative slots -/

theorem
    fullyRecenterHolonomicConfiguration_gravityAuxiliaryDirectionalDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    gravityAuxiliaryDirectionalDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      gravityAuxiliaryDirectionalDerivative current contact := by
  funext direction
  change
    fieldDirectionalDerivative
        (current.gravityAuxiliary ∘
          canonicalSpacetimeContactTranslation contact) 0 direction =
      fieldDirectionalDerivative current.gravityAuxiliary contact direction
  simpa using
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      current.gravityAuxiliary contact 0 direction

theorem
    fullyRecenterHolonomicConfiguration_gravityAuxiliaryExteriorCovariantDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicGravityAuxiliaryExteriorCovariantDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicGravityAuxiliaryExteriorCovariantDerivative current contact := by
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
    holonomicGravityAuxiliaryJet
  rw [fullyRecenterHolonomicConfiguration_gravityConnection_origin]
  apply congrArg
    (pointwisePhysicalBivectorExteriorCovariantDerivative
      (current.gravityConnection contact))
  apply congrArg₂ PointwisePhysicalBivectorJet.mk
  · exact fullyRecenterHolonomicConfiguration_gravityAuxiliary_origin
      current contact
  · exact
      fullyRecenterHolonomicConfiguration_gravityAuxiliaryDirectionalDerivative_origin
        current contact

theorem
    fullyRecenterHolonomicConfiguration_p286GaugeAuxiliaryDirectionalDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    p286GaugeAuxiliaryDirectionalDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      p286GaugeAuxiliaryDirectionalDerivative current contact := by
  funext direction
  unfold p286GaugeAuxiliaryDirectionalDerivative
  change
    fieldDirectionalDerivative
        (holonomicP286GaugeAuxiliaryCoordinate current ∘
          canonicalSpacetimeContactTranslation contact) 0 direction =
      fieldDirectionalDerivative
        (holonomicP286GaugeAuxiliaryCoordinate current) contact direction
  simpa [holonomicP286GaugeAuxiliaryCoordinate,
    fullyRecenterHolonomicConfiguration] using
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      (holonomicP286GaugeAuxiliaryCoordinate current) contact 0 direction

theorem
    fullyRecenterHolonomicConfiguration_p286GaugeAuxiliaryExteriorCovariantDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative current contact := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [
    fullyRecenterHolonomicConfiguration_p286GaugeAuxiliaryDirectionalDerivative_origin]
  simp [fullyRecenterHolonomicConfiguration]

/-! ## Differential-momentum slots -/

theorem scalarDifferentialMomentum_fullyRecenter_unconditional
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (point : BasePoint) :
    scalarDifferentialMomentum source
        (fullyRecenterHolonomicConfiguration current contact)
        direction derivativeDirection point =
      scalarDifferentialMomentum source current direction derivativeDirection
        (canonicalSpacetimeContactTranslation contact point) := by
  unfold scalarDifferentialMomentum
  rw [fullyRecenterHolonomicConfiguration_pointField_unconditional current]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [scalarFrameRelativeCoordinates_zeroChart]

theorem scalarDifferentialMomentum_fullyRecenter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (point : BasePoint) :
    scalarDifferentialMomentum source
        (fullyRecenterHolonomicConfiguration current contact)
        direction derivativeDirection point =
      scalarDifferentialMomentum source current direction derivativeDirection
        (canonicalSpacetimeContactTranslation contact point) :=
  scalarDifferentialMomentum_fullyRecenter_unconditional source current
    contact direction derivativeDirection point

theorem matterDifferentialMomentum_fullyRecenter_unconditional
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (point : BasePoint) :
    matterDifferentialMomentum source
        (fullyRecenterHolonomicConfiguration current contact)
        direction derivativeDirection point =
      matterDifferentialMomentum source current direction derivativeDirection
        (canonicalSpacetimeContactTranslation contact point) := by
  unfold matterDifferentialMomentum matterDifferentialVariationVector
  rw [fullyRecenterHolonomicConfiguration_pointField_unconditional current]
  simp [fullyRecenterHolonomicConfiguration]

theorem matterDifferentialMomentum_fullyRecenter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (point : BasePoint) :
    matterDifferentialMomentum source
        (fullyRecenterHolonomicConfiguration current contact)
        direction derivativeDirection point =
      matterDifferentialMomentum source current direction derivativeDirection
        (canonicalSpacetimeContactTranslation contact point) :=
  matterDifferentialMomentum_fullyRecenter_unconditional source current
    contact direction derivativeDirection point

theorem
    scalarDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fun direction =>
      scalarDifferentialMomentumDivergence source
        (fullyRecenterHolonomicConfiguration current contact) direction 0) =
      fun direction =>
        scalarDifferentialMomentumDivergence source current direction
          contact := by
  funext direction
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  have momentumFunction :
      scalarDifferentialMomentum source
          (fullyRecenterHolonomicConfiguration current contact)
          direction derivativeDirection =
        scalarDifferentialMomentum source current direction
          derivativeDirection ∘
            canonicalSpacetimeContactTranslation contact := by
    funext point
    exact scalarDifferentialMomentum_fullyRecenter_unconditional source current
      contact direction derivativeDirection point
  rw [momentumFunction]
  simpa using
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      (scalarDifferentialMomentum source current direction
        derivativeDirection) contact 0 derivativeDirection

theorem scalarDifferentialMomentumDivergence_fullyRecenter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint) :
    (fun direction =>
      scalarDifferentialMomentumDivergence source
        (fullyRecenterHolonomicConfiguration current contact) direction 0) =
      fun direction =>
        scalarDifferentialMomentumDivergence source current direction
          contact :=
  scalarDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
    source current contact

theorem
    matterDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fun direction =>
      matterDifferentialMomentumDivergence source
        (fullyRecenterHolonomicConfiguration current contact) direction 0) =
      fun direction =>
        matterDifferentialMomentumDivergence source current direction
          contact := by
  funext direction
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  have momentumFunction :
      matterDifferentialMomentum source
          (fullyRecenterHolonomicConfiguration current contact)
          direction derivativeDirection =
        matterDifferentialMomentum source current direction
          derivativeDirection ∘
            canonicalSpacetimeContactTranslation contact := by
    funext point
    exact matterDifferentialMomentum_fullyRecenter_unconditional source current
      contact direction derivativeDirection point
  rw [momentumFunction]
  simpa using
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      (matterDifferentialMomentum source current direction
        derivativeDirection) contact 0 derivativeDirection

theorem matterDifferentialMomentumDivergence_fullyRecenter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint) :
    (fun direction =>
      matterDifferentialMomentumDivergence source
        (fullyRecenterHolonomicConfiguration current contact) direction 0) =
      fun direction =>
        matterDifferentialMomentumDivergence source current direction
          contact :=
  matterDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
    source current contact

/-! ## Whole action-jet naturality -/

/-- The complete mother-action jet of any current at one spacetime occurrence
is literally the action jet of its canonical recentering at the local origin.
Affine translation preserves every derivative slot, including the canonical
zero branch of `fderiv` for a nonsmooth field. -/
theorem generatedActionJet_fullyRecenter_origin_unconditional
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      generatedDiracDualFormNativePointwiseActionJet source current contact := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · exact
      fullyRecenterHolonomicConfiguration_pointField_origin_unconditional
        current contact
  · exact
      fullyRecenterHolonomicConfiguration_gravityConnection_origin current
        contact
  · exact
      fullyRecenterHolonomicConfiguration_gaugeConnection_origin current
        contact
  · exact
      fullyRecenterHolonomicConfiguration_gravityAuxiliaryExteriorCovariantDerivative_origin
        current contact
  · exact
      fullyRecenterHolonomicConfiguration_p286GaugeAuxiliaryExteriorCovariantDerivative_origin
        current contact
  · exact
      scalarDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
        source current contact
  · exact
      matterDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
        source current contact

/-- Backward-compatible smooth-current mouth. -/
theorem generatedActionJet_fullyRecenter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      generatedDiracDualFormNativePointwiseActionJet source current contact :=
  generatedActionJet_fullyRecenter_origin_unconditional source current contact

/-- Whole residual transport is now a consequence of exact action-jet
naturality, rather than a separate field-by-field convention argument. -/
theorem pointwiseJointResidual_fullyRecenter_origin_unconditional
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    diracDualFormNativePointwiseJointResidual source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      diracDualFormNativePointwiseJointResidual source current contact := by
  exact
    diracDualFormNativePointwiseJointResidual_eq_of_generatedActionJet_eq
      source (fullyRecenterHolonomicConfiguration current contact) current
      0 contact
      (generatedActionJet_fullyRecenter_origin_unconditional source current
        contact)

/-- Backward-compatible smooth-current mouth. -/
theorem pointwiseJointResidual_fullyRecenter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (_smooth : current.Smooth)
    (contact : BasePoint) :
    diracDualFormNativePointwiseJointResidual source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      diracDualFormNativePointwiseJointResidual source current contact :=
  pointwiseJointResidual_fullyRecenter_origin_unconditional source current
    contact

end

end
  SaturationMonoid.PhysicsCore.StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
