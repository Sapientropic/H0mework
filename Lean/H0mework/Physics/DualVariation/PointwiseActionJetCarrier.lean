import H0mework.Physics.DualVariation.JointResidualCarrier

/-!
# Dirac-dual form-native pointwise action-jet carrier

This module separates the evaluated first-variation data of the authoritative
Dirac-dual form-native mother action from its nine-coordinate residual
readout.  The carrier contains action terms generated from one source,
holonomic configuration, and spacetime occurrence.  It contains no residual,
zero-fiber witness, equation receipt, branch selector, or candidate write.

This separation is used by the repaired spatial-section recentering proof:
the whole action jet can be compared before the nine residual coordinates are
assembled.  A residual remains a deterministic downstream readout.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativePointwiseActionJetCarrier

open DiracExteriorMatterAction
open StageNineCoframeVariation
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeScalarVariation
open StageNineConjugateMatterVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterPointwiseEquation
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarPointwiseEquation
open StageNineScalarLocalSpinDensity
open StageNineScalarVariation
open StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalLorentzThreeFormDualInverse
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

/-- The minimal evaluated pointwise action jet needed by the authoritative
nine-coordinate residual.

Algebraic action terms are recomputed from the point field and the two live
connection values.  Only the derivative data not present in the point field
are stored.  Consequently this carrier contains neither Euler residuals nor
duplicated algebraic receipts. -/
@[ext] structure DiracDualFormNativePointwiseActionJetCarrier where
  pointField : StageNineContinuumPointField
  gravityConnection : PointwiseLorentzSpinConnection
  p286GaugeConnection : LorentzianIndex → P286LieBlockData
  gravityAuxiliaryExteriorCovariantDerivative : PhysicalBivectorThreeForm
  p286GaugeAuxiliaryExteriorCovariantDerivative : P286GaugeThreeForm
  scalarDifferentialMomentumDivergence : ScalarCoordinateCarrier → ℝ
  matterDifferentialMomentumDivergence : MatterCoordinateCarrier → ℝ

/-- Constant scalar-coordinate variation seen by one pointwise P286
connection. -/
def pointwiseScalarVariationAlgebraicDirection
    (connection : LorentzianIndex → P286LieBlockData)
    (direction : ScalarCoordinateCarrier) :
    LorentzianIndex → ScalarCoordinateCarrier :=
  fun formDirection =>
    scalarMotherLieAction
      (p286LieBlockEmbed (connection formDirection)) direction

/-- Constant matter-coordinate variation seen by the two pointwise
connections. -/
def pointwiseMatterVariationAlgebraicDirection
    (gravityConnection : PointwiseLorentzSpinConnection)
    (gaugeConnection : LorentzianIndex → P286LieBlockData)
    (direction : MatterCoordinateCarrier) :
    LorentzianIndex → DiracExteriorMatterCarrier :=
  fun formDirection =>
    diracMatrixMatterAction
        (diracSpinConnectionLift gravityConnection formDirection)
        (matterCoordinateEquiv.symm direction) +
      diracExteriorMotherLieAction
        (p286LieBlockEmbed (gaugeConnection formDirection))
        (matterCoordinateEquiv.symm direction)

/-- Repaired scalar algebraic coefficient reconstructed from the minimal
pointwise jet. -/
def pointwiseDiracDualScalarAlgebraicDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (jet : DiracDualFormNativePointwiseActionJetCarrier)
    (direction : ScalarCoordinateCarrier) : ℝ :=
  generatedVolumeDensity jet.pointField *
    (scalarGaugeConnectionKineticFirstVariationDensity source 0 point
        jet.pointField
        (pointwiseScalarVariationAlgebraicDirection
          jet.p286GaugeConnection direction) -
      scalarPotentialFirstVariation source jet.pointField direction +
      diracDualScalarYukawaFirstVariationDensity jet.pointField direction)

/-- Repaired matter algebraic coefficient reconstructed from the minimal
pointwise jet. -/
def pointwiseDiracDualMatterAlgebraicDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (jet : DiracDualFormNativePointwiseActionJetCarrier)
    (direction : MatterCoordinateCarrier) : ℝ :=
  generatedVolumeDensity jet.pointField *
    (jet.pointField.conjugateMatter
      (diracDualMatterFieldVariationVector source point jet.pointField
        (matterCoordinateEquiv.symm direction)
        (pointwiseMatterVariationAlgebraicDirection jet.gravityConnection
          jet.p286GaugeConnection direction))).re

/-- Evaluate the complete action jet directly from one source, actual, and
spacetime occurrence.  No downstream residual is read by this constructor. -/
def generatedDiracDualFormNativePointwiseActionJet
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  let field := toContinuumPointField configuration point
  { pointField := field
    gravityConnection := configuration.gravityConnection point
    p286GaugeConnection := configuration.gaugeConnection point
    gravityAuxiliaryExteriorCovariantDerivative :=
      holonomicGravityAuxiliaryExteriorCovariantDerivative configuration point
    p286GaugeAuxiliaryExteriorCovariantDerivative :=
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative configuration point
    scalarDifferentialMomentumDivergence := fun direction =>
      scalarDifferentialMomentumDivergence source configuration direction point
    matterDifferentialMomentumDivergence := fun direction =>
      matterDifferentialMomentumDivergence source configuration direction point }

/-- Replace only the derived gravity-curvature coordinate of an evaluated
action jet.  Every primitive value, connection value, and derivative slot is
kept literally. -/
def pointwiseActionJetWithGravityCurvature
    (jet : DiracDualFormNativePointwiseActionJetCarrier)
    (curvature : PhysicalBivector) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  { jet with
    pointField := { jet.pointField with gravityCurvature := curvature } }

/-- Assemble the authoritative nine residual coordinates from an already
generated action jet.  The P286 auxiliary coefficient remains explicitly
source-owned.  This map is a readout, not an action write. -/
def diracDualFormNativeJointResidualOfActionJet
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (jet : DiracDualFormNativePointwiseActionJetCarrier) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { gravityMultiplier :=
      formNativeGravityMultiplierEulerResidual jet.pointField
    gravityAuxiliary :=
      formNativeGravityAuxiliaryEulerResidual jet.pointField
    p286GaugeAuxiliary :=
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings source) jet.pointField
    lorentzConnection :=
      jet.gravityAuxiliaryExteriorCovariantDerivative +
        formNativeMatterSpinThreeForm source 0 point jet.pointField
    p286GaugeConnection :=
      jet.p286GaugeAuxiliaryExteriorCovariantDerivative +
        formNativeChargedGaugeThreeForm source 0 point jet.pointField
    scalar := fun direction =>
      pointwiseDiracDualScalarAlgebraicDirectionalCoefficient source point jet
          direction -
        jet.scalarDifferentialMomentumDivergence direction
    matter := fun direction =>
      pointwiseDiracDualMatterAlgebraicDirectionalCoefficient source point jet
          direction -
        jet.matterDifferentialMomentumDivergence direction
    conjugateMatter := fun direction =>
      generatedVolumeDensity jet.pointField *
        (matterDualOfCoordinates direction
          (generatedContinuumDiracDualMatterVector source 0 point
            jet.pointField)).re
    coframe :=
      diracDualFormNativeCoframeEulerCovector source point jet.pointField }

/-- Changing only the derived gravity-curvature coordinate of an action jet
changes the joint residual only through the gravity-auxiliary equation.  The
coframe equation is curvature-blind because the authoritative BF term is
topological; its coframe variation is the gauge-plus-matter-minus-reaction
decomposition.

This is an action-jet dependency theorem.  It neither asserts that the new
gravity-auxiliary coordinate vanishes nor supplies a write. -/
theorem diracDualFormNativeJointResidualOfActionJet_withGravityCurvature
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (jet : DiracDualFormNativePointwiseActionJetCarrier)
    (curvature : PhysicalBivector)
    (nondegenerate : Matrix.det jet.pointField.coframe ≠ 0) :
    diracDualFormNativeJointResidualOfActionJet source point
        (pointwiseActionJetWithGravityCurvature jet curvature) =
      { diracDualFormNativeJointResidualOfActionJet source point jet with
        gravityAuxiliary :=
          formNativeGravityAuxiliaryEulerResidual
            { jet.pointField with gravityCurvature := curvature } } := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · apply ContinuousLinearMap.ext
    intro variation
    change
      diracDualFormNativeCoframeEulerCovector source point
          { jet.pointField with gravityCurvature := curvature } variation =
        diracDualFormNativeCoframeEulerCovector source point jet.pointField
          variation
    rw [
      diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
        source point { jet.pointField with gravityCurvature := curvature }
        (by simpa using nondegenerate) variation,
      diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
        source point jet.pointField nondegenerate variation]
    rfl

/-- Zero-chart matter spin depends on the evaluated point field, not on the
ambient label used to name that occurrence. -/
private theorem formNativeMatterSpinThreeForm_zeroChart_point_independent
    (source : SmoothUnifiedSource)
    (firstPoint secondPoint : BasePoint)
    (field : StageNineContinuumPointField) :
    formNativeMatterSpinThreeForm source 0 firstPoint field =
      formNativeMatterSpinThreeForm source 0 secondPoint field := by
  unfold formNativeMatterSpinThreeForm
  apply congrArg lorentzOneFormContinuousDualThreeForm
  apply ContinuousLinearMap.ext
  intro direction
  change
    formNativeLorentzMatterFirstCoefficient source 0 firstPoint field
        direction =
      formNativeLorentzMatterFirstCoefficient source 0 secondPoint field
        direction
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
    generatedVolumeDensity
  simp only [matterDualFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart]

/-- Zero-chart charged gauge response likewise depends only on the evaluated
point field. -/
theorem formNativeChargedGaugeThreeForm_zeroChart_point_independent
    (source : SmoothUnifiedSource)
    (firstPoint secondPoint : BasePoint)
    (field : StageNineContinuumPointField) :
    formNativeChargedGaugeThreeForm source 0 firstPoint field =
      formNativeChargedGaugeThreeForm source 0 secondPoint field := by
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro direction
  change
    formNativeChargedGaugeFirstCoefficient source 0 firstPoint field
        direction =
      formNativeChargedGaugeFirstCoefficient source 0 secondPoint field
        direction
  unfold formNativeChargedGaugeFirstCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
    matterGaugeKineticSum
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart]

/-- In the canonical zero chart, the point label is not an additional action
datum once the complete evaluated jet is fixed.  All position dependence is
already carried by the jet fields and derivative slots themselves. -/
theorem diracDualFormNativeJointResidualOfActionJet_point_independent
    (source : SmoothUnifiedSource)
    (firstPoint secondPoint : BasePoint)
    (jet : DiracDualFormNativePointwiseActionJetCarrier) :
    diracDualFormNativeJointResidualOfActionJet source firstPoint jet =
      diracDualFormNativeJointResidualOfActionJet source secondPoint jet := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · rfl
  · rfl
  · rfl
  · change
      jet.gravityAuxiliaryExteriorCovariantDerivative +
          formNativeMatterSpinThreeForm source 0 firstPoint jet.pointField =
        jet.gravityAuxiliaryExteriorCovariantDerivative +
          formNativeMatterSpinThreeForm source 0 secondPoint jet.pointField
    rw [formNativeMatterSpinThreeForm_zeroChart_point_independent source
      firstPoint secondPoint jet.pointField]
  · change
      jet.p286GaugeAuxiliaryExteriorCovariantDerivative +
          formNativeChargedGaugeThreeForm source 0 firstPoint jet.pointField =
        jet.p286GaugeAuxiliaryExteriorCovariantDerivative +
          formNativeChargedGaugeThreeForm source 0 secondPoint jet.pointField
    rw [formNativeChargedGaugeThreeForm_zeroChart_point_independent source
      firstPoint secondPoint jet.pointField]
  · apply funext
    intro direction
    change
      pointwiseDiracDualScalarAlgebraicDirectionalCoefficient source
            firstPoint jet direction -
          jet.scalarDifferentialMomentumDivergence direction =
        pointwiseDiracDualScalarAlgebraicDirectionalCoefficient source
            secondPoint jet direction -
          jet.scalarDifferentialMomentumDivergence direction
    unfold pointwiseDiracDualScalarAlgebraicDirectionalCoefficient
      scalarGaugeConnectionKineticFirstVariationDensity
      scalarFrameRelativeCovariantDerivative
    simp only [scalarFrameRelativeCoordinates_zeroChart]
  · apply funext
    intro direction
    change
      pointwiseDiracDualMatterAlgebraicDirectionalCoefficient source
            firstPoint jet direction -
          jet.matterDifferentialMomentumDivergence direction =
        pointwiseDiracDualMatterAlgebraicDirectionalCoefficient source
            secondPoint jet direction -
          jet.matterDifferentialMomentumDivergence direction
    unfold pointwiseDiracDualMatterAlgebraicDirectionalCoefficient
      diracDualMatterFieldVariationVector
      matterCovariantDerivativeVariationVector
      matterCovariantDerivativeKineticSum
    simp only [matterDerivativeFrameRelative_zeroChart]
  · apply funext
    intro direction
    change
      generatedVolumeDensity jet.pointField *
          (matterDualOfCoordinates direction
            (generatedContinuumDiracDualMatterVector source 0 firstPoint
              jet.pointField)).re =
        generatedVolumeDensity jet.pointField *
          (matterDualOfCoordinates direction
            (generatedContinuumDiracDualMatterVector source 0 secondPoint
              jet.pointField)).re
    unfold generatedContinuumDiracDualMatterVector
      generatedContinuumMatterKineticVector
      matterCovariantDerivativeVariationVector
      matterCovariantDerivativeKineticSum
      generatedContinuumDiracDualYukawaVector
    simp only [matterDerivativeFrameRelative_zeroChart,
      scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart]
  · change
      fderiv ℝ
          (diracDualFormNativeCoframeLocalDensity source firstPoint
            jet.pointField) jet.pointField.coframe =
        fderiv ℝ
          (diracDualFormNativeCoframeLocalDensity source secondPoint
            jet.pointField) jet.pointField.coframe
    apply congrArg (fun density : LorentzianCoframe → ℝ =>
      fderiv ℝ density jet.pointField.coframe)
    funext candidate
    rw [
      diracDualFormNativeCoframeLocalDensity_eq_constraint_add_commonCore
        source firstPoint jet.pointField candidate,
      diracDualFormNativeCoframeLocalDensity_eq_constraint_add_commonCore
        source secondPoint jet.pointField candidate,
      diracDualFormNativeCoframeCommonCoreDensity_eq_gravity_add_gauge_add_matter
        source firstPoint jet.pointField candidate,
      diracDualFormNativeCoframeCommonCoreDensity_eq_gravity_add_gauge_add_matter
        source secondPoint jet.pointField candidate]
    have matterDensity :
        diracDualFormNativeCoframeMatterDensity source firstPoint
            jet.pointField candidate =
          diracDualFormNativeCoframeMatterDensity source secondPoint
            jet.pointField candidate := by
      unfold diracDualFormNativeCoframeMatterDensity
        generatedDiracDualFormNativeMatterDensity
        generatedDensitizedContinuumScalarDensity
        generatedScalarKineticDensity
        scalarFrameRelativeCovariantDerivative
        generatedScalarPotential
        generatedDensitizedContinuumDiracDualMatterDensity
        generatedDensitizedContinuumMatterKineticDensity
        generatedContinuumMatterKineticVector
        matterCovariantDerivativeVariationVector
        matterCovariantDerivativeKineticSum
        generatedDensitizedContinuumDiracDualYukawaDensity
        generatedContinuumDiracDualYukawaVector
      simp only [withCoframe, scalarFrameRelativeCoordinates_zeroChart,
        matterDualFrameRelative_zeroChart,
        matterDerivativeFrameRelative_zeroChart,
        matterFrameRelative_zeroChart]
    rw [matterDensity]

/-- The existing residual constructor factors exactly through the generated
action jet.  This is a definitional provenance theorem, not an independent
Euler closure. -/
theorem diracDualFormNativePointwiseJointResidual_eq_actionJetReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual source configuration point =
      diracDualFormNativeJointResidualOfActionJet source point
        (generatedDiracDualFormNativePointwiseActionJet source configuration
          point) := by
  rfl

/-- Equality of complete generated action jets transports the whole
nine-coordinate residual in one step.  The two occurrences may differ because
the canonical zero-chart point label carries no additional action datum once
the evaluated jet is fixed. -/
theorem
    diracDualFormNativePointwiseJointResidual_eq_of_generatedActionJet_eq
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (actionJetEq :
      generatedDiracDualFormNativePointwiseActionJet source first firstPoint =
        generatedDiracDualFormNativePointwiseActionJet source second
          secondPoint) :
    diracDualFormNativePointwiseJointResidual source first firstPoint =
      diracDualFormNativePointwiseJointResidual source second secondPoint := by
  rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout,
    diracDualFormNativePointwiseJointResidual_eq_actionJetReadout,
    actionJetEq]
  exact
    diracDualFormNativeJointResidualOfActionJet_point_independent source
      firstPoint secondPoint
      (generatedDiracDualFormNativePointwiseActionJet source second
        secondPoint)

/-- The corresponding whole-carrier zero-fiber transporter.  It consumes an
action-jet equality and does not generate either configuration. -/
theorem
    onDiracDualFormNativePointwiseJointZeroFiber_iff_of_generatedActionJet_eq
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (actionJetEq :
      generatedDiracDualFormNativePointwiseActionJet source first firstPoint =
        generatedDiracDualFormNativePointwiseActionJet source second
          secondPoint) :
    OnDiracDualFormNativePointwiseJointZeroFiber source first firstPoint ↔
      OnDiracDualFormNativePointwiseJointZeroFiber source second
        secondPoint := by
  unfold OnDiracDualFormNativePointwiseJointZeroFiber
  rw [
    diracDualFormNativePointwiseJointResidual_eq_of_generatedActionJet_eq
      source first second firstPoint secondPoint actionJetEq]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativePointwiseActionJetCarrier
