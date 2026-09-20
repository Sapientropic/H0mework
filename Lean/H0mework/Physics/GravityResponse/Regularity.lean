import H0mework.Physics.GravityResponse.Germ
import H0mework.Physics.Geometry.GravityBianchi

/-!
# S9-C3h71b: regularity and propagation boundary of the algebraic response

The C3h70 existing-field response preserves smoothness for every smooth input,
is Lorentz-admissible from the preserved origin skew value, and satisfies the
actual off-shell `gl(4)` Bianchi identity at every point.  Its simplicity
residual transports pointwise, while its P286 algebraic residual is unchanged.

The gravity-auxiliary residual has a stricter boundary away from the canonical
origin: exact transport is equivalent to the new primitive connection actually
realizing the pointwise forced curvature endpoint.  C3h70 currently proves
that realization only at the origin.  Thus Bianchi regularity does not disguise
the missing local-section realization, constraint propagation, or stationarity.
No new field, target curvature, branch, or receipt is accepted here.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseRegularity

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineGlobalIntegratedAction
open StageNineGravityAlgebraicKeepEndpoint
open StageNineGravityAlgebraicKeepResponseGerm
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNinePositiveSourceNativeAlgebraicEliminationLiftDefect
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-- The forced auxiliary is smooth whenever the existing coframe and auxiliary
fields are smooth.  The source scalar is fixed data, not a new field. -/
theorem gravityAlgebraicKeepResponseAuxiliaryField_componentwiseSmooth
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        gravityAlgebraicKeepResponseAuxiliaryField source configuration point
          internalPair spacetimePair := by
  intro internalPair spacetimePair
  have iiPlusComponentSmooth : ContDiff ℝ ∞ fun point =>
      physicalIIPlusBivector (configuration.coframe point)
        internalPair spacetimePair := by
    fin_cases internalPair <;>
      simp [physicalIIPlusBivector, internalBivectorDual,
        lorentzianCoframeHodge, coframeWedge] <;>
      exact ((smooth.1 _ _).mul (smooth.1 _ _)).sub
        ((smooth.1 _ _).mul (smooth.1 _ _))
  have auxiliaryComponentSmooth : ContDiff ℝ ∞ fun point =>
      configuration.gravityAuxiliary point internalPair spacetimePair :=
    smooth.2.2.1 internalPair spacetimePair
  change ContDiff ℝ ∞ fun point =>
    physicalIIPlusBivector (configuration.coframe point)
          internalPair spacetimePair +
      (1 - source.legacy.sigma) *
        (configuration.gravityAuxiliary point internalPair spacetimePair -
          physicalIIPlusBivector (configuration.coframe point)
            internalPair spacetimePair)
  exact iiPlusComponentSmooth.add
    (contDiff_const.mul
      (auxiliaryComponentSmooth.sub iiPlusComponentSmooth))

/-- The complete existing-field response preserves smoothness. -/
theorem gravityAlgebraicKeepResponseUpdate_smooth
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (gravityAlgebraicKeepResponseUpdate source configuration).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, _oldGravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth,
      normalizedAffineLorentzConnectionField_smooth _ _,
      gravityAlgebraicKeepResponseAuxiliaryField_componentwiseSmooth source
        configuration
        ⟨coframeSmooth, _oldGravityConnectionSmooth, gravityAuxiliarySmooth,
          gravityMultiplierSmooth, gaugeConnectionSmooth,
          gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
          conjugateMatterSmooth⟩,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

/-- Lorentz admissibility needs only the preserved origin value to be skew. -/
theorem gravityAlgebraicKeepResponseUpdate_lorentzAdmissible
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (originSkew : LorentzSkew (configuration.gravityConnection 0)) :
    GravityConnectionLorentzAdmissible
      (gravityAlgebraicKeepResponseUpdate source configuration) := by
  intro point
  exact gravityAlgebraicKeepResponseUpdate_lorentzSkew source configuration
    originSkew point

/-- Actual off-shell Bianchi holds everywhere after a smooth response.  This
is kinematic and is not field-equation or stationarity closure. -/
theorem gravityAlgebraicKeepResponseUpdate_bianchi
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantMixedCurvatureDerivative
          (gravityAlgebraicKeepResponseUpdate source configuration)
          point first second third +
        covariantMixedCurvatureDerivative
          (gravityAlgebraicKeepResponseUpdate source configuration)
          point second third first +
        covariantMixedCurvatureDerivative
          (gravityAlgebraicKeepResponseUpdate source configuration)
          point third first second = 0 := by
  exact holonomicGravityGL4Curvature_bianchi
    (gravityAlgebraicKeepResponseUpdate source configuration)
    (gravityAlgebraicKeepResponseUpdate_smooth source configuration smooth)
    point first second third

/-- The origin tetrad postulate is preserved because the response preserves
the primitive connection value there.  This is not away-origin propagation. -/
theorem gravityAlgebraicKeepResponseUpdate_origin_tetradCompatible
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (jet : PointwiseLorentzianCoframeJet)
    (affine : PointwiseAffineConnection)
    (compatible : TetradCompatible jet affine
      (configuration.gravityConnection 0)) :
    TetradCompatible jet affine
      ((gravityAlgebraicKeepResponseUpdate source
        configuration).gravityConnection 0) := by
  rw [gravityAlgebraicKeepResponseUpdate_gravityConnection_origin]
  exact compatible

/-- The positive source-native composition discharges the origin tetrad
premise from the actual source jet and Levi--Civita readout. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_origin_tetradCompatible
    (configuration : StageNineHolonomicConfiguration) :
    TetradCompatible (canonicalPhysicalSource.jetAt 0)
      (canonicalPhysicalSource.jetAt 0).leviCivitaConnection
      ((positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
        (positiveSourceNativeAlgebraicEliminationStateUpdate
          configuration)).gravityConnection 0) := by
  apply gravityAlgebraicKeepResponseUpdate_origin_tetradCompatible
  change TetradCompatible (canonicalPhysicalSource.jetAt 0)
    (canonicalPhysicalSource.jetAt 0).leviCivitaConnection
    (generatedLorentzConnectionAt positiveSmoothUnifiedSource 0)
  exact positive_generatedLorentzConnection_tetradCompatible 0

/-- Simplicity transport is pointwise on the whole canonical chart. -/
theorem gravityAlgebraicKeepResponseUpdate_simplicityResidual_at
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentPointwiseAlgebraicResidual source
      (gravityAlgebraicKeepResponseUpdate source configuration)
      point).gravitySimplicity =
        (1 - source.legacy.sigma) •
          (currentPointwiseAlgebraicResidual source configuration
            point).gravitySimplicity := by
  change
    forcedGravityAuxiliaryKeepEndpoint source.legacy.sigma
          (configuration.coframe point) (configuration.gravityAuxiliary point) -
        physicalIIPlusBivector (configuration.coframe point) =
      (1 - source.legacy.sigma) •
        (configuration.gravityAuxiliary point -
          physicalIIPlusBivector (configuration.coframe point))
  exact forcedGravityAuxiliaryKeepEndpoint_residual _ _ _

/-- The P286 algebraic residual is pointwise unchanged. -/
theorem gravityAlgebraicKeepResponseUpdate_p286Residual_at
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentPointwiseAlgebraicResidual source
      (gravityAlgebraicKeepResponseUpdate source configuration)
      point).p286GaugeAuxiliary =
        (currentPointwiseAlgebraicResidual source configuration
          point).p286GaugeAuxiliary := by
  rfl

/-- Exact away-origin propagation defect.  It is the gap between actual new
curvature and the pointwise forced curvature endpoint. -/
theorem gravityAlgebraicKeepResponseUpdate_auxiliaryResidual_defect_at
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentPointwiseAlgebraicResidual source
        (gravityAlgebraicKeepResponseUpdate source configuration)
        point).gravityAuxiliary -
      (1 - source.legacy.sigma) •
        (currentPointwiseAlgebraicResidual source configuration
          point).gravityAuxiliary =
      holonomicGravityCurvature
          (gravityAlgebraicKeepResponseUpdate source configuration) point -
        forcedGravityCurvatureKeepEndpoint source.legacy.sigma
          (configuration.coframe point)
          (holonomicGravityCurvature configuration point)
          (configuration.gravityAuxiliary point) := by
  change
    (holonomicGravityCurvature
        (gravityAlgebraicKeepResponseUpdate source configuration) point -
      gravityInternalDualEquiv
        (forcedGravityAuxiliaryKeepEndpoint source.legacy.sigma
          (configuration.coframe point)
          (configuration.gravityAuxiliary point))) -
      (1 - source.legacy.sigma) •
        (holonomicGravityCurvature configuration point -
          gravityInternalDualEquiv
            (configuration.gravityAuxiliary point)) = _
  unfold forcedGravityCurvatureKeepEndpoint
  abel

/-- Strict propagation boundary: auxiliary-residual transport at a point is
equivalent to actual realization of the forced curvature there. -/
theorem gravityAlgebraicKeepResponseUpdate_auxiliaryResidual_transport_iff
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentPointwiseAlgebraicResidual source
        (gravityAlgebraicKeepResponseUpdate source configuration)
        point).gravityAuxiliary =
      (1 - source.legacy.sigma) •
        (currentPointwiseAlgebraicResidual source configuration
          point).gravityAuxiliary ↔
      holonomicGravityCurvature
          (gravityAlgebraicKeepResponseUpdate source configuration) point =
        forcedGravityCurvatureKeepEndpoint source.legacy.sigma
          (configuration.coframe point)
          (holonomicGravityCurvature configuration point)
          (configuration.gravityAuxiliary point) := by
  constructor
  · intro transported
    have defectZero :
        (currentPointwiseAlgebraicResidual source
            (gravityAlgebraicKeepResponseUpdate source configuration)
            point).gravityAuxiliary -
          (1 - source.legacy.sigma) •
            (currentPointwiseAlgebraicResidual source configuration
              point).gravityAuxiliary = 0 :=
      sub_eq_zero.mpr transported
    rw [gravityAlgebraicKeepResponseUpdate_auxiliaryResidual_defect_at]
      at defectZero
    exact sub_eq_zero.mp defectZero
  · intro curvatureRealized
    apply sub_eq_zero.mp
    rw [gravityAlgebraicKeepResponseUpdate_auxiliaryResidual_defect_at,
      curvatureRealized, sub_self]

end

end SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseRegularity
