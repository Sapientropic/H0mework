import H0mework.Physics.CoframeJets.GeneratedCoframeFirstJet
import H0mework.Physics.Lorentz.LorentzCoverAndSpinDescent

/-!
# S9-C3h68a: source-native gravity kinematics and actual curvature bridge

This module installs the positive source's generated coframe and Lorentz
connection into an arbitrary existing Stage-9 configuration while preserving
all other primitive fields.  Fréchet differentiation proves that the
connection is computed from the installed coframe's actual first jet.

At the obstruction coordinate, its genuine `dω + ω∧ω` curvature is `1/4`,
exactly the source's independently derived origin-curvature readout.  This is
the missing producer bridge needed before the old source-mouth mismatch can
be used as a holonomic reachability no-go.  It is not a full stationary
configuration and does not set any auxiliary, multiplier, matter, or scalar
field.
-/

namespace SaturationMonoid.PhysicsCore.StageNinePositiveSourceNativeGravityCurvatureBridge

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineCoframeFirstJet
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineHolonomicField
open StageNineLorentzCoverAndSpinDescent
open StageNineSourceGeneratedCoframeFirstJet
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Replace exactly the primitive coframe and Lorentz connection by outputs
of the same positive proof-free source. -/
def installPositiveSourceNativeGravityKinematics
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with
    coframe := positiveSmoothUnifiedSource.legacy.coframeAt
    gravityConnection :=
      generatedLorentzConnectionAt positiveSmoothUnifiedSource }

@[simp] theorem installPositiveSourceNativeGravityKinematics_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (installPositiveSourceNativeGravityKinematics configuration).coframe =
      positiveSmoothUnifiedSource.legacy.coframeAt :=
  rfl

@[simp] theorem installPositiveSourceNativeGravityKinematics_gravityConnection
    (configuration : StageNineHolonomicConfiguration) :
    (installPositiveSourceNativeGravityKinematics
      configuration).gravityConnection =
        generatedLorentzConnectionAt positiveSmoothUnifiedSource :=
  rfl

/-- Every responsibility outside the installed kinematic pair remains
visible and unchanged. -/
theorem installPositiveSourceNativeGravityKinematics_preserves_otherFields
    (configuration : StageNineHolonomicConfiguration) :
    (installPositiveSourceNativeGravityKinematics
        configuration).gravityAuxiliary = configuration.gravityAuxiliary ∧
      (installPositiveSourceNativeGravityKinematics
        configuration).gravitySimplicityMultiplier =
          configuration.gravitySimplicityMultiplier ∧
      (installPositiveSourceNativeGravityKinematics
        configuration).gaugeConnection = configuration.gaugeConnection ∧
      (installPositiveSourceNativeGravityKinematics
        configuration).gaugeAuxiliary = configuration.gaugeAuxiliary ∧
      (installPositiveSourceNativeGravityKinematics
        configuration).scalar = configuration.scalar ∧
      (installPositiveSourceNativeGravityKinematics
        configuration).matter = configuration.matter ∧
      (installPositiveSourceNativeGravityKinematics
        configuration).conjugateMatter = configuration.conjugateMatter := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The installed Lorentz connection is derived from the installed primitive
coframe's genuine Fréchet first jet. -/
theorem installPositiveSourceNativeGravityKinematics_connection_eq_actualFirstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (installPositiveSourceNativeGravityKinematics
        configuration).gravityConnection point =
      (holonomicCoframeFirstJetAt
        (installPositiveSourceNativeGravityKinematics configuration).coframe
        point).lorentzSpinConnection := by
  change generatedLorentzConnectionAt positiveSmoothUnifiedSource point =
    (holonomicCoframeFirstJetAt
      positiveSmoothUnifiedSource.legacy.coframeAt point).lorentzSpinConnection
  exact generatedLorentzConnectionAt_eq_actualCoframeFirstJet _ _

theorem installPositiveSourceNativeGravityKinematics_nondegenerate
    (configuration : StageNineHolonomicConfiguration) :
    (installPositiveSourceNativeGravityKinematics
      configuration).Nondegenerate := by
  intro point
  exact canonicalPhysicalSource_globally_nondegenerate point

/-- Smoothness of a prior configuration is retained after the two source
kinematic fields are installed. -/
theorem installPositiveSourceNativeGravityKinematics_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (installPositiveSourceNativeGravityKinematics configuration).Smooth := by
  rcases smooth with
    ⟨_oldCoframeSmooth, _oldGravityConnectionSmooth,
      gravityAuxiliarySmooth, gravityMultiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth,
      matterSmooth, conjugateMatterSmooth⟩
  have sourceCoframeSmooth : ∀ row column,
      ContDiff ℝ ∞ (fun point =>
        positiveSmoothUnifiedSource.legacy.coframeAt point row column) := by
    intro row column
    exact (contDiff_pi.mp
      (contDiff_pi.mp
        positiveSmoothUnifiedSource.legacy.coframeAt_contDiff row) column).of_le
          (by simp)
  have sourceGravityConnectionSmooth : ∀ direction internalOut internalIn,
      ContDiff ℝ ∞ (fun point =>
        generatedLorentzConnectionAt positiveSmoothUnifiedSource point
          direction internalOut internalIn) := by
    intro direction internalOut internalIn
    exact
      (positive_generatedLorentzConnection_componentwiseSmooth
        direction internalOut internalIn).of_le (by simp)
  exact ⟨by
      simpa [installPositiveSourceNativeGravityKinematics] using
        sourceCoframeSmooth,
    by
      simpa [installPositiveSourceNativeGravityKinematics] using
        sourceGravityConnectionSmooth,
    gravityAuxiliarySmooth, gravityMultiplierSmooth, gaugeConnectionSmooth,
    gaugeAuxiliarySmooth, scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

/-! ## Exact canonical inverse formulas used by the curvature computation -/

theorem canonicalSourceCoframe_inv (point : BasePoint) :
    (canonicalPhysicalSource.coframeAt point)⁻¹ =
      Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
        (-(point 2)) := by
  apply Matrix.inv_eq_left_inv
  rw [canonicalPhysicalSource_coframeAt_eq_transvection]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Matrix.transvection, Matrix.single,
      Matrix.one_apply, Fin.sum_univ_four]

def canonicalSourceMetricInverseCandidate (point : BasePoint) :
    LorentzianMetric :=
  Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
      (-(point 2)) *
    minkowskiInternalMetric *
    (Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
      (-(point 2))).transpose

theorem canonicalSourceMetric_inv (point : BasePoint) :
    (canonicalPhysicalSource.jetAt point).metric⁻¹ =
      canonicalSourceMetricInverseCandidate point := by
  change
    (lorentzianMetricOfCoframe
      (canonicalPhysicalSource.coframeAt point))⁻¹ =
        canonicalSourceMetricInverseCandidate point
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column
  all_goals
    simp [canonicalSourceMetricInverseCandidate,
      lorentzianMetricOfCoframe,
      canonicalPhysicalSource_coframeAt_eq_transvection,
      minkowskiInternalMetric, Matrix.mul_apply,
      Matrix.transvection, Matrix.single, Fin.sum_univ_four]
  all_goals ring

theorem lorentzianMetricOfCoframe_one_inv :
    (lorentzianMetricOfCoframe (1 : LorentzianCoframe))⁻¹ =
      minkowskiInternalMetric := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [lorentzianMetricOfCoframe, minkowskiInternalMetric,
      Matrix.mul_apply, Fin.sum_univ_four]

/-! ## The two derivative coordinates and the actual curvature witness -/

theorem sourceNativeGravityConnection_one_zero_one
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (installPositiveSourceNativeGravityKinematics
      configuration).gravityConnection point 1 0 1 = 0 := by
  change
    (canonicalPhysicalSource.jetAt point).lorentzSpinConnection 1 0 1 = 0
  unfold PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe⁻¹ =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (-(point 2)) by
      exact canonicalSourceCoframe_inv point]
  rw [Matrix.mul_apply]
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (point 2) by
      exact canonicalPhysicalSource_coframeAt_eq_transvection point]
  unfold PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
  rw [canonicalSourceMetric_inv point]
  unfold PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (point 2) by
      exact canonicalPhysicalSource_coframeAt_eq_transvection point]
  simp [
    canonicalSourceMetricInverseCandidate,
    ProofFreeRicherAnholonomicSource.Source.jetAt,
    StageEightProofFreeSource.Source.toPhysicalSource,
    StageEightProofFreeSource.canonicalPhysicalSource,
    StageEightProofFreeSource.canonicalSource,
    ProofFreeRicherAnholonomicSource.shearCoefficient,
    minkowskiInternalMetric, minkowskiInternalSign, Matrix.mulVec,
    Matrix.of_apply, Matrix.mul_apply, Matrix.transvection, Matrix.single,
    Matrix.one_apply,
    dotProduct, Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem sourceNativeGravityConnection_zero_zero_one
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (installPositiveSourceNativeGravityKinematics
      configuration).gravityConnection point 0 0 1 = 0 := by
  change
    (canonicalPhysicalSource.jetAt point).lorentzSpinConnection 0 0 1 = 0
  unfold PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe⁻¹ =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (-(point 2)) by
      exact canonicalSourceCoframe_inv point]
  rw [Matrix.mul_apply]
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (point 2) by
      exact canonicalPhysicalSource_coframeAt_eq_transvection point]
  unfold PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
  rw [canonicalSourceMetric_inv point]
  unfold PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (point 2) by
      exact canonicalPhysicalSource_coframeAt_eq_transvection point]
  simp [
    canonicalSourceMetricInverseCandidate,
    ProofFreeRicherAnholonomicSource.Source.jetAt,
    StageEightProofFreeSource.Source.toPhysicalSource,
    StageEightProofFreeSource.canonicalPhysicalSource,
    StageEightProofFreeSource.canonicalSource,
    ProofFreeRicherAnholonomicSource.shearCoefficient,
    minkowskiInternalMetric, minkowskiInternalSign, Matrix.mulVec,
    Matrix.of_apply, Matrix.mul_apply, Matrix.transvection, Matrix.single,
    Matrix.one_apply,
    dotProduct, Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem sourceNativeGravityConnectionDerivative_zero_one_zero_one
    (configuration : StageNineHolonomicConfiguration) :
    gravityConnectionDerivative
        (installPositiveSourceNativeGravityKinematics configuration)
        0 0 1 0 1 = 0 := by
  unfold gravityConnectionDerivative
  rw [show
    (fun candidate =>
      (installPositiveSourceNativeGravityKinematics
        configuration).gravityConnection candidate 1 0 1) =
        (fun _ : BasePoint => (0 : ℝ)) by
    funext candidate
    exact sourceNativeGravityConnection_one_zero_one configuration candidate]
  simp

theorem sourceNativeGravityConnectionDerivative_one_zero_zero_one
    (configuration : StageNineHolonomicConfiguration) :
    gravityConnectionDerivative
        (installPositiveSourceNativeGravityKinematics configuration)
        0 1 0 0 1 = 0 := by
  unfold gravityConnectionDerivative
  rw [show
    (fun candidate =>
      (installPositiveSourceNativeGravityKinematics
        configuration).gravityConnection candidate 0 0 1) =
        (fun _ : BasePoint => (0 : ℝ)) by
    funext candidate
    exact sourceNativeGravityConnection_zero_zero_one configuration candidate]
  simp

/-- The actual source-native curvature component generated by
`dω + ω∧ω`. -/
theorem installPositiveSourceNativeGravityKinematics_curvature_zero_zero
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (installPositiveSourceNativeGravityKinematics configuration) 0 0 0 =
      (1 / 4 : ℝ) := by
  unfold holonomicGravityCurvature
  dsimp only
  change
    minkowskiInternalSign 0 *
      (gravityConnectionDerivative
          (installPositiveSourceNativeGravityKinematics configuration)
            0 0 1 0 1 -
        gravityConnectionDerivative
          (installPositiveSourceNativeGravityKinematics configuration)
            0 1 0 0 1 +
        ∑ middle : LorentzianIndex,
          ((installPositiveSourceNativeGravityKinematics
                configuration).gravityConnection 0 0 0 middle *
              (installPositiveSourceNativeGravityKinematics
                configuration).gravityConnection 0 1 middle 1 -
            (installPositiveSourceNativeGravityKinematics
                configuration).gravityConnection 0 1 0 middle *
              (installPositiveSourceNativeGravityKinematics
                configuration).gravityConnection 0 0 middle 1)) =
      (1 / 4 : ℝ)
  rw [sourceNativeGravityConnectionDerivative_zero_one_zero_one,
    sourceNativeGravityConnectionDerivative_one_zero_zero_one]
  simp [installPositiveSourceNativeGravityKinematics,
    generatedLorentzConnectionAt,
    PointwiseLorentzianCoframeJet.lorentzSpinConnection,
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix,
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix,
    affineConnectionMatrix,
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix,
    PointwiseLorentzianCoframeJet.leviCivitaConnection,
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaVector,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection,
    PointwiseLorentzianCoframeJet.metricDerivative,
    PointwiseLorentzianCoframeJet.metric,
    lorentzianMetricOfCoframe_one_inv,
    StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ProofFreeRicherAnholonomicSource.Source.jetAt,
    StageNineEnrichedProofFreeSource.SmoothUnifiedSource.legacy,
    StageNineEnrichedProofFreeSource.SmoothUnifiedSource.forget,
    StageEightProofFreeSource.Source.toPhysicalSource,
    StageEightProofFreeSource.canonicalSource,
    ProofFreeRicherAnholonomicSource.shearCoefficient,
    minkowskiInternalMetric, minkowskiInternalSign,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.diagonal_apply, Matrix.one_apply]
  ring

theorem positiveSourceLegacyCurvature_zero_zero :
    positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin 0 0 =
      (1 / 4 : ℝ) := by
  change canonicalPhysicalSource.lorentzCurvatureAtOrigin 0 0 = (1 / 4 : ℝ)
  simp [ProofFreeRicherAnholonomicSource.Source.lorentzCurvatureAtOrigin,
    pairFirst, pairSecond, minkowskiInternalSign,
    canonicalPhysicalSource_curvature_component]

/-- The genuine holonomic curvature and the source's independently derived
curvature readout agree at the exact obstruction coordinate. -/
theorem installPositiveSourceNativeGravityKinematics_curvature_eq_source
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (installPositiveSourceNativeGravityKinematics configuration) 0 0 0 =
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin 0 0 := by
  rw [installPositiveSourceNativeGravityKinematics_curvature_zero_zero,
    positiveSourceLegacyCurvature_zero_zero]

end

end SaturationMonoid.PhysicsCore.StageNinePositiveSourceNativeGravityCurvatureBridge
