import H0mework.Physics.GravityResponse.Germ
import H0mework.Physics.Geometry.JointStateLiftDefect
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity

/-!
# S9-C3h71a: full origin lift-defect support of the algebraic keep response

C3h70 closed the three algebraic coordinates at the canonical origin.  This
module computes the support of the complete nine-coordinate lift defect there.
The response preserves the P286 connection, scalar, matter, and conjugate
matter fields, and preserves the primitive gravity connection value at the
origin.  Consequently the P286, scalar, matter, and conjugate-matter actual
Euler--Lagrange deltas vanish.  Their lift-defect coordinates are exactly the
input trace `(I-K)r`.

The Lorentz and coframe coordinates are left as their actual response deltas
plus the same trace.  This is a complete support normal form, not a proof that
the full defect vanishes.  It accepts no target state, residual certificate,
stationarity receipt, branch, or new field.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseFullDefect

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGravityAlgebraicKeepResponseGerm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellResidualTransportRoot
open StageNineJointStateLiftDefect
open StageNineLorentzConnectionVariation
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineConjugateMatterVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNinePositiveSourceNativeAlgebraicEliminationLiftDefect
open StageNinePositiveSourceNativeAlgebraicEliminationUpdate
open DiracExteriorMatterAction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

abbrev algebraicKeepResponseInput
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  positiveSourceNativeAlgebraicEliminationUpdate configuration

abbrev algebraicKeepResponseImage
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
    (algebraicKeepResponseInput configuration)

@[simp] theorem algebraicKeepResponseImage_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseImage configuration).coframe =
      (algebraicKeepResponseInput configuration).coframe :=
  rfl

@[simp] theorem algebraicKeepResponseImage_gaugeConnection
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseImage configuration).gaugeConnection =
      (algebraicKeepResponseInput configuration).gaugeConnection :=
  rfl

@[simp] theorem algebraicKeepResponseImage_scalar
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseImage configuration).scalar =
      (algebraicKeepResponseInput configuration).scalar :=
  rfl

@[simp] theorem algebraicKeepResponseImage_matter
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseImage configuration).matter =
      (algebraicKeepResponseInput configuration).matter :=
  rfl

@[simp] theorem algebraicKeepResponseImage_conjugateMatter
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseImage configuration).conjugateMatter =
      (algebraicKeepResponseInput configuration).conjugateMatter :=
  rfl

theorem algebraicKeepResponseImage_p286GaugeConnectionResidual_eq
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
      (algebraicKeepResponseImage configuration) point).p286GaugeConnection =
        (currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
          (algebraicKeepResponseInput configuration) point).p286GaugeConnection := by
  rfl

theorem algebraicKeepResponseImage_scalarResidual_eq
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
      (algebraicKeepResponseImage configuration) point).scalar =
        (currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
          (algebraicKeepResponseInput configuration) point).scalar := by
  rfl

theorem algebraicKeepResponseImage_gravityConnection_origin_eq
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseImage configuration).gravityConnection 0 =
      (algebraicKeepResponseInput configuration).gravityConnection 0 := by
  exact gravityAlgebraicKeepResponseUpdate_gravityConnection_origin
    positiveSmoothUnifiedSource (algebraicKeepResponseInput configuration)

theorem algebraicKeepResponseImage_generatedVolumeDensity_eq
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    generatedVolumeDensity
        (toContinuumPointField (algebraicKeepResponseImage configuration) point) =
      generatedVolumeDensity
        (toContinuumPointField (algebraicKeepResponseInput configuration) point) := by
  unfold generatedVolumeDensity toContinuumPointField
  rw [algebraicKeepResponseImage_coframe]

theorem algebraicKeepResponseImage_matterCovariantDerivative_origin_eq
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (algebraicKeepResponseImage configuration) 0 direction =
      holonomicMatterCovariantDerivative
        (algebraicKeepResponseInput configuration) 0 direction := by
  unfold holonomicMatterCovariantDerivative
  rw [algebraicKeepResponseImage_gravityConnection_origin_eq,
    algebraicKeepResponseImage_gaugeConnection,
    algebraicKeepResponseImage_matter]

theorem algebraicKeepResponseImage_matterVariationAlgebraicDirection_origin_eq
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    holonomicMatterVariationAlgebraicDirection
        (algebraicKeepResponseImage configuration) direction 0 formDirection =
      holonomicMatterVariationAlgebraicDirection
        (algebraicKeepResponseInput configuration) direction 0 formDirection := by
  unfold holonomicMatterVariationAlgebraicDirection
  rw [algebraicKeepResponseImage_gravityConnection_origin_eq,
    algebraicKeepResponseImage_gaugeConnection]

theorem algebraicKeepResponseImage_matterDifferentialMomentum_eq
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (point : BasePoint) :
    matterDifferentialMomentum source (algebraicKeepResponseImage configuration)
        direction derivativeDirection point =
      matterDifferentialMomentum source (algebraicKeepResponseInput configuration)
        direction derivativeDirection point := by
  rfl

theorem algebraicKeepResponseImage_matterDifferentialMomentumDivergence_eq
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterDifferentialMomentumDivergence source
        (algebraicKeepResponseImage configuration) direction point =
      matterDifferentialMomentumDivergence source
        (algebraicKeepResponseInput configuration) direction point := by
  rfl

theorem algebraicKeepResponseImage_matterAlgebraicVariationVector_origin_eq
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) :
    matterAlgebraicVariationVector source
        (algebraicKeepResponseImage configuration) direction 0 =
      matterAlgebraicVariationVector source
        (algebraicKeepResponseInput configuration) direction 0 := by
  have derivativeEquality :
      holonomicMatterVariationAlgebraicDirection
          (algebraicKeepResponseImage configuration) direction 0 =
        holonomicMatterVariationAlgebraicDirection
          (algebraicKeepResponseInput configuration) direction 0 := by
    funext formDirection
    exact
      algebraicKeepResponseImage_matterVariationAlgebraicDirection_origin_eq
        configuration direction formDirection
  unfold matterAlgebraicVariationVector matterFieldVariationVector
  rw [matterGaugeKineticSum_zeroChart, matterGaugeKineticSum_zeroChart]
  simp only [toContinuumPointField]
  rw [algebraicKeepResponseImage_coframe,
    algebraicKeepResponseImage_scalar, derivativeEquality]

theorem algebraicKeepResponseImage_matterEulerLagrange_origin_eq
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) :
    matterEulerLagrangeDirectionalCoefficient source
        (algebraicKeepResponseImage configuration) direction 0 =
      matterEulerLagrangeDirectionalCoefficient source
        (algebraicKeepResponseInput configuration) direction 0 := by
  unfold matterEulerLagrangeDirectionalCoefficient
  unfold matterAlgebraicDirectionalCoefficient
  rw [algebraicKeepResponseImage_matterAlgebraicVariationVector_origin_eq,
    algebraicKeepResponseImage_matterDifferentialMomentumDivergence_eq,
    algebraicKeepResponseImage_generatedVolumeDensity_eq,
    algebraicKeepResponseImage_conjugateMatter]

theorem algebraicKeepResponseImage_generatedContinuumMatterVector_origin_eq
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    generatedContinuumMatterVector source 0 0
        (toContinuumPointField (algebraicKeepResponseImage configuration) 0) =
      generatedContinuumMatterVector source 0 0
        (toContinuumPointField (algebraicKeepResponseInput configuration) 0) := by
  have derivativeEquality :
      holonomicMatterCovariantDerivative
          (algebraicKeepResponseImage configuration) 0 =
        holonomicMatterCovariantDerivative
          (algebraicKeepResponseInput configuration) 0 := by
    funext derivativeDirection
    exact algebraicKeepResponseImage_matterCovariantDerivative_origin_eq
      configuration derivativeDirection
  unfold generatedContinuumMatterVector
  simp only [matterDerivativeFrameRelative_zeroChart,
    matterFrameRelative_zeroChart, scalarFrameRelativeCoordinates_zeroChart,
    toContinuumPointField]
  rw [algebraicKeepResponseImage_coframe,
    algebraicKeepResponseImage_scalar, algebraicKeepResponseImage_matter,
    derivativeEquality]

theorem algebraicKeepResponseImage_conjugateMatterEulerLagrange_origin_eq
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) :
    conjugateMatterDirectionalCoefficient source
        (algebraicKeepResponseImage configuration) direction 0 =
      conjugateMatterDirectionalCoefficient source
        (algebraicKeepResponseInput configuration) direction 0 := by
  unfold conjugateMatterDirectionalCoefficient
  rw [algebraicKeepResponseImage_generatedContinuumMatterVector_origin_eq,
    algebraicKeepResponseImage_generatedVolumeDensity_eq]

/-! ## Complete origin support normal form -/

abbrev algebraicKeepResponseLiftDefect
    (configuration : StageNineHolonomicConfiguration) :
    CurrentPointwiseJointShellResidualCarrier :=
  currentJointShellStateLiftDefect positiveSmoothUnifiedSource
    positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
    (algebraicKeepResponseInput configuration) 0

abbrev algebraicKeepResponseInputTrace
    (configuration : StageNineHolonomicConfiguration) :
    CurrentPointwiseJointShellResidualCarrier :=
  currentJointShellResidualTrace positiveSmoothUnifiedSource
    (algebraicKeepResponseInput configuration) 0

def algebraicKeepResponseLorentzActualDelta
    (configuration : StageNineHolonomicConfiguration) :
    LorentzBivectorOneForm → ℝ :=
  (currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
      (algebraicKeepResponseImage configuration) 0).lorentzConnection -
    (currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
      (algebraicKeepResponseInput configuration) 0).lorentzConnection

def algebraicKeepResponseCoframeActualDelta
    (configuration : StageNineHolonomicConfiguration) :
    LorentzianCoframe →L[ℝ] ℝ :=
  (currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
      (algebraicKeepResponseImage configuration) 0).coframe -
    (currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
      (algebraicKeepResponseInput configuration) 0).coframe

theorem algebraicKeepResponseLiftDefect_p286GaugeConnection_eq_trace
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseLiftDefect
        configuration).eulerLagrange.p286GaugeConnection =
      (algebraicKeepResponseInputTrace
        configuration).eulerLagrange.p286GaugeConnection := by
  have split := congrFun
    (currentJointShellStateLiftDefect_eq_actualDelta_add_trace
      positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      (algebraicKeepResponseInput configuration)) 0
  have coordinateSplit := congrArg
    (fun residual : CurrentPointwiseJointShellResidualCarrier =>
      residual.eulerLagrange.p286GaugeConnection) split
  change
    (algebraicKeepResponseLiftDefect
        configuration).eulerLagrange.p286GaugeConnection =
      ((currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
          (algebraicKeepResponseImage configuration) 0).p286GaugeConnection -
        (currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
          (algebraicKeepResponseInput configuration) 0).p286GaugeConnection) +
        (algebraicKeepResponseInputTrace
          configuration).eulerLagrange.p286GaugeConnection at coordinateSplit
  rw [algebraicKeepResponseImage_p286GaugeConnectionResidual_eq,
    sub_self, zero_add] at coordinateSplit
  exact coordinateSplit

theorem algebraicKeepResponseLiftDefect_scalar_eq_trace
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseLiftDefect configuration).eulerLagrange.scalar =
      (algebraicKeepResponseInputTrace configuration).eulerLagrange.scalar := by
  have split := congrFun
    (currentJointShellStateLiftDefect_eq_actualDelta_add_trace
      positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      (algebraicKeepResponseInput configuration)) 0
  have coordinateSplit := congrArg
    (fun residual : CurrentPointwiseJointShellResidualCarrier =>
      residual.eulerLagrange.scalar) split
  change
    (algebraicKeepResponseLiftDefect configuration).eulerLagrange.scalar =
      ((currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
          (algebraicKeepResponseImage configuration) 0).scalar -
        (currentPointwiseEulerLagrangeResidual positiveSmoothUnifiedSource
          (algebraicKeepResponseInput configuration) 0).scalar) +
        (algebraicKeepResponseInputTrace configuration).eulerLagrange.scalar
      at coordinateSplit
  rw [algebraicKeepResponseImage_scalarResidual_eq, sub_self, zero_add]
    at coordinateSplit
  exact coordinateSplit

theorem algebraicKeepResponseLiftDefect_matter_eq_trace
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseLiftDefect configuration).eulerLagrange.matter =
      (algebraicKeepResponseInputTrace configuration).eulerLagrange.matter := by
  funext direction
  have split := congrFun
    (currentJointShellStateLiftDefect_eq_actualDelta_add_trace
      positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      (algebraicKeepResponseInput configuration)) 0
  have coordinateSplit := congrArg
    (fun residual : CurrentPointwiseJointShellResidualCarrier =>
      residual.eulerLagrange.matter direction) split
  change
    (algebraicKeepResponseLiftDefect configuration).eulerLagrange.matter
        direction =
      (matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
          (algebraicKeepResponseImage configuration) direction 0 -
        matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
          (algebraicKeepResponseInput configuration) direction 0) +
        (algebraicKeepResponseInputTrace
          configuration).eulerLagrange.matter direction at coordinateSplit
  rw [algebraicKeepResponseImage_matterEulerLagrange_origin_eq,
    sub_self, zero_add] at coordinateSplit
  exact coordinateSplit

theorem algebraicKeepResponseLiftDefect_conjugateMatter_eq_trace
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseLiftDefect
        configuration).eulerLagrange.conjugateMatter =
      (algebraicKeepResponseInputTrace
        configuration).eulerLagrange.conjugateMatter := by
  funext direction
  have split := congrFun
    (currentJointShellStateLiftDefect_eq_actualDelta_add_trace
      positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      (algebraicKeepResponseInput configuration)) 0
  have coordinateSplit := congrArg
    (fun residual : CurrentPointwiseJointShellResidualCarrier =>
      residual.eulerLagrange.conjugateMatter direction) split
  change
    (algebraicKeepResponseLiftDefect
        configuration).eulerLagrange.conjugateMatter direction =
      (conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
          (algebraicKeepResponseImage configuration) direction 0 -
        conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
          (algebraicKeepResponseInput configuration) direction 0) +
        (algebraicKeepResponseInputTrace
          configuration).eulerLagrange.conjugateMatter direction
      at coordinateSplit
  rw [algebraicKeepResponseImage_conjugateMatterEulerLagrange_origin_eq,
    sub_self, zero_add] at coordinateSplit
  exact coordinateSplit

theorem algebraicKeepResponseLiftDefect_lorentz_eq_actualDelta_add_trace
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseLiftDefect
        configuration).eulerLagrange.lorentzConnection =
      algebraicKeepResponseLorentzActualDelta configuration +
        (algebraicKeepResponseInputTrace
          configuration).eulerLagrange.lorentzConnection := by
  have split := congrFun
    (currentJointShellStateLiftDefect_eq_actualDelta_add_trace
      positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      (algebraicKeepResponseInput configuration)) 0
  exact congrArg
    (fun residual : CurrentPointwiseJointShellResidualCarrier =>
      residual.eulerLagrange.lorentzConnection) split

theorem algebraicKeepResponseLiftDefect_coframe_eq_actualDelta_add_trace
    (configuration : StageNineHolonomicConfiguration) :
    (algebraicKeepResponseLiftDefect configuration).eulerLagrange.coframe =
      algebraicKeepResponseCoframeActualDelta configuration +
        (algebraicKeepResponseInputTrace configuration).eulerLagrange.coframe := by
  have split := congrFun
    (currentJointShellStateLiftDefect_eq_actualDelta_add_trace
      positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      (algebraicKeepResponseInput configuration)) 0
  exact congrArg
    (fun residual : CurrentPointwiseJointShellResidualCarrier =>
      residual.eulerLagrange.coframe) split

def algebraicKeepResponseLiftDefectOriginNormalForm
    (configuration : StageNineHolonomicConfiguration) :
    CurrentPointwiseJointShellResidualCarrier where
  algebraic := 0
  eulerLagrange :=
    { lorentzConnection :=
        algebraicKeepResponseLorentzActualDelta configuration +
          (algebraicKeepResponseInputTrace
            configuration).eulerLagrange.lorentzConnection
      p286GaugeConnection :=
        (algebraicKeepResponseInputTrace
          configuration).eulerLagrange.p286GaugeConnection
      scalar :=
        (algebraicKeepResponseInputTrace configuration).eulerLagrange.scalar
      matter :=
        (algebraicKeepResponseInputTrace configuration).eulerLagrange.matter
      conjugateMatter :=
        (algebraicKeepResponseInputTrace
          configuration).eulerLagrange.conjugateMatter
      coframe := algebraicKeepResponseCoframeActualDelta configuration +
        (algebraicKeepResponseInputTrace configuration).eulerLagrange.coframe }

theorem algebraicKeepResponseLiftDefect_eq_originNormalForm
    (configuration : StageNineHolonomicConfiguration) :
    algebraicKeepResponseLiftDefect configuration =
      algebraicKeepResponseLiftDefectOriginNormalForm configuration := by
  apply CurrentPointwiseJointShellResidualCarrier.ext
  · simpa [algebraicKeepResponseLiftDefectOriginNormalForm,
      algebraicKeepResponseLiftDefect, algebraicKeepResponseInput] using
        positiveSourceNativeGravityAlgebraicKeepResponse_liftDefect_algebraic_origin
          configuration
  · apply CurrentPointwiseEulerLagrangeResidualCarrier.ext
    · simpa [algebraicKeepResponseLiftDefectOriginNormalForm] using
        algebraicKeepResponseLiftDefect_lorentz_eq_actualDelta_add_trace
          configuration
    · simpa [algebraicKeepResponseLiftDefectOriginNormalForm] using
        algebraicKeepResponseLiftDefect_p286GaugeConnection_eq_trace
          configuration
    · simpa [algebraicKeepResponseLiftDefectOriginNormalForm] using
        algebraicKeepResponseLiftDefect_scalar_eq_trace configuration
    · simpa [algebraicKeepResponseLiftDefectOriginNormalForm] using
        algebraicKeepResponseLiftDefect_matter_eq_trace configuration
    · simpa [algebraicKeepResponseLiftDefectOriginNormalForm] using
        algebraicKeepResponseLiftDefect_conjugateMatter_eq_trace configuration
    · simpa [algebraicKeepResponseLiftDefectOriginNormalForm] using
        algebraicKeepResponseLiftDefect_coframe_eq_actualDelta_add_trace
          configuration

end

end SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseFullDefect
