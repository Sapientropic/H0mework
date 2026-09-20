import H0mework.Physics.DualVariation.FieldSectionSpinCovariance
import H0mework.Physics.DualVariation.LocalSpinAction
import H0mework.Physics.DiracCovariance.Covariance
import H0mework.Physics.DiracCovariance.CurvatureReadoutCovariance
import H0mework.Physics.Dirac.ScalarLocalSpinDensity

/-!
# Holonomic local Spin covariance of the Dirac-dual form-native root

The primitive local action writes only the coframe, connection, gravity
two-forms, matter field, and independent dual.  This module regenerates the
curvature and covariant derivatives from those fields and proves that all
eleven coordinates of the resulting continuum point field agree with the
already fixed tensorial Spin transport.

The transformed point field is therefore a readout of one proof-free
primitive action.  It is not supplied to the action as a covariance receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeHolonomicSpinCovariance

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFieldSectionSpinCovariance
open StageNineDiracDualFormNativeLocalSpinAction
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracKineticLocalSpinCovariance
open StageNineDiracKineticLocalSpinCurvatureReadoutCovariance
open StageNineDiracKineticLocalSpinConnection
open StageNineDiracKineticLocalSpinDifferential
open StageNineDiracKineticSpinJurisdiction
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravitySpinCovariance
open StageNineGlobalBundle
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineScalarLocalSpinDensity
open StageNineSpinMatterBundle

open scoped ContDiff MatrixGroups

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The complete primitive root action inherits the generated inhomogeneous
connection and hence preserves the same Lorentz-admissible domain. -/
theorem localSpinDiracDualFormNativeAction_gravityConnection_admissible
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (admissible : GravityConnectionLorentzAdmissible configuration) :
    GravityConnectionLorentzAdmissible
      (localSpinDiracDualFormNativeAction spinField configuration) := by
  change GravityConnectionLorentzAdmissible
    (localSpinDiracKineticAction spinField configuration)
  exact localSpinDiracKineticAction_gravityConnection_admissible
    spinField configuration spinSmooth admissible

/-- The primitive full-root write regenerates the exact lowered curvature
transport consumed by the form-native BF density. -/
theorem holonomicGravityCurvature_localSpinDiracDualFormNative_covariant
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (point : BasePoint) :
    holonomicGravityCurvature
        (localSpinDiracDualFormNativeAction spinField configuration) point =
      spinLorentzLoweredPhysicalBivector
        (spinWeylDual (spinField point))
        (holonomicGravityCurvature configuration point) := by
  change holonomicGravityCurvature
      (localSpinDiracKineticAction spinField configuration) point = _
  exact holonomicGravityCurvature_localSpin_covariant spinField configuration
    spinSmooth smooth admissible point

/-- The primitive full-root write leaves the gauge connection unchanged, so
its derived curvature is definitionally the same actual curvature. -/
@[simp] theorem holonomicGaugeCurvature_localSpinDiracDualFormNative_invariant
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicGaugeCurvature
        (localSpinDiracDualFormNativeAction spinField configuration) point =
      holonomicGaugeCurvature configuration point :=
  rfl

/-- The scalar and gauge primitive fields are unchanged, so their derived
covariant derivative is unchanged as well. -/
@[simp] theorem
    holonomicScalarCovariantDerivative_localSpinDiracDualFormNative_invariant
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        (localSpinDiracDualFormNativeAction spinField configuration)
        point direction =
      holonomicScalarCovariantDerivative configuration point direction :=
  rfl

/-- The full primitive root write regenerates the same covariant matter
derivative as the kinetic action because both share the exact primitive
coframe, Lorentz connection, gauge connection, and matter writes. -/
theorem
    holonomicMatterCovariantDerivative_localSpinDiracDualFormNative_covariant
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (matterSmooth : ContDiff ℝ ∞ fun candidate =>
      matterCoordinateEquiv (configuration.matter candidate))
    (point : BasePoint) (direction : LorentzianIndex)
    (connectionSkew :
      LorentzSkew (configuration.gravityConnection point)) :
    holonomicMatterCovariantDerivative
        (localSpinDiracDualFormNativeAction spinField configuration)
        point direction =
      spinDiracMatterRepresentation (spinField point)
        (holonomicMatterCovariantDerivative configuration point direction) := by
  change holonomicMatterCovariantDerivative
      (localSpinDiracKineticAction spinField configuration) point direction = _
  exact holonomicMatterCovariantDerivative_localSpin_covariant spinField
    configuration spinSmooth matterSmooth point direction connectionSkew

/-- All eleven point-field slots are generated by the same primitive local
Spin action and agree with the fixed tensorial transport.  The only premises
are regularity of the input fields and the Lorentz-admissible connection
domain needed for faithful six-coordinate curvature descent. -/
theorem toContinuumPointField_localSpinDiracDualFormNativeAction
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (point : BasePoint) :
    toContinuumPointField
        (localSpinDiracDualFormNativeAction spinField configuration) point =
      transformDiracDualFormNativePointField (spinField point)
        (toContinuumPointField configuration point) := by
  have matterSmooth : ContDiff ℝ ∞ fun candidate =>
      matterCoordinateEquiv (configuration.matter candidate) :=
    smooth.2.2.2.2.2.2.2.1
  apply StageNineContinuumPointField.ext
  · rfl
  · exact
      holonomicGravityCurvature_localSpinDiracDualFormNative_covariant
        spinField configuration spinSmooth smooth admissible point
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext direction
    exact
      holonomicScalarCovariantDerivative_localSpinDiracDualFormNative_invariant
        spinField configuration point direction
  · rfl
  · funext direction
    exact
      holonomicMatterCovariantDerivative_localSpinDiracDualFormNative_covariant
        spinField configuration spinSmooth matterSmooth point direction
        (admissible point)
  · rfl

/-- The pointwise equality assembles into equality of the complete derived
first-jet sections. -/
theorem toContinuumFieldSection_localSpinDiracDualFormNativeAction
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration) :
    toContinuumFieldSection
        (localSpinDiracDualFormNativeAction spinField configuration) =
      transformDiracDualFormNativeFieldSection spinField
        (toContinuumFieldSection configuration) := by
  funext point
  exact toContinuumPointField_localSpinDiracDualFormNativeAction spinField
    configuration spinSmooth smooth admissible point

/-- The actual holonomic repaired-root action is invariant under the
proof-free primitive local Spin write.  The nondegenerate branch is used only
by the already fixed gauge constitutive density, not by the producer. -/
theorem holonomicDiracDualFormNativeIntegratedUnifiedAction_localSpin_invariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (nondegenerate : configuration.Nondegenerate) :
    holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        (localSpinDiracDualFormNativeAction spinField configuration) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        configuration := by
  unfold holonomicDiracDualFormNativeIntegratedUnifiedAction
  rw [toContinuumFieldSection_localSpinDiracDualFormNativeAction spinField
    configuration spinSmooth smooth admissible]
  exact
    sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction_spin_invariant
      source chart spinField (toContinuumFieldSection configuration)
        nondegenerate

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeHolonomicSpinCovariance
