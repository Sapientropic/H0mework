import H0mework.Physics.FinalJoint.FixedPointwiseJointResidualNormalForm
import H0mework.Physics.FixedJoint.FixedJointResidual

/-!
# Regression: fixed P506/L0 final common zero fiber

The positive side consumes the one source/action-generated common actual.
The negative side retains the historical fixed P506 predecessor's nonzero
origin residual.  No residual is accepted by the positive constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiberRegression

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonPointwiseJointResidualNormalForm
open StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiber
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineFormNativeP286GaugeGeometricKinematics

set_option autoImplicit false

theorem fixedP506L0FinalCommonActionResidual_checkpoint
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).Smooth ∧
      fixedP506L0FinalCommonActionResidual space = 0 ∧
      fixedP506JointResidualSection 0 ≠ 0 := by
  exact
    ⟨fixedP506L0FinalCommonActionActual_smooth space,
      fixedP506L0FinalCommonActionResidual_zero space,
      fixedP506JointResidual_origin_ne_zero⟩

theorem fixedP506JointResidual_predecessor_ne_finalCommon
    (space : StageNineSpatialPoint) :
    fixedP506JointResidualSection 0 ≠
      fixedP506L0FinalCommonActionResidual space := by
  rw [fixedP506L0FinalCommonActionResidual_zero]
  exact fixedP506JointResidual_origin_ne_zero

theorem fixedP506L0FinalCommonPointwiseJointResidualNormalForm_origin_zero
    (space : StageNineSpatialPoint) :
    fixedP506L0FinalCommonPointwiseJointResidualNormalForm space 0 = 0 := by
  have nondegenerate : Matrix.det
      ((fixedP506L0FinalCommonActionActual space).coframe 0) ≠ 0 := by
    rw [fixedP506L0FinalCommonActionActual_coframe_origin]
    norm_num
  rw [←
    fixedP506L0FinalCommonActionActual_pointwiseJointResidual_normalForm
      space 0 nondegenerate]
  exact fixedP506L0FinalCommonActionResidual_zero space

theorem fixedP506L0FinalCommonP286ExteriorDerivative_point_independent
    (space : StageNineSpatialPoint) (first second : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (fixedP506L0FinalCommonActionActual space) first =
      holonomicP286GaugeAuxiliaryExteriorDerivative
        (fixedP506L0FinalCommonActionActual space) second := by
  rw [
    fixedP506L0FinalCommonActionActual_p286ExteriorDerivative_normalForm,
    fixedP506L0FinalCommonActionActual_p286ExteriorDerivative_normalForm]

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiberRegression
