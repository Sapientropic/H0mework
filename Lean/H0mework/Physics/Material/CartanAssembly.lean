import H0mework.Physics.CartanAction.CartanReactionCurrentRestartGlobalRegularity
import H0mework.Physics.CartanAction.CartanP286CriticalPair
import H0mework.Physics.GravityTail.FixedRootNativeWrite

/-! The whole-field Cartan write applied to the exact generated first-assembly
material. Its constructor reads the source/current fields. The four zero
channels are consequences of that write and of the preceding constitutive
refresh; no residual value is an input. Runtime admission is separate. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanReactionCurrentRestartGlobalRegularity
open StageNineDiracDualFormNativeCartanP286CriticalPair
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineLorentzConnectionVariation

noncomputable section

/-- Same-source material successor of the generated first-assembly actual. -/
def firstAssemblyCartanActual : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource firstAssemblyCurrent.configuration

theorem firstAssemblyCartanActual_smooth : firstAssemblyCartanActual.Smooth :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_smooth
    positiveSmoothUnifiedSource firstAssemblyCurrent.configuration
    root_firstAssembly_smooth root_firstAssembly_nondegenerate

theorem firstAssemblyCartanActual_nondegenerate :
    firstAssemblyCartanActual.Nondegenerate :=
  root_firstAssembly_nondegenerate

theorem firstAssemblyCartanActual_lorentzAdmissible :
    GravityConnectionLorentzAdmissible firstAssemblyCartanActual :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzAdmissible
    positiveSmoothUnifiedSource firstAssemblyCurrent.configuration
    root_firstAssembly_nondegenerate

theorem firstAssemblyCartanActual_idempotent :
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        positiveSmoothUnifiedSource firstAssemblyCartanActual =
      firstAssemblyCartanActual :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_idempotent
    positiveSmoothUnifiedSource firstAssemblyCurrent.configuration

theorem firstAssemblyCartanActual_gravityMultiplier_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      firstAssemblyCartanActual point).gravityMultiplier = 0 := by
  change formNativeGravityMultiplierEulerResidual
    (toContinuumPointField firstAssemblyCartanActual point) = 0
  rw [formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity]
  exact sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
    positiveSmoothUnifiedSource firstAssemblyCurrent.configuration point

theorem firstAssemblyCartanActual_gravityAuxiliary_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      firstAssemblyCartanActual point).gravityAuxiliary = 0 :=
  congrFun
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliaryEquation
      positiveSmoothUnifiedSource firstAssemblyCurrent.configuration) point

theorem firstAssemblyCartanActual_p286Auxiliary_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      firstAssemblyCartanActual point).p286GaugeAuxiliary = 0 := by
  change ((rootResidualAt firstAssemblyCurrent).classicalJoint point
    ).p286GaugeAuxiliary = 0
  exact root_firstAssembly_p286GaugeAuxiliaryResidual_eq_zero point

theorem firstAssemblyCartanActual_lorentz_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      firstAssemblyCartanActual point).lorentzConnection = 0 :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at
    positiveSmoothUnifiedSource firstAssemblyCurrent.configuration
    root_firstAssembly_smooth point (root_firstAssembly_nondegenerate point)

theorem firstAssemblyCartanActual_p286Connection_eq_before
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      firstAssemblyCartanActual point).p286GaugeConnection =
      ((rootResidualAt firstAssemblyCurrent).classicalJoint point
        ).p286GaugeConnection :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_p286EulerThreeForm
    positiveSmoothUnifiedSource firstAssemblyCurrent.configuration point

theorem firstAssemblyCartanActual_scalarResidual_eq_before
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      firstAssemblyCartanActual point).scalar =
      ((rootResidualAt firstAssemblyCurrent).classicalJoint point).scalar :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalarResidual_eq_current
    positiveSmoothUnifiedSource firstAssemblyCurrent.configuration point

end
end SaturationMonoid.PhysicsCore.Stage9C.Material
