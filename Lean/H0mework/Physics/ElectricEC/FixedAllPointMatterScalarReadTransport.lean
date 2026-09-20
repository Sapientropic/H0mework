import H0mework.Physics.ConstrainedCauchy.MatterScalarReadTransport
import H0mework.Physics.ElectricJoint.FixedOriginCoframeClosure

/-!
# Fixed P506/L0 all-point matter/scalar read transport

This module specializes the exact Einstein--Cartan read-after-write interface
to the current fixed P506/L0 live-electric global development.  The scalar
Euler reader transports at every spacetime point.  The two matter readers
transport at any point where the final Einstein--Cartan Lorentz connection
agrees with the pre-EC connection.

The conditional matter statements expose the actual remaining coupling of
the current global write.  They do not assume a residual equation and do not
promote the anchored origin connection equality to an all-point claim.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECAllPointMatterScalarReadTransport

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeECFullCauchyMatterScalarReadTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

abbrev PreEC : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

abbrev FinalEC : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

/-- The fixed final EC scalar reader is exactly the pre-EC reader at every
spacetime point. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalarResidual_eq_preEC
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC point).scalar =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        PreEC point).scalar := by
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalarResidual_eq_current
      positiveSmoothUnifiedSource PreEC point

/-- Pointwise primal-matter transport across the fixed EC tail, with its
single true connection-value seam stated explicitly. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matterResidual_eq_preEC_of_connection_eq
    (point : BasePoint)
    (connectionEquality :
      FinalEC.gravityConnection point = PreEC.gravityConnection point) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC point).matter =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        PreEC point).matter := by
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matterResidual_eq_current_of_connection_eq
      positiveSmoothUnifiedSource PreEC point connectionEquality

/-- Pointwise adjoint-matter transport across the fixed EC tail, with the
same connection-value seam. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatterResidual_eq_preEC_of_connection_eq
    (point : BasePoint)
    (connectionEquality :
      FinalEC.gravityConnection point = PreEC.gravityConnection point) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC point).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        PreEC point).conjugateMatter := by
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatterResidual_eq_current_of_connection_eq
      positiveSmoothUnifiedSource PreEC point connectionEquality

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECAllPointMatterScalarReadTransport
