import H0mework.Physics.ElectricJoint.ElectricECResidualTelescoping
import H0mework.Physics.ElectricEC.FixedAllPointMatterScalarReadTransport

/-!
# Fixed P506/L0 matter--scalar downstream changed reads

The authoritative live-electric Einstein--Cartan actual is the existing
five-leg occurrence

```text
U0 --M/S/A--> U1 --P286 algebraic--> U2 --P286 live--> U3
   --Cartan--> U4 --EC--> U5.
```

This module specializes the whole-read telescoping law to the scalar, matter,
and conjugate-matter Euler readers at one arbitrary spacetime occurrence.  It
removes the definitionally silent P286-live edge for all three readers and
the gravity-only Cartan/EC suffix for the scalar reader.  Thus only the true
connection-sensitive downstream deltas remain.

No delta, residual, support coordinate, branch, or target field enters a
write.  These theorems audit the already generated occurrence.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECMatterScalarDeltas

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointLiveElectricECResidualTelescoping
open StageNineDiracDualFormNativeCompleteJointLiveElectricECResidualTelescoping.CompleteJointLiveElectricECSpacetimeOccurrence
open StageNineDiracDualFormNativeCompleteJointLiveElectricECSpacetimeOccurrence
open StageNineDiracDualFormNativeCompleteJointLiveElectricECSpacetimeOccurrence.CompleteJointLiveElectricECSpacetimeOccurrence
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECAllPointMatterScalarReadTransport
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Generic silent-edge laws -/

theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_scalarResidual_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current) point).scalar =
      (diracDualFormNativePointwiseJointResidual source current point).scalar := by
  rfl

theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_matterResidual_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current) point).matter =
      (diracDualFormNativePointwiseJointResidual source current point).matter := by
  rfl

theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_conjugateMatterResidual_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current) point).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual source current point
        ).conjugateMatter := by
  rfl

theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalarResidual_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current) point).scalar =
      (diracDualFormNativePointwiseJointResidual source current point).scalar := by
  rfl

private abbrev FixedOccurrence (point : BasePoint) :=
  fixedP506L0CompleteJointLiveElectricECSpacetimeOccurrence point

/-- Scalar Euler read at one fixed spacetime occurrence. -/
def fixedP506L0ScalarEulerRead
    (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration) :
    ScalarCoordinateCarrier → ℝ :=
  (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
    configuration point).scalar

/-- Matter Euler read at one fixed spacetime occurrence. -/
def fixedP506L0MatterEulerRead
    (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration) :
    MatterCoordinateCarrier → ℝ :=
  (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
    configuration point).matter

/-- Conjugate-matter Euler read at one fixed spacetime occurrence. -/
def fixedP506L0ConjugateMatterEulerRead
    (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration) :
    MatterCoordinateCarrier → ℝ :=
  (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
    configuration point).conjugateMatter

/-! ## Definitionally silent live-electric edge -/

theorem fixedP506L0_scalar_p286LiveElectric_delta_zero
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0ScalarEulerRead point)
        ((FixedOccurrence point).after .p286Algebraic)
        ((FixedOccurrence point).after .p286LiveElectric) =
      0 := by
  unfold completeJointLiveElectricECReadDelta
  rw [sub_eq_zero]
  exact
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_scalarResidual_eq_current
      positiveSmoothUnifiedSource
      ((FixedOccurrence point).after .p286Algebraic) point

theorem fixedP506L0_matter_p286LiveElectric_delta_zero
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0MatterEulerRead point)
        ((FixedOccurrence point).after .p286Algebraic)
        ((FixedOccurrence point).after .p286LiveElectric) =
      0 := by
  unfold completeJointLiveElectricECReadDelta
  rw [sub_eq_zero]
  exact
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_matterResidual_eq_current
      positiveSmoothUnifiedSource
      ((FixedOccurrence point).after .p286Algebraic) point

theorem fixedP506L0_conjugateMatter_p286LiveElectric_delta_zero
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0ConjugateMatterEulerRead point)
        ((FixedOccurrence point).after .p286Algebraic)
        ((FixedOccurrence point).after .p286LiveElectric) =
      0 := by
  unfold completeJointLiveElectricECReadDelta
  rw [sub_eq_zero]
  exact
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_conjugateMatterResidual_eq_current
      positiveSmoothUnifiedSource
      ((FixedOccurrence point).after .p286Algebraic) point

/-! ## Scalar suffix collapse -/

theorem fixedP506L0_scalar_cartan_delta_zero
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0ScalarEulerRead point)
        ((FixedOccurrence point).after .p286LiveElectric)
        ((FixedOccurrence point).after .cartan) =
      0 := by
  unfold completeJointLiveElectricECReadDelta
  rw [sub_eq_zero]
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalarResidual_eq_current
      positiveSmoothUnifiedSource
      ((FixedOccurrence point).after .p286LiveElectric) point

theorem fixedP506L0_scalar_einsteinCartan_delta_zero
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0ScalarEulerRead point)
        ((FixedOccurrence point).after .cartan)
        (FixedOccurrence point).finalActual =
      0 := by
  unfold completeJointLiveElectricECReadDelta
  rw [sub_eq_zero]
  exact
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalarResidual_eq_preEC
      point

/-- On the final actual, the scalar reader is the native M/S/A read plus the
single genuine P286-algebraic changed read.  The live-electric, Cartan, and
Einstein--Cartan suffix contributes no scalar delta. -/
theorem
    fixedP506L0_scalar_final_eq_matterScalar_native_add_p286AlgebraicDelta
    (point : BasePoint) :
    fixedP506L0ScalarEulerRead point (FixedOccurrence point).finalActual =
      fixedP506L0ScalarEulerRead point
          ((FixedOccurrence point).after .matterScalar) +
        completeJointLiveElectricECReadDelta
          (fixedP506L0ScalarEulerRead point)
          ((FixedOccurrence point).after .matterScalar)
          ((FixedOccurrence point).after .p286Algebraic) := by
  rw [
    read_final_eq_matterScalar_native_add_downstreamDeltas
        (FixedOccurrence point)
        (fixedP506L0ScalarEulerRead point),
    fixedP506L0_scalar_p286LiveElectric_delta_zero,
    fixedP506L0_scalar_cartan_delta_zero,
    fixedP506L0_scalar_einsteinCartan_delta_zero]
  simp

/-! ## Matter / adjoint suffix normal form -/

/-- The final primal-matter reader contains exactly the three
connection-sensitive downstream edges: P286 algebraic, Cartan, and EC. -/
theorem
    fixedP506L0_matter_final_eq_matterScalar_native_add_connectionDeltas
    (point : BasePoint) :
    fixedP506L0MatterEulerRead point (FixedOccurrence point).finalActual =
      fixedP506L0MatterEulerRead point
          ((FixedOccurrence point).after .matterScalar) +
        completeJointLiveElectricECReadDelta
          (fixedP506L0MatterEulerRead point)
          ((FixedOccurrence point).after .matterScalar)
          ((FixedOccurrence point).after .p286Algebraic) +
        completeJointLiveElectricECReadDelta
          (fixedP506L0MatterEulerRead point)
          ((FixedOccurrence point).after .p286LiveElectric)
          ((FixedOccurrence point).after .cartan) +
        completeJointLiveElectricECReadDelta
          (fixedP506L0MatterEulerRead point)
          ((FixedOccurrence point).after .cartan)
          (FixedOccurrence point).finalActual := by
  rw [
    read_final_eq_matterScalar_native_add_downstreamDeltas
        (FixedOccurrence point)
        (fixedP506L0MatterEulerRead point),
    fixedP506L0_matter_p286LiveElectric_delta_zero]
  simp

/-- The adjoint reader has the same exact three-edge dependency shape. -/
theorem
    fixedP506L0_conjugateMatter_final_eq_matterScalar_native_add_connectionDeltas
    (point : BasePoint) :
    fixedP506L0ConjugateMatterEulerRead point
        (FixedOccurrence point).finalActual =
      fixedP506L0ConjugateMatterEulerRead point
          ((FixedOccurrence point).after .matterScalar) +
        completeJointLiveElectricECReadDelta
          (fixedP506L0ConjugateMatterEulerRead point)
          ((FixedOccurrence point).after .matterScalar)
          ((FixedOccurrence point).after .p286Algebraic) +
        completeJointLiveElectricECReadDelta
          (fixedP506L0ConjugateMatterEulerRead point)
          ((FixedOccurrence point).after .p286LiveElectric)
          ((FixedOccurrence point).after .cartan) +
        completeJointLiveElectricECReadDelta
          (fixedP506L0ConjugateMatterEulerRead point)
          ((FixedOccurrence point).after .cartan)
          (FixedOccurrence point).finalActual := by
  rw [
    read_final_eq_matterScalar_native_add_downstreamDeltas
        (FixedOccurrence point)
        (fixedP506L0ConjugateMatterEulerRead point),
    fixedP506L0_conjugateMatter_p286LiveElectric_delta_zero]
  simp

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECMatterScalarDeltas
