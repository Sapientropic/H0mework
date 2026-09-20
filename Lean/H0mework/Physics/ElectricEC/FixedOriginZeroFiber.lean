import H0mework.Physics.ElectricEC.FixedOriginTransport
import H0mework.Physics.ElectricJoint.FixedOriginP286ConnectionClosure
import H0mework.Physics.ElectricJoint.FixedOriginScalarClosure

/-!
# Fixed P506/L0 live-electric Einstein--Cartan origin zero fiber

The fixed source/current first generates the complete live-electric global
development and then applies the authoritative Einstein--Cartan action leg.
This module performs the whole-carrier readback on that one final actual.

The Einstein--Cartan leg directly closes its gravity, Lorentz, and coframe
channels and preserves the already generated matter and P286-auxiliary
closures.  Its exact scalar and P286-connection reader transports consume the
two source/action-generated origin closures proved on the preceding common
actual.  No residual coordinate, support branch, target field, equation
certificate, or zero-fiber witness enters either writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginZeroFiber

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginP286ConnectionClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginScalarClosure
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

abbrev FinalECOriginResidual :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
    FinalEC 0

/-- The source/current-only complete live-electric write followed by its
Einstein--Cartan action leg lands on the complete nine-channel origin zero
fiber of one common actual. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentOriginResidual_zero :
    FinalECOriginResidual = 0 := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityMultiplier_origin_zero
  · exact
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityAuxiliary_origin_zero
  · exact
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_p286GaugeAuxiliary_origin_zero
  · exact
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_lorentzConnection_origin_zero
  · rw [
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_p286GaugeConnection_origin_residual_eq_preEC]
    exact
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_p286GaugeConnection_origin_zero
  · rw [
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_origin_residual_eq_preEC]
    exact
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_origin_zero
  · exact
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_origin_zero
  · exact
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_origin_zero
  · exact
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_origin_zero

/-- Stable zero-fiber consumer for the final fixed-lineage Einstein--Cartan
actual. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_onPointwiseOriginZeroFiber :
    OnDiracDualFormNativePointwiseJointZeroFiber positiveSmoothUnifiedSource
      FinalEC 0 :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentOriginResidual_zero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginZeroFiber
