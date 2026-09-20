import H0mework.Physics.CoframeVariation.CoframeLocalVariation
import H0mework.Physics.IdentityGerms.IdentityECCurvatureNormalSection
import H0mework.Physics.Geometry.IIPlusRestriction

/-!
# Dependency-light identity-contact EC load

These definitions prepare the computed `II+` carrier and read the live
curvature-independent coframe load at the identity contact.  They are shared
inputs to both the historical full-normal contact write and the Cauchy
evolution/constraint split.

No curvature target, normal section, response, branch, equation, or
stationarity receipt is stored here.  The historical namespace is retained
only to preserve declaration compatibility while the module dependency is
split from the full-normal producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction

noncomputable section

set_option autoImplicit false

/-- Recompute the holonomic constraint from the live coframe. -/
def diracDualFormNativeECNormalPreparedActual
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  restrictHolonomicConfigurationToIIPlus current

/-- Point field used by the gauge and matter coframe reads. -/
def diracDualFormNativeECNormalContactField
    (current : StageNineHolonomicConfiguration) :
    StageNineContinuumPointField :=
  restrictContinuumPointFieldToIIPlus
    (toContinuumPointField
      (diracDualFormNativeECNormalPreparedActual current) 0)

/-- Curvature-independent part of the repaired identity-contact EC coframe
covector: intrinsic coframe wedge plus live gauge and repaired matter reads. -/
def diracDualFormNativeIdentityECLoad
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    LorentzianCoframe →L[ℝ] ℝ :=
  identityDiracDualECCurvatureObservation
      (gravityInternalPairVarianceNormalization
        (coframeWedge (1 : LorentzianCoframe))) +
    diracDualFormNativeCoframeGaugeEulerCovector source
      (diracDualFormNativeECNormalContactField current) +
    diracDualFormNativeCoframeMatterEulerCovector source 0
      (diracDualFormNativeECNormalContactField current)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
