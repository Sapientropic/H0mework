import H0mework.Physics.DualVariation.P286CanonicalJointActionProducerCore
import H0mework.Physics.GaugeAction.P286CompleteActionResponseOperator

/-!
# P286 required-exterior action-data congruence

The direct P286 exterior target

```text
dB = J_charged - [A,B]
```

reads only the occurrence action data and the primitive `A/B` values listed
by the theorem below.  This module exposes that exact dependency seam for
whole-field producers.  It does not construct a response and accepts no
residual, support coordinate, branch, or equation certificate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286RequiredExteriorActionDataCongruence

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation

noncomputable section

set_option autoImplicit false

/-- Congruence for the direct P286 exterior target at the common occurrence.
Besides the charged action data, it records the primitive connection and
auxiliary values actually consumed by `[A,B]`. -/
theorem
    formNativeCurrentP286RequiredExteriorDerivative_eq_of_originActionData_eq
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (coframeEq : first.coframe 0 = second.coframe 0)
    (gaugeConnectionEq :
      holonomicP286GaugeConnectionCoordinate first 0 =
        holonomicP286GaugeConnectionCoordinate second 0)
    (gaugeAuxiliaryEq :
      holonomicP286GaugeAuxiliaryCoordinate first 0 =
        holonomicP286GaugeAuxiliaryCoordinate second 0)
    (scalarEq : first.scalar 0 = second.scalar 0)
    (scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative first 0 =
        holonomicScalarCovariantDerivative second 0)
    (matterEq : first.matter 0 = second.matter 0)
    (conjugateMatterEq :
      first.conjugateMatter 0 = second.conjugateMatter 0) :
    formNativeCurrentP286RequiredExteriorDerivative source first =
      formNativeCurrentP286RequiredExteriorDerivative source second := by
  have chargedEq :=
    formNativeChargedGaugeThreeForm_eq_of_actionData_eq source first second 0
      coframeEq scalarEq scalarCovariantDerivativeEq matterEq
      conjugateMatterEq
  unfold formNativeCurrentP286RequiredExteriorDerivative
    formNativePhysicalChargedGaugeCurrentThreeForm
  rw [chargedEq, gaugeConnectionEq, gaugeAuxiliaryEq]

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286RequiredExteriorActionDataCongruence
