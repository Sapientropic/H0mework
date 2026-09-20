import H0mework.Physics.CartanAction.CartanReactionCurrentRestart
import H0mework.Physics.Constitutive.P286GaugeGeometricFirstVariation

/-!
# Cartan--P286 critical pair

The current-native Cartan/reaction restart changes only the Lorentz gravity
sector.  This module proves that the complete form-native P286 connection
Euler three-form is therefore retained literally on the same successor.

This is the critical-pair edge needed by a whole-product action write: it
allows an already generated P286 zero to survive the subsequent Cartan write.
It is not a residual-derived update and introduces no source field, branch,
target response, or zero-fiber receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanP286CriticalPair

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

/-- The Cartan/reaction write leaves the complete live P286 covariant
derivative unchanged, including the derivative of the primitive auxiliary
field. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_p286AuxiliaryExteriorCovariantDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative current point := by
  rfl

/-- The action-generated charged P286 current is insensitive to the gravity
fields changed by the Cartan/reaction restart.  Its coframe, scalar, matter,
adjoint matter, and P286 connection inputs are all retained. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_chargedGaugeThreeForm
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    formNativeChargedGaugeThreeForm source 0 point
        (toContinuumPointField
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) point) =
      formNativeChargedGaugeThreeForm source 0 point
        (toContinuumPointField current point) := by
  rfl

/-- Cartan and P286 form a genuine critical pair: applying the source-native
Cartan/reaction write preserves the complete P286 Euler three-form at every
spacetime point. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_p286EulerThreeForm
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm source 0
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) point =
      holonomicFormNativeP286GaugeEulerThreeForm source 0 current point := by
  rw [holonomicFormNativeP286GaugeEulerThreeForm,
    holonomicFormNativeP286GaugeEulerThreeForm,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_p286AuxiliaryExteriorCovariantDerivative,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_chargedGaugeThreeForm]

/-- In particular, a P286 zero already produced on `current` remains a zero
on the same actual after the Cartan/reaction leg. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_p286EulerThreeForm_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (p286Zero :
      holonomicFormNativeP286GaugeEulerThreeForm source 0 current point = 0) :
    holonomicFormNativeP286GaugeEulerThreeForm source 0
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) point =
      0 := by
  rw [
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_p286EulerThreeForm,
    p286Zero]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanP286CriticalPair
