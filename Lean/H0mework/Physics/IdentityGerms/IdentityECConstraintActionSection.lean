import H0mework.Physics.IdentityGerms.IdentityECCurvatureNormalSection
import H0mework.Physics.CoframeVariation.IIPlusCoframeECBalance

/-!
# Identity-contact EC action section

This module records the finite-dimensional algebra forced by the current
residual-linear gravity root.  Given a live non-gravity coframe stress `T`,
the existing action principal generates

```text
response := responseOfStress (-T)
reaction := multiplierOfResponse response
F^raised := dual (II+ 1) - reaction
F_raw := varianceNormalize F^raised.
```

The resulting raw curvature cancels the identity-contact intrinsic `II+`
term and `T` in the repaired Einstein--Cartan coframe equation.  This is an
algebraic transporter from an already generated stress; it is not a source
producer, an actualizer, a branch choice, or a stationarity certificate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECConstraintActionSection

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCartanTangentSimplicityResponse
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIIPlusCoframeECBalance
open StageNineGlobalIntegratedAction
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineTopologicalFourFormPairing

noncomputable section

set_option autoImplicit false

/-- Action-owned coframe response to the negative live non-gravity stress. -/
def identityDiracDualECConstraintActionResponse
    (stress : LorentzianCoframe →L[ℝ] ℝ) : LorentzianCoframe :=
  linearPlebanskiCoframeResponseOfStress (-stress)

/-- Residual-linear reaction generated from the action-owned response. -/
def identityDiracDualECConstraintActionReaction
    (stress : LorentzianCoframe →L[ℝ] ℝ) : PhysicalBivector :=
  linearPlebanskiMultiplierOfCoframeResponse
    (identityDiracDualECConstraintActionResponse stress)

/-- Raised curvature dictated by the residual-linear auxiliary equation. -/
def identityDiracDualECConstraintActionRaisedCurvature
    (stress : LorentzianCoframe →L[ℝ] ℝ) : PhysicalBivector :=
  gravityInternalDualEquiv
      (physicalIIPlusBivector (1 : LorentzianCoframe)) -
    identityDiracDualECConstraintActionReaction stress

/-- Raw lowered curvature section consumed by the holonomic curvature
readout.  Variance normalization is applied exactly once. -/
def identityDiracDualECConstraintActionSection
    (stress : LorentzianCoframe →L[ℝ] ℝ) : PhysicalBivector :=
  gravityInternalPairVarianceNormalization
    (identityDiracDualECConstraintActionRaisedCurvature stress)

/-- Intrinsic computed-`II+` contribution at the identity coframe. -/
def identityDiracDualECIntrinsicIIPlusObservation :
    LorentzianCoframe →L[ℝ] ℝ :=
  identityDiracDualECCurvatureObservation
    (gravityInternalPairVarianceNormalization
      (coframeWedge (1 : LorentzianCoframe)))

/-- Pointwise form of the generic repaired EC cancellation. -/
theorem identityDiracDualECConstraintActionSection_balance_apply
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (variation : LorentzianCoframe) :
    identityDiracDualECCurvatureObservation
          (identityDiracDualECConstraintActionSection stress) variation +
        identityDiracDualECIntrinsicIIPlusObservation variation +
        stress variation =
      0 := by
  change
    gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization
            (gravityInternalPairVarianceNormalization
              (gravityInternalDualEquiv
                    (physicalIIPlusBivector (1 : LorentzianCoframe)) -
                linearPlebanskiMultiplierOfCoframeResponse
                  (linearPlebanskiCoframeResponseOfStress (-stress))))) +
        gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization
            (gravityInternalPairVarianceNormalization
              (coframeWedge (1 : LorentzianCoframe)))) +
        stress variation =
      0
  rw [gravityInternalPairVarianceNormalization_involutive,
    gravityInternalPairVarianceNormalization_involutive,
    gravityInternalDualEquiv_physicalIIPlusBivector_eq_neg_coframeWedge]
  rw [show
      -(coframeWedge (1 : LorentzianCoframe)) -
          linearPlebanskiMultiplierOfCoframeResponse
            (linearPlebanskiCoframeResponseOfStress (-stress)) =
        (-1 : ℝ) • coframeWedge (1 : LorentzianCoframe) +
          (-1 : ℝ) •
            linearPlebanskiMultiplierOfCoframeResponse
              (linearPlebanskiCoframeResponseOfStress (-stress)) by
      module]
  rw [gravityTopologicalWedgeCoefficient_add_right,
    gravityTopologicalWedgeCoefficient_smul_right,
    gravityTopologicalWedgeCoefficient_smul_right,
    identityDiracDualECPrincipal_eq_linearPlebanski]
  have generatedStress := DFunLike.congr_fun
    (linearPlebanskiCoframePrincipal_response_eq_neg (-stress)) variation
  simp only [neg_neg] at generatedStress
  rw [generatedStress]
  ring

/-- **Generic action-section checkpoint.**  The current residual-linear root
turns every live non-gravity coframe stress into a branch-free raw curvature
whose repaired identity-contact EC covector is exactly zero. -/
theorem identityDiracDualECConstraintActionSection_balance
    (stress : LorentzianCoframe →L[ℝ] ℝ) :
    identityDiracDualECCurvatureObservation
          (identityDiracDualECConstraintActionSection stress) +
        identityDiracDualECIntrinsicIIPlusObservation +
        stress =
      0 := by
  apply ContinuousLinearMap.ext
  intro variation
  simpa using
    identityDiracDualECConstraintActionSection_balance_apply stress variation

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECConstraintActionSection
