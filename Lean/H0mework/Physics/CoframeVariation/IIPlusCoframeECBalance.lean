import H0mework.Physics.DualVariation.IIPlusReductionLocalVariation

/-!
# Explicit computed-II+ coframe balance of the Dirac-dual root

The repaired reduced coframe producer already splits into its common
gauge/matter derivative and the pullback of the gravity-auxiliary BF
derivative along `D II+(e)`.  This module closes the remaining algebraic
seam.  On the computed restriction, that gravity term is exactly

```text
W22 (D II+(e)[h]) (N(F_raw) + e wedge e).
```

The terminal theorem combines this Palatini/cosmological-shaped coefficient
with the repaired gauge and complete scalar-plus-Dirac-dual matter Euler
covectors.  It is an explicit readout of an already generated derivative,
not a new action, an Einstein tensor, a normalization choice, or a stationary
actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusCoframeECBalance

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCartanTangentSimplicityResponse
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineTopologicalFourFormPairing
open StageNineTopologicalGravityCurvatureVariancePairing

noncomputable section

set_option autoImplicit false

/-! ## Gravity pullback -/

/-- Applying the internal Lorentz dual twice to the actual `II+` bivector
returns the negative coframe wedge.  This is a convention-locked algebraic
identity, independent of an action equation or solution. -/
theorem gravityInternalDualEquiv_physicalIIPlusBivector_eq_neg_coframeWedge
    (coframe : LorentzianCoframe) :
    gravityInternalDualEquiv (physicalIIPlusBivector coframe) =
      -coframeWedge coframe := by
  simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
    physicalIIPlusBivector] using
    gravityInternalDualLinear_square (coframeWedge coframe)

/-- Exact first-order gravity coefficient after the same actual is restricted
to `B := II+(e)`.  The historical curvature is normalized exactly once; the
coframe-wedge summand is the constitutive/cosmological contribution and is
not a boundary term. -/
theorem
    formNativeGravityAuxiliaryBFFirstVariationDensity_restrictToIIPlus_eq_curvature_add_coframe
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    formNativeGravityAuxiliaryBFFirstVariationDensity
        (restrictContinuumPointFieldToIIPlus field)
        (physicalIIPlusCoframeTangent field.coframe variation) =
      gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent field.coframe variation)
        (gravityInternalPairVarianceNormalization field.gravityCurvature +
          coframeWedge field.coframe) := by
  let tangent := physicalIIPlusCoframeTangent field.coframe variation
  unfold formNativeGravityAuxiliaryBFFirstVariationDensity
    gravityTopologicalBFCoefficient
  change
    gravityTopologicalWedgeCoefficient tangent
          (gravityInternalPairVarianceNormalization field.gravityCurvature) -
        (1 / 2 : ℝ) *
          (gravityTopologicalWedgeCoefficient tangent
              (gravityInternalDualEquiv
                (physicalIIPlusBivector field.coframe)) +
            gravityTopologicalWedgeCoefficient
              (physicalIIPlusBivector field.coframe)
              (gravityInternalDualEquiv tangent)) = _
  rw [gravityTopologicalWedgeCoefficient_internalDual_symmetric
    (physicalIIPlusBivector field.coframe) tangent]
  rw [gravityInternalDualEquiv_physicalIIPlusBivector_eq_neg_coframeWedge]
  rw [show -coframeWedge field.coframe =
      (-1 : ℝ) • coframeWedge field.coframe by simp]
  rw [gravityTopologicalWedgeCoefficient_smul_right]
  rw [gravityTopologicalWedgeCoefficient_add_right]
  ring

/-! ## Complete repaired coframe balance -/

/-- The actual reduced coframe derivative is the explicit first-order
gravity coefficient plus the repaired gauge and complete
scalar/Dirac-dual-matter variational stresses. -/
theorem diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_EC_balance
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
        source point field variation =
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent field.coframe variation)
          (gravityInternalPairVarianceNormalization field.gravityCurvature +
            coframeWedge field.coframe) +
        diracDualFormNativeCoframeGaugeEulerCovector source
          (restrictContinuumPointFieldToIIPlus field) variation +
        diracDualFormNativeCoframeMatterEulerCovector source point
          (restrictContinuumPointFieldToIIPlus field) variation := by
  rw [
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_common_add_bf
      source point field nondegenerate variation]
  rw [diracDualFormNativeCoframeCommonCoreEulerCovector_eq_gauge_add_matter
    source point (restrictContinuumPointFieldToIIPlus field)
      (by simpa using nondegenerate)]
  rw [
    formNativeGravityAuxiliaryBFFirstVariationDensity_restrictToIIPlus_eq_curvature_add_coframe]
  simp only [add_apply]
  ring

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusCoframeECBalance
