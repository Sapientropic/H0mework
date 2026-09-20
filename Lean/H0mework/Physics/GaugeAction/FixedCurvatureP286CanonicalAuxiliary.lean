import H0mework.Physics.Coframe.ResidualLimitCoframeBalanceDecision

/-!
# S9-C3h65a: canonical P286 auxiliary on the fixed-curvature coframe fiber

The C3h64 fixed-reference-curvature gravity fiber forces the coframe to `+I`
or `-I`.  This module proves a stronger, branch-free fact: on every nonzero
radial coframe, the already-defined P286 constitutive solver sends the actual
reference curvature to the actual reference auxiliary.

The radial scalar is universally quantified; it is not a source value, a
tunable coupling, or a selected branch.  The only coupling used below is the
existing positive-source value `g² = 1/2`, and the auxiliary is computed by
`generatedP286GaugeConstitutiveAuxiliary` rather than supplied as a receipt.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineFixedCurvatureP286CanonicalAuxiliary

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryEquation
open StageNineResidualLimitCoframeBalanceDecision

noncomputable section

set_option autoImplicit false

/-- Coordinate form of the actual canonical P286 response.  Radial Hodge
invariance and the fixed positive-source coupling force the reference
auxiliary for every nonzero scale. -/
theorem positiveSourceP286CanonicalAuxiliary_radial_eq_reference
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    p286GaugeConstitutiveAuxiliaryCoordinate
        positiveSmoothUnifiedSource
        (radialCoframe scalar)
        referenceP286CurvatureCoordinate =
      referenceP286AuxiliaryCoordinate := by
  unfold p286GaugeConstitutiveAuxiliaryCoordinate
  rw [positiveSource_generatedGaugeCoupling_eq_half,
    radialCoframe_spacetimeHodge scalar nonzero]
  change (-((1 / 2 : ℝ)⁻¹)) •
      liftGaugeTwoFormOperator lorentzianCoframeHodge
        referenceP286CurvatureCoordinate =
    referenceP286AuxiliaryCoordinate
  funext pair
  simp only [Pi.smul_apply]
  rw [referenceP286HodgeCurvature_apply,
    referenceP286AuxiliaryCoordinate_apply]
  fin_cases pair <;> norm_num [smul_smul]

/-- Raw P286-field form: the production solver, not a stored auxiliary
certificate, returns the actual reference field on every nonzero radial
coframe. -/
theorem generatedP286GaugeConstitutiveAuxiliary_radial_eq_reference
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    generatedP286GaugeConstitutiveAuxiliary
        positiveSmoothUnifiedSource
        (radialCoframe scalar)
        referenceOriginField.gaugeCurvature =
      referenceOriginField.gaugeAuxiliary := by
  funext pair
  apply p286CoordinateEquiv.injective
  simpa [generatedP286GaugeConstitutiveAuxiliary,
    referenceP286CurvatureCoordinate,
    referenceP286AuxiliaryCoordinate] using congrFun
      (positiveSourceP286CanonicalAuxiliary_radial_eq_reference
        scalar nonzero) pair

/-- Positive fixed-curvature branch. -/
theorem generatedP286GaugeConstitutiveAuxiliary_identity_eq_reference :
    generatedP286GaugeConstitutiveAuxiliary
        positiveSmoothUnifiedSource
        (1 : LorentzianCoframe)
        referenceOriginField.gaugeCurvature =
      referenceOriginField.gaugeAuxiliary := by
  simpa [radialCoframe] using
    generatedP286GaugeConstitutiveAuxiliary_radial_eq_reference
      (1 : ℝ) (by norm_num)

/-- Negative fixed-curvature branch.  No branch selector is consumed. -/
theorem generatedP286GaugeConstitutiveAuxiliary_negIdentity_eq_reference :
    generatedP286GaugeConstitutiveAuxiliary
        positiveSmoothUnifiedSource
        (-1 : LorentzianCoframe)
        referenceOriginField.gaugeCurvature =
      referenceOriginField.gaugeAuxiliary := by
  simpa [radialCoframe] using
    generatedP286GaugeConstitutiveAuxiliary_radial_eq_reference
      (-1 : ℝ) (by norm_num)

end

end SaturationMonoid.PhysicsCore.StageNineFixedCurvatureP286CanonicalAuxiliary
