import H0mework.Physics.Exterior.GravityAuxiliaryVariation

/-!
# S9-C3g0: containment regressions for a simultaneous Stage-9 source

The old affine component is not itself integrable; an identity-flat tail and
the canonical origin curvature cannot satisfy the current fixed gravity shell
without further repair.

This module records four containment regressions: an actual constant-curvature
source component is not integrable on `BasePoint = R^4`, while its undefined
Bochner integral nevertheless reduces to zero;
an identity-coframe point with zero gravity curvature is incompatible with
the current simplicity and gravity-auxiliary equations together; and the
canonical source origin does not match the fixed `gravityInternalDual o II+`
constitutive value.

These are containment diagnostics, not a replacement producer and not a
Stage-9 completion criterion.  In particular, component nonintegrability is
not silently strengthened to failure of the current total-density
integrability predicate, whose off-shell sectors can vanish or cancel.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSimultaneousSourceContainment

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNinePlebanskiMultiplierVariation
open StageNineGravityAuxiliaryVariation
open StageNineBlockwiseConstitutive
open SU7MotherLieAlgebra
open MeasureTheory

/-- The positive affine source has a nonzero constant curvature component,
so that component is not integrable over `BasePoint = R^4`. -/
theorem positive_generatedMotherCurvature_hyperPlus_component_not_integrable :
    ¬ MeasureTheory.Integrable (fun _ : BasePoint =>
      (generatedMotherCurvature positiveSmoothUnifiedSource 0 1).1
        hyperPlusIndex hyperPlusIndex |>.im) := by
  rw [integrable_const_iff]
  rw [positive_generatedMotherCurvature_hyperPlus_entry]
  simp [isFiniteMeasure_iff, Real.pi_ne_zero]

/-- Mathlib assigns zero to this undefined Bochner integral.  This is a
negative regression: the raw equality must never be consumed as a finite
action or stationarity certificate. -/
theorem positive_generatedMotherCurvature_hyperPlus_component_integral_eq_zero :
    (∫ _ : BasePoint,
      ((generatedMotherCurvature positiveSmoothUnifiedSource 0 1).1
        hyperPlusIndex hyperPlusIndex).im) = 0 := by
  exact integral_undef
    positive_generatedMotherCurvature_hyperPlus_component_not_integrable

/-- A flat identity-coframe point cannot satisfy both the generated
simplicity equation and the gravity auxiliary equation. -/
theorem identityCoframe_zeroGravityCurvature_rejects_fullGravityShell
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint)
    (coframeIdentity : configuration.coframe point = 1)
    (curvatureZero : holonomicGravityCurvature configuration point = 0) :
    ¬ (GravitySimplicityEquation configuration ∧
      GravityAuxiliaryEquation configuration) := by
  rintro ⟨simplicity, auxiliary⟩
  have shell := auxiliary point
  rw [curvatureZero, simplicity point, coframeIdentity] at shell
  have bivectorZero :
      physicalIIPlusBivector (1 : LorentzianCoframe) = 0 := by
    apply gravityInternalDualEquiv.injective
    simpa using shell.symm
  exact physicalIIPlusBivector_not_zero bivectorZero

/-- The canonical source curvature at the origin does not satisfy the fixed
`gravityInternalDual o II+` constitutive value used by the current Stage-9
gravity auxiliary equation.  No source-to-holonomic-curvature bridge is
asserted here. -/
theorem canonicalPhysicalSource_origin_curvature_ne_gravityDualIIPlus :
    canonicalPhysicalSource.lorentzCurvatureAtOrigin 0 0 ≠
      gravityInternalDualEquiv
        (physicalIIPlusBivector
          (canonicalPhysicalSource.coframeAt 0)) 0 0 := by
  rw [canonicalPhysicalSource.coframeAt_zero]
  have sourceCurvature :
      canonicalPhysicalSource.lorentzCurvatureAtOrigin 0 0 =
        (1 / 4 : ℝ) := by
    simp [Source.lorentzCurvatureAtOrigin, pairFirst, pairSecond,
      minkowskiInternalSign, canonicalPhysicalSource_curvature_component]
  rw [sourceCurvature]
  change (1 / 4 : ℝ) ≠
    gravityInternalDualLinear
      (gravityInternalDualLinear
        (coframeWedge (1 : LorentzianCoframe))) 0 0
  rw [gravityInternalDualLinear_square]
  norm_num [coframeWedge, pairFirst, pairSecond, Matrix.one_apply]

end SaturationMonoid.PhysicsCore.StageNineSimultaneousSourceContainment
