import H0mework.Physics.Constitutive.BlockwiseConstitutive
import H0mework.Realization.Residual.Algebra

/-!
# S9-C3h70a: unique fixed-coframe gravity algebraic keep endpoint

For a fixed coframe `e`, the current strong gravity carrier exposes the
triangular residual pair

`s = B - II+(e)`, `a = F - J B`.

This module solves the scalar keep equations for that pair.  If both residuals
must be multiplied by `1 - sigma`, then the next existing auxiliary and
curvature coordinates are uniquely forced:

`B' = II+(e) + (1-sigma)(B-II+(e))`,

`F' = J B' + (1-sigma)(F-JB)`.

The first formula has the framework affine-relaxation form from `B` toward
`II+(e)`.
The prescribed keep scalar `sigma` is the only scalar input.  No target value,
additional coefficient, branch, source slot, field, shell witness, or
stationarity receipt is supplied.  Uniqueness holds for every `sigma` and
uses only the triangular residual map.

The coframe is deliberately fixed and the multiplier is absent from the
endpoint carrier.  Therefore this classification does not select a coframe or
multiplier, does not claim that the triangular gravity-auxiliary residual is
the complete off-simplicity auxiliary variation, and does not prove an actual
connection, holonomic germ, full residual-section lift, or stationarity.

Here `endpoint` means the unique successor in this algebraic residual chart.
It is unrelated to selected Factor endpoint `11`, and it need not be a
terminal or zero-residual state.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepEndpoint

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive

noncomputable section

set_option autoImplicit false

/-- For a prescribed keep scalar, the unique next auxiliary coordinate forced
by keeping the simplicity residual. -/
def forcedGravityAuxiliaryKeepEndpoint
    (sigma : ℝ)
    (coframe : LorentzianCoframe)
    (auxiliary : PhysicalBivector) : PhysicalBivector :=
  physicalIIPlusBivector coframe +
    (1 - sigma) • (auxiliary - physicalIIPlusBivector coframe)

/-- For a prescribed keep scalar, the unique next curvature coordinate forced
after the auxiliary endpoint has been determined. -/
def forcedGravityCurvatureKeepEndpoint
    (sigma : ℝ)
    (coframe : LorentzianCoframe)
    (curvature auxiliary : PhysicalBivector) : PhysicalBivector :=
  gravityInternalDualEquiv
      (forcedGravityAuxiliaryKeepEndpoint sigma coframe auxiliary) +
    (1 - sigma) •
      (curvature - gravityInternalDualEquiv auxiliary)

/-- The forced auxiliary is exactly the canonical scalar affine state update
from `ResidualTransportCore`; no parallel relaxation law is introduced. -/
theorem forcedGravityAuxiliaryKeepEndpoint_eq_residualTransportUpdate
    (sigma : ℝ)
    (coframe : LorentzianCoframe)
    (auxiliary : PhysicalBivector) :
    forcedGravityAuxiliaryKeepEndpoint sigma coframe auxiliary =
      residualTransportUpdate
        (fun residual : PhysicalBivector =>
          scalarKeepLinearMap (K := ℝ) (E := PhysicalBivector) sigma residual)
        (physicalIIPlusBivector coframe) auxiliary := by
  rw [residualTransportCore_scalar_affine_update]
  unfold forcedGravityAuxiliaryKeepEndpoint
  module

/-- The produced auxiliary has exactly the kept simplicity residual. -/
theorem forcedGravityAuxiliaryKeepEndpoint_residual
    (sigma : ℝ)
    (coframe : LorentzianCoframe)
    (auxiliary : PhysicalBivector) :
    forcedGravityAuxiliaryKeepEndpoint sigma coframe auxiliary -
        physicalIIPlusBivector coframe =
      (1 - sigma) •
        (auxiliary - physicalIIPlusBivector coframe) := by
  unfold forcedGravityAuxiliaryKeepEndpoint
  abel

/-- The produced curvature has exactly the kept triangular auxiliary
residual. -/
theorem forcedGravityCurvatureKeepEndpoint_residual
    (sigma : ℝ)
    (coframe : LorentzianCoframe)
    (curvature auxiliary : PhysicalBivector) :
    forcedGravityCurvatureKeepEndpoint sigma coframe curvature auxiliary -
        gravityInternalDualEquiv
          (forcedGravityAuxiliaryKeepEndpoint sigma coframe auxiliary) =
      (1 - sigma) •
        (curvature - gravityInternalDualEquiv auxiliary) := by
  unfold forcedGravityCurvatureKeepEndpoint
  abel

/-- Fixed-coframe classification: the two keep equations hold exactly for
the forced synchronized endpoint.  No nonzero-scalar premise is needed. -/
theorem candidateGravityKeepResiduals_iff_forcedEndpoint
    (sigma : ℝ)
    (coframe : LorentzianCoframe)
    (curvature auxiliary candidateCurvature candidateAuxiliary :
      PhysicalBivector) :
    (candidateAuxiliary - physicalIIPlusBivector coframe =
        (1 - sigma) •
          (auxiliary - physicalIIPlusBivector coframe) ∧
      candidateCurvature - gravityInternalDualEquiv candidateAuxiliary =
        (1 - sigma) •
          (curvature - gravityInternalDualEquiv auxiliary)) ↔
      candidateAuxiliary =
          forcedGravityAuxiliaryKeepEndpoint sigma coframe auxiliary ∧
        candidateCurvature =
          forcedGravityCurvatureKeepEndpoint sigma coframe curvature
            auxiliary := by
  constructor
  · rintro ⟨auxiliaryResidual, curvatureResidual⟩
    have auxiliaryEquality : candidateAuxiliary =
        forcedGravityAuxiliaryKeepEndpoint sigma coframe auxiliary := by
      unfold forcedGravityAuxiliaryKeepEndpoint
      rw [← auxiliaryResidual]
      abel
    refine ⟨auxiliaryEquality, ?_⟩
    unfold forcedGravityCurvatureKeepEndpoint
    rw [← auxiliaryEquality, ← curvatureResidual]
    abel
  · rintro ⟨rfl, rfl⟩
    exact
      ⟨forcedGravityAuxiliaryKeepEndpoint_residual sigma coframe auxiliary,
        forcedGravityCurvatureKeepEndpoint_residual sigma coframe curvature
          auxiliary⟩

end

end SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepEndpoint
