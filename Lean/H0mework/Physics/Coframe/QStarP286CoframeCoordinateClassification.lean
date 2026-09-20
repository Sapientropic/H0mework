import H0mework.Physics.Matter.QStarP286MatterProjectionTransport

/-!
# S9-C3h61: coordinate classification of the q-star/P286 coframe obligation

The remaining coframe transport law compares two continuous linear
functionals on the sixteen-dimensional coframe variation space.  This module
replaces the unexpanded functional equality by its exact sixteen coordinate
projections.  It does not solve any projection, accept a coframe receipt, or
claim that the current endpoint is stationary.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineQStarP286CoframeCoordinateClassification

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineJointShellResidualCarrier
open StageNineQStarP286JointProjectionTransport
open StageNineQStarP286MatterProjectionTransport

noncomputable section

set_option autoImplicit false

/-- One of the sixteen canonical coframe variation directions. -/
def coframeCoordinateVariation (row column : Fin 4) : LorentzianCoframe :=
  Matrix.single row column (1 : ℝ)

theorem coframe_eq_sum_coordinateVariations (coframe : LorentzianCoframe) :
    coframe =
      ∑ row : Fin 4, ∑ column : Fin 4,
        coframe row column • coframeCoordinateVariation row column := by
  calc
    coframe =
        ∑ row : Fin 4, ∑ column : Fin 4,
          Matrix.single row column (coframe row column) :=
      Matrix.matrix_eq_sum_single coframe
    _ = ∑ row : Fin 4, ∑ column : Fin 4,
          coframe row column • coframeCoordinateVariation row column := by
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro column _
      unfold coframeCoordinateVariation
      rw [Matrix.smul_single]
      simp

/-- Equality of coframe Euler covectors is exactly equality on all sixteen
canonical coordinate variations. -/
theorem coframeCovector_eq_iff_coordinateVariations
    (first second : LorentzianCoframe →L[ℝ] ℝ) :
    first = second ↔
      ∀ row column : Fin 4,
        first (coframeCoordinateVariation row column) =
          second (coframeCoordinateVariation row column) := by
  constructor
  · intro equality row column
    rw [equality]
  · intro coordinateEquality
    apply ContinuousLinearMap.ext
    intro coframe
    rw [coframe_eq_sum_coordinateVariations coframe]
    simp_rw [map_sum, map_smul, coordinateEquality]

/-- Exact finite classification of the only C3h57--C3h60 projection still
open.  The right-hand side contains no supplied target or branch witness: it
only evaluates the actual endpoint and source residuals on a basis. -/
theorem qStarP286CoframeTransportObligation_iff_coordinateVariations :
    QStarP286CoframeTransportObligation ↔
      ∀ row column : Fin 4,
        qStarP286EndpointResidual.eulerLagrange.coframe
            (coframeCoordinateVariation row column) =
          ((1 - positiveSmoothUnifiedSource.legacy.sigma) •
            qStarP286SourceResidual.eulerLagrange.coframe)
              (coframeCoordinateVariation row column) := by
  unfold QStarP286CoframeTransportObligation
  exact coframeCovector_eq_iff_coordinateVariations _ _

end

end SaturationMonoid.PhysicsCore.StageNineQStarP286CoframeCoordinateClassification
