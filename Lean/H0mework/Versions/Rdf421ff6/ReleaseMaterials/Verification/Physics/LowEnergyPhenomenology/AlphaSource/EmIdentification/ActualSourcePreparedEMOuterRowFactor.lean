import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMOuterResidue

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMOuterRowFactor
open Polynomial CanonicalGradedSpatialSource ActualDressedFullCoulomb
open ActualSourcePreparedEMClockEquation ActualSourcePreparedEMOuterResidue
open ActualSourcePreparedFourClockCarrier ActualSourcePreparedEMTwoClockCarrier
open scoped Matrix BigOperators

attribute [local irreducible] sourceEMClockReducedRow sourceEMOuterNumerator
  sourceEMOuterOrder sourceFourClockDenominator sourceEMTwoClockResponseNumerator

private theorem reduced_row_view :
    sourceEMClockReducedRow = fun (event : DressedEvent) (n : PhysicalMomentum) (j : Fin 289) =>
      X*sourceFourClockDenominator event n*sourceEMClockJacobiRow n j -
        sourceEMTwoClockResponseNumerator event n j := by
  delta sourceEMClockReducedRow
  rfl

private theorem outer_numerator_view :
    sourceEMOuterNumerator = fun (event : DressedEvent) (n : PhysicalMomentum) (j : Fin 289) =>
      (sourceEMTwoClockResponseNumerator event n j).coeff 0 := by
  delta sourceEMOuterNumerator
  rfl

private theorem constant_row (d j p : (ℂ[X])[X]) :
    (evalRingHom (0 : ℂ[X])) (X*d*j-p) = -p.coeff 0 := by
  simp only [Polynomial.coe_evalRingHom,eval_sub,eval_mul,eval_X,zero_mul,zero_sub,
    coeff_zero_eq_eval_zero]

/-- The reduced source EM row keeps its exact original spatial coefficient:
its outer constant is the negative two-clock numerator, before any Ward
reconstruction or Thomson readout. -/
theorem source_em_outer_row_constant (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) :
    (evalRingHom (0 : ℂ[X])) (sourceEMClockReducedRow event n j) =
      -sourceEMOuterNumerator event n j := by
  rw [reduced_row_view,outer_numerator_view]
  exact constant_row _ _ _

/-- The same prepared-Pi source factorizes every reduced EM row by its
source-generated outer order; all columns and residual numerator data remain.
No zero, matching, or Thomson premise is introduced. -/
theorem source_em_outer_row_factor (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) :
    (evalRingHom (0 : ℂ[X])) (sourceEMClockReducedRow event n j) =
      -(X : ℂ[X])^sourceEMOuterOrder event n *
        (sourceEMOuterNumerator event n j /ₘ X^sourceEMOuterOrder event n) := by
  rw [source_em_outer_row_constant, neg_mul, source_em_outer_finite_numerator]

end LowEnergy.GaussComposite.ActualSourcePreparedEMOuterRowFactor
