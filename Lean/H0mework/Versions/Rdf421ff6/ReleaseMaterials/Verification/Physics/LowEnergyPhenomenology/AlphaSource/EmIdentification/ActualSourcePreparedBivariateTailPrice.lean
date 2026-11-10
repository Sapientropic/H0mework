import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97ClockOrder

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedBivariateTailPrice
open Polynomial ActualSourcePreparedClockReducedPencil ActualSourcePreparedN3EMAnalyticPrice
open ActualSourcePreparedClockReducedPencil
open ActualDressedEMTensorClock LowEnergy.GaussComposite.ActualDressedOrderedStatic
open scoped BigOperators

def coefficientMass (P : ℂ[X]) : ℝ := ‖P.coeff 0‖+polynomialTailPrice P

def clockTailMass (P : (ℂ[X])[X]) : ℝ :=
  ∑ k ∈ (P.erase 0).support, coefficientMass ((P.erase 0).coeff k)

private theorem coefficient_mass_nonnegative (P : ℂ[X]) : 0≤coefficientMass P := by
  unfold coefficientMass polynomialTailPrice
  positivity

private theorem coefficient_mass_price (P : ℂ[X]) (z : ℂ) (small : ‖z‖≤1) :
    ‖P.eval z‖≤coefficientMass P := by
  have tail := polynomial_tail_price P z small
  have budget : 0≤polynomialTailPrice P := by unfold polynomialTailPrice; positivity
  have linear := mul_le_mul_of_nonneg_left small budget
  have triangle := norm_le_norm_sub_add (P.eval z) (P.coeff 0)
  unfold coefficientMass
  linarith

private theorem clock_eval_sum (P : (ℂ[X])[X]) (eps sigma : ℝ) :
    sourceClockEval eps sigma P=
      ∑ k ∈ P.support,(P.coeff k).eval (eps:ℂ)*(sigma:ℂ)^k := by
  change (P.map (Polynomial.evalRingHom (eps:ℂ))).eval (sigma:ℂ)=_
  rw [eval_map,eval₂_eq_sum]
  rfl

/-- Every nonconstant clock coefficient is priced on one unchanged spatial
unit ball; the budget depends only on the original bivariate coefficients. -/
theorem bivariate_clock_tail_price (P : (ℂ[X])[X]) (eps sigma : ℝ)
    (spatial : ‖(eps:ℂ)‖≤1) (clock : ‖(sigma:ℂ)‖≤1) :
    ‖sourceClockEval eps sigma P-(P.coeff 0).eval (eps:ℂ)‖≤
      clockTailMass P*‖(sigma:ℂ)‖ := by
  have split := congrArg (sourceClockEval eps sigma) (monomial_add_erase P 0)
  have constant : sourceClockEval eps sigma (monomial 0 (P.coeff 0))=(P.coeff 0).eval (eps:ℂ) := by
    simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
      Polynomial.map_monomial,Polynomial.coe_evalRingHom,eval_monomial,pow_zero,mul_one]
  rw [map_add,constant] at split
  have difference : sourceClockEval eps sigma P-(P.coeff 0).eval (eps:ℂ)=
      sourceClockEval eps sigma (P.erase 0) := by linear_combination -split
  rw [difference,clock_eval_sum]
  apply (norm_sum_le _ _).trans
  unfold clockTailMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k inside
  have nonzero : k≠0 := by
    rw [support_erase] at inside
    exact (Finset.mem_erase.mp inside).1
  rw [norm_mul,norm_pow]
  exact mul_le_mul (coefficient_mass_price _ _ spatial)
    (pow_le_of_le_one (norm_nonneg (sigma:ℂ)) clock nonzero)
    (pow_nonneg (norm_nonneg (sigma:ℂ)) _)
    (coefficient_mass_nonnegative _)

end LowEnergy.GaussComposite.ActualSourcePreparedBivariateTailPrice
