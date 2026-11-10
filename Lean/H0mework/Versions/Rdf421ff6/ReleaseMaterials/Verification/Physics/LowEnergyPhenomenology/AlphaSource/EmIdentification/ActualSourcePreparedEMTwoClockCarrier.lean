import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMTemporalFreeReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedClockReducedPencil

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMTwoClockCarrier
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedUniformMaterialCoefficients ActualDressedSylvester
open ActualDressedOrderedStatic ActualDressedZeroDamping ActualDressedUniformClockNonzero
open ActualDressedEMTemporal ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedNoetherPi
open ActualSourcePreparedFourClockCarrier ActualSourcePreparedClockReducedPencil
open ActualSourcePreparedEMTemporalFreeReturn PreparationVacuumActionFieldLift
open scoped Matrix BigOperators
attribute [local irreducible] commonNumerator commonDenominator dressedStaticPolarization

/-- This is the actual temporal EM restriction of the original full numerator,
before either spatial specialization or a clock endpoint is selected. -/
def sourceEMClockNumerator (event : DressedEvent) (n : PhysicalMomentum) (j : Fin 289) :
    (ℂ[X])[X] := staticIRClockSlice
      (∑ i : Fin 289, (MvPolynomial.C (sourceTemporalEMForce i) : Parameters) * commonNumerator event n i j)

def sourceEMTwoClockNumerator (event : DressedEvent) (n : PhysicalMomentum) (j : Fin 289) :
    (ℂ[X])[X] := X^2 * sourceEMClockNumerator event n j

private theorem clock_eval_slice (eps sigma : ℝ) (P : Parameters) :
    sourceClockEval eps sigma (staticIRClockSlice P) = MvPolynomial.eval (irValues eps sigma 0) P := by
  change (clockSpecialize eps (staticIRClockSlice P)).eval (sigma : ℂ) = _
  rw [ir_clock_specialize, damping_slice_eval]

private theorem original_em_clear (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0 < sigma) (j : Fin 289) :
    sourceClockEval eps sigma (sourceFourClockClearing event n) *
      sourcePreparedEMTemporalPi event (eps^2 • n) (sigma : ℂ) j =
      sourceClockEval eps sigma (sourceEMClockNumerator event n j) := by
  unfold sourceEMClockNumerator sourceFourClockClearing sourcePreparedEMTemporalPi
  rw [clock_eval_slice, clock_eval_slice]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have paid : 0 < (sigma : ℂ).re := by simpa only [Complex.ofReal_re] using positive
  rw [source_prepared_pi_actual event (eps^2 • n) (sigma : ℂ) paid]
  rw [mul_left_comm, static_pi_clear event n eps sigma positive i j]

private theorem source_clearing_nonzero (event : DressedEvent) (n : PhysicalMomentum) (eps : ℝ) :
    clockSpecialize eps (sourceFourClockClearing event n) ≠ 0 := by
  have value := actual_common_ir_denominator_nonzero event n eps 1 0 (by norm_num)
  have eval : (clockSpecialize eps (sourceFourClockClearing event n)).eval (1 : ℂ) ≠ 0 := by
    rw [sourceFourClockClearing, ir_clock_specialize]
    have same := damping_slice_eval eps 1 (commonDenominator event n)
    simp only [Complex.ofReal_one] at same
    exact fun zero => value (same.symm.trans zero)
  exact fun zero => eval (by rw [zero, eval_zero])

private theorem source_two_clock_ratio (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0 < sigma) (j : Fin 289) :
    (clockSpecialize eps (sourceEMTwoClockNumerator event n j)).eval (sigma : ℂ) /
      (clockSpecialize eps (sourceFourClockClearing event n)).eval (sigma : ℂ) =
        (sigma : ℂ)^2 * sourcePreparedEMTemporalPi event (eps^2 • n) (sigma : ℂ) j := by
  have clear := original_em_clear event n eps sigma positive j
  have nonzero : sourceClockEval eps sigma (sourceFourClockClearing event n) ≠ 0 := by
    rw [sourceFourClockClearing, clock_eval_slice]
    exact actual_common_ir_denominator_nonzero event n eps sigma 0 positive
  change sourceClockEval eps sigma (sourceEMTwoClockNumerator event n j) /
    sourceClockEval eps sigma (sourceFourClockClearing event n) = _
  simp only [sourceEMTwoClockNumerator, map_mul, map_pow, sourceClockEval, RingHom.comp_apply,
    clockSpecialize, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_evalRingHom, eval_X]
  change (sigma : ℂ)^2 * sourceClockEval eps sigma (sourceEMClockNumerator event n j) /
    sourceClockEval eps sigma (sourceFourClockClearing event n) = _
  rw [← clear]
  field_simp

/-- The actual sigma-two EM price generates its stronger common clock factor
on all original forcing columns before epsilon is specialized. -/
theorem source_em_two_clock_numerator_factor (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) :
    (X : (ℂ[X])[X]) ^ sourceFourClockOrder event n ∣ sourceEMTwoClockNumerator event n j := by
  apply bivariate_bounded_clock_factor _ _ (source_clearing_nonzero event n)
  intro eps
  refine ⟨2 * emTemporalPrice event (eps^2 • n) (fieldUnit j), ?_⟩
  intro sigma positive small
  rw [source_two_clock_ratio event n eps sigma positive j, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  exact source_prepared_em_temporal_pi_two_clock_price event (eps^2 • n) sigma positive small j

def sourceEMTwoClockResponseNumerator (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) : (ℂ[X])[X] :=
  sourceEMTwoClockNumerator event n j /ₘ X ^ sourceFourClockOrder event n

theorem source_em_two_clock_response_factor (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) :
    X ^ sourceFourClockOrder event n * sourceEMTwoClockResponseNumerator event n j =
      sourceEMTwoClockNumerator event n j := by
  obtain ⟨Q, same⟩ := source_em_two_clock_numerator_factor event n j
  unfold sourceEMTwoClockResponseNumerator
  rw [same, mul_divByMonic_cancel_left Q (monic_X_pow _)]

private theorem clock_eval_X (eps sigma : ℝ) :
    sourceClockEval eps sigma (X : (ℂ[X])[X]) = (sigma : ℂ) := by
  simp only [sourceClockEval, RingHom.comp_apply, clockSpecialize,
    Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_evalRingHom, eval_X]

private theorem normalized_clear (c d n D N s response : ℂ) (nonzero : c ≠ 0)
    (den : c*d = D) (num : c*n = s*N) (clear : D*response = N) : d*s*response = n := by
  apply mul_left_cancel₀ nonzero
  calc
    c*(d*s*response) = s*(c*d*response) := by ring
    _ = s*N := by rw [den, clear]
    _ = c*n := num.symm

/-- The original Pi clearing supplies the same Dbar as full K. The stronger
EM quotient now directly returns sigma squared times the actual prepared row. -/
theorem source_em_two_clock_reduced_pi_clear (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0 < sigma) (j : Fin 289) :
    sourceClockEval eps sigma (sourceFourClockDenominator event n) * (sigma : ℂ)^2 *
      sourcePreparedEMTemporalPi event (eps^2 • n) (sigma : ℂ) j =
      sourceClockEval eps sigma (sourceEMTwoClockResponseNumerator event n j) := by
  have den := congrArg (sourceClockEval eps sigma) (source_four_clock_denominator_factor event n)
  have num := congrArg (sourceClockEval eps sigma) (source_em_two_clock_response_factor event n j)
  simp only [map_mul, map_pow, clock_eval_X] at den num
  simp only [sourceEMTwoClockNumerator, map_mul, map_pow, clock_eval_X] at num
  exact normalized_clear _ _ _ _ _ _ _
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr positive.ne')) den num
    (original_em_clear event n eps sigma positive j)

end LowEnergy.GaussComposite.ActualSourcePreparedEMTwoClockCarrier
