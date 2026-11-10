import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchurClockBalance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3EMAnalyticPrice

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 1024
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchurClockPrice
open Polynomial CanonicalGradedSpatialSource ActualDressedFullCoulomb ActualDressedCorrectedGreen
open PreparationVacuumPhysicalCharacteristic
open ActualDressedOrderedStatic ActualDressedNoetherCoulombUnit ActualDressedUniformMaterialCoefficients
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedSchurClockField
open ActualSourcePreparedSchurClockBalance ActualSourcePreparedAuxiliarySchurBalance
open ActualSourcePreparedN3EMChargeRead ActualSourcePreparedN3EMAnalyticPrice
open LowEnergy.ActualDressedVisiblePole
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
attribute [local irreducible] sourceSchurClockDeterminant sourceSchurClockBalanceNumerator

/-- Reduction follows specialization of the complete source balance. The
spatial parameter remains in its own pole order, radius and coefficients. -/
def sourceSchurDampingFraction (event : DressedEvent) (n : PhysicalMomentum) (eps : ℝ) : RatFunc ℂ :=
  readFraction (clockSpecialize eps (sourceSchurClockBalanceNumerator event n))
    (clockSpecialize eps (sourceSchurClockDeterminant event n))

theorem source_schur_damping_read (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ)
    (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    let R := sourceSchurDampingFraction event n eps
    sourceSchurEMBalance event n eps sigma=R.num.eval (sigma : ℂ)/R.denom.eval (sigma : ℂ) := by
  have chart : (clockSpecialize eps (sourceSchurClockDeterminant event n)).eval (sigma : ℂ)≠0 := by
    change sourceClockEval eps sigma (sourceSchurClockDeterminant event n)≠0
    rw [source_schur_clock_determinant_eval]
    exact source_schur_determinant_nonzero event n eps sigma positive regular
  rw [source_schur_clock_balance_fraction]
  exact (reduced_read_at_regular _ _ (sigma : ℂ) chart).symm

private theorem full_principal_price (R : RatFunc ℂ) (z : ℂ) (away : z≠0)
    (small : ‖z‖ ≤ sourceEMAnalyticRadius R) :
    0<sourceEMAnalyticRadius R ∧
    ‖R.num.eval z/R.denom.eval z-(principalNumerator R 0).eval z/z^poleOrder R 0-
      sourceEMAnalyticCenter R‖ ≤ sourceEMAnalyticSlope R*‖z‖ := by
  have price := source_em_analytic_price R z small
  have center : (rootRemainder R 0).coeff 0≠0 := by
    simpa only [←coeff_zero_eq_eval_zero] using root_remainder_nonzero R 0
  have margin := polynomial_read_margin (rootRemainder R 0) center z small
  have remainder : (rootRemainder R 0).eval z≠0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (half_pos (norm_pos_iff.mpr center)) margin)
  have principal := complete_principal_part R 0 z away remainder
  simp only [sub_zero] at principal
  refine ⟨price.1, ?_⟩
  rw [principal]
  simpa only [add_sub_cancel_left] using price.2

/-- Every clock pole of the full driver/background/lower response is retained.
The original source coefficients generate the remaining positive radius and
linear price, without a caller remainder or zero-pole assumption. -/
theorem source_schur_full_clock_principal_price (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0)
    (small : ‖(sigma : ℂ)‖ ≤ sourceEMAnalyticRadius (sourceSchurDampingFraction event n eps)) :
    let R := sourceSchurDampingFraction event n eps
    0<sourceEMAnalyticRadius R ∧
    ‖sourceSchurEMBalance event n eps sigma-(principalNumerator R 0).eval (sigma : ℂ)/
      (sigma : ℂ)^poleOrder R 0-sourceEMAnalyticCenter R‖ ≤ sourceEMAnalyticSlope R*‖(sigma : ℂ)‖ := by
  have away : (sigma : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  have price := full_principal_price (sourceSchurDampingFraction event n eps) (sigma : ℂ) away small
  rw [←source_schur_damping_read event n eps sigma positive regular] at price
  exact price

private theorem scaled_price (b c x p a : ℂ) (budget : ℝ)
    (paid : ‖x-p-a‖ ≤ budget) : ‖b*(c+x)-b*(c+p+a)‖ ≤ ‖b‖*budget := by
  have difference : b*(c+x)-b*(c+p+a)=b*(x-p-a) := by ring
  rw [difference,norm_mul]
  exact mul_le_mul_of_nonneg_left paid (norm_nonneg b)

/-- The unchanged finite Noether coefficient consumes the full principal and
its source remainder price with the original action scale. -/
theorem source_em_full_clock_coefficient_price (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (positive : 0<sigma)
    (regular : correctedDet event e.val 0 sigma n≠0)
    (small : ‖(sigma : ℂ)‖ ≤ sourceEMAnalyticRadius (sourceSchurDampingFraction event n e.val)) :
    let R := sourceSchurDampingFraction event n e.val
    let b := noetherPairScale^2/(2*(lapse : ℂ))
    0<sourceEMAnalyticRadius R ∧
    ‖(e.val : ℂ)^4*sourceN3TemporalEMCoefficient event e.val sigma n-
      b*((3/4 : ℂ)+(principalNumerator R 0).eval (sigma : ℂ)/(sigma : ℂ)^poleOrder R 0+
        sourceEMAnalyticCenter R)‖ ≤ ‖b‖*(sourceEMAnalyticSlope R*‖(sigma : ℂ)‖) := by
  have price := source_schur_full_clock_principal_price event n e.val sigma positive regular small
  refine ⟨price.1, ?_⟩
  rw [source_em_schur_finite_return event e sigma n unit positive regular]
  exact scaled_price _ _ _ _ _ _ price.2

end LowEnergy.GaussComposite.ActualSourcePreparedSchurClockPrice
