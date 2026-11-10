import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97UnitChartReturn

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97JointCone
open Polynomial CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedOrderedStatic
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedSchur97Cofactor
open ActualSourcePreparedSchur97RatioTail ActualSourcePreparedSchur97UnitChartReturn
open ActualSourcePreparedN3EMAnalyticPrice ActualSourcePreparedBivariateTailPrice
open ActualSourcePreparedSchur97ClockOrder ActualSourcePreparedSchur97NoetherFraction
open scoped Matrix BigOperators

def spatialUnit (P : ℂ[X]) : ℂ[X] := P /ₘ X^P.natTrailingDegree

private theorem power_quotient (P : ℂ[X]) (m : ℕ) (factor : X^m ∣ P) :
    X^m*(P/ₘX^m) = P := by
  obtain ⟨Q,same⟩ := factor
  rw [same,mul_divByMonic_cancel_left Q (monic_X_pow m)]

private theorem spatial_factor (P : ℂ[X]) :
    X^P.natTrailingDegree * spatialUnit P = P := by
  exact power_quotient P P.natTrailingDegree (X_pow_dvd_iff.mpr
    (fun k low => coeff_eq_zero_of_lt_natTrailingDegree (p:=P) low))

private theorem spatial_origin (P : ℂ[X]) :
    (spatialUnit P).coeff 0 = P.coeff P.natTrailingDegree := by
  have coefficient := congrArg (fun Q : ℂ[X] => Q.coeff P.natTrailingDegree) (spatial_factor P)
  have leading := coeff_X_pow_mul (spatialUnit P) P.natTrailingDegree 0
  simp only [zero_add] at leading
  rw [leading] at coefficient
  exact coefficient

private theorem spatial_value (P : ℂ[X]) (z : ℂ) :
    P.eval z = z^P.natTrailingDegree * (spatialUnit P).eval z := by
  have factor := congrArg (fun Q : ℂ[X] => Q.eval z) (spatial_factor P)
  simpa only [eval_mul,eval_pow,eval_X] using factor.symm

private theorem spatial_ratio (A B : ℂ[X]) (z : ℂ) (away : z ≠ 0) :
    (z^B.natTrailingDegree/z^A.natTrailingDegree)*(A.eval z/B.eval z) =
      (spatialUnit A).eval z/(spatialUnit B).eval z := by
  rw [spatial_value A,spatial_value B,div_mul_div_comm]
  rw [mul_comm (z^B.natTrailingDegree),mul_assoc,
    mul_div_mul_left _ _ (pow_ne_zero _ away),mul_comm _ (z^B.natTrailingDegree),
    mul_div_mul_left _ _ (pow_ne_zero _ away)]

def clockLeading (P : (ℂ[X])[X]) : ℂ[X] := (bivariateClockUnit P).coeff 0

def spatialWeight (A B : (ℂ[X])[X]) (eps : ℝ) : ℂ :=
  (eps : ℂ)^(clockLeading B).natTrailingDegree /
    (eps : ℂ)^(clockLeading A).natTrailingDegree

def jointSpatialRadius (B : (ℂ[X])[X]) : ℝ :=
  min (1/2) (polynomialReadRadius (spatialUnit (clockLeading B)))

def clockRatioSlope (A B : (ℂ[X])[X]) (eps : ℝ) : ℝ :=
  2*(‖(clockLeading B).eval (eps : ℂ)‖*clockTailMass (bivariateClockUnit A) +
    ‖(clockLeading A).eval (eps : ℂ)‖*clockTailMass (bivariateClockUnit B)) /
    ‖(clockLeading B).eval (eps : ℂ)‖^2

/-- The clock cap pays the epsilon-weighted clock error. It is generated
from both original polynomial supports, without a chosen matching scale. -/
def jointClockRadius (A B : (ℂ[X])[X]) (eps : ℝ) : ℝ :=
  min (bivariateRatioRadius (bivariateClockUnit B) eps)
    (‖(eps : ℂ)‖/(1+‖spatialWeight A B eps‖*|clockRatioSlope A B eps|))

private theorem leading_origin (B : (ℂ[X])[X]) (nonzero : B ≠ 0) :
    (spatialUnit (clockLeading B)).coeff 0 ≠ 0 := by
  rw [spatial_origin,clockLeading,bivariate_clock_unit_origin]
  exact coeff_natTrailingDegree_ne_zero.mpr (coeff_natTrailingDegree_ne_zero.mpr nonzero)

private theorem leading_value (B : (ℂ[X])[X]) (nonzero : B ≠ 0)
    (eps : ℝ) (away : (eps : ℂ) ≠ 0)
    (spatial : ‖(eps : ℂ)‖ ≤ jointSpatialRadius B) :
    (clockLeading B).eval (eps : ℂ) ≠ 0 := by
  have origin := leading_origin B nonzero
  have margin := polynomial_read_margin (spatialUnit (clockLeading B)) origin
    (eps : ℂ) (spatial.trans (min_le_right _ _))
  have positive := half_pos (norm_pos_iff.mpr origin)
  have unit_value := norm_pos_iff.mp (positive.trans_le margin)
  rw [spatial_value]
  exact mul_ne_zero (pow_ne_zero _ away) unit_value

theorem joint_spatial_radius_positive (B : (ℂ[X])[X]) (nonzero : B ≠ 0) :
    0 < jointSpatialRadius B := by
  exact lt_min (by norm_num) (polynomial_read_radius_positive _ (leading_origin B nonzero))

theorem joint_clock_radius_positive (A B : (ℂ[X])[X]) (eps : ℝ)
    (nonzero : B ≠ 0) (positive : 0 < eps)
    (spatial : ‖(eps : ℂ)‖ ≤ jointSpatialRadius B) :
    0 < jointClockRadius A B eps := by
  have away := Complex.ofReal_ne_zero.mpr positive.ne'
  have origin := leading_value B nonzero eps away spatial
  have denominator : 0 < 1+‖spatialWeight A B eps‖*|clockRatioSlope A B eps| := by positivity
  exact lt_min (bivariate_ratio_radius_positive _ eps origin)
    (div_pos (norm_pos_iff.mpr away) denominator)

private theorem clock_budget (A B : (ℂ[X])[X]) (eps sigma : ℝ)
    (small : ‖(sigma : ℂ)‖ ≤ jointClockRadius A B eps) :
    ‖spatialWeight A B eps‖*clockRatioSlope A B eps*‖(sigma : ℂ)‖ ≤ ‖(eps : ℂ)‖ := by
  have denominator : 0 < 1+‖spatialWeight A B eps‖*|clockRatioSlope A B eps| := by positivity
  have cap := (le_div_iff₀ denominator).mp (small.trans (min_le_right _ _))
  have slope := mul_le_mul_of_nonneg_left (le_abs_self (clockRatioSlope A B eps))
    (norm_nonneg (spatialWeight A B eps))
  have paid := mul_le_mul_of_nonneg_right slope (norm_nonneg (sigma : ℂ))
  nlinarith [norm_nonneg (sigma : ℂ)]

private theorem join_prices (A B : (ℂ[X])[X]) (eps sigma : ℝ) (read : ℂ)
    (nonzero : B ≠ 0) (away : (eps : ℂ) ≠ 0)
    (spatial : ‖(eps : ℂ)‖ ≤ jointSpatialRadius B)
    (clock : ‖(sigma : ℂ)‖ ≤ jointClockRadius A B eps)
    (price : ‖read-(clockLeading A).eval (eps : ℂ)/(clockLeading B).eval (eps : ℂ)‖ ≤
      clockRatioSlope A B eps*‖(sigma : ℂ)‖) :
    ‖spatialWeight A B eps*read -
      (spatialUnit (clockLeading A)).coeff 0/(spatialUnit (clockLeading B)).coeff 0‖ ≤
      (1+polynomialRatioSlope (spatialUnit (clockLeading A))
        (spatialUnit (clockLeading B)))*‖(eps : ℂ)‖ := by
  have inner := polynomial_ratio_price (spatialUnit (clockLeading A))
    (spatialUnit (clockLeading B)) (leading_origin B nonzero) (eps : ℂ)
    (spatial.trans (min_le_right _ _))
  rw [←spatial_ratio (clockLeading A) (clockLeading B) (eps : ℂ) away] at inner
  have budget : ‖spatialWeight A B eps‖*(clockRatioSlope A B eps*‖(sigma : ℂ)‖) ≤
      ‖(eps : ℂ)‖ := by
    simpa only [mul_assoc] using clock_budget A B eps sigma clock
  have paid := (mul_le_mul_of_nonneg_left price (norm_nonneg (spatialWeight A B eps))).trans budget
  calc
    _ ≤ ‖spatialWeight A B eps*read - spatialWeight A B eps*
        ((clockLeading A).eval (eps : ℂ)/(clockLeading B).eval (eps : ℂ))‖ +
        ‖spatialWeight A B eps*((clockLeading A).eval (eps : ℂ)/
          (clockLeading B).eval (eps : ℂ)) -
          (spatialUnit (clockLeading A)).coeff 0/(spatialUnit (clockLeading B)).coeff 0‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖(eps : ℂ)‖ + polynomialRatioSlope (spatialUnit (clockLeading A))
        (spatialUnit (clockLeading B))*‖(eps : ℂ)‖ := by
      apply add_le_add _ inner
      rw [←mul_sub,norm_mul]
      exact paid
    _ = _ := by ring

attribute [local irreducible] sourceSchur97LiteralNoetherNumerator sourceSchur97Determinant
  sourceClockEval bivariateClockUnit Matrix.det

/-- One original regular seed generates a positive joint source region and
a single epsilon error budget for the complete fraction. All four source
orders remain explicit; this does not identify an unweighted Thomson limit. -/
theorem source_schur97_joint_cone_price (event : DressedEvent) (n : PhysicalMomentum)
    (eps₀ sigma₀ : ℝ) (unit : spatialSquare n = 1) (positive₀ : 0 < eps₀)
    (small₀ : eps₀ ≤ 1/2) (damping₀ : 0 < sigma₀)
    (regular₀ : correctedDet event eps₀ 0 sigma₀ n ≠ 0) :
    let A := sourceSchur97LiteralNoetherNumerator event n
    let B := sourceSchur97Determinant event n
    0 < jointSpatialRadius B ∧
    ∀ eps sigma : ℝ, 0 < eps → eps ≤ jointSpatialRadius B → 0 < sigma →
      ‖(sigma : ℂ)‖ ≤ jointClockRadius A B eps →
      0 < jointClockRadius A B eps ∧ correctedDet event eps 0 sigma n ≠ 0 ∧
      ‖spatialWeight A B eps*
        (((sigma : ℂ)^B.natTrailingDegree/(sigma : ℂ)^A.natTrailingDegree)*
          (sourceClockEval eps sigma A/sourceClockEval eps sigma B)) -
        (spatialUnit (clockLeading A)).coeff 0/(spatialUnit (clockLeading B)).coeff 0‖ ≤
        (1+polynomialRatioSlope (spatialUnit (clockLeading A))
          (spatialUnit (clockLeading B)))*‖(eps : ℂ)‖ := by
  let A := sourceSchur97LiteralNoetherNumerator event n
  let B := sourceSchur97Determinant event n
  have point : sourceClockEval eps₀ sigma₀ B ≠ 0 := by
    simpa only [B,sourceSchur97Determinant] using
      (ActualSourcePreparedSchur97Polynomial.source_schur97_polynomial_original_regular_iff
        event n eps₀ sigma₀ unit positive₀ small₀ damping₀).mpr regular₀
  have nonzero : B ≠ 0 := fun zero => point (by rw [zero,map_zero])
  refine ⟨joint_spatial_radius_positive B nonzero,?_⟩
  intro eps sigma positive spatial damping clock
  have eps_norm : ‖(eps : ℂ)‖ = eps := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  have spatial_norm : ‖(eps : ℂ)‖ ≤ jointSpatialRadius B := by
    simpa only [eps_norm] using spatial
  have half : eps ≤ 1/2 := spatial.trans (min_le_left _ _)
  have origin := leading_value B nonzero eps (Complex.ofReal_ne_zero.mpr positive.ne') spatial_norm
  have unit_clock : ‖(sigma : ℂ)‖ ≤ bivariateRatioRadius (bivariateClockUnit B) eps :=
    clock.trans (min_le_left _ _)
  have original := source_schur97_original_regular_on_unit_radius event n eps sigma unit
    positive half damping origin unit_clock
  have tail := (source_schur97_fraction_joint_tail_price event n eps sigma
    (spatial_norm.trans ((min_le_left _ _).trans (by norm_num)))
    (Complex.ofReal_ne_zero.mpr damping.ne') origin unit_clock).2
  exact ⟨joint_clock_radius_positive A B eps nonzero positive spatial_norm,original,
    join_prices A B eps sigma _ nonzero (Complex.ofReal_ne_zero.mpr positive.ne')
      spatial_norm clock tail⟩

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97JointCone
