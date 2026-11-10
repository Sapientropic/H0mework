import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97JointTail

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97RatioTail
open Polynomial CanonicalGradedSpatialSource ActualSourcePreparedClockReducedPencil
open PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb
open ActualSourcePreparedN3EMAnalyticPrice
open ActualSourcePreparedBivariateTailPrice ActualSourcePreparedSchur97JointTail
open ActualSourcePreparedSchur97Cofactor ActualSourcePreparedSchur97Polynomial
open ActualSourcePreparedN3EMChargeRead ActualSourcePreparedSchur97NoetherFraction
open ActualDressedOrderedStatic ActualDressedNoetherCoulombUnit ActualDressedCorrectedGreen
open ActualDressedEMTensorClock
open ActualDressedUniformMaterialCoefficients ActualSourcePreparedAuxiliaryClockReduction
open Filter Set
open scoped Topology Matrix
open scoped BigOperators

/-- A source-native ratio price for the joint clock tail.  The denominator
margin is paid on the source principal coefficient; no coordinate limit or
experimental value is smuggled into this read. -/
theorem bivariate_ratio_tail_price (A B : (ℂ[X])[X]) (eps sigma : ℝ)
    (spatial : ‖(eps : ℂ)‖ ≤ 1) (clock : ‖(sigma : ℂ)‖ ≤ 1)
    (bzero : ((B.coeff 0).eval (eps : ℂ)) ≠ 0)
    (margin_budget : clockTailMass B * ‖(sigma : ℂ)‖ ≤
      ‖(B.coeff 0).eval (eps : ℂ)‖ / 2) :
    ‖sourceClockEval eps sigma A / sourceClockEval eps sigma B -
      (A.coeff 0).eval (eps : ℂ) / (B.coeff 0).eval (eps : ℂ)‖ ≤
      (2 * (‖(B.coeff 0).eval (eps : ℂ)‖ * clockTailMass A +
        ‖(A.coeff 0).eval (eps : ℂ)‖ * clockTailMass B) /
        ‖(B.coeff 0).eval (eps : ℂ)‖ ^ 2) * ‖(sigma : ℂ)‖ := by
  let a₀ : ℂ := (A.coeff 0).eval (eps : ℂ)
  let b₀ : ℂ := (B.coeff 0).eval (eps : ℂ)
  let aσ : ℂ := sourceClockEval eps sigma A
  let bσ : ℂ := sourceClockEval eps sigma B
  have aError : ‖aσ - a₀‖ ≤ clockTailMass A * ‖(sigma : ℂ)‖ := by
    exact bivariate_clock_tail_price A eps sigma spatial clock
  have bError : ‖bσ - b₀‖ ≤ clockTailMass B * ‖(sigma : ℂ)‖ := by
    exact bivariate_clock_tail_price B eps sigma spatial clock
  have bzero' : b₀ ≠ 0 := by simpa [b₀] using bzero
  have margin : ‖b₀‖ / 2 ≤ ‖bσ‖ := by
    have reverse := norm_sub_norm_le b₀ bσ
    rw [norm_sub_rev] at reverse
    have paid : ‖bσ - b₀‖ ≤ ‖b₀‖ / 2 := by
      exact bError.trans margin_budget
    linarith
  have value : bσ ≠ 0 := by
    exact norm_pos_iff.mp (lt_of_lt_of_le (half_pos (norm_pos_iff.mpr bzero')) margin)
  have split : aσ / bσ - a₀ / b₀ =
      ((aσ - a₀) * b₀ + a₀ * (b₀ - bσ)) / (bσ * b₀) := by
    field_simp [bzero', value]
    ring
  have numerator : ‖(aσ - a₀) * b₀ + a₀ * (b₀ - bσ)‖ ≤
      (‖b₀‖ * clockTailMass A + ‖a₀‖ * clockTailMass B) * ‖(sigma : ℂ)‖ := by
    have aPaid := mul_le_mul_of_nonneg_right aError (norm_nonneg b₀)
    have bPaid := mul_le_mul_of_nonneg_left bError (norm_nonneg a₀)
    calc
      _ ≤ ‖(aσ - a₀) * b₀‖ + ‖a₀ * (b₀ - bσ)‖ := norm_add_le _ _
      _ = ‖aσ - a₀‖ * ‖b₀‖ + ‖a₀‖ * ‖bσ - b₀‖ := by
        rw [norm_mul, norm_mul, norm_sub_rev b₀ bσ]
      _ ≤ clockTailMass A * ‖(sigma : ℂ)‖ * ‖b₀‖ +
          ‖a₀‖ * (clockTailMass B * ‖(sigma : ℂ)‖) := add_le_add aPaid bPaid
      _ = (‖b₀‖ * clockTailMass A + ‖a₀‖ * clockTailMass B) * ‖(sigma : ℂ)‖ := by ring
  have denominator : ‖b₀‖ ^ 2 / 2 ≤ ‖bσ‖ * ‖b₀‖ := by
    have paid := mul_le_mul_of_nonneg_right margin (norm_nonneg b₀)
    nlinarith
  have lower : 0 < ‖b₀‖ ^ 2 / 2 := by positivity
  have budgets : 0 ≤
      (‖b₀‖ * clockTailMass A + ‖a₀‖ * clockTailMass B) * ‖(sigma : ℂ)‖ := by
    have aBudget : 0 ≤ clockTailMass A := by
      have coefficient_budget (P : ℂ[X]) : 0 ≤ coefficientMass P := by
        unfold coefficientMass polynomialTailPrice
        positivity
      unfold clockTailMass
      exact Finset.sum_nonneg (fun _ _ => coefficient_budget _)
    have bBudget : 0 ≤ clockTailMass B := by
      have coefficient_budget (P : ℂ[X]) : 0 ≤ coefficientMass P := by
        unfold coefficientMass polynomialTailPrice
        positivity
      unfold clockTailMass
      exact Finset.sum_nonneg (fun _ _ => coefficient_budget _)
    positivity
  rw [split, norm_div, norm_mul]
  calc
    _ ≤ ((‖b₀‖ * clockTailMass A + ‖a₀‖ * clockTailMass B) *
        ‖(sigma : ℂ)‖) / (‖bσ‖ * ‖b₀‖) :=
      div_le_div_of_nonneg_right numerator (by positivity)
    _ ≤ ((‖b₀‖ * clockTailMass A + ‖a₀‖ * clockTailMass B) *
        ‖(sigma : ℂ)‖) / (‖b₀‖ ^ 2 / 2) :=
      div_le_div_of_nonneg_left budgets lower denominator
    _ = _ := by simp [a₀, b₀]; ring

private theorem tail_mass_nonnegative (P : (ℂ[X])[X]) : 0 ≤ clockTailMass P := by
  unfold clockTailMass
  apply Finset.sum_nonneg
  intro k _
  unfold coefficientMass polynomialTailPrice
  positivity

def bivariateRatioRadius (B : (ℂ[X])[X]) (eps : ℝ) : ℝ :=
  min 1 (‖(B.coeff 0).eval (eps : ℂ)‖ / (2 * (1 + clockTailMass B)))

theorem bivariate_ratio_radius_positive (B : (ℂ[X])[X]) (eps : ℝ)
    (origin : (B.coeff 0).eval (eps : ℂ) ≠ 0) :
    0 < bivariateRatioRadius B eps := by
  have mass := tail_mass_nonnegative B
  exact lt_min (by norm_num) (div_pos (norm_pos_iff.mpr origin) (by positivity))

private theorem radius_budget (B : (ℂ[X])[X]) (eps sigma : ℝ)
    (small : ‖(sigma : ℂ)‖ ≤ bivariateRatioRadius B eps) :
    clockTailMass B * ‖(sigma : ℂ)‖ ≤ ‖(B.coeff 0).eval (eps : ℂ)‖ / 2 := by
  have mass := tail_mass_nonnegative B
  have denominator : 0 < 2 * (1 + clockTailMass B) := by positivity
  have cap := (le_div_iff₀ denominator).mp
    (small.trans (min_le_right _ _))
  nlinarith [norm_nonneg (sigma : ℂ)]

def bivariateClockUnit (P : (ℂ[X])[X]) : (ℂ[X])[X] :=
  P /ₘ X ^ P.natTrailingDegree

private theorem power_quotient (P : (ℂ[X])[X]) (m : ℕ) (factor : X^m ∣ P) :
    X^m * (P /ₘ X^m) = P := by
  obtain ⟨Q, same⟩ := factor
  rw [same, mul_divByMonic_cancel_left Q (monic_X_pow m)]

theorem bivariate_clock_unit_factor (P : (ℂ[X])[X]) :
    X ^ P.natTrailingDegree * bivariateClockUnit P = P := by
  exact power_quotient P P.natTrailingDegree (X_pow_dvd_iff.mpr
    (fun k low => coeff_eq_zero_of_lt_natTrailingDegree (p := P) low))

theorem bivariate_clock_unit_origin (P : (ℂ[X])[X]) :
    (bivariateClockUnit P).coeff 0 = P.coeff P.natTrailingDegree := by
  have coefficient := congrArg (fun Q : (ℂ[X])[X] => Q.coeff P.natTrailingDegree)
    (bivariate_clock_unit_factor P)
  have leading := coeff_X_pow_mul (bivariateClockUnit P) P.natTrailingDegree 0
  simp only [zero_add] at leading
  rw [leading] at coefficient
  exact coefficient

private theorem unit_eval (P : (ℂ[X])[X]) (eps sigma : ℝ) :
    sourceClockEval eps sigma P = (sigma : ℂ)^P.natTrailingDegree *
      sourceClockEval eps sigma (bivariateClockUnit P) := by
  have factor := congrArg (sourceClockEval eps sigma) (bivariate_clock_unit_factor P)
  have clock : sourceClockEval eps sigma (X : (ℂ[X])[X]) = (sigma : ℂ) := by
    simp only [sourceClockEval, RingHom.comp_apply, clockSpecialize,
      Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_evalRingHom, eval_X]
  simpa only [map_mul, map_pow, clock] using factor.symm

private theorem normalized_fraction (A B : (ℂ[X])[X]) (eps sigma : ℝ)
    (away : (sigma : ℂ) ≠ 0) :
    ((sigma : ℂ)^B.natTrailingDegree / (sigma : ℂ)^A.natTrailingDegree) *
      (sourceClockEval eps sigma A / sourceClockEval eps sigma B) =
      sourceClockEval eps sigma (bivariateClockUnit A) /
        sourceClockEval eps sigma (bivariateClockUnit B) := by
  rw [unit_eval A, unit_eval B, div_mul_div_comm]
  rw [mul_comm ((sigma : ℂ)^B.natTrailingDegree), mul_assoc,
    mul_div_mul_left _ _ (pow_ne_zero _ away), mul_comm _ ((sigma : ℂ)^B.natTrailingDegree),
    mul_div_mul_left _ _ (pow_ne_zero _ away)]

private theorem normalized_read_price (A B : (ℂ[X])[X]) (eps sigma : ℝ) (x : ℂ)
    (spatial : ‖(eps : ℂ)‖ ≤ 1) (away : (sigma : ℂ) ≠ 0)
    (read : x = sourceClockEval eps sigma A / sourceClockEval eps sigma B)
    (origin : ((bivariateClockUnit B).coeff 0).eval (eps : ℂ) ≠ 0)
    (clock : ‖(sigma : ℂ)‖ ≤ bivariateRatioRadius (bivariateClockUnit B) eps) :
    let AU := bivariateClockUnit A
    let BU := bivariateClockUnit B
    0 < bivariateRatioRadius BU eps ∧
    ‖((sigma : ℂ)^B.natTrailingDegree / (sigma : ℂ)^A.natTrailingDegree) * x -
      (AU.coeff 0).eval (eps : ℂ) / (BU.coeff 0).eval (eps : ℂ)‖ ≤
      (2 * (‖(BU.coeff 0).eval (eps : ℂ)‖ * clockTailMass AU +
        ‖(AU.coeff 0).eval (eps : ℂ)‖ * clockTailMass BU) /
        ‖(BU.coeff 0).eval (eps : ℂ)‖^2) * ‖(sigma : ℂ)‖ := by
  have clock_unit : ‖(sigma : ℂ)‖ ≤ 1 := clock.trans (min_le_left _ _)
  refine ⟨bivariate_ratio_radius_positive (bivariateClockUnit B) eps origin, ?_⟩
  rw [read, normalized_fraction A B eps sigma away]
  exact bivariate_ratio_tail_price (bivariateClockUnit A) (bivariateClockUnit B)
    eps sigma spatial clock_unit origin (radius_budget (bivariateClockUnit B) eps sigma clock)

attribute [local irreducible] Matrix.det Matrix.adjugate Matrix.mulVec
  sourceSchur97Polynomial sourceSchur97Force sourceClockEval
  sourceAuxiliaryClockFactor nativeClockDenominator dotProduct

/-- The exact literal numerator emitted by the original actual Noether
fraction.  This preserves its polynomial multiplication representation. -/
def sourceSchur97LiteralNoetherNumerator (event : DressedEvent) (n : PhysicalMomentum) :
    (ℂ[X])[X] :=
  (C (C (noetherPairScale^2)) * (C (X : ℂ[X]))^4) *
    ((sourceAuxiliaryClockFactor event n * nativeClockDenominator n) *
      dotProduct sourceSchur97Force
        ((sourceSchur97Polynomial event n).adjugate *ᵥ sourceSchur97Force))

attribute [local irreducible] sourceSchur97LiteralNoetherNumerator sourceSchur97Determinant
  bivariateClockUnit sourceN3TemporalEMCoefficient

/-- One original regular point generates the spatial puncture on which the
normalized determinant has a nonzero origin and its own positive clock radius. -/
theorem source_schur97_unit_spatial_chart (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n = 1) (positive : 0 < eps)
    (small : eps ≤ 1/2) (damping : 0 < sigma)
    (regular : correctedDet event eps 0 sigma n ≠ 0) :
    ∀ᶠ spatial : ℝ in 𝓝[>] 0,
      ((bivariateClockUnit (sourceSchur97Determinant event n)).coeff 0).eval
        (spatial : ℂ) ≠ 0 ∧
      0 < bivariateRatioRadius (bivariateClockUnit (sourceSchur97Determinant event n)) spatial := by
  have point : sourceClockEval eps sigma (sourceSchur97Determinant event n) ≠ 0 := by
    simpa only [sourceSchur97Determinant] using
      (source_schur97_polynomial_original_regular_iff event n eps sigma unit positive small damping).mpr regular
  have nonzero : sourceSchur97Determinant event n ≠ 0 := by
    intro zero
    apply point
    rw [zero, map_zero]
  have coefficient : (bivariateClockUnit (sourceSchur97Determinant event n)).coeff 0 ≠ 0 := by
    rw [bivariate_clock_unit_origin]
    exact coeff_natTrailingDegree_ne_zero.mpr nonzero
  have inclusion : Ioi (0 : ℝ) ⊆ {0}ᶜ := fun x positive => by simpa using positive.ne'
  have chart := (source_static_punctured_chart _ coefficient).filter_mono
    (nhdsWithin_mono 0 inclusion)
  filter_upwards [chart] with spatial origin
  exact ⟨origin, bivariate_ratio_radius_positive _ _ origin⟩

/-- The full source fraction keeps both actual clock orders and obtains a
principal coefficient with a budget on its generated unit-denominator chart. -/
theorem source_schur97_fraction_joint_tail_price (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (spatial : ‖(eps : ℂ)‖ ≤ 1) (away : (sigma : ℂ) ≠ 0)
    (origin : ((bivariateClockUnit (sourceSchur97Determinant event n)).coeff 0).eval
      (eps : ℂ) ≠ 0)
    (clock : ‖(sigma : ℂ)‖ ≤
      bivariateRatioRadius (bivariateClockUnit (sourceSchur97Determinant event n)) eps) :
    let A := bivariateClockUnit (sourceSchur97LiteralNoetherNumerator event n)
    let B := bivariateClockUnit (sourceSchur97Determinant event n)
    0 < bivariateRatioRadius B eps ∧
    ‖((sigma : ℂ)^(sourceSchur97Determinant event n).natTrailingDegree /
        (sigma : ℂ)^(sourceSchur97LiteralNoetherNumerator event n).natTrailingDegree) *
      (sourceClockEval eps sigma (sourceSchur97LiteralNoetherNumerator event n) /
        sourceClockEval eps sigma (sourceSchur97Determinant event n)) -
      (A.coeff 0).eval (eps : ℂ) / (B.coeff 0).eval (eps : ℂ)‖ ≤
      (2 * (‖(B.coeff 0).eval (eps : ℂ)‖ * clockTailMass A +
        ‖(A.coeff 0).eval (eps : ℂ)‖ * clockTailMass B) /
        ‖(B.coeff 0).eval (eps : ℂ)‖^2) * ‖(sigma : ℂ)‖ := by
  exact normalized_read_price (sourceSchur97LiteralNoetherNumerator event n)
    (sourceSchur97Determinant event n) eps sigma
    (sourceClockEval eps sigma (sourceSchur97LiteralNoetherNumerator event n) /
      sourceClockEval eps sigma (sourceSchur97Determinant event n))
    spatial away rfl origin clock

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97RatioTail
