import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97RatioTail

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97UnitChartReturn
open Polynomial CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedOrderedStatic
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedSchur97Polynomial
open ActualSourcePreparedSchur97Cofactor ActualSourcePreparedSchur97RatioTail
open ActualSourcePreparedBivariateTailPrice ActualSourcePreparedN3EMAnalyticPrice
open ActualSourcePreparedSchur97NoetherFraction ActualSourcePreparedN3EMChargeRead
open ActualDressedNoetherCoulombUnit ActualSourcePreparedAuxiliaryClockReduction
open scoped Matrix BigOperators

private theorem mass_nonnegative (P : (ℂ[X])[X]) : 0 ≤ clockTailMass P := by
  unfold clockTailMass
  apply Finset.sum_nonneg
  intro k _
  unfold coefficientMass polynomialTailPrice
  positivity

private theorem unit_value_nonzero (P : (ℂ[X])[X]) (eps sigma : ℝ)
    (spatial : ‖(eps : ℂ)‖ ≤ 1) (origin : (P.coeff 0).eval (eps : ℂ) ≠ 0)
    (clock : ‖(sigma : ℂ)‖ ≤ bivariateRatioRadius P eps) :
    sourceClockEval eps sigma P ≠ 0 := by
  have mass := mass_nonnegative P
  have denominator : 0 < 2*(1+clockTailMass P) := by positivity
  have cap := (le_div_iff₀ denominator).mp (clock.trans (min_le_right _ _))
  have budget : clockTailMass P*‖(sigma : ℂ)‖ ≤ ‖(P.coeff 0).eval (eps : ℂ)‖/2 := by
    nlinarith [norm_nonneg (sigma : ℂ)]
  have tail := (bivariate_clock_tail_price P eps sigma spatial
    (clock.trans (min_le_left _ _))).trans budget
  have reverse := norm_sub_norm_le ((P.coeff 0).eval (eps : ℂ)) (sourceClockEval eps sigma P)
  rw [norm_sub_rev] at reverse
  have center := norm_pos_iff.mpr origin
  have margin : 0 < ‖sourceClockEval eps sigma P‖ := by linarith
  exact norm_pos_iff.mp margin

private theorem raw_value_nonzero (P : (ℂ[X])[X]) (eps sigma : ℝ)
    (away : (sigma : ℂ) ≠ 0)
    (unit_value : sourceClockEval eps sigma (bivariateClockUnit P) ≠ 0) :
    sourceClockEval eps sigma P ≠ 0 := by
  have factor := congrArg (sourceClockEval eps sigma) (bivariate_clock_unit_factor P)
  have clock : sourceClockEval eps sigma (X : (ℂ[X])[X]) = (sigma : ℂ) := by
    simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
      Polynomial.map_X,Polynomial.coe_evalRingHom,eval_X]
  simp only [map_mul,map_pow,clock] at factor
  exact factor ▸ mul_ne_zero (pow_ne_zero _ away) unit_value

attribute [local irreducible] bivariateClockUnit sourceSchur97Determinant
  sourceSchur97Polynomial Matrix.det sourceClockEval

/-- The source unit radius now supplies the original full289 Green chart,
instead of taking that regularity as an additional owner return. -/
theorem source_schur97_original_regular_on_unit_radius (event : DressedEvent)
    (n : PhysicalMomentum) (eps sigma : ℝ) (unit : spatialSquare n = 1)
    (positive : 0 < eps) (small : eps ≤ 1/2) (damping : 0 < sigma)
    (origin : ((bivariateClockUnit (sourceSchur97Determinant event n)).coeff 0).eval
      (eps : ℂ) ≠ 0)
    (clock : ‖(sigma : ℂ)‖ ≤
      bivariateRatioRadius (bivariateClockUnit (sourceSchur97Determinant event n)) eps) :
    correctedDet event eps 0 sigma n ≠ 0 := by
  have spatial : ‖(eps : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
    linarith
  have normalized := unit_value_nonzero
    (bivariateClockUnit (sourceSchur97Determinant event n)) eps sigma spatial origin clock
  have raw := raw_value_nonzero (sourceSchur97Determinant event n) eps sigma
    (Complex.ofReal_ne_zero.mpr damping.ne') normalized
  apply (source_schur97_polynomial_original_regular_iff event n eps sigma unit positive small damping).mp
  simpa only [sourceSchur97Determinant] using raw

/-- The unchanged actual Noether reader now consumes the source-generated
unit-radius chart directly. All numerator weights remain literal. -/
theorem source_schur97_noether_on_unit_radius (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum) (sigma : ℝ) (unit : spatialSquare n = 1)
    (positive : 0 < e.val) (small : e.val ≤ 1/2) (damping : 0 < sigma)
    (origin : ((bivariateClockUnit (sourceSchur97Determinant event n)).coeff 0).eval
      (e.val : ℂ) ≠ 0)
    (clock : ‖(sigma : ℂ)‖ ≤
      bivariateRatioRadius (bivariateClockUnit (sourceSchur97Determinant event n)) e.val) :
    (e.val : ℂ)^4 * sourceN3TemporalEMCoefficient event e.val sigma n =
      sourceClockEval e.val sigma ((C (C (noetherPairScale^2)) * (C (X : ℂ[X]))^4) *
        ((sourceAuxiliaryClockFactor event n * nativeClockDenominator n) *
          dotProduct sourceSchur97Force
            ((sourceSchur97Polynomial event n).adjugate *ᵥ sourceSchur97Force)))/
        sourceClockEval e.val sigma (sourceSchur97Determinant event n) := by
  exact source_schur97_noether_fraction event e n sigma unit positive small damping
    (source_schur97_original_regular_on_unit_radius event n e.val sigma unit positive small
      damping origin clock)

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97UnitChartReturn
