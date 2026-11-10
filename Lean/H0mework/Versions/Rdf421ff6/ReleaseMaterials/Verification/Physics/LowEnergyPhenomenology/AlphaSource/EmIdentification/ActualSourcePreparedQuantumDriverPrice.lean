import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedQuantumDriverCofactor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3EMAnalyticPrice

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedQuantumDriverPrice
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumMixedPrincipal
open PreparationVacuumPhysicalCharacteristic PreparationVacuumFullOriginResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumStaticPoleResponse
open PreparationPhysicalStaticSpatialCouplingReturn
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedNoetherCoulombUnit
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator ActualDressedZeroDamping
open ActualSourcePreparedN3EMAnalyticPrice ActualSourcePreparedN3EMChargeRead
open ActualSourcePreparedN3MovingResponse ActualSourcePreparedTemporalQuantumRead
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalQuantumIR ActualSourcePreparedQuantumDriverCofactor
open LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators Matrix.Norms.Operator

/-- All clock poles stay in the exact finite principal polynomial. The source
root remainder supplies the radius, analytic center and linear tail price. -/
def rationalReaderBudget (R : RatFunc ℂ) (z : ℂ) : ℝ :=
  ‖(principalNumerator R 0).eval z/z^poleOrder R 0‖ +
    ‖sourceEMAnalyticCenter R‖ + sourceEMAnalyticSlope R * ‖z‖

theorem rational_read_budget (R : RatFunc ℂ) (z : ℂ) (away : z ≠ 0)
    (small : ‖z‖ ≤ sourceEMAnalyticRadius R) :
    ‖R.num.eval z/R.denom.eval z‖ ≤ rationalReaderBudget R z := by
  have price := source_em_analytic_price R z small
  have center : (rootRemainder R 0).coeff 0 ≠ 0 := by
    simpa only [←Polynomial.coeff_zero_eq_eval_zero] using root_remainder_nonzero R 0
  have margin := polynomial_read_margin (rootRemainder R 0) center z small
  have regular : (rootRemainder R 0).eval z ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (half_pos (norm_pos_iff.mpr center)) margin)
  have principal := complete_principal_part R 0 z away regular
  simp only [sub_zero] at principal
  rw [principal]
  unfold rationalReaderBudget
  have analytic := norm_add_le
    ((analyticNumerator R 0).eval z/(rootRemainder R 0).eval z-sourceEMAnalyticCenter R)
    (sourceEMAnalyticCenter R)
  rw [sub_add_cancel] at analytic
  calc
    _ ≤ ‖(principalNumerator R 0).eval z/z^poleOrder R 0‖ +
      ‖(analyticNumerator R 0).eval z/(rootRemainder R 0).eval z‖ := norm_add_le _ _
    _ ≤ ‖(principalNumerator R 0).eval z/z^poleOrder R 0‖ +
      (sourceEMAnalyticSlope R * ‖z‖ + ‖sourceEMAnalyticCenter R‖) :=
        add_le_add le_rfl (analytic.trans (add_le_add price.2 le_rfl))
    _ = _ := by ring

def sourceQuantumNativeReaderBudget (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius) : ℝ :=
  ∑ i, rationalReaderBudget (sourceQuantumNativeReaderFraction event e n unit small i) (sigma : ℂ)

def sourceQuantumNativeReaderRadius (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i => sourceEMAnalyticRadius (sourceQuantumNativeReaderFraction event e n unit small i))

theorem source_quantum_native_reader_radius_positive (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius) :
    0 < sourceQuantumNativeReaderRadius event e n unit small := by
  apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
  intro i _
  apply polynomial_read_radius_positive
  simpa only [←Polynomial.coeff_zero_eq_eval_zero] using
    root_remainder_nonzero (sourceQuantumNativeReaderFraction event e n unit small i) 0

private theorem reader_radius_le (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius) (i : Fin 289) :
    sourceQuantumNativeReaderRadius event e n unit small ≤
      sourceEMAnalyticRadius (sourceQuantumNativeReaderFraction event e n unit small i) :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- This prices the actual driver reader, including all 289 components, without
a uniform-in-epsilon premise or a vanishing clock pole assumption. -/
theorem source_quantum_native_reader_budget (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (chart : (dampingDeterminant event e.val n).eval (sigma : ℂ) ≠ 0)
    (radius : ‖(sigma : ℂ)‖ ≤ sourceQuantumNativeReaderRadius event e n unit small) :
    ‖sourceSpatialStaticSourceReader n unit ⟨e.val^2, pow_pos e.property.1 2, small⟩
      (sourceTemporalActualQuantumDriver event e sigma n)‖ ≤
        sourceQuantumNativeReaderBudget event e sigma n unit small := by
  have away : (sigma : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt positive)
  have paid (i : Fin 289) :
      ‖sourceSpatialStaticSourceReader n unit ⟨e.val^2, pow_pos e.property.1 2, small⟩
        (sourceTemporalActualQuantumDriver event e sigma n) i‖ ≤
      rationalReaderBudget (sourceQuantumNativeReaderFraction event e n unit small i) (sigma : ℂ) := by
    rw [source_quantum_native_reader_fraction event e sigma n unit small positive chart i]
    exact rational_read_budget _ _ away (radius.trans (reader_radius_le event e n unit small i))
  have nonnegative (i : Fin 289) : 0 ≤
      rationalReaderBudget (sourceQuantumNativeReaderFraction event e n unit small i) (sigma : ℂ) :=
    (norm_nonneg _).trans (paid i)
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => nonnegative i))).mpr
  intro i
  exact (paid i).trans (Finset.single_le_sum (fun j _ => nonnegative j) (Finset.mem_univ i))

/-- The source clock-coefficient budget directly replaces the actual reader
norm in the native epsilon-squared inverse price. Its epsilon dependence stays
explicit; no joint clock/spatial limit is inferred. -/
theorem source_temporal_quantum_ir_budget (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (chart : (dampingDeterminant event e.val n).eval (sigma : ℂ) ≠ 0)
    (radius : ‖(sigma : ℂ)‖ ≤ sourceQuantumNativeReaderRadius event e n unit small) :
    let kappa : staticDomain := ⟨e.val^2, pow_pos e.property.1 2, small⟩
    let driver := sourceTemporalActualQuantumDriver event e sigma n
    ‖-(e.val : ℂ)^4 * (sourceN3TemporalEMCoefficient event e.val sigma n -
        noetherPairScale^2 * dotProduct sourceTemporalEMForce
          (sourceNativeStaticMatrix e.val n*ᵥsourceTemporalEMForce) -
        noetherPairScale^2 * dotProduct sourceTemporalEMForce
          (sourceSpatialStaticRegularField n unit kappa driver)) -
      noetherPairScale^2 * dotProduct sourceTemporalEMForce
        (sourceSpatialStaticPoleCoefficient n unit kappa driver)‖ ≤
      ‖noetherPairScale^2‖ * ((∑ i, ‖sourceTemporalEMForce i‖) *
        ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit kappa)‖ *
        (2*staticInverseBudget^2*effectiveErrorBudget*kappa.val) *
        sourceQuantumNativeReaderBudget event e sigma n unit small) := by
  have nonzero : MvPolynomial.eval (irValues e.val sigma 0)
      (LowEnergy.GaussComposite.ActualDressedVisiblePole.commonDeterminant event n) ≠ 0 := by
    rw [←damping_slice_eval]; exact chart
  have regular := ActualDressedEMTensorClock.actual_common_chart_original event e.val sigma 0 n positive nonzero
  have price := source_temporal_quantum_spatial_pole_price event e sigma n unit small positive regular
  have budget := source_quantum_native_reader_budget event e sigma n unit small positive chart radius
  have error_nonnegative := effectiveErrorBudget_nonneg
  apply price.trans
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul_of_nonneg_left budget (by positivity)
  · exact norm_nonneg _

end LowEnergy.GaussComposite.ActualSourcePreparedQuantumDriverPrice
