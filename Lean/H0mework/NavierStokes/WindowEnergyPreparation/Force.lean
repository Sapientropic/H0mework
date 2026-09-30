import H0mework.NavierStokes.WindowEnergyPreparation.Initial
import H0mework.NavierStokes.WindowSourcePreparation.ForcingPhysical

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeWindowStressPreparationForce
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativePhysicalFourier NativeFullOrderSynthesis
open NativeWindowStressPreparationInitial
open NativeWindowPreparationInitial (Tensor)
open NativeWindowPreparationWrite (fraction fraction_smooth)
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
noncomputable section

def coefficient (point : BasePoint) : ℝ := fraction (canonicalTimeProjection point)

theorem coefficient_smooth : ContDiff ℝ ∞ coefficient := fraction_smooth.comp canonicalTimeProjection.contDiff

def spatialPair (F : Finset IntegerWavevector) : BasePoint → Tensor := pair F ∘ canonicalSpatialProjection

theorem spatialPair_smooth (F : Finset IntegerWavevector) : ContDiff ℝ ∞ (spatialPair F) :=
  (pair_smooth F).comp canonicalSpatialProjection.contDiff

def spatialBudget (order : ℕ) : ℝ := pairBudget order*‖canonicalSpatialProjection‖^order

theorem spatialPair_bound (F : Finset IntegerWavevector) (order : ℕ) (point : BasePoint) :
    ‖iteratedFDeriv ℝ order (spatialPair F) point‖ ≤ spatialBudget order := by
  rw [spatialPair,canonicalSpatialProjection.iteratedFDeriv_comp_right (pair_smooth F) point
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  apply ((iteratedFDeriv ℝ order (pair F) (canonicalSpatialProjection point)).norm_compContinuousLinearMap_le
    (fun _ => canonicalSpatialProjection)).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (pair_bound F order _) (pow_nonneg (norm_nonneg _) _)

def correction (F : Finset IntegerWavevector) (point : BasePoint) : Tensor :=
  coefficient point • spatialPair F point

theorem correction_smooth (F : Finset IntegerWavevector) : ContDiff ℝ ∞ (correction F) :=
  coefficient_smooth.smul (spatialPair_smooth F)

theorem correction_original (F : Finset IntegerWavevector) (time : ℝ) (space : PhysicalSpace)
    (output input : Coordinate) : correction F (canonicalCauchySlicePoint time space) (output,input) =
      fraction time * NativeWindowStressPreparationWrite.fullPairRate stackedShortCurrent F output input 0
        (circlePoint space) := by
  simp only [correction,coefficient,spatialPair,Function.comp_apply,canonicalTimeProjection_slice,
    canonicalSpatialProjection_slice,PiLp.smul_apply,smul_eq_mul,pair_original]

theorem stress_writer (F : Finset IntegerWavevector) (time : ℝ) (space : PhysicalSpace)
    (output input : Coordinate) :
    HasDerivAt (fun actual => NativeWindowFiniteGramFourier.stress stackedShortCurrent actual F output input
      (circlePoint space))
      ((∫ shift : ℝ, NativeForwardWindowSource.kernel shift •
        NativeWindowStressPreparationWrite.fullPairRate stackedShortCurrent F output input (time-shift))
          (circlePoint space)-correction F (canonicalCauchySlicePoint time space) (output,input)) time := by
  have actual := (ContinuousMap.evalCLM ℝ (circlePoint space)).hasFDerivAt.comp_hasDerivAt time
    (NativeWindowStressPreparationWrite.stress_generator stackedShortCurrent F output input time)
  simpa only [Function.comp_def,ContinuousMap.evalCLM_apply,ContinuousMap.sub_apply,
    ContinuousMap.smul_apply,smul_eq_mul,correction_original] using! actual

def pointBudget (order : ℕ) (point : BasePoint) : ℝ := ∑ rank ∈ Finset.range (order+1),
  (order.choose rank : ℝ)*‖iteratedFDeriv ℝ rank coefficient point‖*spatialBudget (order-rank)

theorem pointBudget_continuous (order : ℕ) : Continuous (pointBudget order) := by
  apply continuous_finsetSum
  intro rank _
  exact (continuous_const.mul (coefficient_smooth.continuous_iteratedFDeriv
    (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤))).norm).mul continuous_const

theorem correction_bound (F : Finset IntegerWavevector) (order : ℕ) (point : BasePoint) :
    ‖iteratedFDeriv ℝ order (correction F) point‖ ≤ pointBudget order point := by
  apply (norm_iteratedFDeriv_smul_le coefficient_smooth (spatialPair_smooth F) point
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).trans
  apply Finset.sum_le_sum
  intro rank _
  exact mul_le_mul_of_nonneg_left (spatialPair_bound F (order-rank) point)
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

theorem exists_uniform_all_order_bound (order : ℕ) {domain : Set BasePoint} (compact : IsCompact domain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Finset IntegerWavevector) (point : BasePoint), point ∈ domain →
      ‖iteratedFDeriv ℝ order (correction F) point‖ ≤ C := by
  obtain ⟨C,bounded⟩ := compact.exists_bound_of_continuousOn (pointBudget_continuous order).continuousOn
  refine ⟨max C 0,le_max_right _ _,fun F point inside => ?_⟩
  exact (correction_bound F order point).trans
    ((le_abs_self _).trans ((bounded point inside).trans (le_max_left _ _)))

theorem exists_uniform_all_order_Lp (order : ℕ) (exponent : ℝ≥0∞) {domain : Set BasePoint}
    (compact : IsCompact domain) : ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Finset IntegerWavevector,
      MemLp (iteratedFDeriv ℝ order (correction F)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (correction F)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal C*volume domain^(1/exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  obtain ⟨C,nonnegative,paid⟩ := exists_uniform_all_order_bound order compact
  refine ⟨C,nonnegative,fun F => ?_⟩
  have bound : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order (correction F) point‖ ≤ C := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact paid F point inside
  have continuous := (correction_smooth F).continuous_iteratedFDeriv
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable _ bound,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) bound⟩

theorem correction_after (F : Finset IntegerWavevector) (point : BasePoint)
    (after : -1 ≤ canonicalTimeProjection point) : correction F point = 0 := by
  rw [correction,coefficient,NativeWindowPreparationWrite.fraction_after _ after,zero_smul]

end
end SaturationMonoid.NavierStokes.NativeWindowStressPreparationForce
