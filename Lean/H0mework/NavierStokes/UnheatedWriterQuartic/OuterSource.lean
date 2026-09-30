import H0mework.NavierStokes.UnheatedWriterQuartic.OuterRows
import H0mework.NavierStokes.UnheatedWriterQuartic.Source
import H0mework.NavierStokes.UnheatedWriterTriad.WeightedRows

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticOuterSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeWholeH1Pairing NativeUnheatedSourceGradient
open NativeUnheatedTriadChannels NativeUnheatedQuarticEnvelope NativeUnheatedQuarticOuterRows
open NativeUnheatedSourceWeightedTail NativeCompleteStressCarrier
open NativeUnheatedQuarticSource
noncomputable section
variable {nu : Viscosity}

theorem fiber_absolute_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) :
    (∑' d, ‖term seed wave i j response outside l m outer d time‖) ≤
      (cap nu*weight outer.1)*‖wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst outer.2 i‖*
        ‖wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (wave-outer.1-outer.2) j‖*
          envelope (physical seed time nonnegative) regular outer.1 := by
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  let C := (cap nu*weight outer.1)*‖U outer.2 i‖*‖U (wave-outer.1-outer.2) j‖
  have compare := (term_summable seed wave i j response outside l m outer time).norm.tsum_le_tsum
    (g := fun d => C*(NativeMovingCriticalProduct.amplitude U d*NativeMovingCriticalProduct.amplitude U (outer.1-d))) (fun d => ?_)
    ((pair_summable (physical seed time nonnegative) outer.1).mul_left C)
  · rw [tsum_mul_left] at compare
    exact compare
  · have first := NativeUnheatedPairInverseFlux.coordinate_bound U d l
    have second := NativeUnheatedPairInverseFlux.coordinate_bound U (outer.1-d) m
    rw [← amplitude_original] at first second
    have pair := mul_le_mul first second (norm_nonneg _) (norm_nonneg _)
    have coefficient := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (tree_bound nu wave i j response outside l m outer) (norm_nonneg (U outer.2 i)))
      (norm_nonneg (U (wave-outer.1-outer.2) j))
    have paid := mul_le_mul coefficient pair (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (by dsimp [C]; unfold cap; positivity [nu.coeff_pos, weight_pos outer.1])
    convert! paid using 1
    simp only [term, NativeUnheatedQuarticTime.product, NativeUnheatedTriadRows.velocity_original, norm_mul, U]
    ring

theorem fiber_majorant (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) :
    (∑' d, ‖term seed wave i j response outside l m outer d time‖) ≤
      ‖NativeUnheatedTriadSum.term (positiveKernel nu) wave i j 0
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (scalarLift (envelope (physical seed time nonnegative) regular)) outer‖ := by
  have cap0 : 0 ≤ cap nu := by unfold cap; positivity [nu.coeff_pos]
  simp only [NativeUnheatedTriadSum.term, NativeUnheatedTriadSum.innerTerm, positiveKernel, scalarLift,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg cap0, Real.norm_of_nonneg (weight_pos outer.1).le,
    Real.norm_of_nonneg (envelope_nonnegative _ _ outer.1)]
  exact (fiber_absolute_bound seed time nonnegative regular wave i j response outside l m outer).trans_eq (by ring)

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) :
    Summable (fun indices : Pair × IntegerWavevector => ‖term seed wave i j response outside l m indices.1 indices.2 time‖) :=
  whole_summable nu wave i j 0 _ _ _ (fun outer d => term seed wave i j response outside l m outer d time)
    (fun outer => term_summable seed wave i j response outside l m outer time)
    (fiber_majorant seed time nonnegative regular wave i j response outside l m)

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) :
    (∑' indices : Pair × IntegerWavevector, ‖term seed wave i j response outside l m indices.1 indices.2 time‖) ≤
      NativeUnheatedQuarticSource.bound seed*mass seed time := by
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  have generated := whole_bound nu wave i j 0 U U (scalarLift (envelope (physical seed time nonnegative) regular))
    (fun outer d => term seed wave i j response outside l m outer d time)
    (fun outer => term_summable seed wave i j response outside l m outer time)
    (fiber_majorant seed time nonnegative regular wave i j response outside l m)
  rw [scalarLift_norm] at generated
  have vel : ‖U‖ ≤ NativeUnifiedCompleteSource.budget seed :=
    (wholeVelocity_norm_le (velocity seed time)).trans (velocity_bound seed time)
  have scalar0 : 0 ≤ 3*cap nu*‖NativeUnheatedTriadSum.weights‖ := by unfold cap; positivity [nu.coeff_pos]
  have budget0 := (norm_nonneg U).trans vel
  have square := mul_le_mul vel vel (norm_nonneg _) budget0
  have paid := mul_le_mul (mul_le_mul_of_nonneg_left square scalar0)
    (source_envelope_norm_le seed time nonnegative regular) (norm_nonneg _)
    (mul_nonneg scalar0 (mul_nonneg budget0 budget0))
  apply generated.trans
  convert! paid using 1
  · ring
  · unfold NativeUnheatedQuarticSource.bound
    ring

theorem coefficient_full (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ wave i j response outside,
      NativeUnheatedTriadSource.coefficient seed 2 wave i j response outside time =
        ∑ l : Coordinate, ∑ m : Coordinate, ∑' indices : Pair × IntegerWavevector,
          term seed wave i j response outside l m indices.1 indices.2 time := by
  filter_upwards [NativeUnheatedQuarticOuterRows.coefficient_expansion seed, physical_H1_ae seed]
    with time actual regular nonnegative wave i j response outside
  rw [actual nonnegative]
  have sums (l m : Coordinate) := (absolute_summable seed time nonnegative (regular nonnegative) wave i j response outside l m).of_norm
  have outerSums (l m : Coordinate) := (sums l m).prod
  rw [Summable.tsum_finsetSum (fun l (_ : l ∈ (Finset.univ : Finset Coordinate)) =>
    summable_sum (fun m (_ : m ∈ (Finset.univ : Finset Coordinate)) => outerSums l m))]
  apply Finset.sum_congr rfl
  intro l _
  rw [Summable.tsum_finsetSum (fun m (_ : m ∈ (Finset.univ : Finset Coordinate)) => outerSums l m)]
  apply Finset.sum_congr rfl
  intro m _
  exact (sums l m).tsum_prod.symm

theorem term_integrable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) (d : IntegerWavevector) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (term seed wave i j response outside l m outer d) (volume.restrict (Icc 0 horizon)) := by
  have continuous : ContinuousOn (term seed wave i j response outside l m outer d) (Icc 0 horizon) := by
    simpa only [term, uIcc_of_le nonnegative] using!
      (NativeUnheatedQuarticTime.product_ac seed (outer.2,i) (wave-outer.1-outer.2,j) (d,l) (outer.1-d,m)
        0 horizon le_rfl nonnegative).continuousOn.const_mul (tree nu wave i j response outside l m outer)
  exact continuous.integrableOn_Icc

theorem norm_integrals_summable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Summable (fun indices : Pair × IntegerWavevector =>
      ∫ time in Icc 0 horizon, ‖term seed wave i j response outside l m indices.1 indices.2 time‖) := by
  apply summable_of_sum_le (c := NativeUnheatedQuarticSource.bound seed*
    NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) horizon)
    (fun _ => integral_nonneg fun _ => norm_nonneg _)
  intro observed
  rw [← integral_finsetSum observed (fun index _ => (term_integrable seed wave i j response outside l m index.1 index.2 horizon nonnegative).norm)]
  have paid := integral_mono_ae (integrable_finsetSum observed (fun index _ =>
    (term_integrable seed wave i j response outside l m index.1 index.2 horizon nonnegative).norm))
    ((mass_integrable seed horizon nonnegative).const_mul (NativeUnheatedQuarticSource.bound seed)) (by
      filter_upwards [ae_restrict_of_ae (physical_H1_ae seed), ae_restrict_mem measurableSet_Icc] with time actual inside
      exact ((absolute_summable seed time inside.1 (actual inside.1) wave i j response outside l m).sum_le_tsum observed
        (fun _ _ => norm_nonneg _)).trans (absolute_bound seed time inside.1 (actual inside.1) wave i j response outside l m))
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (mass_integral_bound seed horizon nonnegative) (NativeUnheatedQuarticSource.bound_nonnegative seed))

theorem weighted_fubini (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (test : ℝ → ℝ) (smooth : ContinuousOn test (Icc 0 horizon)) :
    (∫ time in Icc 0 horizon, test time • ∑' indices : Pair × IntegerWavevector,
      term seed wave i j response outside l m indices.1 indices.2 time) =
      ∑' indices : Pair × IntegerWavevector, ∫ time in Icc 0 horizon,
        test time • term seed wave i j response outside l m indices.1 indices.2 time := by
  obtain ⟨measured, ceiling, bounded⟩ := NativeUnheatedTriadWeightedRows.test_resources horizon test smooth
  let rows : (Pair × IntegerWavevector) → ℝ → ℂ :=
    fun index time => term seed wave i j response outside l m index.1 index.2 time
  have each (index : Pair × IntegerWavevector) : Integrable (rows index) (volume.restrict (Icc 0 horizon)) :=
    term_integrable seed wave i j response outside l m index.1 index.2 horizon nonnegative
  have normSums : Summable (fun index => ∫ time in Icc 0 horizon, ‖rows index time‖) :=
    norm_integrals_summable seed wave i j response outside l m horizon nonnegative
  have pointwise : ∀ᵐ time ∂volume.restrict (Icc 0 horizon), Summable (fun index => rows index time) := by
    filter_upwards [ae_restrict_of_ae (physical_H1_ae seed), ae_restrict_mem measurableSet_Icc] with time actual inside
    exact (absolute_summable seed time inside.1 (actual inside.1) wave i j response outside l m).of_norm
  exact NativeUnheatedTriadWeightedSum.weighted_integral_tsum rows each normSums test measured ceiling bounded pointwise

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticOuterSource
