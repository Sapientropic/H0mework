import H0mework.NavierStokes.UnheatedWriterTriad.ChannelWrite
import H0mework.NavierStokes.UnheatedWriterTriad.CubicIdentity
import H0mework.NavierStokes.UnheatedWriterQuartic.Time

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeWholeH1Pairing NativeUnheatedSourceGradient
open NativeUnheatedTriadKernel NativeUnheatedTriadChannels NativeUnheatedTriadChannelWrite
open NativeUnheatedPairNegativeKernel NativeUnheatedSourceWeightedTail
noncomputable section
variable {nu : Viscosity}

abbrev Pair := IntegerWavevector × IntegerWavevector

def tree (nu : Viscosity) (wave : IntegerWavevector) (i j response l m : Coordinate) (outer : Pair) : ℂ :=
  normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response * pressure outer.2 l m i

def term (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) (d : IntegerWavevector) (time : ℝ) : ℂ :=
  tree nu wave i j response l m outer * NativeUnheatedQuarticTime.product seed
    (d,l) (outer.2-d,m) (wave-outer.1-outer.2,j) (outer.1,outside) time

theorem frequency (wave : IntegerWavevector) (outer : Pair) (d : IntegerWavevector) :
    d + (outer.2-d) + (wave-outer.1-outer.2) + outer.1 = wave := by abel

theorem tree_bound (nu : Viscosity) (wave : IntegerWavevector) (i j response l m : Coordinate) (outer : Pair) :
    ‖tree nu wave i j response l m outer‖ ≤ cap nu * NativeCompleteStressCarrier.weight outer.1 := by
  rw [tree, norm_mul]
  apply (mul_le_mul_of_nonneg_left (pressure_bound outer.2 l m i) (norm_nonneg _)).trans
  have same : ‖normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response‖ * root outer.2 =
      ‖NativeUnheatedTriadChannels.kernel nu 0 i j response outer.2 (wave-outer.1-outer.2) outer.1‖ := by
    rw [normalizer, NativeUnheatedTriadChannels.kernel, norm_smul, norm_smul]
    simp only [Matrix.cons_val_zero, norm_mul, root, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    ring
  change ‖normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response‖ * root outer.2 ≤ _
  rw [same]
  exact NativeUnheatedTriadChannels.kernel_bound nu 0 i j response _ _ _

theorem inner_zero (seed : GeneratedWholeRestartCurrent nu) (wave c d : IntegerWavevector)
    (i j response outside l m : Coordinate) (time : ℝ) :
    term seed wave i j response outside l m (c,0) d time = 0 := by
  simp [term, tree, pressure, NativeTimeJetCarrier.projectedDivergenceCLM_apply,
    ThreeDimensionalVorticityCoefficientRawSourceCore.transverseProjection]

theorem term_summable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) (time : ℝ) :
    Summable (fun d => term seed wave i j response outside l m outer d time) := by
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  have pairs := NativeHigherTimeJets.mixed_pair_summable U U outer.2 m l
  simpa only [term, NativeUnheatedQuarticTime.product, NativeUnheatedTriadRows.velocity_original,
    mul_assoc, U] using! ((pairs.mul_left (tree nu wave i j response l m outer)).mul_right
      (U (wave-outer.1-outer.2) j)).mul_right (U outer.1 outside)

theorem inner_sum (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) (time : ℝ) :
    (∑' d, term seed wave i j response outside l m outer d time) =
      tree nu wave i j response l m outer *
        ((∑' d, wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst d l *
          wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (outer.2-d) m) *
          wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (wave-outer.1-outer.2) j *
          wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst outer.1 outside) := by
  simp only [term, NativeUnheatedQuarticTime.product, NativeUnheatedTriadRows.velocity_original]
  simp_rw [← mul_assoc]
  rw [tsum_mul_right, tsum_mul_right]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  ring

theorem source_action (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector) (i : Coordinate) :
    NativeUnheatedTriadRows.action seed time wave i = NativeTimeJetCarrier.projectedDivergenceCLM wave
      (NativeHigherTimeJets.mixedFlux (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) wave) i := by
  simp only [NativeUnheatedTriadRows.action, NativeUnheatedTriadRows.decode_apply,
    nonlinear, dif_pos nonnegative, dif_pos regular]
  change root wave • wholeVelocity (negativeAction (physical seed time nonnegative) (physical seed time nonnegative) regular regular) wave i =
    NativeWholeH1Mixed.row (physical seed time nonnegative) (physical seed time nonnegative) wave i
  rw [NativeUnheatedCubicRows.negative_row, Pi.smul_apply]
  by_cases zero : wave = 0
  · simp only [zero, NativeUnheatedCubicRows.row_zero, Pi.zero_apply, smul_zero]
  · exact smul_inv_smul₀ (root_positive wave zero).ne' _

theorem first_row (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (outer : Pair) (time : ℝ) :
    NativeUnheatedTriadSource.row seed 0 wave i j response outside outer time =
      normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response *
        (NativeUnheatedTriadRows.action seed time outer.2 i *
          NativeUnheatedTriadRows.velocity seed time (wave-outer.1-outer.2) j *
          NativeUnheatedTriadRows.velocity seed time outer.1 outside) := by
  simp only [NativeUnheatedTriadSource.row, NativeUnheatedTriadSum.term, NativeUnheatedTriadSum.innerTerm,
    NativeUnheatedTriadChannels.kernel, NativeUnheatedTriadSource.input, Fin.ext_iff,
    NativeUnheatedTriadRows.action, NativeUnheatedTriadRows.decode_apply, NativeUnheatedTriadRows.velocity_original,
    wholeVelocityCLM_apply, velocity, normalizer, root]
  norm_num [Complex.real_smul]
  ring

theorem source_fiber (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (outer : Pair) :
    NativeUnheatedTriadSource.row seed 0 wave i j response outside outer time =
      ∑ l : Coordinate, ∑ m : Coordinate, ∑' d, term seed wave i j response outside l m outer d time := by
  rw [first_row, source_action seed time nonnegative regular, NativeUnheatedCubicIdentity.row_channels]
  simp only [inner_sum, tree, NativeUnheatedTriadRows.velocity_original, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem coefficient_expansion (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ wave i j response outside,
      NativeUnheatedTriadSource.coefficient seed 0 wave i j response outside time =
        ∑' outer : Pair, ∑ l : Coordinate, ∑ m : Coordinate, ∑' d,
          term seed wave i j response outside l m outer d time := by
  filter_upwards [physical_H1_ae seed] with time generated nonnegative wave i j response outside
  have original := NativeUnheatedTriadSum.value_eq_tsum (NativeUnheatedTriadChannels.kernel nu 0 i j response) (cap nu)
    (NativeUnheatedTriadChannels.kernel_bound nu 0 i j response) wave i j outside
    (NativeUnheatedTriadSource.input seed 0 0 time) (NativeUnheatedTriadSource.input seed 0 1 time)
    (NativeUnheatedTriadSource.input seed 0 2 time)
  change NativeUnheatedTriadSource.coefficient seed 0 wave i j response outside time =
    ∑' outer, NativeUnheatedTriadSource.row seed 0 wave i j response outside outer time at original
  rw [original]
  apply tsum_congr
  intro outer
  exact source_fiber seed time nonnegative (generated nonnegative) wave i j response outside outer

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticRows
