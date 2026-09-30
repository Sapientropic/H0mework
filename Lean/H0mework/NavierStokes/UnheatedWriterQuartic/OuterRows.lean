import H0mework.NavierStokes.UnheatedWriterQuartic.Rows

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticOuterRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeWholeH1Pairing NativeUnheatedSourceGradient
open NativeUnheatedTriadChannels NativeUnheatedTriadChannelWrite NativeUnheatedPairNegativeKernel
open NativeUnheatedSourceWeightedTail
noncomputable section
variable {nu : Viscosity}
abbrev Pair := IntegerWavevector × IntegerWavevector

def tree (nu : Viscosity) (wave : IntegerWavevector) (i j response outside l m : Coordinate) (outer : Pair) : ℂ :=
  normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response*pressure outer.1 l m outside

def term (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) (d : IntegerWavevector) (time : ℝ) : ℂ :=
  tree nu wave i j response outside l m outer*NativeUnheatedQuarticTime.product seed
    (outer.2,i) (wave-outer.1-outer.2,j) (d,l) (outer.1-d,m) time

theorem frequency (wave : IntegerWavevector) (outer : Pair) (d : IntegerWavevector) :
    outer.2+(wave-outer.1-outer.2)+d+(outer.1-d) = wave := by abel

theorem tree_bound (nu : Viscosity) (wave : IntegerWavevector) (i j response outside l m : Coordinate) (outer : Pair) :
    ‖tree nu wave i j response outside l m outer‖ ≤ cap nu*NativeCompleteStressCarrier.weight outer.1 := by
  have third : (![outer.2, wave-outer.1-outer.2, outer.1] (2 : Fin 3)) = outer.1 := rfl
  rw [tree, norm_mul]
  apply (mul_le_mul_of_nonneg_left (pressure_bound outer.1 l m outside) (norm_nonneg _)).trans
  have same : ‖normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response‖*root outer.1 =
      ‖NativeUnheatedTriadChannels.kernel nu 2 i j response outer.2 (wave-outer.1-outer.2) outer.1‖ := by
    rw [normalizer, NativeUnheatedTriadChannels.kernel, norm_smul, norm_smul]
    simp only [third, norm_mul, root, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    ring
  change ‖normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response‖*root outer.1 ≤ _
  rw [same]
  exact NativeUnheatedTriadChannels.kernel_bound nu 2 i j response _ _ _

theorem inner_zero (seed : GeneratedWholeRestartCurrent nu) (wave a d : IntegerWavevector)
    (i j response outside l m : Coordinate) (time : ℝ) :
    term seed wave i j response outside l m (0,a) d time = 0 := by
  simp [term, tree, pressure, NativeTimeJetCarrier.projectedDivergenceCLM_apply,
    ThreeDimensionalVorticityCoefficientRawSourceCore.transverseProjection]

theorem term_summable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) (time : ℝ) :
    Summable (fun d => term seed wave i j response outside l m outer d time) := by
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  have pairs := NativeHigherTimeJets.mixed_pair_summable U U outer.1 m l
  have paid := pairs.mul_left (tree nu wave i j response outside l m outer*U outer.2 i*U (wave-outer.1-outer.2) j)
  convert! paid using 1
  funext d
  simp only [term, NativeUnheatedQuarticTime.product, NativeUnheatedTriadRows.velocity_original, U]
  ring

theorem inner_sum (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) (time : ℝ) :
    (∑' d, term seed wave i j response outside l m outer d time) =
      tree nu wave i j response outside l m outer*
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst outer.2 i*
          wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (wave-outer.1-outer.2) j*
          ∑' d, wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst d l*
            wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (outer.1-d) m) := by
  simp only [term, NativeUnheatedQuarticTime.product, NativeUnheatedTriadRows.velocity_original]
  simp_rw [mul_assoc]
  rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]

theorem last_row (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (outer : Pair) (time : ℝ) :
    NativeUnheatedTriadSource.row seed 2 wave i j response outside outer time =
      normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response*
        (NativeUnheatedTriadRows.velocity seed time outer.2 i*
          NativeUnheatedTriadRows.velocity seed time (wave-outer.1-outer.2) j*
          NativeUnheatedTriadRows.action seed time outer.1 outside) := by
  have third : (![outer.2, wave-outer.1-outer.2, outer.1] (2 : Fin 3)) = outer.1 := rfl
  simp only [NativeUnheatedTriadSource.row, NativeUnheatedTriadSum.term, NativeUnheatedTriadSum.innerTerm,
    NativeUnheatedTriadChannels.kernel, NativeUnheatedTriadSource.input, Fin.ext_iff,
    NativeUnheatedTriadRows.action, NativeUnheatedTriadRows.decode_apply, NativeUnheatedTriadRows.velocity_original,
    wholeVelocityCLM_apply, velocity, normalizer, root, third]
  norm_num [Complex.real_smul]
  ring

theorem source_fiber (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (outer : Pair) :
    NativeUnheatedTriadSource.row seed 2 wave i j response outside outer time =
      ∑ l : Coordinate, ∑ m : Coordinate, ∑' d, term seed wave i j response outside l m outer d time := by
  rw [last_row, NativeUnheatedQuarticRows.source_action seed time nonnegative regular, NativeUnheatedCubicIdentity.row_channels]
  simp only [inner_sum, tree, NativeUnheatedTriadRows.velocity_original, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem coefficient_expansion (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ wave i j response outside,
      NativeUnheatedTriadSource.coefficient seed 2 wave i j response outside time =
        ∑' outer : Pair, ∑ l : Coordinate, ∑ m : Coordinate, ∑' d,
          term seed wave i j response outside l m outer d time := by
  filter_upwards [physical_H1_ae seed] with time generated nonnegative wave i j response outside
  have original := NativeUnheatedTriadSum.value_eq_tsum (NativeUnheatedTriadChannels.kernel nu 2 i j response) (cap nu)
    (NativeUnheatedTriadChannels.kernel_bound nu 2 i j response) wave i j outside
    (NativeUnheatedTriadSource.input seed 2 0 time) (NativeUnheatedTriadSource.input seed 2 1 time)
    (NativeUnheatedTriadSource.input seed 2 2 time)
  change NativeUnheatedTriadSource.coefficient seed 2 wave i j response outside time =
    ∑' outer, NativeUnheatedTriadSource.row seed 2 wave i j response outside outer time at original
  rw [original]
  exact tsum_congr fun outer => source_fiber seed time nonnegative (generated nonnegative) wave i j response outside outer

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticOuterRows
