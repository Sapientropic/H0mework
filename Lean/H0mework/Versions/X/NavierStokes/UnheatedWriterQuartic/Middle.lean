import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.Source

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticMiddle
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeWholeH1Pairing NativeUnheatedSourceGradient
open NativeUnheatedTriadChannels NativeUnheatedTriadChannelWrite NativeUnheatedPairNegativeKernel
open NativeUnheatedQuarticRows NativeUnheatedQuarticEnvelope NativeUnheatedQuarticSource
open NativeUnheatedSourceWeightedTail NativeCompleteStressCarrier
noncomputable section
variable {nu : Viscosity}

def tree (nu : Viscosity) (wave : IntegerWavevector) (i j response l m : Coordinate) (outer : Pair) : ℂ :=
  normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response * pressure (wave-outer.1-outer.2) l m j

def term (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) (d : IntegerWavevector) (time : ℝ) : ℂ :=
  tree nu wave i j response l m outer * NativeUnheatedQuarticTime.product seed
    (d,l) (wave-outer.1-outer.2-d,m) (outer.2,i) (outer.1,outside) time

theorem frequency (wave : IntegerWavevector) (outer : Pair) (d : IntegerWavevector) :
    d + (wave-outer.1-outer.2-d) + outer.2 + outer.1 = wave := by abel

theorem tree_bound (nu : Viscosity) (wave : IntegerWavevector) (i j response l m : Coordinate) (outer : Pair) :
    ‖tree nu wave i j response l m outer‖ ≤ cap nu * weight outer.1 := by
  rw [tree, norm_mul]
  apply (mul_le_mul_of_nonneg_left (pressure_bound (wave-outer.1-outer.2) l m j) (norm_nonneg _)).trans
  have same : ‖normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response‖ * root (wave-outer.1-outer.2) =
      ‖NativeUnheatedTriadChannels.kernel nu 1 i j response outer.2 (wave-outer.1-outer.2) outer.1‖ := by
    rw [normalizer, NativeUnheatedTriadChannels.kernel, norm_smul, norm_smul]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, norm_mul, root, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    ring
  change ‖normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response‖ * root (wave-outer.1-outer.2) ≤ _
  rw [same]
  exact NativeUnheatedTriadChannels.kernel_bound nu 1 i j response _ _ _

theorem term_summable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) (time : ℝ) :
    Summable (fun d => term seed wave i j response outside l m outer d time) := by
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  have pairs := NativeHigherTimeJets.mixed_pair_summable U U (wave-outer.1-outer.2) m l
  simpa only [term, NativeUnheatedQuarticTime.product, NativeUnheatedTriadRows.velocity_original,
    mul_assoc, U] using! ((pairs.mul_left (tree nu wave i j response l m outer)).mul_right
      (U outer.2 i)).mul_right (U outer.1 outside)

theorem inner_sum (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) (time : ℝ) :
    (∑' d, term seed wave i j response outside l m outer d time) =
      tree nu wave i j response l m outer *
        ((∑' d, wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst d l *
          wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (wave-outer.1-outer.2-d) m) *
          wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst outer.2 i *
          wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst outer.1 outside) := by
  simp only [term, NativeUnheatedQuarticTime.product, NativeUnheatedTriadRows.velocity_original]
  simp_rw [← mul_assoc]
  rw [tsum_mul_right, tsum_mul_right]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  ring

theorem first_row (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (outer : Pair) (time : ℝ) :
    NativeUnheatedTriadSource.row seed 1 wave i j response outside outer time =
      normalizer nu outer.2 (wave-outer.1-outer.2) outer.1 i j response *
        (NativeUnheatedTriadRows.velocity seed time outer.2 i *
          NativeUnheatedTriadRows.action seed time (wave-outer.1-outer.2) j *
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
    NativeUnheatedTriadSource.row seed 1 wave i j response outside outer time =
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
      NativeUnheatedTriadSource.coefficient seed 1 wave i j response outside time =
        ∑' outer : Pair, ∑ l : Coordinate, ∑ m : Coordinate, ∑' d,
          term seed wave i j response outside l m outer d time := by
  filter_upwards [physical_H1_ae seed] with time generated nonnegative wave i j response outside
  have original := NativeUnheatedTriadSum.value_eq_tsum (NativeUnheatedTriadChannels.kernel nu 1 i j response) (cap nu)
    (NativeUnheatedTriadChannels.kernel_bound nu 1 i j response) wave i j outside
    (NativeUnheatedTriadSource.input seed 1 0 time) (NativeUnheatedTriadSource.input seed 1 1 time)
    (NativeUnheatedTriadSource.input seed 1 2 time)
  change NativeUnheatedTriadSource.coefficient seed 1 wave i j response outside time =
    ∑' outer, NativeUnheatedTriadSource.row seed 1 wave i j response outside outer time at original
  rw [original]
  exact tsum_congr fun outer => source_fiber seed time nonnegative (generated nonnegative) wave i j response outside outer

theorem fiber_majorant (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) :
    (∑' d, ‖term seed wave i j response outside l m outer d time‖) ≤
      ‖NativeUnheatedTriadSum.term (positiveKernel nu) wave i 0 outside
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (scalarLift (envelope (physical seed time nonnegative) regular))
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) outer‖ := by
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  let C := (cap nu * weight outer.1) * ‖U outer.2 i‖ * ‖U outer.1 outside‖
  have cap0 : 0 ≤ cap nu * weight outer.1 := by unfold cap; positivity [nu.coeff_pos, weight_pos outer.1]
  have compare := (term_summable seed wave i j response outside l m outer time).norm.tsum_le_tsum
    (g := fun d => C * (NativeMovingCriticalProduct.amplitude U d * NativeMovingCriticalProduct.amplitude U (wave-outer.1-outer.2-d))) (fun d => ?_)
    ((pair_summable (physical seed time nonnegative) (wave-outer.1-outer.2)).mul_left C)
  · rw [tsum_mul_left] at compare
    change _ ≤ C * envelope (physical seed time nonnegative) regular (wave-outer.1-outer.2) at compare
    change _ ≤ ‖(↑(cap nu * weight outer.1) : ℂ) *
      (U outer.2 i * (envelope (physical seed time nonnegative) regular (wave-outer.1-outer.2) : ℂ)) * U outer.1 outside‖
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg cap0,
      Complex.norm_real, Real.norm_of_nonneg (envelope_nonnegative _ _ _)]
    exact compare.trans_eq (by dsimp only [C]; ring)
  · have first := NativeUnheatedPairInverseFlux.coordinate_bound U d l
    have second := NativeUnheatedPairInverseFlux.coordinate_bound U (wave-outer.1-outer.2-d) m
    rw [← amplitude_original] at first second
    have productBound := mul_le_mul first second (norm_nonneg _) (norm_nonneg _)
    have treePaid := mul_le_mul (tree_bound nu wave i j response l m outer) productBound
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) cap0
    have paid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right treePaid
      (norm_nonneg (U outer.2 i))) (norm_nonneg (U outer.1 outside))
    convert! paid using 1 <;> simp only [term, NativeUnheatedQuarticTime.product,
      NativeUnheatedTriadRows.velocity_original, norm_mul, C, U] <;> ring

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) :
    Summable (fun indices : Pair × IntegerWavevector => ‖term seed wave i j response outside l m indices.1 indices.2 time‖) := by
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  exact whole_summable nu wave i 0 outside U (scalarLift (envelope (physical seed time nonnegative) regular)) U
    (fun outer d => term seed wave i j response outside l m outer d time)
    (fun outer => term_summable seed wave i j response outside l m outer time)
    (fiber_majorant seed time nonnegative regular wave i j response outside l m)

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) :
    (∑' indices : Pair × IntegerWavevector, ‖term seed wave i j response outside l m indices.1 indices.2 time‖) ≤
      NativeUnheatedQuarticSource.bound seed * mass seed time := by
  have generated := whole_bound nu wave i 0 outside _ _ _ _
    (fun outer => term_summable seed wave i j response outside l m outer time)
    (fiber_majorant seed time nonnegative regular wave i j response outside l m)
  rw [scalarLift_norm] at generated
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  have vel : ‖U‖ ≤ NativeUnifiedCompleteSource.budget seed :=
    (wholeVelocity_norm_le (velocity seed time)).trans (velocity_bound seed time)
  have aPaid := source_envelope_norm_le seed time nonnegative regular
  have scalar0 : 0 ≤ 3 * cap nu * ‖NativeUnheatedTriadSum.weights‖ := by unfold cap; positivity [nu.coeff_pos]
  have budget0 := (norm_nonneg U).trans vel
  have a0 := mul_nonneg (Real.sqrt_nonneg constant) (mass_nonnegative seed time)
  have paid := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left vel scalar0) aPaid (norm_nonneg _)
    (mul_nonneg scalar0 budget0)) vel (norm_nonneg _) (mul_nonneg (mul_nonneg scalar0 budget0) a0)
  exact generated.trans (paid.trans_eq (by dsimp only [NativeUnheatedQuarticSource.bound]; ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticMiddle
