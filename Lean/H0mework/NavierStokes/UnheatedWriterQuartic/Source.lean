import H0mework.NavierStokes.UnheatedWriterQuartic.Rows
import H0mework.NavierStokes.UnheatedWriterQuartic.EnvelopeSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeWholeH1Pairing NativeUnheatedSourceGradient
open NativeUnheatedTriadChannels NativeUnheatedQuarticRows NativeUnheatedQuarticEnvelope
open NativeUnheatedSourceWeightedTail NativeCompleteStressCarrier
noncomputable section
variable {nu : Viscosity}

def scalarLift (value : NativeFullOrderAction.ScalarL2) : NativeUnheatedTriadSum.E :=
  ⟨fun wave _ => (value wave : ℂ), value.2.mono' (fun wave => by simp only [pi_norm_const, Complex.norm_real]; rfl)⟩

theorem scalarLift_norm (value : NativeFullOrderAction.ScalarL2) : ‖scalarLift value‖ = ‖value‖ := by
  apply le_antisymm <;> apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) <;>
    intro wave <;> simp only [scalarLift, pi_norm_const, Complex.norm_real, Real.norm_eq_abs, le_refl]

def positiveKernel (nu : Viscosity) (_ _ c : IntegerWavevector) : ℂ := (cap nu * weight c : ℝ)

theorem positiveKernel_bound (nu : Viscosity) (a b c : IntegerWavevector) :
    ‖positiveKernel nu a b c‖ ≤ cap nu * weight c := by
  have nonnegative : 0 ≤ cap nu * weight c := by unfold cap; positivity [nu.coeff_pos, weight_pos c]
  simp only [positiveKernel, Complex.norm_real, Real.norm_of_nonneg nonnegative, le_refl]

theorem whole_summable (nu : Viscosity) (wave : IntegerWavevector) (i j k : Coordinate)
    (L M R : NativeUnheatedTriadSum.E) (rows : Pair → IntegerWavevector → ℂ)
    (fibers : ∀ outer, Summable (rows outer))
    (majorant : ∀ outer, (∑' d, ‖rows outer d‖) ≤
      ‖NativeUnheatedTriadSum.term (positiveKernel nu) wave i j k L M R outer‖) :
    Summable (fun indices : Pair × IntegerWavevector => ‖rows indices.1 indices.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun outer => (fibers outer).norm,
    (NativeUnheatedTriadSum.absolute_summable (positiveKernel nu) (cap nu) (positiveKernel_bound nu)
      wave i j k L M R).of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) majorant⟩

theorem whole_bound (nu : Viscosity) (wave : IntegerWavevector) (i j k : Coordinate)
    (L M R : NativeUnheatedTriadSum.E) (rows : Pair → IntegerWavevector → ℂ)
    (fibers : ∀ outer, Summable (rows outer))
    (majorant : ∀ outer, (∑' d, ‖rows outer d‖) ≤
      ‖NativeUnheatedTriadSum.term (positiveKernel nu) wave i j k L M R outer‖) :
    (∑' indices : Pair × IntegerWavevector, ‖rows indices.1 indices.2‖) ≤
      (3 * cap nu * ‖NativeUnheatedTriadSum.weights‖) * ‖L‖ * ‖M‖ * ‖R‖ := by
  have sums := whole_summable nu wave i j k L M R rows fibers majorant
  rw [sums.tsum_prod]
  exact (sums.prod.tsum_le_tsum majorant
    (NativeUnheatedTriadSum.absolute_summable (positiveKernel nu) (cap nu) (positiveKernel_bound nu)
      wave i j k L M R)).trans
    (NativeUnheatedTriadSum.absolute_bound (positiveKernel nu) (cap nu) (positiveKernel_bound nu)
      wave i j k L M R)

private def upper (nu : Viscosity) (wave : IntegerWavevector) (j outside : Coordinate)
    (value : NativeFullOrderAction.ScalarL2) (U : NativeUnheatedTriadSum.E) (outer : Pair) : ℂ :=
  NativeUnheatedTriadSum.term (positiveKernel nu) wave 0 j outside (scalarLift value) U U outer

private theorem upper_norm (nu : Viscosity) (wave : IntegerWavevector) (j outside : Coordinate)
    (value : NativeFullOrderAction.ScalarL2) (positive : ∀ k, 0 ≤ value k)
    (U : NativeUnheatedTriadSum.E) (outer : Pair) :
    ‖upper nu wave j outside value U outer‖ =
      (cap nu * weight outer.1) * value outer.2 * ‖U (wave-outer.1-outer.2) j‖ * ‖U outer.1 outside‖ := by
  have cap0 : 0 ≤ cap nu := by unfold cap; positivity [nu.coeff_pos]
  simp only [upper, NativeUnheatedTriadSum.term, NativeUnheatedTriadSum.innerTerm, positiveKernel,
    scalarLift, norm_mul, Complex.norm_real, Real.norm_of_nonneg cap0, Real.norm_of_nonneg (weight_pos outer.1).le,
    Real.norm_of_nonneg (positive outer.2)]
  ring

theorem fiber_absolute_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (outer : Pair) :
    (∑' d, ‖term seed wave i j response outside l m outer d time‖) ≤
      (cap nu * weight outer.1) * envelope (physical seed time nonnegative) regular outer.2 *
        ‖wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (wave-outer.1-outer.2) j‖ *
        ‖wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst outer.1 outside‖ := by
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  let C := (cap nu * weight outer.1) * ‖U (wave-outer.1-outer.2) j‖ * ‖U outer.1 outside‖
  have c0 : 0 ≤ C := by dsimp [C]; unfold cap; positivity [nu.coeff_pos, weight_pos outer.1]
  have compare := (term_summable seed wave i j response outside l m outer time).norm.tsum_le_tsum
    (g := fun d => C * (NativeMovingCriticalProduct.amplitude U d * NativeMovingCriticalProduct.amplitude U (outer.2-d))) (fun d => ?_)
    ((pair_summable (physical seed time nonnegative) outer.2).mul_left C)
  · rw [tsum_mul_left] at compare
    change _ ≤ C * envelope (physical seed time nonnegative) regular outer.2 at compare
    exact compare.trans_eq (by dsimp only [C, U]; ring)
  · have first := NativeUnheatedPairInverseFlux.coordinate_bound U d l
    have second := NativeUnheatedPairInverseFlux.coordinate_bound U (outer.2-d) m
    rw [← amplitude_original] at first second
    have productBound := mul_le_mul first second (norm_nonneg _) (norm_nonneg _)
    have treePaid := mul_le_mul (tree_bound nu wave i j response l m outer) productBound
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by unfold cap; positivity [nu.coeff_pos, weight_pos outer.1])
    have paid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right treePaid
      (norm_nonneg (U (wave-outer.1-outer.2) j))) (norm_nonneg (U outer.1 outside))
    convert! paid using 1 <;> simp only [term, NativeUnheatedQuarticTime.product,
      NativeUnheatedTriadRows.velocity_original, norm_mul, C, U] <;> ring

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) :
    Summable (fun indices : Pair × IntegerWavevector => ‖term seed wave i j response outside l m indices.1 indices.2 time‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun outer => (term_summable seed wave i j response outside l m outer time).norm, ?_⟩
  have paid := NativeUnheatedTriadSum.absolute_summable (positiveKernel nu) (cap nu) (positiveKernel_bound nu)
    wave 0 j outside (scalarLift (envelope (physical seed time nonnegative) regular))
    (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
  apply paid.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
  intro outer
  change _ ≤ ‖upper nu wave j outside _ _ outer‖
  rw [upper_norm nu wave j outside _ (envelope_nonnegative _ _) _ outer]
  exact fiber_absolute_bound seed time nonnegative regular wave i j response outside l m outer

def bound (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  (3 * cap nu * ‖NativeUnheatedTriadSum.weights‖) * Real.sqrt constant * NativeUnifiedCompleteSource.budget seed ^ 2

theorem bound_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ bound seed := by
  unfold bound cap
  positivity [nu.coeff_pos]

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) :
    (∑' indices : Pair × IntegerWavevector, ‖term seed wave i j response outside l m indices.1 indices.2 time‖) ≤
      bound seed * mass seed time := by
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  let A := envelope (physical seed time nonnegative) regular
  have upperSums := NativeUnheatedTriadSum.absolute_summable (positiveKernel nu) (cap nu) (positiveKernel_bound nu)
    wave 0 j outside (scalarLift A) U U
  rw [(absolute_summable seed time nonnegative regular wave i j response outside l m).tsum_prod]
  have compare := (absolute_summable seed time nonnegative regular wave i j response outside l m).prod.tsum_le_tsum
    (fun outer => by
      change _ ≤ ‖upper nu wave j outside A U outer‖
      rw [upper_norm nu wave j outside A (envelope_nonnegative _ _) U outer]
      exact fiber_absolute_bound seed time nonnegative regular wave i j response outside l m outer) upperSums
  have generated := NativeUnheatedTriadSum.absolute_bound (positiveKernel nu) (cap nu) (positiveKernel_bound nu)
    wave 0 j outside (scalarLift A) U U
  rw [scalarLift_norm] at generated
  have vel : ‖U‖ ≤ NativeUnifiedCompleteSource.budget seed :=
    (wholeVelocity_norm_le (velocity seed time)).trans (velocity_bound seed time)
  have aPaid := source_envelope_norm_le seed time nonnegative regular
  have scalar0 : 0 ≤ 3 * cap nu * ‖NativeUnheatedTriadSum.weights‖ := by unfold cap; positivity [nu.coeff_pos]
  have budget0 := (norm_nonneg U).trans vel
  have a0 := mul_nonneg (Real.sqrt_nonneg constant) (mass_nonnegative seed time)
  have paid := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left aPaid scalar0) vel (norm_nonneg _)
    (mul_nonneg scalar0 a0)) vel (norm_nonneg _) (mul_nonneg (mul_nonneg scalar0 a0) budget0)
  exact (compare.trans generated).trans (paid.trans_eq (by dsimp only [bound]; ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticSource
