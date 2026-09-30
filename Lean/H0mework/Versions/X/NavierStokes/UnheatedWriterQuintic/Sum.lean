import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.SumWeights

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticSum
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeUnheatedQuinticWeights NativeUnheatedTriadSum NativeHigherTimeJets
noncomputable section

def term (kernel : Index → ℂ) (wave : IntegerWavevector) (i j l m : Coordinate)
    (L R U V : E) (index : Index) : ℂ :=
  kernel index*(L index.2 i*R (index.1.2-index.2) j*U (wave-index.1.1-index.1.2) l*V index.1.1 m)

def value (kernel : Index → ℂ) (wave : IntegerWavevector) (i j l m : Coordinate) (L R U V : E) : ℂ :=
  ∑' index, term kernel wave i j l m L R U V index

variable (kernel : Index → ℂ) (cap : ℝ) (wave : IntegerWavevector)
  (bounded : ∀ index, ‖kernel index‖ ≤ cap*eta (wave-index.1.1-index.1.2)*eta index.1.1)

include bounded

theorem budget_nonnegative : 0 ≤ cap := by
  have paid := (norm_nonneg (kernel ((0,wave),0))).trans (bounded ((0,wave),0))
  simpa only [sub_zero, sub_self, eta, NativeCompleteStressCarrier.weight, if_true, Real.one_rpow, mul_one] using paid

theorem point_bound (i j l m : Coordinate) (L R U V : E) (outer : Pair) (d : IntegerWavevector) :
    ‖term kernel wave i j l m L R U V (outer,d)‖ ≤
      (cap*eta (wave-outer.1-outer.2)*eta outer.1*‖U (wave-outer.1-outer.2)‖*‖V outer.1‖)*‖L d i*R (outer.2-d) j‖ := by
  have endpoint := mul_le_mul (norm_le_pi_norm (U (wave-outer.1-outer.2)) l) (norm_le_pi_norm (V outer.1) m)
    (norm_nonneg _) (norm_nonneg _)
  have coefficient := mul_le_mul (bounded (outer,d)) endpoint (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by positivity [budget_nonnegative kernel cap wave bounded, eta_nonnegative (wave-outer.1-outer.2), eta_nonnegative outer.1])
  have paid := mul_le_mul_of_nonneg_right coefficient (norm_nonneg (L d i*R (outer.2-d) j))
  convert! paid using 1 <;> simp only [term, norm_mul] <;> ring

theorem fiber_summable (i j l m : Coordinate) (L R U V : E) (outer : Pair) :
    Summable (fun d => ‖term kernel wave i j l m L R U V (outer,d)‖) :=
  (((mixed_pair_summable L R outer.2 j i).norm).mul_left
    (cap*eta (wave-outer.1-outer.2)*eta outer.1*‖U (wave-outer.1-outer.2)‖*‖V outer.1‖)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (point_bound kernel cap wave bounded i j l m L R U V outer)

theorem fiber_bound (i j l m : Coordinate) (L R U V : E) (outer : Pair) :
    (∑' d, ‖term kernel wave i j l m L R U V (outer,d)‖) ≤
      (3*cap*‖L‖*‖R‖)*plane wave U V outer := by
  have compare := (fiber_summable kernel cap wave bounded i j l m L R U V outer).tsum_le_tsum
    (point_bound kernel cap wave bounded i j l m L R U V outer)
    (((mixed_pair_summable L R outer.2 j i).norm).mul_left
      (cap*eta (wave-outer.1-outer.2)*eta outer.1*‖U (wave-outer.1-outer.2)‖*‖V outer.1‖))
  rw [tsum_mul_left] at compare
  exact compare.trans ((mul_le_mul_of_nonneg_left (NativeUnheatedPairInverseFlux.absolute_pair_bound L R outer.2 j i)
    (by positivity [budget_nonnegative kernel cap wave bounded, eta_nonnegative (wave-outer.1-outer.2), eta_nonnegative outer.1])).trans_eq
      (by unfold plane; ring))

theorem absolute_summable (i j l m : Coordinate) (L R U V : E) :
    Summable (fun index => ‖term kernel wave i j l m L R U V index‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fiber_summable kernel cap wave bounded i j l m L R U V,
    ((plane_summable wave U V).mul_left (3*cap*‖L‖*‖R‖)).of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
      (fiber_bound kernel cap wave bounded i j l m L R U V)⟩

theorem absolute_bound (i j l m : Coordinate) (L R U V : E) :
    (∑' index, ‖term kernel wave i j l m L R U V index‖) ≤
      (3*cap*‖etaL2‖^2)*‖L‖*‖R‖*‖U‖*‖V‖ := by
  have sums := absolute_summable kernel cap wave bounded i j l m L R U V
  rw [sums.tsum_prod]
  have compare := sums.prod.tsum_le_tsum (fiber_bound kernel cap wave bounded i j l m L R U V)
    ((plane_summable wave U V).mul_left (3*cap*‖L‖*‖R‖))
  rw [tsum_mul_left] at compare
  exact compare.trans ((mul_le_mul_of_nonneg_left (plane_bound wave U V)
    (by positivity [budget_nonnegative kernel cap wave bounded])).trans_eq (by ring))

theorem value_bound (i j l m : Coordinate) (L R U V : E) :
    ‖value kernel wave i j l m L R U V‖ ≤ (3*cap*‖etaL2‖^2)*‖L‖*‖R‖*‖U‖*‖V‖ :=
  (norm_tsum_le_tsum_norm (absolute_summable kernel cap wave bounded i j l m L R U V)).trans
    (absolute_bound kernel cap wave bounded i j l m L R U V)

omit bounded in
theorem value_measurable (i j l m : Coordinate) (L R U V : ℝ → E) (measure : Measure ℝ)
    (left : AEStronglyMeasurable L measure) (right : AEStronglyMeasurable R measure)
    (third : AEStronglyMeasurable U measure) (fourth : AEStronglyMeasurable V measure) :
    AEStronglyMeasurable (fun time => value kernel wave i j l m (L time) (R time) (U time) (V time)) measure := by
  have read (f : ℝ → E) (measured : AEStronglyMeasurable f measure) (k : IntegerWavevector) (coordinate : Coordinate) :
      AEStronglyMeasurable (fun time => f time k coordinate) measure :=
    ((ContinuousLinearMap.proj coordinate : (Coordinate → ℂ) →L[ℝ] ℂ).comp
      (lp.evalCLM ℝ (fun _ : IntegerWavevector => Coordinate → ℂ) 2 k)).continuous.comp_aestronglyMeasurable measured
  have rows (index : Index) : AEStronglyMeasurable (fun time => term kernel wave i j l m (L time) (R time) (U time) (V time) index) measure :=
    ((((read L left index.2 i).mul (read R right (index.1.2-index.2) j)).mul
      (read U third (wave-index.1.1-index.1.2) l)).mul (read V fourth index.1.1 m)).const_mul (kernel index)
  exact (AEMeasurable.tsum fun index => (rows index).aemeasurable).aestronglyMeasurable

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticSum
