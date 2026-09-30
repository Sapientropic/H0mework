import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.StressLimit
import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Physical
import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.TimeAction
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeMixedHeatLimit
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open NativeFullOrderAction NativeFullOrderSynthesis NativeWindowSpacetimeFourier
noncomputable section

section LocalSeries
variable {Index E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem local_iterated_tsum (f : Index → E → F) (smooth : ∀ i, ContDiff ℝ ∞ (f i))
    {domain : Set E} (opened : IsOpen domain) (convex : Convex ℝ domain)
    (bound : ℕ → Index → ℝ) (paid : ∀ n, Summable (bound n))
    (bounded : ∀ n i x, x ∈ domain → ‖iteratedFDeriv ℝ n (f i) x‖ ≤ bound n i)
    (n : ℕ) (x : E) (inside : x ∈ domain) :
    iteratedFDeriv ℝ n (fun y => ∑' i, f i y) x = ∑' i, iteratedFDeriv ℝ n (f i) x := by
  induction n generalizing x with
  | zero =>
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ n previous =>
    have germ : iteratedFDeriv ℝ n (fun y => ∑' i, f i y) =ᶠ[𝓝 x]
        fun y => ∑' i, iteratedFDeriv ℝ n (f i) y := by
      filter_upwards [opened.mem_nhds inside] with y member
      exact previous y member
    have differentiable (i : Index) : Differentiable ℝ (iteratedFDeriv ℝ n (f i)) :=
      (smooth i).differentiable_iteratedFDeriv
        (by exact_mod_cast (show (n : ℕ∞) < ⊤ from WithTop.coe_lt_top n))
    have derivative := hasFDerivAt_tsum_of_isPreconnected (paid (n+1)) opened convex.isPreconnected
      (fun i y _ => (differentiable i y).hasFDerivAt)
      (fun i y member => by rw [norm_fderiv_iteratedFDeriv]; exact bounded (n+1) i y member)
      inside ((paid n).of_norm_bounded (fun i => bounded n i x inside)) inside
    simp only [iteratedFDeriv_succ_eq_comp_left,Function.comp_def]
    rw [germ.fderiv_eq, derivative.fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm.toContinuousLinearEquiv.map_tsum

theorem multiplier_jet_error (f : Index → E → F) (smooth : ∀ i, ContDiff ℝ ∞ (f i))
    {domain : Set E} (opened : IsOpen domain) (convex : Convex ℝ domain)
    (bound : ℕ → Index → ℝ) (paid : ∀ n, Summable (bound n))
    (nonnegative : ∀ n i, 0 ≤ bound n i)
    (bounded : ∀ n i x, x ∈ domain → ‖iteratedFDeriv ℝ n (f i) x‖ ≤ bound n i)
    (multiplier : Index → ℝ) (low : ∀ i, 0 ≤ multiplier i) (high : ∀ i, multiplier i ≤ 1)
    (n : ℕ) (x : E) (inside : x ∈ domain) :
    ‖iteratedFDeriv ℝ n (fun y => ∑' i, multiplier i • f i y) x -
      iteratedFDeriv ℝ n (fun y => ∑' i, f i y) x‖ ≤ ∑' i, (1-multiplier i)*bound n i := by
  have scaled (j : ℕ) (i : Index) (y : E) :
      iteratedFDeriv ℝ j (fun y => multiplier i • f i y) y = multiplier i • iteratedFDeriv ℝ j (f i) y :=
    iteratedFDeriv_const_smul_apply ((smooth i).of_le
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt
  have scaled_bound (j : ℕ) (i : Index) (y : E) (member : y ∈ domain) :
      ‖iteratedFDeriv ℝ j (fun y => multiplier i • f i y) y‖ ≤ bound j i := by
    rw [scaled,norm_smul,Real.norm_of_nonneg (low i)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (high i)).trans (bounded j i y member)
  rw [local_iterated_tsum _ (fun i => (smooth i).const_smul (multiplier i)) opened convex bound paid scaled_bound n x inside,
    local_iterated_tsum f smooth opened convex bound paid bounded n x inside]
  have basePaid := (paid n).of_norm_bounded (fun i => bounded n i x inside)
  have scaledPaid := (paid n).of_norm_bounded (fun i => scaled_bound n i x inside)
  rw [← scaledPaid.tsum_sub basePaid]
  have errorPaid : Summable (fun i => (1-multiplier i)*bound n i) :=
    (paid n).of_nonneg_of_le (fun i => mul_nonneg (sub_nonneg.mpr (high i)) (nonnegative n i))
      (fun i => mul_le_of_le_one_left (nonnegative n i) (sub_le_self 1 (low i)))
  have errorBound (i : Index) :
      ‖iteratedFDeriv ℝ n (fun y => multiplier i • f i y) x - iteratedFDeriv ℝ n (f i) x‖ ≤
        (1-multiplier i)*bound n i := by
    have difference : multiplier i • iteratedFDeriv ℝ n (f i) x - iteratedFDeriv ℝ n (f i) x =
        (multiplier i-1) • iteratedFDeriv ℝ n (f i) x := by rw [sub_smul,one_smul]
    rw [scaled,difference,norm_smul,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (high i)),neg_sub]
    exact mul_le_mul_of_nonneg_left (bounded n i x inside) (sub_nonneg.mpr (high i))
  have norms := errorPaid.of_nonneg_of_le (fun i => norm_nonneg _) errorBound
  exact (norm_tsum_le_tsum_norm norms).trans (norms.tsum_le_tsum errorBound errorPaid)

theorem multiplier_jets_uniform {Parameter : Type*} {filter : Filter Parameter}
    (f : Index → E → F) (smooth : ∀ i, ContDiff ℝ ∞ (f i))
    {domain : Set E} (opened : IsOpen domain) (convex : Convex ℝ domain)
    (bound : ℕ → Index → ℝ) (paid : ∀ n, Summable (bound n))
    (nonnegative : ∀ n i, 0 ≤ bound n i)
    (bounded : ∀ n i x, x ∈ domain → ‖iteratedFDeriv ℝ n (f i) x‖ ≤ bound n i)
    (multiplier : Parameter → Index → ℝ) (low : ∀ p i, 0 ≤ multiplier p i)
    (high : ∀ p i, multiplier p i ≤ 1)
    (converges : ∀ i, Tendsto (fun p => multiplier p i) filter (𝓝 1)) (n : ℕ) :
    TendstoUniformlyOn
      (fun p => iteratedFDeriv ℝ n (fun y => ∑' i, multiplier p i • f i y))
      (iteratedFDeriv ℝ n (fun y => ∑' i, f i y)) filter domain := by
  have limit : Tendsto (fun p => ∑' i, (1-multiplier p i)*bound n i) filter (𝓝 0) := by
    have result := tendsto_tsum_of_dominated_convergence (bound := bound n) (g := fun _ => (0 : ℝ))
      (f := fun p i => (1-multiplier p i)*bound n i) (𝓕 := filter)
      (paid n) (fun i => by
        have one : Tendsto (fun _ : Parameter => (1 : ℝ)) filter (𝓝 1) := tendsto_const_nhds
        simpa only [sub_self,zero_mul] using (one.sub (converges i)).mul_const (bound n i))
      (Eventually.of_forall fun p i => by
        rw [Real.norm_of_nonneg (mul_nonneg (sub_nonneg.mpr (high p i)) (nonnegative n i))]
        exact mul_le_of_le_one_left (nonnegative n i) (sub_le_self 1 (low p i)))
    simpa only [tsum_zero] using result
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon positive
  filter_upwards [limit.eventually (gt_mem_nhds positive)] with p small
  intro x inside
  rw [dist_comm,dist_eq_norm]
  exact (multiplier_jet_error f smooth opened convex bound paid nonnegative bounded
    (multiplier p) (low p) (high p) n x inside).trans_lt small

end LocalSeries
end
end SaturationMonoid.NavierStokes.NativeMixedHeatLimit
