import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Complete.Carrier

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeCompleteCovariance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
noncomputable section
local instance variationalPhysicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance variationalPhysicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}
private theorem quadratic_bound (L B C : ℝ) (B0 : 0 ≤ B) (C0 : 0 ≤ C)
    (paid : ∀a : ℝ,2*a*L ≤ C+a^2*B) : L^2 ≤ C*B := by
  by_cases zero : B=0
  · have Lzero : L=0 := by
      by_contra nonzero
      have h:=paid ((C+1)/(2*L))
      rw [zero,mul_zero,add_zero] at h
      have left : 2*((C+1)/(2*L))*L=C+1 := by field_simp
      rw [left] at h
      linarith only [h]
    simp only [Lzero,zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,le_refl]
  · have Bpos : 0 < B := lt_of_le_of_ne B0 (Ne.symm zero)
    have h:=mul_le_mul_of_nonneg_left (paid (L/B)) B0
    have first : B*(2*(L/B)*L)=2*L^2 := by field_simp
    have last : B*(C+(L/B)^2*B)=B*C+L^2 := by field_simp
    rw [first,last] at h
    nlinarith only [h]
private theorem weighted_young (r m u a : ℝ) (positive : 0 < r) :
    2*a*(u*m) ≤ m^2/r+a^2*(r*u^2) := by
  have paid:=div_nonneg (sq_nonneg (m-a*r*u)) positive.le
  have same : (m-a*r*u)^2/r=m^2/r-2*a*(u*m)+a^2*(r*u^2) := by field_simp; ring
  rw [same] at paid
  linarith only [paid]

private theorem current_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Continuous (NativeWindowHistoryCovarianceCurrent.value seed M time) := by
  have same : NativeWindowHistoryCovarianceCurrent.value seed M time=
      NativeWindowAbsoluteTimePhysicalCurrent.currentRead seed M time 0 := by
    funext x
    exact congrArg Complex.re (NativeWindowAbsoluteTimePhysicalCurrent.current_read seed M time 0 x)
  rw [same]
  exact (NativeWindowAbsoluteTimePhysicalCurrent.currentRead seed M time 0).continuous

private theorem component_square (m : Coordinate → ℝ) (i : Coordinate) : (m i)^2 ≤ ∑j,(m j)^2 :=
  Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

set_option backward.isDefEq.respectTransparency false in
private theorem finite_variational (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (i : Coordinate) (g : C(Torus,ℝ)) (a : ℝ) :
    2*a*(∫x : Torus,g x*NativeWindowHistoryCovarianceMetric.momentum seed M time i x) ≤
      8*NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon+
        a^2*(∫x : Torus,NativeWindowHistoryCovarianceCurrent.value seed M time x*(g x)^2) := by
  let r:=NativeWindowHistoryCovarianceCurrent.value seed M time
  let n:=NativeWindowHistoryCovarianceBudget.numerator seed M time
  let m:=NativeWindowHistoryCovarianceMetric.momentum seed M time i
  have positive (x : Torus) : 0 < r x := by
    linarith [(NativeWindowHistoryCovarianceCurrent.lower seed M time inside.1 x).1]
  have rc : Continuous r:=current_continuous seed M time
  have nc : Continuous n:=continuous_finsetSum _ (fun j _ =>
    (NativeWindowHistoryCovarianceMetric.momentum seed M time j).continuous.pow 2)
  have regularN : Integrable (fun x : Torus => n x/r x) :=
    (nc.div rc (fun x => (positive x).ne')).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have regularG : Integrable (fun x : Torus => r x*(g x)^2) :=
    (rc.mul (g.continuous.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have regularL : Integrable (fun x : Torus => g x*m x) :=
    (g.continuous.mul m.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have point (x : Torus) : 2*a*(g x*m x) ≤ n x/r x+a^2*(r x*(g x)^2) := by
    have row : (m x)^2 ≤ n x := component_square
      (fun j => NativeWindowHistoryCovarianceMetric.momentum seed M time j x) i
    exact (weighted_young (r x) (m x) (g x) a (positive x)).trans
      (add_le_add (div_le_div_of_nonneg_right row (positive x).le) le_rfl)
  have integrated:=integral_mono (regularL.const_mul (2*a)) (regularN.add (regularG.const_mul (a^2))) point
  simp only [Pi.add_apply] at integrated
  rw [integral_add regularN (regularG.const_mul (a^2)),integral_const_mul,integral_const_mul] at integrated
  exact integrated.trans (add_le_add (NativeWindowHistoryCovarianceBudget.source seed horizon M time inside) le_rfl)

set_option backward.isDefEq.respectTransparency false in
theorem source_variational (seed : GeneratedWholeRestartCurrent nu) (horizon time : ℝ)
    (inside : time∈Icc 0 horizon) (i : Coordinate) (c : Test) (a : ℝ) :
    2*a*action seed time i c ≤ 8*NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon+
      a^2*‖testMap seed time c‖^2 := by
  rw [weighted_square]
  exact le_of_tendsto_of_tendsto ((finite_action_tendsto seed time i c).const_mul (2*a))
    (tendsto_const_nhds.add ((density_square_tendsto seed time (polynomial c)).const_mul (a^2)))
    (Eventually.of_forall fun M => finite_variational seed horizon M time inside i (polynomial c) a)


def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  8*NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ budget seed horizon := by
  unfold budget NativeWindowHistorySchurTemporalControl.gradientBudget
  positivity

theorem source_test_bound (seed : GeneratedWholeRestartCurrent nu) (horizon time : ℝ)
    (inside : time∈Icc 0 horizon) (i : Coordinate) (c : Test) :
    ‖action seed time i c‖ ≤ Real.sqrt (budget seed horizon)*‖testMap seed time c‖ := by
  have paid:=quadratic_bound (action seed time i c) (‖testMap seed time c‖^2) (budget seed horizon)
    (sq_nonneg _) (budget_nonnegative seed horizon) (source_variational seed horizon time inside i c)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt (budget_nonnegative seed horizon)] using paid

end
end SaturationMonoid.NavierStokes.NativeCompleteCovariance
