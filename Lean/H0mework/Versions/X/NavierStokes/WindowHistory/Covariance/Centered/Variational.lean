import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.Trace

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeCenteredCovariance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowAbsoluteTimeFourier (Fiber Space physical field)
noncomputable section
local instance variationalPhysicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance variationalPhysicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem finite_centered_variational (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time∈Icc 0 horizon) (N : ℕ)
    (g : Coordinate→C(Torus,ℝ)) (a : ℝ) :
    2*a*(∑i : Coordinate,∫x : Torus,
      g i x*NativeWindowHistoryCovarianceMetric.momentum seed N time i x)≤
      NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon+
        a^2*(∑i : Coordinate,∫x : Torus,
          NativeWindowHistoryCreationCovariance.trace seed N time x*(g i x)^2) := by
  let m := fun i : Coordinate => NativeWindowHistoryCovarianceMetric.momentum seed N time i
  let q := NativeWindowHistoryCreationCovariance.trace seed N time
  let f := NativeWindowHistoryCovarianceMetric.fisher seed N time
  have point (x : Torus) := NativeWindowHistoryCovarianceMetric.momentum_test seed N time x
    (fun i => a*g i x)
  have leftRegular (i : Coordinate) : Integrable (fun x : Torus => g i x*m i x) :=
    ((g i).continuous.mul (m i).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have rightRegular (i : Coordinate) : Integrable (fun x : Torus => q x*(g i x)^2) :=
    (q.continuous.mul ((g i).continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have fisherRegular : Integrable (fun x : Torus => f x) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have integrated := integral_mono
    ((integrable_finsetSum Finset.univ (fun i _ => (leftRegular i).const_mul a)).const_mul 2)
    ((integrable_finsetSum Finset.univ (fun i _ => rightRegular i)).const_mul (a^2) |>.add fisherRegular)
    (fun x => by
      have h:=point x
      change 2*(∑i : Coordinate,a*(g i x*m i x))≤
        a^2*(∑i : Coordinate,q x*(g i x)^2)+f x
      have left : (∑i : Coordinate,a*(g i x*m i x))=
          ∑i : Coordinate,a*g i x*m i x := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      have right : a^2*(∑i : Coordinate,q x*(g i x)^2)=
          q x*(∑i : Coordinate,(a*g i x)^2) := by
        rw [← Finset.mul_sum]
        simp only [mul_pow,← Finset.mul_sum]
        ring
      rw [left,right]
      exact h)
  change (∫x : Torus,2*(∑i : Coordinate,a*(g i x*m i x)))≤
    ∫x : Torus,(a^2*(∑i : Coordinate,q x*(g i x)^2)+f x) at integrated
  rw [integral_const_mul,
    integral_finsetSum Finset.univ (fun i _ => (leftRegular i).const_mul a),
    integral_add ((integrable_finsetSum Finset.univ (fun i _ => rightRegular i)).const_mul (a^2))
      fisherRegular,integral_const_mul,
    integral_finsetSum Finset.univ (fun i _ => rightRegular i)] at integrated
  simp only [integral_const_mul] at integrated
  have energy := NativeWindowHistoryCovarianceMetric.fisher_original seed N time
  have paid := (NativeWindowHistoryMeanGradient.gradient_residual_le seed N _).trans
    (NativeWindowHistorySchurTemporalControl.source_gradient seed horizon N time inside)
  rw [energy] at integrated
  rw [← Finset.mul_sum] at integrated
  linarith only [integrated,paid]

def centeredActionCost (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (c : Coordinate→NativeCompleteCovariance.Test) : ℝ :=
  ∑i : Coordinate,∫x : Torus,fullTrace seed time x*
    (NativeCompleteCovariance.polynomial (c i) x)^2

theorem source_centered_variational (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time∈Icc 0 horizon)
    (c : Coordinate→NativeCompleteCovariance.Test) (a : ℝ) :
    2*a*(∑i : Coordinate,NativeCompleteCovariance.action seed time i (c i))≤
      NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon+
        a^2*centeredActionCost seed time c := by
  let g : Coordinate→C(Torus,ℝ) := fun i => NativeCompleteCovariance.polynomial (c i)
  have left : Tendsto (fun N => 2*a*(∑i : Coordinate,∫x : Torus,
      g i x*NativeWindowHistoryCovarianceMetric.momentum seed N time i x)) atTop
      (𝓝 (2*a*(∑i : Coordinate,NativeCompleteCovariance.action seed time i (c i)))) :=
    (tendsto_finsetSum Finset.univ (fun i _ =>
      NativeCompleteCovariance.finite_action_tendsto seed time i (c i))).const_mul (2*a)
  have right : Tendsto (fun N => NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon+
      a^2*(∑i : Coordinate,∫x : Torus,
        NativeWindowHistoryCreationCovariance.trace seed N time x*(g i x)^2)) atTop
      (𝓝 (NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon+
        a^2*centeredActionCost seed time c)) := by
    dsimp only [centeredActionCost]
    exact tendsto_const_nhds.add
      ((tendsto_finsetSum Finset.univ (fun i _ =>
        trace_square_tendsto seed time inside.1 (g i))).const_mul (a^2))
  exact le_of_tendsto_of_tendsto left right
    (Eventually.of_forall fun N => finite_centered_variational seed horizon time inside N g a)

theorem centeredActionCost_nonnegative (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (nonnegative : 0≤time)
    (c : Coordinate→NativeCompleteCovariance.Test) :
    0≤centeredActionCost seed time c := by
  let g : Coordinate→C(Torus,ℝ) := fun i => NativeCompleteCovariance.polynomial (c i)
  have tends : Tendsto (fun N => ∑i : Coordinate,∫x : Torus,
      NativeWindowHistoryCreationCovariance.trace seed N time x*(g i x)^2) atTop
      (𝓝 (centeredActionCost seed time c)) := by
    dsimp only [centeredActionCost]
    exact tendsto_finsetSum Finset.univ
      (fun i _ => trace_square_tendsto seed time nonnegative (g i))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds tends
  apply Eventually.of_forall
  intro N
  apply Finset.sum_nonneg
  intro i _
  apply integral_nonneg
  intro x
  exact mul_nonneg (NativeWindowHistoryCreationCovariance.trace_nonnegative seed N time x)
    (sq_nonneg _)

private theorem quadratic_bound (L B C : ℝ) (B0 : 0≤B) (C0 : 0≤C)
    (paid : ∀a : ℝ,2*a*L≤C+a^2*B) : L^2≤C*B := by
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

theorem source_centered_action_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time∈Icc 0 horizon)
    (c : Coordinate→NativeCompleteCovariance.Test) :
    ‖∑i : Coordinate,NativeCompleteCovariance.action seed time i (c i)‖≤
      Real.sqrt (NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon)*
        Real.sqrt (centeredActionCost seed time c) := by
  have B0:=centeredActionCost_nonnegative seed time inside.1 c
  have G0 : 0≤NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon := le_max_left _ _
  have paid:=quadratic_bound
    (∑i : Coordinate,NativeCompleteCovariance.action seed time i (c i))
    (centeredActionCost seed time c)
    (NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon) B0 G0
    (source_centered_variational seed horizon time inside c)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  simpa only [Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt G0,Real.sq_sqrt B0] using paid


end
end SaturationMonoid.NavierStokes.NativeCenteredCovariance
