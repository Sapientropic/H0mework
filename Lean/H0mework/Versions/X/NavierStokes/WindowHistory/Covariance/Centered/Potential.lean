import H0mework.Versions.X.NavierStokes.WindowSchurMean.CenteredResidualCost
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.RelativeCreation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeCenteredPotential
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier (Torus)
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem waveTest_polynomial (M : ℕ) (l : wholePhysical) (i : Coordinate) :
    NativeCompleteCovariance.polynomial (NativeWindowHistoryMeanWeightedResidualTest.waveTest M l i)=
      NativeWindowStressOseenTest.evaluate (modes M) (modes M) i
        (NativeWholeH1Mixed.restrict M l) := by
  apply ContinuousMap.ext
  intro x
  simp only [NativeWindowHistoryMeanWeightedResidualTest.waveTest,map_sum,map_add,
    NativeWindowStressOseenTest.evaluate_apply,ContinuousMap.sum_apply]
  simp [NativeCompleteCovariance.polynomial,NativeCompleteCovariance.character,
    NativeCompleteCovariance.component,NativeWindowStressHeatBalance.basis]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k inside
  rw [NativeWholeH1Mixed.restrict_row,if_pos inside,UnitAddTorus.mFourier_neg]
  simp only [Complex.conj_re,Complex.conj_im]
  ring

theorem source_trace_norm_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (N : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    ‖NativeWindowStressHeatSource.physical
        (NativeWindowHistoryCreationCovariance.trace seed N time)‖≤
      NativeWindowHistoryCreationSource.densityBudget seed horizon := by
  let f:=NativeWindowHistoryCreationCovariance.trace seed N time
  let s:=NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube N)
  have point (x : Torus) : f x ≤ s x :=
    NativeWindowHistoryCreationCovariance.trace_le_stress seed N time inside.1 x
  have first : Integrable (fun x : Torus => (f x)^2) :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have last : Integrable (fun x : Torus => (s x)^2) :=
    (s.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have integrated := integral_mono first last (fun x =>
    pow_le_pow_left₀ (NativeWindowHistoryCreationCovariance.trace_nonnegative seed N time x) (point x) 2)
  have normed : ‖NativeWindowStressHeatSource.physical f‖^2≤
      ‖NativeWindowStressHeatSource.physical s‖^2 := by
    rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,
      NativeWindowStressHeatSource.physical_inner,NativeWindowStressHeatSource.physical_inner]
    simpa only [pow_two] using integrated
  have comparison : ‖NativeWindowStressHeatSource.physical f‖≤
      ‖NativeWindowStressHeatSource.physical s‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp normed
  exact comparison.trans (NativeWindowHistoryCreationSource.trace_bound seed N time horizon inside)

theorem source_budget_cap (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilon : ℝ) (positive : 0<epsilon) (N : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) :
    NativeWindowHistoryCreationForm.budget
      ‖NativeWindowStressHeatSource.physical
        (NativeWindowHistoryCreationCovariance.trace seed N time)‖
      (epsilon*(2*Real.pi)^2)≤
        NativeWindowHistoryCreationSource.budget seed horizon epsilon := by
  have bound := source_trace_norm_bound seed horizon N time inside
  have power := pow_le_pow_left₀
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left bound (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  unfold NativeWindowHistoryCreationSource.budget NativeWindowHistoryCreationForm.budget
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))

theorem finite_potential_read (seed : GeneratedWholeRestartCurrent nu)
    (N : ℕ) (time : ℝ) (M : ℕ) (v : NativeFiniteActionResolvent.physicalSpace (modes M)) :
    (∫x : Torus,NativeWindowHistoryCreationCovariance.trace seed N time x*
      NativeWindowHistoryCreationGeometry.square (modes M) v x)=
        ∑i : Coordinate,∫x : Torus,
          NativeWindowHistoryCreationCovariance.trace seed N time x*
            (NativeWindowStressOseenTest.evaluate (modes M) (modes M) i v x)^2 := by
  simp only [NativeWindowHistoryCreationGeometry.square,ContinuousMap.sum_apply,
    Finset.mul_sum,← pow_two,ContinuousMap.pow_apply]
  exact integral_finsetSum Finset.univ (fun i _ =>
    ((NativeWindowHistoryCreationCovariance.trace seed N time).continuous.mul
      ((NativeWindowStressOseenTest.evaluate (modes M) (modes M) i v).continuous.pow 2))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

def fullPotential (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M : ℕ)
    (v : NativeFiniteActionResolvent.physicalSpace (modes M)) : ℝ :=
  ∑i : Coordinate,∫x : Torus,NativeCenteredCovariance.fullTrace seed time x*
    (NativeWindowStressOseenTest.evaluate (modes M) (modes M) i v x)^2

theorem source_fullPotential_form_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilon : ℝ) (positive : 0<epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon)
    (v : NativeFiniteActionResolvent.physicalSpace (modes M)) :
    fullPotential seed time M v≤
      epsilon*NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1+
        NativeWindowHistoryCreationSource.budget seed horizon epsilon*
          NativeFiniteActionResolvent.pairing (modes M) v v := by
  have tends : Tendsto (fun N => ∑i : Coordinate,∫x : Torus,
      NativeWindowHistoryCreationCovariance.trace seed N time x*
        (NativeWindowStressOseenTest.evaluate (modes M) (modes M) i v x)^2)
      atTop (𝓝 (fullPotential seed time M v)) := by
    dsimp only [fullPotential]
    exact tendsto_finsetSum Finset.univ (fun i _ =>
      NativeCenteredCovariance.trace_square_tendsto seed time inside.1
        (NativeWindowStressOseenTest.evaluate (modes M) (modes M) i v))
  apply le_of_tendsto tends
  apply Eventually.of_forall
  intro N
  have source := NativeWindowHistoryCreationGeometry.square_absorption
    (NativeWindowHistoryCreationCovariance.trace seed N time)
    (modes M) (modes_zero M) (modes_closed M) v epsilon positive
  rw [finite_potential_read seed N time M v] at source
  have cap := source_budget_cap seed horizon epsilon positive N time inside
  have mass0 : 0≤NativeFiniteActionResolvent.pairing (modes M) v v :=
    real_inner_self_nonneg (x := NativeFiniteActionResolvent.coefficients (modes M) v)
  exact source.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right cap mass0))

theorem centeredWCost_fullPotential (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) :
    NativeCenteredCovariance.centeredWCost seed M time=
      fullPotential seed time M
        (NativeWholeH1Mixed.restrict M
          (NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
            (NativeWindowHistoryMeanProjection.mean
              (NativeWindowTraceWholeHistory.finiteHistory seed time M)))) := by
  unfold NativeCenteredCovariance.centeredWCost NativeCenteredCovariance.centeredActionCost fullPotential
  simp_rw [waveTest_polynomial]

theorem source_centeredWCost_form_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →
      let l:=NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
        (NativeWindowHistoryMeanProjection.mean
          (NativeWindowTraceWholeHistory.finiteHistory seed time M))
      let v:=NativeWholeH1Mixed.restrict M l
      NativeCenteredCovariance.centeredWCost seed M time≤
        epsilon*NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1+
          C*NativeFiniteActionResolvent.pairing (modes M) v v := by
  refine ⟨NativeWindowHistoryCreationSource.budget seed horizon epsilon,
    NativeWindowHistoryCreationSource.budget_nonnegative seed horizon epsilon positive,
    fun M time inside => ?_⟩
  dsimp only
  rw [centeredWCost_fullPotential]
  exact source_fullPotential_form_bound seed horizon epsilon positive M time inside _

theorem source_spatial_cost_with_centered_form (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C D : ℝ,0≤C ∧0≤D ∧∀M≥low,∀time∈Icc 0 horizon,
      let l:=NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
        (NativeWindowHistoryMeanProjection.mean
          (NativeWindowTraceWholeHistory.finiteHistory seed time M))
      let v:=NativeWholeH1Mixed.restrict M l
      (nu.coeff/4)*‖l‖^2≤
        Real.sqrt (NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon)*
          Real.sqrt (epsilon*NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1+
            C*NativeFiniteActionResolvent.pairing (modes M) v v)+D := by
  obtain ⟨C,C0,form⟩:=source_centeredWCost_form_bound seed horizon epsilon positive
  obtain ⟨low,D,D0,cost⟩:=NativeCenteredCovariance.source_centered_spatial_cost seed horizon
  refine ⟨low,C,D,C0,D0,fun M above time inside => ?_⟩
  dsimp only
  let l:=NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
    (NativeWindowHistoryMeanProjection.mean
      (NativeWindowTraceWholeHistory.finiteHistory seed time M))
  let v:=NativeWholeH1Mixed.restrict M l
  have bounded:=form M time inside
  dsimp only at bounded
  have sqrtBound:=Real.sqrt_le_sqrt bounded
  have scale:=mul_le_mul_of_nonneg_left sqrtBound
    (Real.sqrt_nonneg (NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon))
  exact (cost M above time inside).trans (add_le_add_left scale D)

end
end SaturationMonoid.NavierStokes.NativeCenteredPotential
