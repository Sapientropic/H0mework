import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Current
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.PhysicalStress

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceLimit
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private abbrev read : C(Torus,ℝ) →L[ℝ] Lp ℝ 1 (volume : Measure Torus) :=
  ContinuousMap.toLp 1 volume ℝ

def value (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Lp ℝ 1 (volume : Measure Torus) :=
  read (ContinuousMap.const Torus (2:ℝ))-
    (1/8:ℝ) • (∑ i : Coordinate,NativeWindowAbsoluteTimePhysicalStress.stress seed time i i)

private theorem finite_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    read (NativeWindowAbsoluteTimePhysicalCurrent.currentRead seed M time 0)=
      read (ContinuousMap.const Torus (2:ℝ))+
        (1/8:ℝ) • (∑i : Coordinate,read (NativeWindowFiniteGramFourier.stress seed time
          (NativeWholeH1Mixed.modes M) i i)) := by
  simp only [read,NativeWindowAbsoluteTimePhysicalCurrent.currentRead,Fin.cases_zero,map_add,
    map_smul,map_sum]

private theorem finite_stress (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i : Coordinate) :
    Tendsto (fun M => read (NativeWindowFiniteGramFourier.stress seed time
      (NativeWholeH1Mixed.modes M) i i)) atTop
      (𝓝 (-NativeWindowAbsoluteTimePhysicalStress.stress seed time i i)) := by
  have source:=NativeWindowAbsoluteTimePhysicalStress.stress_tendsto seed time i i
  simpa only [Function.comp_def,neg_neg] using source.neg

theorem source_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Tendsto (fun M => read (NativeWindowAbsoluteTimePhysicalCurrent.currentRead seed M time 0)) atTop
      (𝓝 (value seed time)) := by
  have source:=tendsto_finsetSum Finset.univ (fun i _ => finite_stress seed time i)
  have last := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/8:ℝ)) atTop (𝓝 (1/8:ℝ))).smul source
  have constant : Tendsto (fun _ : ℕ => read (ContinuousMap.const Torus (2:ℝ))) atTop
      (𝓝 (read (ContinuousMap.const Torus (2:ℝ)))) := tendsto_const_nhds
  have total := constant.add last
  simpa only [finite_read,value,sub_eq_add_neg,Finset.sum_neg_distrib,smul_neg,neg_smul] using total


set_option backward.isDefEq.respectTransparency false in
theorem source_lower (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ∀ᵐ x ∂(volume : Measure Torus),2≤value seed time x := by
  have each (i : Coordinate) : ∀ᵐ x ∂(volume : Measure Torus),
      NativeWindowAbsoluteTimePhysicalStress.stress seed time i i x≤0 := by
    filter_upwards [NativeWindowAbsoluteTimePhysicalStress.stress_ae seed time i i] with x actual
    rw [actual,real_inner_self_eq_norm_sq]
    exact neg_nonpos.mpr (sq_nonneg _)
  have all : ∀ᵐ x ∂(volume : Measure Torus),
      (∑i : Coordinate,NativeWindowAbsoluteTimePhysicalStress.stress seed time i i x)≤0 := by
    filter_upwards [each 0,each 1,each 2] with x h0 h1 h2
    simp only [Fin.sum_univ_three]
    linarith only [h0,h1,h2]
  have constant : read (ContinuousMap.const Torus (2:ℝ))=ᵐ[volume] fun _ : Torus => (2:ℝ) := by
    have raw:=ContinuousMap.coeFn_toLp (p := (1:ℝ≥0∞)) (𝕜 := ℝ)
      (volume : Measure Torus) (ContinuousMap.const Torus (2:ℝ))
    exact raw.trans (Eventually.of_forall fun x => by simp)
  let s:=fun i : Coordinate => NativeWindowAbsoluteTimePhysicalStress.stress seed time i i
  filter_upwards [Lp.coeFn_sub (read (ContinuousMap.const Torus (2:ℝ)))
      ((1/8:ℝ) • (∑i : Coordinate,s i)),
    Lp.coeFn_smul (1/8:ℝ) (∑i : Coordinate,s i),
    Lp.coeFn_finsetSum Finset.univ s,constant,all] with x hs hm hsum hc ha
  have nonpos : (∑i : Coordinate,s i x)≤0 := ha
  change 2≤(read (ContinuousMap.const Torus (2:ℝ))-(1/8:ℝ) • (∑i : Coordinate,s i)) x
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hm]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hsum,hc]
  simp only [Finset.sum_apply]
  nlinarith only [nonpos]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem value_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0≤time) :
    value seed (step.2.clockAdvance+time)=value step.1 time := by
  simp only [value,NativeWindowAbsoluteTimePhysicalStress.stress_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceLimit
