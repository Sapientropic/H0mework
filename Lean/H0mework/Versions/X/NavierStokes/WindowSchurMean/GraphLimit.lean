import H0mework.Versions.X.NavierStokes.WindowSchurMean.Graph
import H0mework.Versions.X.NavierStokes.WindowSchurMean.Recovery

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanGraphLimit
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open NativeResolventCompactness (State Wave)
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowHistoryMeanForceResolution (resolved)
open NativeWindowHistorySchurTemporalControl (temporalResponse)
noncomputable section
variable {nu : Viscosity}

theorem laplacian_row (nu : Viscosity) (M : ℕ) (v : wholePhysical) (k : Wave) :
    (laplacianFiber nu M v).1 k=
      if k.1∈modes M then integerWaveViscousMultiplier k.1 • v.1 k else 0 := by
  classical
  apply PiLp.ext
  intro i
  change (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)).1 k.1 i=_
  rw [NativeWindowOperatorGreen.laplacian_row]
  change integerWaveViscousMultiplier k.1 •
    (complexSharpSupportProjection (modes M) (NativeEndpointVelocityCarrier.wholeVelocity v.1)) k.1 i=_
  rw [complexSharpSupportProjection_apply]
  by_cases member:k.1∈modes M
  · rw [if_pos member,if_pos member,NativeEndpointVelocityCarrier.wholeVelocity_nonzero]
    rfl
  · simp only [if_neg member,Pi.zero_apply,smul_zero,PiLp.zero_apply]

theorem source_row_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time) (k : Wave) :
    Tendsto (fun M => (laplacianFiber nu M (mean (resolved seed M time))).1 k) atTop
      (𝓝 (integerWaveViscousMultiplier k.1 • (NativeForwardWindowSource.source seed time).fst k)) := by
  have original:=(lp.evalCLM ℝ (fun _ : Wave => EuclideanSpace ℂ Coordinate) 2 k).continuous.tendsto _ |>.comp
    (NativeWindowHistoryMeanRecovery.source_tendsto seed time nonnegative)
  apply (original.const_smul (integerWaveViscousMultiplier k.1)).congr'
  filter_upwards [nonzero_integerWave_eventually_mem_puncturedFrequencyCube k.1 k.2] with M member
  exact ((laplacian_row nu M (mean (resolved seed M time)) k).trans (if_pos member)).symm

theorem state_square (v : State) :
    (∑'k : Wave,ENNReal.ofReal (‖v k‖^2))=ENNReal.ofReal (‖v‖^2) := by
  have sum:HasSum (fun k : Wave => ‖v k‖^2) (‖v‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p:=(2:ℝ≥0∞)) (by norm_num) v
  exact (ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg ‖v k‖) sum.summable).symm.trans
    (congrArg ENNReal.ofReal sum.tsum_eq)

theorem state_fatou (v : ℕ → State) (limit : Wave → EuclideanSpace ℂ Coordinate)
    (converges : ∀k,Tendsto (fun M => v M k) atTop (𝓝 (limit k))) :
    (∑'k : Wave,ENNReal.ofReal (‖limit k‖^2))≤liminf (fun M => ENNReal.ofReal (‖v M‖^2)) atTop := by
  have row (k : Wave) : liminf (fun M => ENNReal.ofReal (‖v M k‖^2)) atTop=ENNReal.ofReal (‖limit k‖^2) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((converges k).norm.pow 2)).liminf_eq
  have fatou:=lintegral_liminf_le (u:=(atTop : Filter ℕ)) (μ:=(Measure.count : Measure Wave))
    (fun M => measurable_of_countable (fun k => ENNReal.ofReal (‖v M k‖^2)))
  simpa only [row,lintegral_count,state_square] using fatou

def velocityCost (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ℝ≥0∞ :=
  ∑'k : Wave,ENNReal.ofReal (‖integerWaveViscousMultiplier k.1 • (NativeForwardWindowSource.source seed time).fst k‖^2)

def residualCost (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ℝ≥0∞ :=
  liminf (fun M => ENNReal.ofReal (‖laplacianAction nu M (temporalResponse seed M time)‖^2)) atTop

theorem source_fatou (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time) :
    velocityCost seed time≤
      liminf (fun M => ENNReal.ofReal (‖laplacianFiber nu M (mean (resolved seed M time))‖^2)) atTop :=
  state_fatou (fun M => (laplacianFiber nu M (mean (resolved seed M time))).1) _
    (source_row_tendsto seed time nonnegative)

private theorem liminf_affine (a C : ℝ≥0∞) (finite : a≠⊤) (v : ℕ → ℝ≥0∞) :
    liminf (fun M => a*v M+C) atTop=a*liminf v atTop+C := by
  have monotone : Monotone (fun x : ℝ≥0∞ => a*x+C) := by
    intro x y le
    exact add_le_add (mul_le_mul_of_nonneg_left le (show 0≤a from bot_le)) le_rfl
  exact (monotone.map_liminf_of_continuousAt v
    ((ENNReal.continuous_const_mul finite).add continuous_const).continuousAt).symm

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧∀ time∈Icc 0 horizon,
      velocityCost seed time≤ENNReal.ofReal epsilon*residualCost seed time+ENNReal.ofReal C := by
  obtain ⟨low,C,C0,source⟩:=NativeWindowHistoryMeanGraph.source_mean_graph (nu:=nu) seed horizon nonnegative epsilon positive
  refine ⟨C,C0,fun time inside => ?_⟩
  have eventual:∀ᶠ M : ℕ in atTop,
      ENNReal.ofReal (‖laplacianFiber nu M (mean (resolved seed M time))‖^2)≤
        ENNReal.ofReal epsilon*ENNReal.ofReal (‖laplacianAction nu M (temporalResponse seed M time)‖^2)+ENNReal.ofReal C := by
    filter_upwards [eventually_ge_atTop low] with M above
    have paid:=ENNReal.ofReal_le_ofReal (source M above time inside)
    rw [ENNReal.ofReal_add (mul_nonneg positive.le (sq_nonneg _)) C0,ENNReal.ofReal_mul positive.le] at paid
    exact paid
  exact (source_fatou seed time inside.1).trans ((liminf_le_liminf eventual).trans_eq
    (liminf_affine (ENNReal.ofReal epsilon) (ENNReal.ofReal C) ENNReal.ofReal_ne_top _))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem velocityCost_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    velocityCost seed (step.2.clockAdvance+time)=velocityCost step.1 time :=
  congrArg (fun v : State => ∑'k : Wave,ENNReal.ofReal (‖integerWaveViscousMultiplier k.1 • v k‖^2))
    (congrArg (fun v => v.fst) (NativeForwardWindowSource.source_next seed step generated time nonnegative))

theorem residualCost_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    residualCost seed (step.2.clockAdvance+time)=residualCost step.1 time :=
  congrArg (fun u : ℕ → NativeWindowHistoryOseen.H =>
    liminf (fun M => ENNReal.ofReal (‖laplacianAction nu M (u M)‖^2)) atTop)
      (funext fun M => NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanGraphLimit
