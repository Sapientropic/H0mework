import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Coupling

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowMetricGraphGreen
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryOseen (H action forcingHistory)
open NativeWindowHistoryMeanProjection (embed mean projection)
open NativeWindowTraceWholeHistory (metric metricAction finiteHistory)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeWindowMetricGraphCoupling (coupling principalWork)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

private theorem residual_square (v : H) :
    NativeWindowHistoryMeanProjection.residual (NativeWindowHistoryMeanProjection.residual v)=
      NativeWindowHistoryMeanProjection.residual v := by
  change NativeWindowHistoryMeanProjection.residual v-projection (NativeWindowHistoryMeanProjection.residual v)=_
  rw [NativeWindowHistoryMeanProjection.projection_residual,sub_zero]

theorem mass_split (v : H) : ‖v‖^2=‖mean v‖^2+‖NativeWindowHistoryMeanProjection.residual v‖^2 := by
  have source := NativeWindowHistoryMeanProjection.energy_split v
  change ‖v‖^2=‖embed (mean v)‖^2+‖NativeWindowHistoryMeanProjection.residual v‖^2 at source
  simpa only [NativeWindowHistoryMeanProjection.embed_norm] using source

theorem graph_split (nu : Viscosity) (M : ℕ) (v : H) : ‖laplacianAction nu M v‖^2=
    ‖laplacianFiber nu M (mean v)‖^2+‖laplacianAction nu M (NativeWindowHistoryMeanProjection.residual v)‖^2 := by
  have source := mass_split (laplacianAction nu M v)
  change ‖laplacianAction nu M v‖^2=‖mean ((laplacianFiber nu M).compLpL 2 averageMeasure v)‖^2+
    ‖NativeWindowHistoryMeanProjection.residual ((laplacianFiber nu M).compLpL 2 averageMeasure v)‖^2 at source
  simpa only [NativeWindowHistoryMeanProjection.mean_comp,NativeWindowHistoryMeanProjection.residual_comp] using! source

private theorem embedded_heat (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (u : wholePhysical) :
    inner ℝ (embed u) (metricAction seed frame M F R (laplacianAction nu M (embed u)))=
      inner ℝ (metric seed frame M F R u) (laplacianFiber nu M u) := by
  change inner ℝ (embed u) ((metric seed frame M F R).compLpL 2 averageMeasure
    ((laplacianFiber nu M).compLpL 2 averageMeasure (embed u)))=_
  rw [NativeWindowHistoryMeanProjection.comp_embed,NativeWindowHistoryMeanProjection.comp_embed,
    NativeWindowHistoryMeanProjection.embed_inner,NativeWindowMetricGraphHistory.metric_symmetric]

private theorem diagonal_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A T : E →L[ℝ] E) (p q h : E) (same : p+q=h) :
    2*inner ℝ h (T (A h))=2*inner ℝ p (T (A p))+2*inner ℝ q (T (A q))+
      2*(inner ℝ p (T (A q))+inner ℝ q (T (A p))) := by
  rw [← same]
  simp only [map_add,inner_add_left,inner_add_right]
  ring

/-- Both diagonal advective blocks retain the original full-pressure action. -/
def diagonalWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : H) : ℝ :=
  2*inner ℝ (projection v) (metricAction seed frame M F R
    (action seed M time (projection v)+nu.coeff • laplacianAction nu M (projection v)))+
  2*inner ℝ (NativeWindowHistoryMeanProjection.residual v) (metricAction seed frame M F R
    (action seed M time (NativeWindowHistoryMeanProjection.residual v)+
      nu.coeff • laplacianAction nu M (NativeWindowHistoryMeanProjection.residual v)))

private theorem diagonal_heat {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (x a l : E) (n : ℝ) :
    inner ℝ x (T (a+n • l))=inner ℝ x (T a)+n*inner ℝ x (T l) := by
  rw [map_add,map_smul,inner_add_right,real_inner_smul_right]

theorem green_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : H) :
    2*inner ℝ v (metricAction seed frame M F R (action seed M time v))=
      principalWork seed M frame time F R (mean v) (NativeWindowHistoryMeanProjection.residual v)+
        diagonalWork seed M frame time F R v := by
  have original := diagonal_split (E := H) (action seed M time) (metricAction seed frame M F R)
    (projection v) (NativeWindowHistoryMeanProjection.residual v) v (NativeWindowHistoryMeanProjection.split v)
  have first := embedded_heat seed frame M F R (mean v)
  have last := NativeWindowMetricGraphHistory.action_symmetric seed frame M F R
    (NativeWindowHistoryMeanProjection.residual v) (laplacianAction nu M (NativeWindowHistoryMeanProjection.residual v))
  have d1 := diagonal_heat (E := H) (metricAction seed frame M F R) (projection v)
    (action seed M time (projection v)) (laplacianAction nu M (projection v)) nu.coeff
  have d2 := diagonal_heat (E := H) (metricAction seed frame M F R) (NativeWindowHistoryMeanProjection.residual v)
    (action seed M time (NativeWindowHistoryMeanProjection.residual v))
    (laplacianAction nu M (NativeWindowHistoryMeanProjection.residual v)) nu.coeff
  have cross : coupling seed M frame time F R (mean v) (NativeWindowHistoryMeanProjection.residual v)=
    inner ℝ (projection v) (metricAction seed frame M F R (action seed M time (NativeWindowHistoryMeanProjection.residual v)))+
    inner ℝ (NativeWindowHistoryMeanProjection.residual v) (metricAction seed frame M F R (action seed M time (projection v))) := by
    simp only [coupling,residual_square]
    rfl
  have meanRead : inner ℝ (embed (mean v)) (metricAction seed frame M F R (laplacianAction nu M (embed (mean v))))=
    inner ℝ (projection v) (metricAction seed frame M F R (laplacianAction nu M (projection v))) := rfl
  have principal : principalWork seed M frame time F R (mean v) (NativeWindowHistoryMeanProjection.residual v)=
    -2*nu.coeff*inner ℝ (projection v) (metricAction seed frame M F R (laplacianAction nu M (projection v)))-
      2*nu.coeff*inner ℝ (NativeWindowHistoryMeanProjection.residual v)
        (metricAction seed frame M F R (laplacianAction nu M (NativeWindowHistoryMeanProjection.residual v)))+
      2*coupling seed M frame time F R (mean v) (NativeWindowHistoryMeanProjection.residual v) := by
    have meanEquality := first.symm.trans meanRead
    simpa only [principalWork] using! congrArg₂
      (fun x y : ℝ => -2*nu.coeff*x-2*nu.coeff*y+
        2*coupling seed M frame time F R (mean v) (NativeWindowHistoryMeanProjection.residual v)) meanEquality last
  have expression : 2*inner ℝ v (metricAction seed frame M F R (action seed M time v))=
      (-2*nu.coeff*inner ℝ (projection v) (metricAction seed frame M F R (laplacianAction nu M (projection v)))-
        2*nu.coeff*inner ℝ (NativeWindowHistoryMeanProjection.residual v)
          (metricAction seed frame M F R (laplacianAction nu M (NativeWindowHistoryMeanProjection.residual v)))+
        2*coupling seed M frame time F R (mean v) (NativeWindowHistoryMeanProjection.residual v))+
        diagonalWork seed M frame time F R v := by
    unfold diagonalWork
    linarith only [original,cross,d1,d2]
  exact expression.trans (congrArg (fun x => x+diagonalWork seed M frame time F R v) principal.symm)

theorem source_green_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M : ℕ,
      ∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,∀ v : H,
      2*inner ℝ v (metricAction seed frame M (integerWaveFrequencyCube cutoff) radius (action seed M time v)) ≤
        -(nu.coeff^2/2)*‖laplacianAction nu M v‖^2+C*‖v‖^2+
          diagonalWork seed M frame time (integerWaveFrequencyCube cutoff) radius v := by
  have fact := @NativeWindowMetricGraphCoupling.source_principal_bound nu seed horizon nonnegative
  rcases fact with ⟨low,C,C0,paid⟩
  refine ⟨low,C,C0,fun radius above cutoff covered M frame frameInside time timeInside v => ?_⟩
  have bound := paid radius above cutoff covered M frame frameInside time timeInside (mean v)
    (NativeWindowHistoryMeanProjection.residual v)
  have read := congrArg₂ (fun x y : ℝ => -(nu.coeff^2/2)*x+C*y) (graph_split nu M v).symm (mass_split v).symm
  simpa only [] using! (green_split seed M frame time _ radius v).trans_le (add_le_add (bound.trans_eq read) le_rfl)

def sourceEnergy (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (finiteHistory seed time M) (metricAction seed frame M F R (finiteHistory seed time M))

def sourceRate (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : ℝ :=
  2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M F R
    (action seed M time (finiteHistory seed time M)+forcingHistory seed M time))

private theorem paired_derivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (symmetric : ∀ x y,inner ℝ (T x) y=inner ℝ x (T y))
    {f : ℝ → E} {d : E} {t : ℝ} (derivative : HasDerivAt f d t) :
    HasDerivAt (fun s => inner ℝ (f s) (T (f s))) (2*inner ℝ (f t) (T d)) t := by
  have last := T.hasFDerivAt.comp_hasDerivAt t derivative
  have original := derivative.inner ℝ last
  have same := symmetric (f t) d
  have swap := real_inner_comm (T (f t)) d
  have value : inner ℝ (f t) (T d)+inner ℝ d ((T ∘ f) t)=2*inner ℝ (f t) (T d) := by
    change inner ℝ (f t) (T d)+inner ℝ d (T (f t))=_
    linarith only [same,swap]
  rw [value] at original
  exact original

theorem source_energy_derivative (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) :
    HasDerivAt (sourceEnergy seed frame M F R) (sourceRate seed frame M F R time) time := by
  simpa only [sourceEnergy,sourceRate] using! paired_derivative (E := H) (metricAction seed frame M F R)
    (NativeWindowMetricGraphHistory.action_symmetric seed frame M F R)
    (NativeWindowHistoryOseen.source_hasDerivAt seed M time)

private theorem inner_rate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (h a f : E) :
    2*inner ℝ h (T (a+f))=2*inner ℝ h (T a)+2*inner ℝ h (T f) := by
  rw [map_add,inner_add_right,mul_add]

private theorem source_rate_upper (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time b : ℝ)
    (bound : 2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M F R
      (action seed M time (finiteHistory seed time M))) ≤ b) :
    sourceRate seed frame M F R time ≤ b+
      2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M F R (forcingHistory seed M time)) := by
  have same : sourceRate seed frame M F R time=
    2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M F R (action seed M time (finiteHistory seed time M)))+
      2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M F R (forcingHistory seed M time)) := by
    simpa only [sourceRate] using! inner_rate (E := H) (metricAction seed frame M F R)
      (finiteHistory seed time M) (action seed M time (finiteHistory seed time M)) (forcingHistory seed M time)
  exact same.trans_le (add_le_add bound le_rfl)

theorem source_rate_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M : ℕ,
      ∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,
      sourceRate seed frame M (integerWaveFrequencyCube cutoff) radius time ≤
        -(nu.coeff^2/2)*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C*‖finiteHistory seed time M‖^2+
          diagonalWork seed M frame time (integerWaveFrequencyCube cutoff) radius (finiteHistory seed time M)+
          2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M (integerWaveFrequencyCube cutoff) radius
            (forcingHistory seed M time)) := by
  have fact := @source_green_bound nu seed horizon nonnegative
  rcases fact with ⟨low,C,C0,paid⟩
  exact ⟨low,C,C0,fun radius above cutoff covered M frame frameInside time timeInside =>
    source_rate_upper seed frame M _ radius time _
      (paid radius above cutoff covered M frame frameInside time timeInside (finiteHistory seed time M))⟩

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem diagonal_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) (frame time : ℝ)
    (frame0 : 0 ≤ frame) (time0 : 0 ≤ time) (v : H) :
    diagonalWork seed M (step.2.clockAdvance+frame) (step.2.clockAdvance+time) F R v=
      diagonalWork step.1 M frame time F R v := by
  have operators := NativeWindowHistoryOseen.whole_next seed M step generated time time0
  simp only [Prod.mk.injEq] at operators
  simp only [diagonalWork,operators.1,NativeWindowTraceWholeHistory.metricAction_next seed step generated frame frame0]

theorem source_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) (frame time : ℝ)
    (frame0 : 0 ≤ frame) (time0 : 0 ≤ time) :
    (sourceEnergy seed (step.2.clockAdvance+frame) M F R (step.2.clockAdvance+time),
      sourceRate seed (step.2.clockAdvance+frame) M F R (step.2.clockAdvance+time))=
      (sourceEnergy step.1 frame M F R time,sourceRate step.1 frame M F R time) := by
  have operators := NativeWindowHistoryOseen.whole_next seed M step generated time time0
  simp only [Prod.mk.injEq] at operators
  simp only [sourceEnergy,sourceRate,operators.1,
    NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time time0 M,
    NativeWindowTraceWholeHistory.metricAction_next seed step generated frame frame0,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time time0]

end
end SaturationMonoid.NavierStokes.NativeWindowMetricGraphGreen
