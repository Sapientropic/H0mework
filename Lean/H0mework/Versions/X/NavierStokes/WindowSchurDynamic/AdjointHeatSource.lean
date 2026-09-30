import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.AdjointHeatKernel
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianCommutator

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointHeatSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryDynamicHistory (kernelAction)
open NativeWindowHistoryDynamicEnergy (principal)
open NativeWindowTraceWholeHistory (projected)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeWindowHistorySchurTemporalControl (energy temporalResponse temporalBudget)
open NativeWindowHistoryJacobianControl (heat form)
open NativeWindowHistoryAdjointHeatKernel
noncomputable section
variable {nu : Viscosity}

def pullback (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) : H :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time) (heat nu M v)

theorem pullback_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    projected M (pullback seed M time v)=pullback seed M time v :=
  adjoint_projected seed M time (heat nu M v)

private theorem projected_input {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K P L : E →L[ℝ] E) (kept : ∀ v,K (P v)=K v) (a : ℝ) (v : E) :
    K (v+a • L v)=K (P v+a • L v) := by
  rw [map_add,map_add,kept]

theorem pullback_principal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    pullback seed M time v=
      ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time) (principal nu M v) := by
  simpa only [pullback,heat,NativeWindowHistoryDynamicEnergy.principal,add_apply,smul_apply,ContinuousLinearMap.id_apply,
    NativeWindowTraceWholeHistory.projected] using! projected_input (E := H)
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time))
    ((NativeWindowTraceWholeHistory.projection M).compLpL 2 NativeForwardWindowPairingReadout.averageMeasure)
    (laplacianAction nu M) (adjoint_projection seed M time) nu.coeff v

theorem pullback_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    energy nu M (pullback seed M time v)=form nu M (pullback seed M time v) v :=
  adjoint_energy seed M time (heat nu M v)

theorem energy_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    energy nu M (pullback seed M time v) ≤ energy nu M v := by
  have paid := NativeWindowHistoryJacobianControl.form_young seed M (pullback seed M time v) v 1
  rw [← pullback_energy] at paid
  norm_num only [one_pow,one_mul,mul_one] at paid
  linarith only [paid]

theorem laplacian_projection (nu : Viscosity) (M : ℕ) (v : H) :
    laplacianAction nu M (projected M v)=laplacianAction nu M v := by
  let L := NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (projected M v),L.coeFn_compLpL v,
    (NativeWindowTraceWholeHistory.projection M).coeFn_compLpL v] with lag first last source
  have point : projected M v lag=NativeWindowTraceWholeHistory.projection M (v lag) := source
  exact first.trans ((congrArg L point).trans
    ((NativeWindowHistoryOseenGap.lift_projection M _ (v lag)).trans last.symm))

private theorem heat_projection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K P L : E →L[ℝ] E) (kept : ∀ v,K (P v)=K v) (lap : ∀ v,L (P v)=L v) (a : ℝ) (v : E) :
    K (P v+a • L (P v))=K (v+a • L v) := by
  rw [lap,map_add,map_add,kept]

theorem input_projection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    pullback seed M time (projected M v)=pullback seed M time v := by
  simpa only [pullback,heat,add_apply,smul_apply,ContinuousLinearMap.id_apply,
    NativeWindowTraceWholeHistory.projected] using! heat_projection (E := H)
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time))
    ((NativeWindowTraceWholeHistory.projection M).compLpL 2 NativeForwardWindowPairingReadout.averageMeasure)
    (laplacianAction nu M) (adjoint_projection seed M time) (laplacian_projection nu M) nu.coeff v

theorem projected_energy_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    energy nu M (pullback seed M time v) ≤ energy nu M (projected M v) :=
  (congrArg (energy nu M) (input_projection seed M time v).symm).trans_le
    (energy_bound seed M time (projected M v))

private theorem adjoint_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : E →L[ℝ] E) (a q : E) : inner ℝ (K a) q=inner ℝ (K.adjoint q) a := by
  rw [ContinuousLinearMap.adjoint_inner_left,real_inner_comm]

theorem pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v a : H) :
    form nu M v (kernelAction seed M time a)=inner ℝ (pullback seed M time v) a := by
  rw [NativeWindowHistoryJacobianControl.form_symmetric]
  simpa only [form,pullback] using! adjoint_pair (E := H) (kernelAction seed M time) a (heat nu M v)

theorem test_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    NativeWindowHistoryDynamicEnergy.test seed M time v=principal nu M v-
      ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H)
        (NativeWindowHistorySchurTranspose.transposeAction seed M time) (pullback seed M time v) := by
  exact congrArg (fun p : H => principal nu M v-
    ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (NativeWindowHistorySchurTranspose.transposeAction seed M time) p)
    (pullback_principal seed M time v).symm

def source (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  pullback seed M time (temporalResponse seed M time)

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
    energy nu M (source seed M time) ≤ temporalBudget seed horizon :=
  (energy_bound seed M time (temporalResponse seed M time)).trans
    (NativeWindowHistorySchurTemporalControl.source_temporal_energy seed horizon M time inside)

theorem source_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (a : H) :
    form nu M (temporalResponse seed M time) (kernelAction seed M time a)=inner ℝ (source seed M time) a :=
  pairing seed M time (temporalResponse seed M time) a

private theorem negative_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (v a b : E) :
    inner ℝ v (L (-a-b))= -inner ℝ v (L a)-inner ℝ v (L b) := by
  rw [map_sub,map_neg,inner_sub_right,inner_neg_right]

theorem source_commutator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (j : ThreeDimensionalPeriodicCoarseFilterCore.Coordinate) (time : ℝ) (v : H) :
    form nu M (temporalResponse seed M time)
      (NativeWindowHistorySpatialWords.operator M [j] (NativeWindowHistoryJacobianControl.jacobian seed M time v)-
        NativeWindowHistoryJacobianControl.jacobian seed M time (NativeWindowHistorySpatialWords.operator M [j] v))=
      -inner ℝ (source seed M time) (NativeWindowHistoryJacobianCommutator.advectorDerivative seed M j time
        (NativeWindowHistoryJacobianControl.correction seed M time v))-
      inner ℝ (source seed M time) (NativeWindowHistoryJacobianCommutator.transposeDerivative seed M j time v) := by
  have actual := congrArg (form nu M (temporalResponse seed M time))
    (NativeWindowHistoryJacobianCommutator.jacobian_commutator seed M j time v)
  have split := negative_pair (E := H) (heat nu M) (temporalResponse seed M time)
    (kernelAction seed M time (NativeWindowHistoryJacobianCommutator.advectorDerivative seed M j time
      (NativeWindowHistoryJacobianControl.correction seed M time v)))
    (kernelAction seed M time (NativeWindowHistoryJacobianCommutator.transposeDerivative seed M j time v))
  exact actual.trans (split.trans (congrArg₂ (fun a b : ℝ => -a-b)
    (source_pairing seed M time _) (source_pairing seed M time _)))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem pullback_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) (v : H) :
    pullback seed M (step.2.clockAdvance+time) v=pullback step.1 M time v :=
  congrArg (fun K : H →L[ℝ] H => ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) K (heat nu M v))
    (NativeWindowHistoryDynamicHistory.kernelAction_next seed M step generated time time0)

theorem source_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    source seed M (step.2.clockAdvance+time)=source step.1 M time :=
  (pullback_next seed M step generated time time0 (temporalResponse seed M (step.2.clockAdvance+time))).trans
    (congrArg (pullback step.1 M time) (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointHeatSource
