import H0mework.Versions.X.NavierStokes.WindowEnergyTraceWhole.Joint

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceWholeHistory
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativeEndpointVelocityCarrier NativeResolventAdjoint
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

private def lift (M : ℕ) (op : Module.End ℝ (physicalSpace (modes M))) : wholePhysical →L[ℝ] wholePhysical :=
  (includeCLM (modes M) (modes_closed M)).comp ((LinearMap.toContinuousLinearMap op).comp
    (restrictCLM (modes M) (modes_zero M) (modes_closed M)))

private theorem lift_pairing (M : ℕ) (op : Module.End ℝ (physicalSpace (modes M))) (v : wholePhysical) :
    inner ℝ v (lift M op v)=pairing (modes M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)
      (op (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)) := by
  change inner ℝ v (includeCLM (modes M) (modes_closed M)
    (op (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)))=_
  rw [real_inner_comm,include_inner (modes M) (modes_zero M) (modes_closed M),pairing_symmetric]

def metric (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    wholePhysical →L[ℝ] wholePhysical := projection M-joint seed frame M F R

theorem metric_original (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (R : ℕ) (v : wholePhysical) : metric seed frame M F R v=
      includeCLM (modes M) (modes_closed M) (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)) := by
  let r := restrictCLM (modes M) (modes_zero M) (modes_closed M) v
  let T : Module.End ℝ (physicalSpace (modes M)) := NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R
  change includeCLM (modes M) (modes_closed M) r-
    includeCLM (modes M) (modes_closed M) (((LinearMap.id : Module.End ℝ (physicalSpace (modes M)))-T) r)=includeCLM (modes M) (modes_closed M) (T r)
  rw [LinearMap.sub_apply,LinearMap.id_apply,map_sub]
  abel

theorem projection_square (M : ℕ) (v : wholePhysical) : ‖projection M v‖^2=
    pairing (modes M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v) := by
  rw [projection,ContinuousLinearMap.comp_apply,include_norm (modes M) (modes_zero M) (modes_closed M)]
  exact (real_inner_self_eq_norm_sq _).symm

theorem metric_point (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (R : ℕ) (v : wholePhysical) : inner ℝ v (metric seed frame M F R v)=
      pairing (modes M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)
        (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R
          (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)) := by
  rw [metric_original,real_inner_comm,include_inner (modes M) (modes_zero M) (modes_closed M),pairing_symmetric]

def projected (M : ℕ) (v : H) : H := (projection M).compLpL 2 averageMeasure v

theorem projection_idempotent (M : ℕ) (v : wholePhysical) : projection M (projection M v)=projection M v := by
  change includeCLM (modes M) (modes_closed M)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (includeCLM (modes M) (modes_closed M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)))=_
  rw [restrict_include]
  rfl

theorem projected_idempotent (M : ℕ) (v : H) : projected M (projected M v)=projected M v := by
  apply Lp.ext
  filter_upwards [(projection M).coeFn_compLpL (projected M v),(projection M).coeFn_compLpL v] with shift first last
  change (((projection M).compLpL 2 averageMeasure (projected M v)) shift)=_
  have innerRead : projected M v shift=projection M (v shift) := last
  rw [first,innerRead,projection_idempotent]


def metricAction (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) : H →L[ℝ] H :=
  (metric seed frame M F R).compLpL 2 averageMeasure

def gradient (M : ℕ) (v : H) : ℝ := ∫ shift,
  NativeCommonAdvectorAction.curlPair (modes M)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) (v shift)).1
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) (v shift)).1 ∂averageMeasure

theorem gradient_integrable (nu : Viscosity) (M : ℕ) (v : H) : Integrable (fun shift =>
    NativeCommonAdvectorAction.curlPair (modes M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (v shift)).1
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (v shift)).1) averageMeasure := by
  let op := NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
  have actual := L2.integrable_inner (𝕜 := ℝ) v ((lift M op).compLpL 2 averageMeasure v)
  apply actual.congr
  filter_upwards [(lift M op).coeFn_compLpL v] with shift read
  rw [read,lift_pairing,NativeWindowOperatorGreen.laplacian_pairing]

theorem metric_pairing (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (R : ℕ) (v : H) : inner ℝ v (metricAction seed frame M F R v)=∫ shift,
      pairing (modes M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) (v shift))
        (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R
          (restrictCLM (modes M) (modes_zero M) (modes_closed M) (v shift))) ∂averageMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(metric seed frame M F R).coeFn_compLpL v] with shift read
  change inner ℝ (v shift) (((metric seed frame M F R).compLpL 2 averageMeasure v) shift)=_
  rw [read,metric_point]

private theorem lift_coercivity (nu : Viscosity) (M : ℕ) (op : Module.End ℝ (physicalSpace (modes M)))
    (coercive : ∀ x : physicalSpace (modes M),pairing (modes M) x x+(nu.coeff/2)*
      NativeCommonAdvectorAction.curlPair (modes M) x.1 x.1 ≤ pairing (modes M) x (op x)) (v : H) :
    ‖projected M v‖^2+(nu.coeff/2)*gradient M v ≤ inner ℝ v ((lift M op).compLpL 2 averageMeasure v) := by
  have mass := (Lp.memLp (projected M v)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have cost := gradient_integrable nu M v
  have target := L2.integrable_inner (𝕜 := ℝ) v ((lift M op).compLpL 2 averageMeasure v)
  have estimate := integral_mono_ae (mass.add (cost.const_mul (nu.coeff/2))) target (by
    filter_upwards [(projection M).coeFn_compLpL v,(lift M op).coeFn_compLpL v] with shift projectRead operatorRead
    change ‖projected M v shift‖^2+(nu.coeff/2)*_ ≤ inner ℝ (v shift) (((lift M op).compLpL 2 averageMeasure v) shift)
    have project : projected M v shift=projection M (v shift) := projectRead
    rw [project,operatorRead,projection_square,lift_pairing]
    exact coercive _)
  have massRead := norm_square (projected M v)
  have costRead : (nu.coeff/2)*gradient M v=∫ shift,(nu.coeff/2)*NativeCommonAdvectorAction.curlPair (modes M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (v shift)).1
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (v shift)).1 ∂averageMeasure :=
    (integral_const_mul (nu.coeff/2) _).symm
  have sumRead := (congrArg₂ (fun x y : ℝ => x+y) massRead costRead).trans
    (integral_add mass (cost.const_mul (nu.coeff/2))).symm
  have targetRead := L2.inner_def (𝕜 := ℝ) v ((lift M op).compLpL 2 averageMeasure v)
  exact sumRead.trans_le (estimate.trans_eq targetRead.symm)

theorem source_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∀ R ≥ low,∀ cutoff ≥ low,∀ M,∀ frame ∈ Icc 0 horizon,∀ v : H,
      ‖projected M v‖^2+(nu.coeff/2)*gradient M v ≤
        inner ℝ v (metricAction seed frame M (integerWaveFrequencyCube cutoff) R v) := by
  obtain ⟨low,paid⟩ := NativeWindowTraceCutOperator.source_coercivity seed horizon nonnegative
  refine ⟨low,fun R above cutoff covered M frame inside v => ?_⟩
  let op := NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) (integerWaveFrequencyCube cutoff) R
  have same : metric seed frame M (integerWaveFrequencyCube cutoff) R=lift M op := by
    apply ContinuousLinearMap.ext
    intro x
    exact metric_original seed frame M (integerWaveFrequencyCube cutoff) R x
  have actual := lift_coercivity nu M op (paid R above cutoff covered (modes M) (modes_zero M) (modes_closed M) frame inside) v
  change _ ≤ inner ℝ v ((metric seed frame M (integerWaveFrequencyCube cutoff) R).compLpL 2 averageMeasure v)
  rw [same]
  exact actual

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem metricAction_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame : ℝ) (nonnegative : 0 ≤ frame)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    metricAction seed (step.2.clockAdvance+frame) M F R=metricAction step.1 frame M F R := by
  have same : metric seed (step.2.clockAdvance+frame) M F R=metric step.1 frame M F R :=
    congrArg (fun op : wholePhysical →L[ℝ] wholePhysical => projection M-op)
      (joint_next seed step generated frame nonnegative M F R)
  exact congrArg (fun op : wholePhysical →L[ℝ] wholePhysical => op.compLpL 2 averageMeasure) same

end
end SaturationMonoid.NavierStokes.NativeWindowTraceWholeHistory
