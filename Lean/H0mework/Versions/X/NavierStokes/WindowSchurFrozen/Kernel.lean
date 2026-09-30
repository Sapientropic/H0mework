import H0mework.Versions.X.NavierStokes.WindowHistoryOseen.Gap

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryFrozenInverse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint
open NativeWholeResolvent (wholePhysical restrictCLM restrict_energy)
open NativePhysicalPairing (includeCLM include_norm restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (forwardFiber lift)
open NativeWindowTraceWholeHistory (projection)
noncomputable section
variable {nu : Viscosity}

def physical (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    physicalSpace (modes M) ≃L[ℝ] physicalSpace (modes M) :=
  (physicalResolver (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time)
    1 (by norm_num)).toContinuousLinearEquiv

theorem physical_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    physical seed M time f-NativeWindowTraceAdjoint.forward seed M time (physical seed M time f)=f := by
  simpa only [one_smul] using! resolver_write
    (physicalOperator (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time))
    (pairing (modes M)) (pairing_faithful (modes M))
    (physicalOperator_dissipative (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time)) 1 (by norm_num) f

theorem physical_balance (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    ‖coefficients (modes M) f‖^2=‖coefficients (modes M) (physical seed M time f)‖^2+
      ‖coefficients (modes M) (f-physical seed M time f)‖^2+
      2*nu.coeff*curlPair (modes M) (physical seed M time f).1 (physical seed M time f).1 := by
  simpa only [mul_one] using! physicalResolver_balance (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time) 1 (by norm_num) f

theorem physical_unique (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v f : physicalSpace (modes M))
    (equation : v-NativeWindowTraceAdjoint.forward seed M time v=f) : v=physical seed M time f := by
  have injective := implicitMap_injective
    (physicalOperator (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time))
    (pairing (modes M)) (pairing_faithful (modes M))
    (physicalOperator_dissipative (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time)) 1 (by norm_num)
  apply injective
  simpa only [implicitMap,LinearMap.sub_apply,LinearMap.id_apply,LinearMap.smul_apply,one_smul] using!
    equation.trans (physical_write seed M time f).symm

theorem physical_inverse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    physical seed M time (v-NativeWindowTraceAdjoint.forward seed M time v)=v :=
  (physical_unique seed M time v _ rfl).symm

def kernel (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  lift M (physical seed M time).toContinuousLinearMap

theorem kernel_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : wholePhysical) :
    projection M (kernel seed M time f)=kernel seed M time f :=
  NativeWindowHistoryOseenGap.projection_lift M _ f

theorem kernel_projection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : wholePhysical) :
    kernel seed M time (projection M f)=kernel seed M time f :=
  NativeWindowHistoryOseenGap.lift_projection M _ f

theorem kernel_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : wholePhysical) :
    kernel seed M time f-forwardFiber seed M time (kernel seed M time f)=projection M f := by
  let v:=restrictCLM (modes M) (modes_zero M) (modes_closed M) f
  change includeCLM (modes M) (modes_closed M) (physical seed M time v)-
    forwardFiber seed M time (includeCLM (modes M) (modes_closed M) (physical seed M time v))=_
  rw [forwardFiber,NativeWindowHistoryOseen.lift_included,← map_sub,physical_write]
  rfl

theorem kernel_inverse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    kernel seed M time (v-forwardFiber seed M time v)=projection M v := by
  change includeCLM (modes M) (modes_closed M)
    (physical seed M time (restrictCLM (modes M) (modes_zero M) (modes_closed M) (v-forwardFiber seed M time v)))=_
  rw [map_sub]
  change includeCLM (modes M) (modes_closed M) (physical seed M time
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) v-
      restrictCLM (modes M) (modes_zero M) (modes_closed M)
        (includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.forward seed M time
          (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)))))=_
  rw [restrict_include,physical_inverse]
  rfl

theorem kernel_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    ‖kernel seed M time v‖≤‖v‖ := by
  have paid := resolver_contraction (modes M)
    (physicalOperator (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time))
    (physicalOperator_dissipative (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time))
    1 (by norm_num) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)
  change ‖includeCLM (modes M) (modes_closed M) (physical seed M time
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))‖≤_
  rw [include_norm (modes M) (modes_zero M)]
  exact paid.trans (restrict_energy (modes M) (modes_zero M) (modes_closed M) v)

theorem kernel_norm (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ‖kernel seed M time‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  simpa only [one_mul] using kernel_bound seed M time v

theorem kernel_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : wholePhysical) :
    let r:=physical seed M time (restrictCLM (modes M) (modes_zero M) (modes_closed M) f)
    ‖kernel seed M time f‖^2+2*nu.coeff*curlPair (modes M) r.1 r.1 ≤ ‖f‖^2 := by
  dsimp only
  let input:=restrictCLM (modes M) (modes_zero M) (modes_closed M) f
  have balance:=physical_balance seed M time input
  have mass:=pow_le_pow_left₀ (norm_nonneg (coefficients (modes M) input))
    (restrict_energy (modes M) (modes_zero M) (modes_closed M) f) 2
  have extra:=sq_nonneg ‖coefficients (modes M) (input-physical seed M time input)‖
  have normed : ‖kernel seed M time f‖=‖coefficients (modes M) (physical seed M time input)‖ :=
    include_norm (modes M) (modes_zero M) (modes_closed M) _
  rw [normed]
  linarith only [balance,mass,extra]

theorem kernel_difference (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (s t : ℝ) (v : wholePhysical) :
    kernel seed M s v-kernel seed M t v=kernel seed M s
      ((forwardFiber seed M s-forwardFiber seed M t) (kernel seed M t v)) := by
  have first := (congrArg (kernel seed M s) (kernel_write seed M t v)).trans (kernel_projection seed M s v)
  have second := (kernel_inverse seed M s (kernel seed M t v)).trans (kernel_projected seed M t v)
  calc
    _=kernel seed M s (kernel seed M t v-forwardFiber seed M t (kernel seed M t v))-
      kernel seed M s (kernel seed M t v-forwardFiber seed M s (kernel seed M t v)) := congrArg₂ (fun a b : wholePhysical => a-b) first.symm second.symm
    _=kernel seed M s ((kernel seed M t v-forwardFiber seed M t (kernel seed M t v))-
      (kernel seed M t v-forwardFiber seed M s (kernel seed M t v))) := (map_sub _ _ _).symm
    _=_ := congrArg (kernel seed M s) (by simp only [sub_apply]; abel)

theorem kernel_difference_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (s t : ℝ) :
    ‖kernel seed M s-kernel seed M t‖≤‖forwardFiber seed M s-forwardFiber seed M t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (kernel seed M s-kernel seed M t) (norm_nonneg (forwardFiber seed M s-forwardFiber seed M t))
  intro v
  change ‖kernel seed M s v-kernel seed M t v‖≤_
  rw [kernel_difference]
  exact (kernel_bound seed M s _).trans (((forwardFiber seed M s-forwardFiber seed M t).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (kernel_bound seed M t v) (norm_nonneg (forwardFiber seed M s-forwardFiber seed M t))))

private theorem continuous_dominated {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : ℝ → E) (g : ℝ → F) (continuous : Continuous f) (bound : ∀ s t,‖g s-g t‖≤‖f s-f t‖) : Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro time
  apply Metric.continuousAt_iff.mpr
  intro epsilon positive
  obtain ⟨delta,delta0,source⟩ := Metric.continuousAt_iff.mp continuous.continuousAt epsilon positive
  refine ⟨delta,delta0,fun sample inside => ?_⟩
  have actual : dist (g sample) (g time)≤dist (f sample) (f time) := by simpa only [dist_eq_norm] using bound sample time
  exact actual.trans_lt (source inside)

theorem kernel_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (kernel seed M) := by
  simpa only [] using! continuous_dominated (E := wholePhysical →L[ℝ] wholePhysical) (F := wholePhysical →L[ℝ] wholePhysical)
    (forwardFiber seed M) (kernel seed M) (NativeWindowHistoryOseen.forwardFiber_continuous seed M) (kernel_difference_bound seed M)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem kernel_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    kernel seed M (step.2.clockAdvance+time)=kernel step.1 M time := by
  have original:=NativeWindowTraceAdjoint.source_next seed M step generated time time0
  simp only [Prod.mk.injEq] at original
  apply ContinuousLinearMap.ext
  intro v
  change includeCLM (modes M) (modes_closed M) (physical seed M (step.2.clockAdvance+time)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))=_
  apply congrArg (includeCLM (modes M) (modes_closed M))
  apply physical_unique
  rw [← original.2.1]
  exact physical_write seed M (step.2.clockAdvance+time) _

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryFrozenInverse
