import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.RawCompletion.Form

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeRawCompletionTransfer
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent (physicalSpace pairing coefficients)
open NativeCommonAdvectorAction (curlPair)
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_norm restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryCreationGeometry (transport square)
open NativeWindowHistorySchurCompletion (completion)
open NativeWindowHistorySchurSampleControl (sample)
open NativeWindowHistorySchurTranspose (transposeAction)
open NativeWindowHistorySchurAdvectorFiber (family)
open NativeWindowHistoryOseen (H)
open NativeWindowTraceWholeHistory (gradient)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance sourcePhysicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sourcePhysicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance sourceHistorySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistorySpatialWords (history operator commutator)
open NativeWindowHistoryAllOrderCausal (load created)
open NativeWindowHistoryJacobianCommutator (advectorDerivative)

set_option backward.isDefEq.respectTransparency false in
theorem commutator_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (t : ℝ) :
    commutator seed M [j] t (finiteHistory seed t M)=advectorDerivative seed M j t (finiteHistory seed t M) := by
  let h:=finiteHistory seed t M
  let A:=NativeWindowHistoryOseen.action seed M t
  let D:=operator M [j]
  have split : commutator seed M [j] t h=D (A h)-A (D h):=rfl
  rw [split]
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (D (A h)) (A (D h)),
    NativeWindowHistoryJacobianCommutator.spatial_ae M j (A h),
    NativeWindowHistoryOseen.action_ae seed M t h,
    NativeWindowHistoryOseen.action_ae seed M t (D h),
    NativeWindowHistoryJacobianCommutator.spatial_ae M j h,
    NativeWindowHistoryOseen.history_original seed M t,
    NativeWindowHistoryJacobianCommutator.advectorDerivative_ae seed M j t h]
    with lag subtract differentiated acted last word original vertex
  change D (A h) lag=NativeWindowHistorySpatialWords.fiber M [j] (A h lag) at differentiated
  change A h lag=NativeWindowHistoryOseen.forwardFiber seed M (t-lag) (h lag) at acted
  change A (D h) lag=NativeWindowHistoryOseen.forwardFiber seed M (t-lag) (D h lag) at last
  change D h lag=NativeWindowHistorySpatialWords.fiber M [j] (h lag) at word
  change h lag=includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.value seed M (t-lag)) at original
  change advectorDerivative seed M j t h lag=family nu M (D h lag) (h lag) at vertex
  have left:=subtract.trans (congrArg₂ (fun u v : wholePhysical => u-v)
    (differentiated.trans (congrArg (NativeWindowHistorySpatialWords.fiber M [j]) acted))
    (last.trans (congrArg (NativeWindowHistoryOseen.forwardFiber seed M (t-lag)) word)))
  have right:=vertex.trans (congrArg (fun v : wholePhysical => family nu M v (h lag)) word)
  apply left.trans
  apply Eq.trans _ right.symm
  rw [original]
  change NativeWindowHistorySpatialWords.fiber M [j]
    (NativeWindowHistoryOseen.lift M (NativeWindowTraceAdjoint.forward seed M (t-lag))
      (includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.value seed M (t-lag))))-
    NativeWindowHistoryOseen.lift M (NativeWindowTraceAdjoint.forward seed M (t-lag))
      (NativeWindowHistorySpatialWords.fiber M [j]
        (includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.value seed M (t-lag))))=_
  simp only [NativeWindowHistoryJacobianCommutator.fiber_included,NativeWindowHistoryOseen.lift_included,
    NativeWindowHistorySchurAdvectorFiber.family_original,restrict_include,← map_sub]
  apply congrArg (includeCLM (modes M) (modes_closed M))
  have finite:=NativeWindowHistorySpatialTransport.frozen_derivative nu M j
    (NativeWindowTraceAdjoint.value seed M (t-lag)) (NativeWindowTraceAdjoint.value seed M (t-lag))
  rw [NativeWindowHistoryMeanAction.frozen_source,NativeWindowHistoryDynamicKernel.transport_apply] at finite
  exact sub_eq_iff_eq_add.mpr (finite.trans (add_comm _ _))

def remainder (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (t : ℝ) : H :=
  load seed M [j] t-transposeAction seed M t (history seed M [j] t)

set_option backward.isDefEq.respectTransparency false in
theorem remainder_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (t : ℝ) :
    remainder seed M j t=advectorDerivative seed M j t (NativeWindowHistorySchurTemporalControl.temporalResponse seed M t)+
      operator M [j] (NativeWindowHistoryOseen.forcingHistory seed M t) := by
  have same : advectorDerivative seed M j t (completion seed M t)=transposeAction seed M t (history seed M [j] t) := by
    apply Lp.ext
    filter_upwards [NativeWindowHistoryJacobianCommutator.advectorDerivative_ae seed M j t (completion seed M t),
      NativeWindowHistorySchurTranspose.transpose_ae seed M t (history seed M [j] t)] with lag first last
    exact first.trans last.symm
  have split:=congrArg (advectorDerivative seed M j t) (NativeWindowHistorySchurCompletion.source_split seed M t)
  rw [map_add,same] at split
  have first:=congrArg (fun z : H => z+operator M [j] (NativeWindowHistoryOseen.forcingHistory seed M t))
    ((commutator_original seed M j t).trans split)
  change load seed M [j] t=
    (transposeAction seed M t (history seed M [j] t)+
      advectorDerivative seed M j t (NativeWindowHistorySchurTemporalControl.temporalResponse seed M t))+
        operator M [j] (NativeWindowHistoryOseen.forcingHistory seed M t) at first
  change load seed M [j] t-transposeAction seed M t (history seed M [j] t)=_
  exact sub_eq_iff_eq_add.mpr (first.trans (by abel))

theorem source_work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (t : ℝ) (nonnegative : 0≤t) :
    NativeJointNonlinearWork.work seed M j t=
      inner ℝ (history seed M [j] t) (transposeAction seed M t (history seed M [j] t))+
        inner ℝ (history seed M [j] t) (remainder seed M j t) := by
  rw [← NativeJointNonlinearWork.source_work seed M j t nonnegative,remainder,inner_sub_right (𝕜:=ℝ) (E:=H)]
  ring

theorem source_work_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀j : Coordinate,∀t∈Icc 0 horizon,
      2*NativeJointNonlinearWork.work seed M j t≤epsilon*gradient M (history seed M [j] t)+
        C*‖history seed M [j] t‖^2+2*inner ℝ (history seed M [j] t) (remainder seed M j t) := by
  obtain ⟨low,C,C0,paid⟩:=source_form seed horizon nonnegative epsilon positive
  refine ⟨low,C,C0,fun M above j t inside => ?_⟩
  have bound:=(le_abs_self _).trans (paid M above t inside (history seed M [j] t))
  rw [source_work seed M j t inside.1]
  linarith only [bound]

set_option backward.isDefEq.respectTransparency false in
theorem source_first_word_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃K : ℝ,0≤K ∧∀M≥low,∀j : Coordinate,∀a : ℝ,∀start : a∈Icc 0 horizon,
      ∀t∈Ioo a horizon,
        deriv (NativeWindowHistoryAllOrderJointEnergy.energy seed M [j] a horizon start.2) t+
          (nu.coeff/4)*gradient M (history seed M [j] t)≤
            K*NativeWindowHistoryAllOrderJointEnergy.energy seed M [j] a horizon start.2 t+
              2*inner ℝ (history seed M [j] t) (remainder seed M j t)-
                2*inner ℝ (created seed M [j] a horizon start.2 t) (load seed M [j] t) := by
  obtain ⟨low,C,C0,paid⟩:=source_form seed horizon nonnegative (nu.coeff/4) (by positivity [nu.coeff_pos])
  obtain ⟨K,K0,source⟩:=NativeJointNonlinearWork.source_first_word_generator seed horizon
  refine ⟨low,K+2*C,by positivity,fun M above j a start t inside => ?_⟩
  have positiveTime : 0≤t:=start.1.trans inside.1.le
  have bound:=(le_abs_self _).trans (paid M above t ⟨positiveTime,inside.2.le⟩ (history seed M [j] t))
  have mass:=mul_le_mul_of_nonneg_left
    (NativeWindowHistoryAllOrderJointEnergy.whole_mass seed M [j] a horizon start.2 t) C0
  have actual:=source M j a start t inside
  rw [source_work seed M j t positiveTime] at actual
  nlinarith only [bound,mass,actual]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem remainder_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (t : ℝ) (nonnegative : 0≤t) :
    remainder seed M j (step.2.clockAdvance+t)=remainder step.1 M j t := by
  simp only [remainder,NativeWindowHistoryAllOrderCausal.load_next seed M [j] step generated t nonnegative,
    NativeWindowHistorySpatialWords.history_next seed M [j] step generated t nonnegative,
    NativeWindowHistorySchurTranspose.transpose_next seed M step generated t nonnegative]
end
end SaturationMonoid.NavierStokes.NativeRawCompletionTransfer
