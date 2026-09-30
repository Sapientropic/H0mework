import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Cross.Balance
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.CreatedLoadControl

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeJointNonlinearWork
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent (physicalSpace pairing)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM restrict_include)
open NativeWindowHistoryDynamicKernel (transport)
open NativeWindowHistorySpatialTransport (finite)
open NativeWindowTraceAdjoint (value forward)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open NativeWindowHistorySpatialWords (history fiber operator commutator)
open NativeWindowHistoryAllOrderCausal (load created)
open NativeWindowHistoryOseen (H)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

def nonlinear (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (s : ℝ) : physicalSpace (modes M) :=
  NativeWindowStageNineSource.lift (modes M) (NativeUnheatedSourceWeightedTail.nonlinear seed s)

set_option backward.isDefEq.respectTransparency false in
theorem cutoff_cancellation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (s : ℝ) (positive : 0 ≤ s) :
    transport nu M (value seed M s) (value seed M s)+NativeWindowStageNineSource.forcing seed M s=
      nonlinear seed M s := by
  have raw : value seed M s=NativeWindowStressOseenSource.load M seed s :=
    NativeWindowStageNineSource.lift_load seed s positive M
  have projected : NativeWindowStageNineSource.lift (modes M) (NativeUnheatedSourceQuadraticApprox.value M seed s)=
      transport nu M (value seed M s) (value seed M s) := by
    rw [NativeWindowStageNineSource.lift_action,raw,NativeWindowHistoryDynamicKernel.transport_apply]
    rfl
  rw [NativeWindowStageNineSource.forcing,map_sub,projected]
  unfold nonlinear
  abel

private theorem transport_zero (M : ℕ) (u v : physicalSpace (modes M)) : pairing (modes M) v (transport nu M u v)=0 := by
  have skew:=NativeWindowHistoryJacobianForm.transport_skew nu M u v v
  rw [← NativeWindowHistoryDynamicKernel.transport_apply] at skew
  linarith only [skew]

set_option backward.isDefEq.respectTransparency false in
theorem sample_work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (s : ℝ) (positive : 0 ≤ s) :
    pairing (modes M) (finite M j (value seed M s))
      (transport nu M (finite M j (value seed M s)) (value seed M s)+finite M j (NativeWindowStageNineSource.forcing seed M s))=
        pairing (modes M) (finite M j (value seed M s)) (finite M j (nonlinear seed M s)) := by
  have derivative : finite M j (transport nu M (value seed M s) (value seed M s))=
      transport nu M (finite M j (value seed M s)) (value seed M s)+
        transport nu M (value seed M s) (finite M j (value seed M s)) := by
    simp only [NativeWindowHistoryDynamicKernel.transport_apply]
    exact NativeWindowHistorySpatialTransport.transport_derivative
      (modes M) (modes_zero M) (modes_closed M) nu (value seed M s) (value seed M s) j
  have source:=congrArg (finite M j) (cutoff_cancellation seed M s positive)
  rw [map_add,derivative] at source
  have paired:=congrArg (pairing (modes M) (finite M j (value seed M s))) source
  rw [map_add,map_add,transport_zero,add_zero] at paired
  rw [map_add]
  exact paired

def work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (t : ℝ) : ℝ :=
  ∫lag,pairing (modes M) (finite M j (value seed M (t-lag)))
    (finite M j (nonlinear seed M (t-lag))) ∂averageMeasure

private theorem first_fiber (M : ℕ) (j : Coordinate) (v : physicalSpace (modes M)) :
    fiber M [j] (includeCLM (modes M) (modes_closed M) v)=
      includeCLM (modes M) (modes_closed M) (finite M j v) :=
  NativeWindowHistoryOseen.lift_included M _ v

private theorem first_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (t : ℝ) :
    history seed M [j] t=ᵐ[averageMeasure] fun lag =>
      includeCLM (modes M) (modes_closed M) (finite M j (value seed M (t-lag))) := by
  filter_upwards [(fiber M [j]).coeFn_compLpL (finiteHistory seed t M),NativeWindowHistoryOseen.history_original seed M t]
    with lag actual original
  exact actual.trans ((congrArg (fiber M [j]) original).trans (first_fiber M j _))

private theorem vertex (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (s : ℝ) :
    finite M j (forward seed M s (value seed M s))-forward seed M s (finite M j (value seed M s))=
      transport nu M (finite M j (value seed M s)) (value seed M s) := by
  have actual:=NativeWindowHistorySpatialTransport.frozen_derivative nu M j (value seed M s) (value seed M s)
  rw [NativeWindowHistoryMeanAction.frozen_source] at actual
  exact sub_eq_iff_eq_add.mpr (actual.trans (add_comm _ _))

private theorem commutator_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (t : ℝ) :
    commutator seed M [j] t (finiteHistory seed t M)=ᵐ[averageMeasure] fun lag =>
      includeCLM (modes M) (modes_closed M)
        (transport nu M (finite M j (value seed M (t-lag))) (value seed M (t-lag))) := by
  let h:=finiteHistory seed t M
  let x:=history seed M [j] t
  let A:=NativeWindowHistoryOseen.action seed M t
  let D:=operator M [j]
  have split : commutator seed M [j] t h=D (A h)-A x := rfl
  rw [split]
  filter_upwards [Lp.coeFn_sub (D (A h)) (A x),
    (fiber M [j]).coeFn_compLpL (A h),NativeWindowHistoryOseen.action_ae seed M t h,
    NativeWindowHistoryOseen.action_ae seed M t x,
    NativeWindowHistoryOseen.history_original seed M t,first_ae seed M j t]
    with lag sub left acted right original word
  change D (A h) lag=fiber M [j] (A h lag) at left
  change A h lag=NativeWindowHistoryOseen.forwardFiber seed M (t-lag) (h lag) at acted
  change A x lag=NativeWindowHistoryOseen.forwardFiber seed M (t-lag) (x lag) at right
  change h lag=includeCLM (modes M) (modes_closed M) (value seed M (t-lag)) at original
  change x lag=includeCLM (modes M) (modes_closed M) (finite M j (value seed M (t-lag))) at word
  rw [sub,Pi.sub_apply,left,acted,right,original,word]
  change fiber M [j] (NativeWindowHistoryOseen.lift M (forward seed M (t-lag))
    (includeCLM (modes M) (modes_closed M) (value seed M (t-lag))))-
    NativeWindowHistoryOseen.lift M (forward seed M (t-lag))
      (includeCLM (modes M) (modes_closed M) (finite M j (value seed M (t-lag))))=_
  rw [NativeWindowHistoryOseen.lift_included,NativeWindowHistoryOseen.lift_included,first_fiber,← map_sub,vertex]

private theorem load_pair_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (t : ℝ) (nonnegative : 0 ≤ t) :
    (fun lag => inner ℝ (history seed M [j] t lag) (load seed M [j] t lag))=ᵐ[averageMeasure]
      fun lag => pairing (modes M) (finite M j (value seed M (t-lag)))
        (finite M j (nonlinear seed M (t-lag))) := by
  let c:=commutator seed M [j] t (finiteHistory seed t M)
  let f:=operator M [j] (NativeWindowHistoryOseen.forcingHistory seed M t)
  filter_upwards [first_ae seed M j t,Lp.coeFn_add c f,commutator_ae seed M j t,
    (fiber M [j]).coeFn_compLpL (NativeWindowHistoryOseen.forcingHistory seed M t),
    NativeWindowHistoryOseen.forcingHistory_ae seed M t,NativeWindowTraceEndpointWindow.average_interval]
    with lag word add nonlinearPart acted forced support
  have positive : 0 ≤ t-lag := by linarith [support.2]
  change load seed M [j] t lag=c lag+f lag at add
  change c lag=_ at nonlinearPart
  change f lag=fiber M [j] (NativeWindowHistoryOseen.forcingHistory seed M t lag) at acted
  rw [word,add,nonlinearPart,acted,forced,NativeWindowHistoryOseen.forcingValue_original seed M (t-lag) positive,
    first_fiber,← map_add,NativePhysicalPairing.include_inner (modes M) (modes_zero M),restrict_include]
  exact sample_work seed M j (t-lag) positive

theorem work_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (t : ℝ) (nonnegative : 0 ≤ t) :
    Integrable (fun lag => pairing (modes M) (finite M j (value seed M (t-lag)))
      (finite M j (nonlinear seed M (t-lag)))) averageMeasure :=
  (L2.integrable_inner (𝕜 := ℝ) (history seed M [j] t) (load seed M [j] t)).congr
    (load_pair_ae seed M j t nonnegative)

theorem source_work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (t : ℝ) (nonnegative : 0 ≤ t) :
    inner ℝ (history seed M [j] t) (load seed M [j] t)=work seed M j t := by
  rw [L2.inner_def,work]
  exact integral_congr_ae (load_pair_ae seed M j t nonnegative)

set_option backward.isDefEq.respectTransparency false in
theorem pure_forcing_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (t : ℝ) (nonnegative : 0 ≤ t) :
    NativeCenteredCrossWork.pureWork seed M j t+
      inner ℝ (history seed M [j] t) (operator M [j] (NativeWindowHistoryOseen.forcingHistory seed M t))=
        work seed M j t-NativeCenteredCrossWork.work seed M j t-
          inner ℝ (history seed M [j] t)
            (NativeWindowHistoryMeanStrainControl.action seed M t (history seed M [j] t)) := by
  have source:=source_work seed M j t nonnegative
  rw [NativeWindowHistoryMeanStrainSource.load_split] at source
  simp only [inner_add_right (𝕜 := ℝ) (E := H)] at source
  rw [NativeCenteredCrossWork.fluctuation_split] at source
  linarith only [source]

set_option backward.isDefEq.respectTransparency false in
theorem source_first_word_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃K : ℝ,0 ≤ K ∧ ∀M (j : Coordinate) (a : ℝ) (start : a∈Icc 0 horizon)
      (t : ℝ),t∈Ioo a horizon →
      deriv (NativeWindowHistoryAllOrderJointEnergy.energy seed M [j] a horizon start.2) t+
        (nu.coeff/2)*gradient M (history seed M [j] t) ≤
          K*NativeWindowHistoryAllOrderJointEnergy.energy seed M [j] a horizon start.2 t+
            2*work seed M j t-
            2*inner ℝ (created seed M [j] a horizon start.2 t) (load seed M [j] t) := by
  obtain ⟨K,K0,source⟩:=NativeWindowHistoryAllOrderJointControl.source_generator seed horizon
  refine ⟨K,K0,fun M j a start t inside => ?_⟩
  have actual:=source M [j] a start t inside
  rw [NativeWindowHistoryAllOrderJointEnergy.mixedLoad_original seed M [j] a horizon start.2 t
    (Ioo_subset_Icc_self inside),inner_sub_left,source_work seed M j t (start.1.trans inside.1.le)] at actual
  nlinarith only [actual]


set_option backward.isDefEq.respectTransparency false in
theorem source_joint (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃K : ℝ,0 ≤ K ∧ ∀M (j : Coordinate) (a : ℝ) (start : a∈Icc 0 horizon),∀b∈Icc a horizon,
      (3/4:ℝ)*NativeWindowHistoryAllOrderJointEnergy.energy seed M [j] a horizon start.2 b+
        (nu.coeff/4)*(∫t in a..b,gradient M (history seed M [j] t)) ≤
          NativeWindowHistoryAllOrderJointEnergy.energy seed M [j] a horizon start.2 a+
            K*(∫t in a..b,NativeWindowHistoryAllOrderJointEnergy.energy seed M [j] a horizon start.2 t)+
              ∫t in a..b,2*work seed M j t := by
  obtain ⟨K,K0,source⟩:=NativeWindowHistoryAllOrderCreatedLoadControl.source_joint seed horizon
  refine ⟨K,K0,fun M j a start b inside => ?_⟩
  have original:=source M [j] a start b inside
  have read : (∫t in a..b,2*inner ℝ (history seed M [j] t) (load seed M [j] t))=
      ∫t in a..b,2*work seed M j t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have t0 : 0 ≤ t := start.1.trans (by rw [uIcc_of_le inside.1] at ht; exact ht.1)
    exact congrArg (fun r : ℝ => 2*r) (source_work seed M j t t0)
  rwa [read] at original


open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem work_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (t : ℝ) (nonnegative : 0 ≤ t) :
    work seed M j (step.2.clockAdvance+t)=work step.1 M j t := by
  rw [← source_work seed M j (step.2.clockAdvance+t) (add_nonneg step.2.clockAdvance_pos.le nonnegative),
    NativeWindowHistorySpatialWords.history_next seed M [j] step generated t nonnegative,
    NativeWindowHistoryAllOrderCausal.load_next seed M [j] step generated t nonnegative,
    source_work step.1 M j t nonnegative]

end
end SaturationMonoid.NavierStokes.NativeJointNonlinearWork
