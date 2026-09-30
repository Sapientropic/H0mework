import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.MeanStrainControl
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Causal

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanStrainSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent (physicalSpace)
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM restrict_include)
open NativeWindowHistorySpatialTransport (finite)
open NativeWindowHistoryDynamicKernel (transport)
open NativeWindowTraceAdjoint (value forward)
open NativeWindowHistoryOseen (H forcingHistory lift_included)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open NativeWindowHistorySpatialWords (fiber operator history commutator)
open NativeWindowHistoryAllOrderCausal (load)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

private theorem first_fiber (M : ℕ) (j : Coordinate) (v : physicalSpace (modes M)) :
    fiber M [j] (includeCLM (modes M) (modes_closed M) v)=
      includeCLM (modes M) (modes_closed M) (finite M j v) := lift_included M _ v

private theorem first_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (t : ℝ) :
    history seed M [j] t=ᵐ[averageMeasure] fun lag =>
      includeCLM (modes M) (modes_closed M) (finite M j (value seed M (t-lag))) := by
  filter_upwards [(fiber M [j]).coeFn_compLpL (finiteHistory seed t M),
    NativeWindowHistoryOseen.history_original seed M t] with lag read original
  exact read.trans ((congrArg (fiber M [j]) original).trans (first_fiber M j _))

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
  rw [lift_included,lift_included,first_fiber,← map_sub,vertex]

def fluctuation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (t : ℝ) : H :=
  commutator seed M [j] t (finiteHistory seed t M)-NativeWindowHistoryMeanStrainControl.action seed M t (history seed M [j] t)

theorem fluctuation_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (t : ℝ) :
    fluctuation seed M j t=ᵐ[averageMeasure] fun lag => includeCLM (modes M) (modes_closed M)
      (transport nu M (finite M j (value seed M (t-lag)))
        (NativeWindowHistoryCreationCovariance.centered seed M t (t-lag))) := by
  filter_upwards [Lp.coeFn_sub (commutator seed M [j] t (finiteHistory seed t M))
    (NativeWindowHistoryMeanStrainControl.action seed M t (history seed M [j] t)),commutator_ae seed M j t,
    NativeWindowHistoryMeanStrainControl.action_ae seed M t (history seed M [j] t),first_ae seed M j t]
    with lag subtract actual strain original
  have subtractRead : fluctuation seed M j t lag=
      commutator seed M [j] t (finiteHistory seed t M) lag-
        NativeWindowHistoryMeanStrainControl.action seed M t (history seed M [j] t) lag := subtract
  rw [subtractRead,actual,strain,original,NativeWindowHistoryMeanStrainControl.fiber_original,restrict_include,
    ← map_sub,← map_sub]
  rfl

private theorem split_add {E : Type*} [AddCommGroup E] (c s f : E) : c+f=s+((c-s)+f) := by abel

private theorem split_work_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x total strain remainder : E) (bound : ℝ) (split : total=strain+remainder)
    (paid : |2*inner ℝ x strain|≤bound) :
    2*inner ℝ x total≤bound+2*inner ℝ x remainder := by
  rw [split,inner_add_right,mul_add]
  exact add_le_add ((le_abs_self _).trans paid) (le_refl _)

theorem load_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (t : ℝ) :
    load seed M [j] t=NativeWindowHistoryMeanStrainControl.action seed M t (history seed M [j] t)+
      (fluctuation seed M j t+operator M [j] (forcingHistory seed M t)) := by
  exact split_add (commutator seed M [j] t (finiteHistory seed t M))
    (NativeWindowHistoryMeanStrainControl.action seed M t (history seed M [j] t))
    (operator M [j] (forcingHistory seed M t))

set_option backward.isDefEq.respectTransparency false in
theorem source_self_load (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃C : ℝ,0≤C ∧∀M (j : Coordinate) t,t∈Icc 0 horizon →
      2*inner ℝ (history seed M [j] t) (load seed M [j] t)≤
        epsilon*gradient M (history seed M [j] t)+C*‖history seed M [j] t‖^2+
          2*inner ℝ (history seed M [j] t)
            (fluctuation seed M j t+operator M [j] (forcingHistory seed M t)) := by
  obtain ⟨C,C0,paid⟩:=NativeWindowHistoryMeanStrainControl.source_form seed horizon epsilon positive
  refine ⟨C,C0,fun M j t inside => ?_⟩
  exact split_work_le (history seed M [j] t) (load seed M [j] t)
    (NativeWindowHistoryMeanStrainControl.action seed M t (history seed M [j] t))
    (fluctuation seed M j t+operator M [j] (forcingHistory seed M t))
    (epsilon*gradient M (history seed M [j] t)+C*‖history seed M [j] t‖^2)
    (load_split seed M j t) (paid M t inside (history seed M [j] t))
end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanStrainSource
