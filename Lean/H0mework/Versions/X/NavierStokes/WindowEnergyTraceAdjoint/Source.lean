import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HistoryPairWindow
import H0mework.Physics.DiracEvolution.GalerkinEvolution

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceAdjoint
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed NativeResolventAdjoint
open NativeUnheatedGlobalNegativeOne
noncomputable section
variable {nu : Viscosity}

def value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : physicalSpace (modes M) :=
  NativeWindowStageNineSource.lift (modes M) (state seed time)

def curlMap (M : ℕ) : physicalSpace (modes M) →L[ℝ] ComplexVorticityHilbertState :=
  ∑ k∈modes M,(lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 k).comp
    (((fourierCurlCoefficientContinuousLinearMap k).restrictScalars ℝ).comp
      ((evaluation k).comp ((physicalSpace (modes M)).subtypeL)))

theorem curlMap_apply (M : ℕ) (u : physicalSpace (modes M)) : curlMap M u=curlLift (modes M) u.1 := by
  simp only [curlMap,sum_apply,ContinuousLinearMap.comp_apply]
  rfl

def advector (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) := curlMap M (value seed M time)

theorem advector_reality (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    FiniteStateFourierReality (advector seed M time) := by
  rw [advector,curlMap_apply]
  exact curlLift_reality (modes M) (modes_closed M) _ (physical_reality (fun {_} inside => modes_closed M _ inside) _)

def forward (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) :=
  LinearMap.toContinuousLinearMap (physicalOperator (modes M) (modes_zero M) (modes_closed M) nu
    (advector seed M time) (advector_reality seed M time))

def dual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) :=
  LinearMap.toContinuousLinearMap (physicalOperator (modes M) (modes_zero M) (modes_closed M) nu
    (-advector seed M time) (negative_reality (advector_reality seed M time)))

theorem value_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (value seed M) :=
  (NativeWindowStageNineSource.lift (modes M)).continuous.comp (NativeWindowHierarchyPairWindow.state_continuous seed)

theorem advector_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (advector seed M) :=
  (curlMap M).continuous.comp (value_continuous seed M)

private theorem frozen_continuous (M : Finset IntegerWavevector) (nu : Viscosity)
    (path : ℝ → ComplexVorticityHilbertState) (continuous : Continuous path) :
    Continuous (fun time => frozenOperator M nu (path time)) := by
  have coefficient (k : IntegerWavevector) : Continuous (fun time => finiteStateVelocityCoefficient (path time) k) :=
    (biotSavartVelocityCLM k).continuous.comp ((evaluation k).continuous.comp continuous)
  have pairs (p q : IntegerWavevector) : Continuous (fun time => pairCLM (path time) p q) := by
    unfold pairCLM
    have scalar : Continuous (fun time => complexWavevector q ⬝ᵥ finiteStateVelocityCoefficient (path time) p) := by
      unfold dotProduct
      fun_prop
    exact ((continuous_const.mul scalar).neg).smul continuous_const
  have convection (k : IntegerWavevector) : Continuous (fun time => convectionCLM M (path time) k) := by
    unfold convectionCLM
    apply continuous_finsetSum _ (fun p _ => ?_)
    apply continuous_finsetSum _ (fun q _ => ?_)
    by_cases same : p+q=k
    · simpa only [if_pos same] using pairs p q
    · simp only [if_neg same]; exact continuous_const
  have rows (k : IntegerWavevector) : Continuous (fun time => rowCLM M nu (path time) k) :=
    continuous_const.clm_comp ((convection k).sub continuous_const)
  unfold frozenOperator
  fun_prop

theorem forward_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (forward seed M) := by
  rw [continuous_clm_apply]
  intro u
  apply Continuous.subtype_mk
  exact (frozen_continuous (modes M) nu (advector seed M) (advector_continuous seed M)).clm_apply continuous_const

theorem dual_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (dual seed M) := by
  rw [continuous_clm_apply]
  intro u
  apply Continuous.subtype_mk
  exact (frozen_continuous (modes M) nu (fun time => -advector seed M time) (advector_continuous seed M).neg).clm_apply continuous_const

theorem adjoint_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (u v : physicalSpace (modes M)) : pairing (modes M) (forward seed M time u) v=pairing (modes M) u (dual seed M time v) :=
  operator_adjoint (modes M) (modes_zero M) (modes_closed M) nu (advector seed M time) (advector_reality seed M time) u v

theorem forward_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0≤time) :
    (forward seed M time).toLinearMap=NativeWindowStageNineSource.sourceOperator seed M time := by
  have same : advector seed M time=NativeWindowStressOseenSource.advector M seed time := by
    rw [advector,curlMap_apply,value,NativeWindowStageNineSource.lift_load seed time nonnegative]
    rfl
  simp only [forward,same]
  rfl

theorem source_action_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : ∀ᵐ time : ℝ,0≤time →
    NativeWindowStageNineSource.lift (modes M) (rate seed time)=forward seed M time (value seed M time)+
      NativeWindowStageNineSource.forcing seed M time := by
  filter_upwards [NativeWindowStageNineSource.source_action_ae seed M] with time actual nonnegative
  rw [← forward_original seed M time nonnegative] at actual
  simpa only [value,NativeWindowStageNineSource.lift_load seed time nonnegative] using! actual nonnegative

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem source_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    (value seed M (step.2.clockAdvance+time),forward seed M (step.2.clockAdvance+time),dual seed M (step.2.clockAdvance+time))=
      (value step.1 M time,forward step.1 M time,dual step.1 M time) := by
  have same : advector seed M (step.2.clockAdvance+time)=advector step.1 M time := by
    simp only [advector,value,state_next seed step generated time nonnegative]
  simp only [value,state_next seed step generated time nonnegative,forward,dual,same]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceAdjoint
