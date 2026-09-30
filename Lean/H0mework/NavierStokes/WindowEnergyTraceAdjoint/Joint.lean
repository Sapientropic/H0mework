import H0mework.NavierStokes.WindowEnergyTraceAdjoint.Time
import H0mework.NavierStokes.WindowEnergyTraceOperator.Action

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceAdjoint
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed NativeResolventAdjoint
open NativeUnheatedGlobalNegativeOne
open NativeWindowTraceOperator (jointTest)
noncomputable section
variable {nu : Viscosity}

private theorem pair_hasDerivAt (M : ℕ) {f g : ℝ →physicalSpace (modes M)}
    {f' g' : physicalSpace (modes M)} {time : ℝ} (first : HasDerivAt f f' time) (last : HasDerivAt g g' time) :
    HasDerivAt (fun t => pairing (modes M) (f t) (g t))
      (pairing (modes M) f' (g time)+pairing (modes M) (f time) g') time := by
  have generated:=((LinearMap.toContinuousLinearMap (coefficients (modes M))).hasFDerivAt.comp_hasDerivAt time first).inner ℝ
    ((LinearMap.toContinuousLinearMap (coefficients (modes M))).hasFDerivAt.comp_hasDerivAt time last)
  convert! generated using 1
  exact add_comm _ _

def joint (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) : physicalSpace (modes M) := jointTest seed observation (modes M) F radius (value seed M time)

def responseRate (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) : physicalSpace (modes M) :=
  jointTest seed observation (modes M) F radius (forward seed M time (value seed M time))+
    dual seed M time (joint seed observation M F radius time)+
      jointTest seed observation (modes M) F radius (NativeWindowStageNineSource.forcing seed M time)

def propagated (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) : ℝ → physicalSpace (modes M) :=
  backward seed M start finish ordered (joint seed observation M F radius finish)

def response (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (time : ℝ) : physicalSpace (modes M) :=
  joint seed observation M F radius time-propagated seed observation M F radius start finish ordered time

theorem joint_physical (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) (x : physicalSpace (modes M)) :
    pairing (modes M) x (joint seed observation M F radius time)=
      ∑ i : Coordinate,inner ℝ (NativeWindowTraceEnergy.relative seed F radius observation)
        (NativeWindowStressHeatSource.physical (NativeWindowStressOseenTest.evaluate (modes M) F i x*
          NativeWindowStressOseenTest.evaluate (modes M) F i (value seed M time)))-
            nu.coeff*pairing (modes M) x (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu (value seed M time)) :=
  NativeWindowTraceOperatorAction.jointTest_physical seed observation (modes M) F radius (modes_zero M) (modes_closed M) x _

theorem joint_derivative_ae (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) : ∀ᵐ time : ℝ,HasDerivAt (joint seed observation M F radius)
      (jointTest seed observation (modes M) F radius (NativeWindowStageNineSource.lift (modes M) (rate seed time))) time := by
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed] with time actual
  exact (LinearMap.toContinuousLinearMap (jointTest seed observation (modes M) F radius)).hasFDerivAt.comp_hasDerivAt time
    ((NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt time actual)

theorem response_terminal (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) : response seed observation M F radius start finish ordered finish=0 := by
  rw [response,propagated,backward_terminal,sub_self]

theorem response_derivative_ae (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (nonnegative : 0 ≤ start) : ∀ᵐ time : ℝ,time∈Ioo start finish →
    HasDerivAt (response seed observation M F radius start finish ordered)
      (responseRate seed observation M F radius time-dual seed M time (response seed observation M F radius start finish ordered time)) time := by
  filter_upwards [joint_derivative_ae seed observation M F radius,source_action_ae seed M] with time derivative actual inside
  have original:=actual (nonnegative.trans inside.1.le)
  have adjoint:HasDerivAt (propagated seed observation M F radius start finish ordered)
      (-dual seed M time (propagated seed observation M F radius start finish ordered time)) time :=
    (backward_derivative seed M start finish ordered _ time (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
  have difference:=derivative.sub adjoint
  rw [original] at difference
  convert! difference using 1
  simp only [responseRate,response,map_add,map_sub]
  abel

theorem propagated_mass_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (time : ℝ) (inside : time∈Icc start finish) :
    ‖coefficients (modes M) (propagated seed observation M F radius start finish ordered time)‖≤
      ‖coefficients (modes M) (joint seed observation M F radius finish)‖ := backward_mass_bound seed M start finish ordered _ time inside

theorem propagated_source_green (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (nonnegative : 0 ≤ start) : ∀ᵐ time : ℝ,time∈Ioo start finish →
    HasDerivAt (fun t => pairing (modes M) (value seed M t) (propagated seed observation M F radius start finish ordered t))
      (pairing (modes M) (NativeWindowStageNineSource.forcing seed M time)
        (propagated seed observation M F radius start finish ordered time)) time := by
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed,source_action_ae seed M] with time actual action inside
  have first:HasDerivAt (value seed M) (NativeWindowStageNineSource.lift (modes M) (rate seed time)) time :=
    (NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt time actual
  have last:HasDerivAt (propagated seed observation M F radius start finish ordered)
      (-dual seed M time (propagated seed observation M F radius start finish ordered time)) time :=
    (backward_derivative seed M start finish ordered _ time (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
  have generated:=pair_hasDerivAt M first last
  rw [action (nonnegative.trans inside.1.le),map_add,LinearMap.add_apply,map_neg,adjoint_pairing] at generated
  simpa only [add_comm,add_neg_cancel_right] using generated

theorem response_source_green (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (nonnegative : 0 ≤ start) : ∀ᵐ time : ℝ,time∈Ioo start finish →
    HasDerivAt (fun t => pairing (modes M) (value seed M t) (response seed observation M F radius start finish ordered t))
      (pairing (modes M) (NativeWindowStageNineSource.forcing seed M time) (response seed observation M F radius start finish ordered time)+
        pairing (modes M) (value seed M time) (responseRate seed observation M F radius time)) time := by
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed,source_action_ae seed M,
    response_derivative_ae seed observation M F radius start finish ordered nonnegative] with time actual action responseDerivative inside
  have first:HasDerivAt (value seed M) (NativeWindowStageNineSource.lift (modes M) (rate seed time)) time :=
    (NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt time actual
  have generated:=pair_hasDerivAt M first (responseDerivative inside)
  rw [action (nonnegative.trans inside.1.le),map_add,LinearMap.add_apply,map_sub,adjoint_pairing] at generated
  have equal : (pairing (modes M) (value seed M time) (dual seed M time (response seed observation M F radius start finish ordered time))+
      pairing (modes M) (NativeWindowStageNineSource.forcing seed M time) (response seed observation M F radius start finish ordered time))+
      (pairing (modes M) (value seed M time) (responseRate seed observation M F radius time)-
        pairing (modes M) (value seed M time) (dual seed M time (response seed observation M F radius start finish ordered time)))=
      pairing (modes M) (NativeWindowStageNineSource.forcing seed M time) (response seed observation M F radius start finish ordered time)+
        pairing (modes M) (value seed M time) (responseRate seed observation M F radius time) := by ring
  rw [equal] at generated
  exact generated

end
end SaturationMonoid.NavierStokes.NativeWindowTraceAdjoint
