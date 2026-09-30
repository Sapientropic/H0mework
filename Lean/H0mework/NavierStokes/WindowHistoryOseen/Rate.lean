import H0mework.NavierStokes.WindowHistoryOseen.Action

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryOseen
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeResolventCompactness NativeFiniteActionResolvent NativeWholeH1Mixed NativeEndpointVelocityCarrier
open NativeWholeResolvent (wholePhysical)
open NativePhysicalPairing (includeCLM)
open NativeNegativeOneInclusion (lowerCLM lowerWeight lowerWeight_positive)
open NativeWindowAugmentedFixedOperator (rowRead)
noncomputable section
variable {nu : Viscosity}

def weakDecode (wave : IntegerWavevector) (coordinate : Coordinate) : State →L[ℝ] ℂ :=
  if zero : wave=0 then 0 else (lowerWeight ⟨wave,zero⟩)⁻¹ • NativeUnheatedTriadRows.decode wave coordinate

theorem weakDecode_lower (wave : IntegerWavevector) (coordinate : Coordinate) (value : State) :
    weakDecode wave coordinate (lowerCLM value)=NativeUnheatedTriadRows.decode wave coordinate value := by
  by_cases zero : wave=0
  · subst wave
    simp [weakDecode,NativeUnheatedTriadRows.decode_apply,wholeVelocity_zero]
  · have row : wholeVelocity (lowerCLM value) wave coordinate=
        lowerWeight ⟨wave,zero⟩ • wholeVelocity value wave coordinate := by
      rw [wholeVelocity_nonzero _ ⟨wave,zero⟩,wholeVelocity_nonzero _ ⟨wave,zero⟩]
      rfl
    rw [weakDecode,dif_neg zero,smul_apply,NativeUnheatedTriadRows.decode_apply,
      NativeUnheatedTriadRows.decode_apply,row,smul_comm,inv_smul_smul₀ (lowerWeight_positive ⟨wave,zero⟩).ne']

def weakFunctional (M : Finset IntegerWavevector) : State →L[ℝ] physicalSpace M →L[ℝ] ℝ :=
  ∑ k ∈ M,∑ i : Coordinate,(innerSL ℝ).bilinearComp (weakDecode k i)
    (LinearMap.toContinuousLinearMap (rowRead M k i))

def weakLift (M : Finset IntegerWavevector) : State →L[ℝ] physicalSpace M :=
  (NativeWindowStageNineSource.riesz M).symm.toContinuousLinearMap.comp (weakFunctional M)

theorem weakLift_lower (M : Finset IntegerWavevector) (value : State) :
    weakLift M (lowerCLM value)=NativeWindowStageNineSource.lift M value := by
  have same : weakFunctional M (lowerCLM value)=NativeWindowStageNineSource.sourceFunctional M value := by
    ext test
    simp only [weakFunctional,NativeWindowStageNineSource.sourceFunctional,sum_apply,
      ContinuousLinearMap.bilinearComp_apply,weakDecode_lower]
  rw [weakLift,ContinuousLinearMap.comp_apply,same]
  rfl

def velocityPath (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical :=
  includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.value seed M time)

def rateRead (nu : Viscosity) (M : ℕ) : NativeCompleteStressAction.FullSpace →L[ℝ] wholePhysical :=
  (includeCLM (modes M) (modes_closed M)).comp
    ((weakLift (modes M)).comp (NativeCompleteStressAction.momentumCLM nu))

def velocityRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical :=
  if 0 ≤ time then rateRead nu M (NativeUnifiedCompleteSource.source seed time) else 0

def rateBudget (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : ℝ :=
  ‖rateRead nu M‖*NativeUnifiedCompleteSource.budget seed

theorem rateBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : 0 ≤ rateBudget seed M :=
  mul_nonneg (norm_nonneg (rateRead nu M)) (Real.sqrt_nonneg _)

theorem velocityRate_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ‖velocityRate seed M time‖ ≤ rateBudget seed M := by
  by_cases positive : 0 ≤ time
  · rw [velocityRate,if_pos positive]
    exact ((rateRead nu M).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (NativeUnifiedCompleteSource.source_bound seed time) (norm_nonneg (rateRead nu M)))
  · rw [velocityRate,if_neg positive,norm_zero]
    exact rateBudget_nonnegative seed M

theorem velocityRate_measurable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    AEStronglyMeasurable (velocityRate seed M) (volume : Measure ℝ) := by
  have measured := (rateRead nu M).continuous.comp_aestronglyMeasurable (NativeUnifiedCompleteSource.source_measurable seed)
  simpa only [velocityRate,Set.piecewise,Ici,mem_ofPred_eq] using!
    (measured.restrict.piecewise (s := Ici (0 : ℝ)) (g := fun _ => (0 : wholePhysical)) measurableSet_Ici aestronglyMeasurable_const)

theorem velocityRate_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    ∀ᵐ time : ℝ,velocityRate seed M time=includeCLM (modes M) (modes_closed M)
      (NativeWindowStageNineSource.lift (modes M) (NativeUnheatedGlobalNegativeOne.rate seed time)) := by
  filter_upwards [NativeUnheatedGlobalNegativeOne.lower_rate_ae seed] with time actual
  by_cases positive : 0 ≤ time
  · rw [velocityRate,if_pos positive,rateRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
      ← actual positive,weakLift_lower]
  · rw [velocityRate,if_neg positive,NativeWindowHierarchyPairWindow.rate_before seed time (lt_of_not_ge positive),map_zero,map_zero]

theorem velocityPath_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    ∀ᵐ time : ℝ,HasDerivAt (velocityPath seed M) (velocityRate seed M time) time := by
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed,velocityRate_original seed M]
    with time actual original
  rw [original]
  exact (includeCLM (modes M) (modes_closed M)).hasFDerivAt.comp_hasDerivAt time
    ((NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt time actual)

theorem velocityRate_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    IntervalIntegrable (velocityRate seed M) volume a b := by
  apply intervalIntegrable_iff.mpr
  have constants : IntervalIntegrable (fun _ : ℝ => rateBudget seed M) volume a b := intervalIntegrable_const
  exact constants.def'.mono' (velocityRate_measurable seed M).restrict
    (Eventually.of_forall (velocityRate_bound seed M))

theorem velocityPath_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    velocityPath seed M b-velocityPath seed M a=∫ time in a..b,velocityRate seed M time := by
  let read := (includeCLM (modes M) (modes_closed M)).comp (NativeWindowStageNineSource.lift (modes M))
  change read (NativeUnheatedGlobalNegativeOne.state seed b)-read (NativeUnheatedGlobalNegativeOne.state seed a)=_
  rw [← map_sub,NativeWindowHierarchyPairWindow.source_write_total]
  rw [← read.intervalIntegral_comp_comm (NativeWindowHierarchyPairWindow.rate_integrable_total seed a b)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [velocityRate_original seed M] with time original _
  exact original.symm

theorem velocityPath_difference (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    ‖velocityPath seed M b-velocityPath seed M a‖ ≤ rateBudget seed M*|b-a| := by
  rw [velocityPath_write]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun time _ => velocityRate_bound seed M time)

theorem velocityPath_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (velocityPath seed M) :=
  (includeCLM (modes M) (modes_closed M)).continuous.comp (NativeWindowTraceAdjoint.value_continuous seed M)

theorem velocityPath_quotient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time displacement : ℝ) :
    ‖displacement⁻¹ • (velocityPath seed M (time+displacement)-velocityPath seed M time)‖ ≤ rateBudget seed M := by
  by_cases zero : displacement=0
  · simp only [zero,inv_zero,zero_smul,norm_zero]
    exact rateBudget_nonnegative seed M
  · rw [norm_smul,Real.norm_eq_abs,abs_inv]
    have bound := velocityPath_difference seed M time (time+displacement)
    rw [add_sub_cancel_left] at bound
    calc
      _ ≤ |displacement|⁻¹*(rateBudget seed M*|displacement|) :=
        mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr (abs_nonneg _))
      _ = rateBudget seed M := by field_simp

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryOseen
