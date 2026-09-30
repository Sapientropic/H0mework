import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HierarchyWords
import H0mework.Versions.X.NavierStokes.WindowSourcePreparation.Source

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowStageNineSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open NativeWindowStressOseenTest
open NativeFiniteActionResolvent NativeResolventAdjoint NativeWindowOperatorGreen NativeWindowAugmentedFixedOperator
open NativeResolventCompactness NativeUnheatedGlobalNegativeOne NativeWholeH1Mixed NativeWindowStressOseenSource
open NativeUnheatedIntegralBilinear NativeUnheatedPairGlobalEvolution
noncomputable section
variable {nu : Viscosity}

def sourceFunctional (M : Finset IntegerWavevector) : State →L[ℝ] physicalSpace M →L[ℝ] ℝ :=
  ∑ k ∈ M,∑ i : Coordinate,(innerSL ℝ).bilinearComp (NativeUnheatedTriadRows.decode k i)
    (LinearMap.toContinuousLinearMap (rowRead M k i))

def riesz (M : Finset IntegerWavevector) : physicalSpace M ≃L[ℝ] (physicalSpace M →L[ℝ] ℝ) :=
  ((duality M).trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

def lift (M : Finset IntegerWavevector) : State →L[ℝ] physicalSpace M :=
  (riesz M).symm.toContinuousLinearMap.comp (sourceFunctional M)

theorem lift_pairing (M : Finset IntegerWavevector) (data : State) (value : physicalSpace M) :
    pairing M (lift M data) value=∑ k ∈ M,∑ i : Coordinate,inner ℝ
      (NativeUnheatedTriadRows.decode k i data) (value.1 k i) := by
  have generated := congrArg (fun f : physicalSpace M →L[ℝ] ℝ => f value)
    ((riesz M).apply_symm_apply (sourceFunctional M data))
  change pairing M (lift M data) value=sourceFunctional M data value at generated
  simpa only [sourceFunctional,sum_apply,ContinuousLinearMap.bilinearComp_apply,innerSL_apply_apply] using! generated

theorem lift_equal (M : Finset IntegerWavevector) (data : State) (value : physicalSpace M)
    (same : ∀ k∈M,∀ i,NativeUnheatedTriadRows.decode k i data=value.1 k i) : lift M data=value := by
  apply (riesz M).injective
  ext testValue
  change pairing M (lift M data) testValue=pairing M value testValue
  rw [lift_pairing]
  have rows : (∑ k ∈ M,∑ i : Coordinate,inner ℝ (NativeUnheatedTriadRows.decode k i data) (testValue.1 k i))=
      ∑ k ∈ M,∑ i : Coordinate,inner ℝ (value.1 k i) (testValue.1 k i) := by
    apply Finset.sum_congr rfl
    intro k inside
    simp only [same k inside]
  rw [rows]
  change _=inner ℝ (coefficients M value) (coefficients M testValue)
  rw [PiLp.inner_apply,Fintype.sum_prod_type]
  exact (Finset.sum_coe_sort M (fun k => ∑ i : Coordinate,inner ℝ (value.1 k i) (testValue.1 k i))).symm

theorem lift_load (seed : GeneratedWholeRestartCurrent nu) (sample : ℝ) (nonnegative : 0 ≤ sample) (M : ℕ) :
    lift (modes M) (state seed sample)=load M seed sample := by
  apply lift_equal
  exact load_reads seed sample nonnegative M (modes M) (fun _ inside _ => inside)

theorem lift_action (seed : GeneratedWholeRestartCurrent nu) (sample : ℝ) (M : ℕ) :
    lift (modes M) (NativeUnheatedSourceQuadraticApprox.value M seed sample)=K M seed sample (load M seed sample) := by
  apply lift_equal
  exact action_reads seed sample M (modes M) (fun _ inside _ => inside)

theorem lift_gradient_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    ∀ᵐ sample : ℝ,0 ≤ sample →lift (modes M) (NativeWindowHistoryGradient.gradientState seed sample)=
      laplacian (modes M) (modes_zero M) (modes_closed M) nu (load M seed sample) := by
  filter_upwards [gradient_decode_ae seed] with sample actual nonnegative
  apply lift_equal
  intro k inside i
  rw [actual nonnegative,NativeUnheatedTriadRows.velocity,
    load_reads seed sample nonnegative M (modes M) (fun _ inside _ => inside) k inside i,laplacian_row]
  rfl

def forcing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) : physicalSpace (modes M) :=
  lift (modes M) (NativeUnheatedSourceWeightedTail.nonlinear seed sample-
    NativeUnheatedSourceQuadraticApprox.value M seed sample)

def sourceOperator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) :=
  physicalOperator (modes M) (modes_zero M) (modes_closed M) nu (advector M seed sample) (advector_reality M seed sample)

theorem source_action_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    ∀ᵐ sample : ℝ,0 ≤ sample →lift (modes M) (rate seed sample)=
      sourceOperator seed M sample (load M seed sample)+forcing seed M sample := by
  filter_upwards [lift_gradient_ae seed M] with sample gradient nonnegative
  have original : rate seed sample=NativeUnheatedSourceWeightedTail.nonlinear seed sample-
      nu.coeff • NativeWindowHistoryGradient.gradientState seed sample := by
    simp only [NativeWindowHistoryGradient.gradientState,smul_sub,smul_smul]
    rw [mul_inv_cancel₀ nu.coeff_pos.ne',one_smul]
    simp only [one_smul]
    abel
  rw [original,map_sub,map_smul,gradient nonnegative,sourceOperator,operator_split]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,forcing,map_sub,lift_action,K,neg_smul]
  abel

theorem word_action_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) :
    ∀ᵐ sample : ℝ,0 ≤ sample →
      NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) directions
          (lift (modes M) (rate seed sample))=
        let D:=NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) directions
        sourceOperator seed M sample (D (load M seed sample))+
          NativeWindowStageNineWords.bracket D (sourceOperator seed M sample) (load M seed sample)+
          D (forcing seed M sample) := by
  filter_upwards [source_action_ae seed M] with sample original nonnegative
  rw [original nonnegative]
  exact NativeWindowStageNineWords.action_split _ _ _ _ _ _ _

def coefficient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) (sample : ℝ) : physicalSpace (modes M) :=
  NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) directions (lift (modes M) (state seed sample))

def coefficientRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) (sample : ℝ) : physicalSpace (modes M) :=
  NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) directions (lift (modes M) (rate seed sample))

theorem coefficient_row (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) (sample : ℝ)
    (nonnegative : 0 ≤ sample) (k : IntegerWavevector) (inside : k∈modes M) (i : Coordinate) :
    (coefficient seed M directions sample).1 k i=
      NativeWindowStageNineWords.multiplier directions k*NativeUnheatedTriadRows.velocity seed sample k i := by
  rw [coefficient,lift_load seed sample nonnegative,NativeWindowStageNineWords.word_row]
  have read := load_reads seed sample nonnegative M (modes M) (fun _ inside _ => inside) k inside i
  exact congrArg (fun z : ℂ => NativeWindowStageNineWords.multiplier directions k*z) read.symm

theorem coefficient_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) :
    ∀ᵐ sample : ℝ,0<sample →HasDerivAt (coefficient seed M directions) (coefficientRate seed M directions sample) sample := by
  filter_upwards [source_hasDerivAt_ae seed] with sample actual positive
  exact (LinearMap.toContinuousLinearMap (NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) directions)).hasFDerivAt.comp_hasDerivAt sample
    ((lift (modes M)).hasFDerivAt.comp_hasDerivAt sample (actual positive))

theorem coefficient_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate)
    (a b : ℝ) (a0 : 0≤a) (b0 : 0≤b) :
    coefficient seed M directions b-coefficient seed M directions a=
      ∫sample in a..b,coefficientRate seed M directions sample := by
  let D:=(LinearMap.toContinuousLinearMap (NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) directions)).comp (lift (modes M))
  have original := congrArg D (source_integral seed a b a0 b0)
  rw [map_sub,← D.intervalIntegral_comp_comm (rate_intervalIntegrable seed a b a0 b0)] at original
  exact original

theorem coefficient_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) :
    coefficient seed M directions 0=
      NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) directions
        (lift (modes M) (NativeWholeH1Pairing.inverseGradient (NativeForwardWindowSource.source seed (-2)).fst)) := by
  rw [NativeWindowPreparationSource.window_initial seed (-2) le_rfl]
  rfl

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem coefficient_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (M : ℕ) (directions : List Coordinate)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    coefficient seed M directions (step.2.clockAdvance+time)=coefficient step.1 M directions time := by
  simp only [coefficient,state_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowStageNineSource
