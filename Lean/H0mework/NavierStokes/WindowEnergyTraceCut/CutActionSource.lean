import H0mework.NavierStokes.WindowEnergyTraceCut.CutResponseSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCutAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventCompactness NativeResolventAdjoint
open NativeWindowTraceAdjoint (value forward dual)
open NativeWindowTraceEndpointWindow (terminal)
open NativeWindowTraceCutOperator (jointTest)
open NativeUnheatedStressPairEvolution (kernelWeight)
noncomputable section
variable {nu : Viscosity}

def form (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) : State →L[ℝ] State →L[ℝ] ℝ :=
  let co:=LinearMap.toContinuousLinearMap (coefficients (modes M))
  let lift:=NativeWindowStageNineSource.lift (modes M)
  (innerSL ℝ).bilinearComp (co.comp lift)
    (co.comp ((LinearMap.toContinuousLinearMap (jointTest seed frame (modes M) F radius)).comp lift))

theorem form_apply (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (x y : State) : form seed frame M F radius x y=
      pairing (modes M) (NativeWindowStageNineSource.lift (modes M) x)
        (jointTest seed frame (modes M) F radius (NativeWindowStageNineSource.lift (modes M) y)) := rfl

def diagonal (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (sample : ℝ) : ℝ := pairing (modes M) (value seed M sample) (terminal seed frame M F radius sample)

def actual (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (sample : ℝ) : ℝ :=
  pairing (modes M) (NativeWindowTraceCutResponse.forcing seed frame M F radius sample) (value seed M sample)+
    pairing (modes M) (NativeWindowStageNineSource.forcing seed M sample) (terminal seed frame M F radius sample)

theorem diagonal_original (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) : diagonal seed frame M F radius=NativeWindowHierarchyPairWindow.pair seed (form seed frame M F radius) := rfl

theorem actual_original (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) : ∀ᵐ sample : ℝ,0 ≤ sample →actual seed frame M F radius sample=
      NativeWindowHierarchyPairWindow.action seed (form seed frame M F radius) sample := by
  filter_upwards [NativeWindowTraceAdjoint.source_action_ae seed M] with sample source sample0
  simp only [NativeWindowHierarchyPairWindow.action,form_apply,source sample0,map_add,LinearMap.add_apply,actual,
    NativeWindowTraceCutResponse.forcing]
  change (pairing (modes M) (jointTest seed frame (modes M) F radius (forward seed M sample (value seed M sample))) (value seed M sample)+
    pairing (modes M) (dual seed M sample (terminal seed frame M F radius sample)) (value seed M sample)+
    pairing (modes M) (jointTest seed frame (modes M) F radius (NativeWindowStageNineSource.forcing seed M sample)) (value seed M sample))+
    pairing (modes M) (NativeWindowStageNineSource.forcing seed M sample) (terminal seed frame M F radius sample)=_
  rw [pairing_symmetric (modes M) (dual seed M sample _),← NativeWindowTraceAdjoint.adjoint_pairing]
  rw [pairing_symmetric (modes M) (jointTest seed frame (modes M) F radius (forward seed M sample _)),
    pairing_symmetric (modes M) (jointTest seed frame (modes M) F radius (NativeWindowStageNineSource.forcing seed M sample))]
  dsimp only [terminal,value]
  ring

theorem actual_integrable (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (a0 : 0≤a) (b0 : 0≤b) : IntervalIntegrable (actual seed frame M F radius) volume a b := by
  apply (intervalIntegrable_iff').mpr
  refine ((intervalIntegrable_iff').mp (NativeWindowHierarchyPairWindow.action_integrable seed (form seed frame M F radius) a b)).congr ?_
  filter_upwards [ae_restrict_of_ae (actual_original seed frame M F radius),ae_restrict_mem measurableSet_uIcc] with sample source inside
  exact (source ((le_min a0 b0).trans inside.1)).symm

theorem unweighted_write (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (a0 : 0≤a) (b0 : 0≤b) :
    diagonal seed frame M F radius b-diagonal seed frame M F radius a=∫sample in a..b,actual seed frame M F radius sample := by
  apply NativeUnheatedIntegralBilinear.integral_of_ac_derivative _ _
    (NativeWindowHierarchyPairWindow.pair_ac seed (form seed frame M F radius) a b)
    (actual_integrable seed frame M F radius a b a0 b0)
  filter_upwards [NativeWindowHierarchyPairWindow.pair_derivative seed (form seed frame M F radius),
    actual_original seed frame M F radius] with sample derivative source inside
  rw [source ((le_min a0 b0).trans inside.1)]
  exact derivative

def window (seed : GeneratedWholeRestartCurrent nu) (frame sampling : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius order : ℕ) : ℝ :=
  ∫sample in sampling+1..sampling+2,kernelWeight order sampling 0 sample • actual seed frame M F radius sample

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (frame sampling : ℝ) (sampling0 : 0 ≤ sampling)
    (M : ℕ) (F : Finset IntegerWavevector) (radius order : ℕ) : window seed frame sampling M F radius order=
      NativeWindowHierarchyPairWindow.window seed (form seed frame M F radius) (order+1) sampling := by
  rw [NativeWindowHierarchyPairWindow.window_write]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [actual_original seed frame M F radius] with sample source inside
  rw [uIoc_of_le (by linarith : sampling+1 ≤ sampling+2)] at inside
  rw [source (by linarith [inside.1])]

theorem window_diagonal (seed : GeneratedWholeRestartCurrent nu) (frame sampling : ℝ) (sampling0 : 0 ≤ sampling)
    (M : ℕ) (F : Finset IntegerWavevector) (radius order : ℕ) : window seed frame sampling M F radius order=
      ∫sample in sampling+1..sampling+2,kernelWeight (order+1) sampling 0 sample • diagonal seed frame M F radius sample := by
  rw [weighted_write seed frame sampling sampling0 M F radius order,NativeWindowHierarchyPairWindow.window_original,← diagonal_original]

def responseRemainder (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (sample : ℝ) : ℝ :=
  pairing (modes M) (NativeWindowTraceCutResponse.forcing seed frame M F radius sample)
    (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F radius (value seed M sample)+
      NativeWindowTraceAdjoint.backward seed M a b ab (terminal seed frame M F radius b) sample)+
    pairing (modes M) (NativeWindowStageNineSource.forcing seed M sample) (terminal seed frame M F radius sample)

theorem response_split (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (sample : ℝ) : actual seed frame M F radius sample=
      NativeWindowTraceCutResponse.work seed frame M F radius a b ab sample+responseRemainder seed frame M F radius a b ab sample := by
  simp only [actual,NativeWindowTraceCutResponse.work,NativeWindowTraceCutResponse.response,responseRemainder,
    terminal,jointTest,LinearMap.sub_apply,LinearMap.id_apply,map_add,map_sub]
  ring

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem form_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame : ℝ) (frame0 : 0≤frame)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    form seed (step.2.clockAdvance+frame) M F radius=form step.1 frame M F radius := by
  simp only [form,NativeWindowTraceCutOperator.jointTest_next seed step generated frame frame0]

theorem window_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame sampling : ℝ) (frame0 : 0≤frame) (sampling0 : 0 ≤ sampling)
    (M : ℕ) (F : Finset IntegerWavevector) (radius order : ℕ) :
    window seed (step.2.clockAdvance+frame) (step.2.clockAdvance+sampling) M F radius order=
      window step.1 frame sampling M F radius order := by
  rw [weighted_write seed _ _ (add_nonneg step.2.clockAdvance_pos.le sampling0),weighted_write step.1 frame sampling sampling0,
    form_next seed step generated frame frame0 M F radius,
    NativeWindowHierarchyPairWindow.window_next seed (form step.1 frame M F radius) (order+1) step generated sampling sampling0]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCutAction
