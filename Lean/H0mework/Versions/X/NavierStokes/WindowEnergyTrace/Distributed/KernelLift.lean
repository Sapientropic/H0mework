import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.CenteredRate
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.SourceTest

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeResponseKernelLift
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceAdjoint (value)
open NativeWindowDistributedAdjoint (response load testAction)
open NativeResponseRateDecomposition (advection)
open NativeDistributedSourceTest (sourceTest)
open NativeForwardWindowSource (kernel)
open NativeForwardWindowJets (kernelJet)
noncomputable section
variable {nu : Viscosity}

def amplitude (nu : Viscosity) (observation time : ℝ) : ℝ :=
  kernel (observation-time)/nu.coeff

def kernelLift (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a≤b) (time : ℝ) :=
  response seed M observation test a b ab time-amplitude nu observation time • test

def liftedLoad (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (time : ℝ) :=
  amplitude nu observation time • advection seed M time test+
    (kernelJet 1 (observation-time)/nu.coeff) • test

theorem amplitude_derivative (observation time : ℝ) :
    HasDerivAt (amplitude nu observation)
      (-kernelJet 1 (observation-time)/nu.coeff) time := by
  have generated := (NativeForwardWindowSource.kernel_smooth.differentiable (by simp)
    (observation-time)).hasDerivAt.comp time
      ((hasDerivAt_const time observation).sub (hasDerivAt_id time))
  simpa only [amplitude,kernelJet,iteratedDeriv_succ,iteratedDeriv_zero,
    Function.comp_def,sub_zero,sub_self,zero_sub,mul_neg_one] using! generated.div_const nu.coeff

theorem response_restore (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a≤b) (time : ℝ) :
    response seed M observation test a b ab time=
      kernelLift seed M observation test a b ab time+amplitude nu observation time • test := by
  simp only [kernelLift,sub_add_cancel]

theorem kernelLift_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a≤b) (time : ℝ) (inside : time∈Icc a b) :
    HasDerivWithinAt (kernelLift seed M observation test a b ab)
      (nu.coeff • testAction (nu := nu) M (kernelLift seed M observation test a b ab time)+
        advection seed M time (kernelLift seed M observation test a b ab time)+
        liftedLoad seed M observation test time) (Icc a b) time := by
  have actual := (NativeWindowDistributedAdjoint.response_derivative seed M observation test a b ab time inside).sub
    ((amplitude_derivative (nu := nu) observation time).smul_const test).hasDerivWithinAt
  apply actual.congr_deriv
  rw [NativeResponseRateDecomposition.dual_decomposition]
  simp only [kernelLift,liftedLoad,load,amplitude,map_sub,map_smul,smul_sub,smul_smul]
  rw [mul_div_cancel₀ _ nu.coeff_pos.ne']
  module

theorem kernel_nonnegative_clock_zero (observation : ℝ) (nonnegative : 0≤observation) :
    kernel observation=0 := by
  by_contra nonzero
  have := NativeForwardWindowSource.kernel_support observation nonzero
  linarith

theorem kernel_left_endpoint : kernel (-2)=0 := by
  by_contra nonzero
  have inside : (-2 : ℝ)∈Metric.ball (-3/2 : ℝ) (1/2 : ℝ) := by
    have member : (-2 : ℝ)∈Function.support (NativeForwardWindowSource.bump.normed volume) := nonzero
    rw [NativeForwardWindowSource.bump.support_normed_eq] at member
    exact member
  norm_num [Metric.mem_ball,Real.dist_eq] at inside

theorem kernelLift_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (nonnegative : 0≤observation) (test : physicalSpace (modes M)) (b : ℝ) (ordered : 0≤b) :
    kernelLift seed M observation test 0 b ordered 0=response seed M observation test 0 b ordered 0 := by
  simp only [kernelLift,amplitude,sub_zero,kernel_nonnegative_clock_zero observation nonnegative,
    zero_div,zero_smul,sub_zero]

theorem kernelLift_terminal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (nonnegative : 0≤observation) (test : physicalSpace (modes M)) :
    kernelLift seed M observation test 0 (observation+2) (by linarith) (observation+2)=0 := by
  rw [kernelLift,NativeWindowDistributedAdjoint.response_terminal]
  have endpoint : observation-(observation+2)=(-2 : ℝ) := by ring
  simp only [amplitude,endpoint,kernel_left_endpoint,zero_div,zero_smul,sub_zero]

theorem source_test_green (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (observation : ℝ) (nonnegative : 0≤observation) :
    let test := sourceTest seed M observation
    let q := kernelLift seed M observation test 0 (observation+2) (by linarith)
    ‖coefficients (modes M) test‖^2=
      pairing (modes M) (value seed M 0) (q 0)+
        ∫ time in (0 : ℝ)..(observation+2),
          pairing (modes M) (NativeWindowStageNineSource.forcing seed M time) (q time)+
          amplitude nu observation time *
            pairing (modes M) (NativeWindowStageNineSource.forcing seed M time) test := by
  dsimp only
  rw [← NativeDistributedSourceTest.source_pair,
    NativeWindowDistributedAdjoint.window_source_green seed M observation nonnegative]
  rw [← kernelLift_initial seed M observation nonnegative]
  congr 1
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only
  rw [response_restore]
  simp only [map_add,map_smul,smul_eq_mul]

theorem centered_forcing_restore (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (observation frame sample time : ℝ) (test : physicalSpace (modes M))
    (a b : ℝ) (ab : a≤b) :
    NativeResponseTensorPayment.pairTensor M (NativeCenteredResponseRate.forcing seed M frame sample)
      (response seed M observation test a b ab time)=
    NativeResponseTensorPayment.pairTensor M (NativeCenteredResponseRate.forcing seed M frame sample)
      (kernelLift seed M observation test a b ab time)+
      amplitude nu observation time •
        NativeResponseTensorPayment.pairTensor M (NativeCenteredResponseRate.forcing seed M frame sample) test := by
  rw [response_restore]
  simp only [← NativeResponseTensorPayment.pairTensorCLM_apply,map_add,map_smul]

end
end SaturationMonoid.NavierStokes.NativeResponseKernelLift
