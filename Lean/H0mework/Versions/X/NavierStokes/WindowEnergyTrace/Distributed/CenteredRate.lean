import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Rate
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.CenteredClock
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.CenteredPayment

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeCenteredResponseRate
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceAdjoint (value forward)
open NativeWindowTraceDualEvolution (mass inverse lifted)
open NativeWindowDistributedAdjoint (response load testAction)
open NativeResponseTensorPayment (pairTensor pairTensorCLM liftedRate)
open NativeResponseTensorClock (clockInput)
open NativeCenteredResponseTensor (centered tensor)
open NativeCenteredResponseClock (clockWork)
open NativeCenteredResponsePayment (heatWork)
open NativeResponseRateDecomposition (advection metricDefect forward_decomposition liftedRate_decomposition)
noncomputable section
variable {nu : Viscosity}

def forcing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ) :=
  NativeWindowStageNineSource.forcing seed M time+
    forward seed M time (NativeWindowHistoryMeanAction.meanValue seed M frame)

def remainingRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ) (w g : physicalSpace (modes M)) :=
  let v := centered seed M frame time
  let z := lifted seed M F radius time w
  pairTensor M (advection seed M time v) z+pairTensor M v (advection seed M time z)+
    pairTensor M (forcing seed M frame time) z+
    pairTensor M v (inverse seed M F radius time (metricDefect seed M F radius time z))-
    pairTensor M v (inverse seed M F radius time g)

theorem tensor_rate_decomposition (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ)
    (invertible : (mass seed M F radius time).IsInvertible) (w g : physicalSpace (modes M)) :
    let u := value seed M time
    let v := centered seed M frame time
    let z := lifted seed M F radius time w
    pairTensor M (forward seed M time u+NativeWindowStageNineSource.forcing seed M time) z+
      pairTensor M v (liftedRate seed M F radius time w g)=
      (pairTensor M ((-nu.coeff) • testAction (nu := nu) M v) z+
        pairTensor M v (nu.coeff • testAction (nu := nu) M z))+
      remainingRate seed M F radius frame time w g-
      tensor seed M F radius frame time (clockInput seed M F radius time w) := by
  dsimp only
  rw [NativeCenteredResponseTensor.centered_action_split seed M frame time,
    forward_decomposition seed M time (centered seed M frame time),
    liftedRate_decomposition seed M F radius time invertible w g]
  dsimp only [remainingRate,forcing]
  change pairTensorCLM M (_+_) _+pairTensorCLM M _ (_+_+_) =
    (pairTensorCLM M _ _+pairTensorCLM M _ _)+
      (pairTensorCLM M _ _+pairTensorCLM M _ _+pairTensorCLM M _ _+
        pairTensorCLM M _ _-pairTensorCLM M _ _)-
      pairTensorCLM M (centered seed M frame time)
        (inverse seed M F radius time (deriv (mass seed M F radius) time (lifted seed M F radius time w)))
  simp only [map_add,map_sub,add_apply]
  abel

theorem source_tensor_square_rate (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∀ radius ≥ low, ∀ outerRadius M observation frame
      (test : physicalSpace (modes M)) a b (ordered : a ≤ b),
      ∀ᵐ time : ℝ, time ∈ Ioo a b → time ∈ Ioo 0 horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test a b ordered
      let v := centered seed M frame time
      let z := lifted seed M F radius time (p time)
      HasDerivAt (fun t => ‖tensor seed M F radius frame t (p t)‖^2)
        (heatWork nu M v z+
          2*inner ℝ (tensor seed M F radius frame time (p time))
            (remainingRate seed M F radius frame time (p time) (load (nu := nu) observation M test time))+
          clockWork seed M F radius frame time (p time)) time := by
  obtain ⟨first,rate⟩ := NativeCenteredResponseTensor.source_tensor_rate seed horizon nonnegative
  obtain ⟨last,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  refine ⟨max first last,fun radius above outerRadius M observation frame test a b ordered => ?_⟩
  filter_upwards [rate radius ((le_max_left first last).trans above) outerRadius M observation frame test a b ordered]
    with time actual physical clock
  let F := integerWaveFrequencyCube outerRadius
  let p := response seed M observation test a b ordered
  let v := centered seed M frame time
  let z := lifted seed M F radius time (p time)
  have generated := inverted radius ((le_max_right first last).trans above) M F
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) time (Ioo_subset_Icc_self clock)
  have written := actual physical clock
  dsimp only at written ⊢
  rw [tensor_rate_decomposition seed M F radius frame time generated (p time)
    (load (nu := nu) observation M test time)] at written
  apply written.norm_sq.congr_deriv
  change 2*inner ℝ (pairTensor M v z) ((_+_)+_-_)=_
  simp only [heatWork,clockWork,inner_add_right,inner_sub_right,inner_neg_right]
  change 2*(inner ℝ (pairTensor M v z) _+inner ℝ (pairTensor M v z) _+
      inner ℝ (pairTensor M v z) _-inner ℝ (pairTensor M v z) _)=
    2*(inner ℝ (pairTensor M v z) _+inner ℝ (pairTensor M v z) _)+
      2*inner ℝ (pairTensor M v z) _+2*(-inner ℝ (pairTensor M v z) _)
  dsimp only [testAction,F,p,v,z]
  ring

end
end SaturationMonoid.NavierStokes.NativeCenteredResponseRate
