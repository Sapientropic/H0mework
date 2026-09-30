import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.TensorClock
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.ConvectionTensor

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeResponseRateDecomposition
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceAdjoint (value forward dual)
open NativeWindowTraceDualEvolution (mass inverse lifted)
open NativeWindowDistributedAdjoint (response load testAction)
open NativeDistributedLyapunov (potential)
open NativeResponseTensorPayment (pairTensor pairTensorCLM pairTensorCLM_apply mixedTensor liftedRate spatial)
open NativeResponseTensorClock (clockInput clockWork)
noncomputable section
variable {nu : Viscosity}

def advection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Module.End ℝ (physicalSpace (modes M)) :=
  NativeWindowOperatorGreen.convection (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time)

theorem forward_decomposition (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (z : physicalSpace (modes M)) :
    forward seed M time z=(-nu.coeff) • testAction (nu := nu) M z+advection seed M time z :=
  NativeDistributedLyapunov.forward_split seed M time z

theorem dual_decomposition (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (z : physicalSpace (modes M)) :
    -dual seed M time z=nu.coeff • testAction (nu := nu) M z+advection seed M time z := by
  have actual := congrArg (fun A : Module.End ℝ (physicalSpace (modes M)) => A z)
    (NativeWindowOperatorGreen.adjoint_split (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time))
  change dual seed M time z=(-nu.coeff) • testAction (nu := nu) M z-advection seed M time z at actual
  rw [actual]
  module

def metricDefect (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) (z : physicalSpace (modes M)) :=
  nu.coeff • (testAction (nu := nu) M (mass seed M F radius time z)-
      mass seed M F radius time (testAction (nu := nu) M z))+
    advection seed M time (mass seed M F radius time z)-mass seed M F radius time (advection seed M time z)

theorem metricDefect_potential (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) (z : physicalSpace (modes M)) :
    metricDefect seed M F radius time z=
      nu.coeff • (testAction (nu := nu) M (potential seed M F radius time z)-
        potential seed M F radius time (testAction (nu := nu) M z))+
      nu.coeff • (advection seed M time (testAction (nu := nu) M z)-
        testAction (nu := nu) M (advection seed M time z))+
      (advection seed M time (potential seed M F radius time z)-
        potential seed M F radius time (advection seed M time z)) := by
  simp only [metricDefect,NativeDistributedLyapunov.mass_split,map_add,map_smul]
  change nu.coeff • (testAction (nu := nu) M z+
      nu.coeff • testAction (nu := nu) M (testAction (nu := nu) M z)+
      testAction (nu := nu) M (potential seed M F radius time z)-
      (testAction (nu := nu) M z+nu.coeff • testAction (nu := nu) M (testAction (nu := nu) M z)+
        potential seed M F radius time (testAction (nu := nu) M z)))+
    (advection seed M time z+nu.coeff • advection seed M time (testAction (nu := nu) M z)+
      advection seed M time (potential seed M F radius time z))-
    (advection seed M time z+nu.coeff • testAction (nu := nu) M (advection seed M time z)+
      potential seed M F radius time (advection seed M time z))=_
  module

theorem liftedRate_decomposition (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (invertible : (mass seed M F radius time).IsInvertible) (w g : physicalSpace (modes M)) :
    let z := lifted seed M F radius time w
    liftedRate seed M F radius time w g=
      nu.coeff • testAction (nu := nu) M z+advection seed M time z+
        inverse seed M F radius time (metricDefect seed M F radius time z-
          deriv (mass seed M F radius) time z-g) := by
  intro z
  have restore : mass seed M F radius time z=w := invertible.self_apply_inverse w
  have action : -dual seed M time w-g-deriv (mass seed M F radius) time z=
      mass seed M F radius time (nu.coeff • testAction (nu := nu) M z+advection seed M time z)+
        (metricDefect seed M F radius time z-deriv (mass seed M F radius) time z-g) := by
    rw [dual_decomposition,← restore]
    simp only [metricDefect,map_add,map_smul]
    module
  change (mass seed M F radius time).inverse
    (-dual seed M time w-g-deriv (mass seed M F radius) time z)=_
  rw [action,map_add,invertible.inverse_apply_self]
  rfl

def remainingRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) (w g : physicalSpace (modes M)) :=
  let u := value seed M time
  let z := lifted seed M F radius time w
  pairTensor M (advection seed M time u) z+pairTensor M u (advection seed M time z)+
    pairTensor M (NativeWindowStageNineSource.forcing seed M time) z+
    pairTensor M u (inverse seed M F radius time (metricDefect seed M F radius time z))-
    pairTensor M u (inverse seed M F radius time g)

theorem tensor_rate_decomposition (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (invertible : (mass seed M F radius time).IsInvertible) (w g : physicalSpace (modes M)) :
    let u := value seed M time
    let z := lifted seed M F radius time w
    pairTensor M (forward seed M time u+NativeWindowStageNineSource.forcing seed M time) z+
      pairTensor M u (liftedRate seed M F radius time w g)=
      (pairTensor M ((-nu.coeff) • testAction (nu := nu) M u) z+
        pairTensor M u (nu.coeff • testAction (nu := nu) M z))+
      remainingRate seed M F radius time w g-
      mixedTensor seed M F radius time (clockInput seed M F radius time w) := by
  dsimp only
  rw [forward_decomposition,liftedRate_decomposition seed M F radius time invertible w g]
  dsimp only [remainingRate]
  change pairTensorCLM M (_+_) _+pairTensorCLM M _ (_+_+_) =
    (pairTensorCLM M _ _+pairTensorCLM M _ _)+
      (pairTensorCLM M _ _+pairTensorCLM M _ _+pairTensorCLM M _ _+
        pairTensorCLM M _ _-pairTensorCLM M _ _)-
      pairTensorCLM M (value seed M time)
        (inverse seed M F radius time (deriv (mass seed M F radius) time (lifted seed M F radius time w)))
  simp only [map_add,map_sub,add_apply]
  abel

theorem source_tensor_square_rate (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∀ radius ≥ low, ∀ outerRadius M observation
      (test : physicalSpace (modes M)) a b (ordered : a ≤ b),
      ∀ᵐ time : ℝ, time ∈ Ioo a b → time ∈ Ioo 0 horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test a b ordered
      let u := value seed M time
      let z := lifted seed M F radius time (p time)
      HasDerivAt (fun t => ‖mixedTensor seed M F radius t (p t)‖^2)
        (2*nu.coeff*((∑ j : Coordinate,‖pairTensor M u (spatial M j z)‖^2)-
          ∑ j : Coordinate,‖pairTensor M (spatial M j u) z‖^2)+
        2*inner ℝ (mixedTensor seed M F radius time (p time))
          (remainingRate seed M F radius time (p time) (load (nu := nu) observation M test time))+
        clockWork seed M F radius time (p time)) time := by
  obtain ⟨first,rate⟩ := NativeResponseTensorPayment.source_tensor_rate seed horizon nonnegative
  obtain ⟨last,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  refine ⟨max first last,fun radius above outerRadius M observation test a b ordered => ?_⟩
  filter_upwards [rate radius ((le_max_left first last).trans above) outerRadius M observation test a b ordered]
    with time actual physical clock
  let F := integerWaveFrequencyCube outerRadius
  let p := response seed M observation test a b ordered
  let u := value seed M time
  let z := lifted seed M F radius time (p time)
  have generated := inverted radius ((le_max_right first last).trans above) M F
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) time (Ioo_subset_Icc_self clock)
  have written := actual physical clock
  dsimp only at written ⊢
  rw [tensor_rate_decomposition seed M F radius time generated (p time)
    (load (nu := nu) observation M test time)] at written
  have square := written.norm_sq
  apply square.congr_deriv
  have heat := NativeResponseTensorPayment.opposite_diffusion_square (nu := nu) M u z
  change 2*inner ℝ (pairTensor M u z)
    (pairTensor M ((-nu.coeff) • testAction (nu := nu) M u) z+
      pairTensor M u (nu.coeff • testAction (nu := nu) M z))=_ at heat
  change 2*inner ℝ (pairTensor M u z) ((_+_)+_-_)=_
  simp only [inner_add_right,inner_sub_right] at ⊢ heat
  change _ = 2*nu.coeff*((∑ j : Coordinate,‖pairTensor M u (spatial M j z)‖^2)-
      ∑ j : Coordinate,‖pairTensor M (spatial M j u) z‖^2)+
    2*inner ℝ (pairTensor M u z)
      (remainingRate seed M F radius time (p time) (load (nu := nu) observation M test time))+
    2*inner ℝ (pairTensor M u z) (-mixedTensor seed M F radius time (clockInput seed M F radius time (p time)))
  rw [inner_neg_right]
  linarith only [heat]

end
end SaturationMonoid.NavierStokes.NativeResponseRateDecomposition
