import H0mework.NavierStokes.WindowEnergyTraceCoupled.CoupledBound

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCoupled
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint NativeUnheatedIntegralBilinear
open NativeWindowTraceAdjoint (value forward dual propagated response)
open NativeWindowTraceDualEvolution (mass inverse lifted)
noncomputable section
variable {nu : Viscosity}

theorem combined_ac (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) :
    AbsolutelyContinuousOnInterval (combined seed observation M F radius start finish ordered) start finish :=
  (NativeWindowTraceAdjoint.value_ac seed M start finish).sub
    (NativeWindowTraceAdjoint.backward_ac seed M start finish ordered (NativeWindowTraceAdjoint.joint seed observation M F radius finish))

theorem energy_ac (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) :
    AbsolutelyContinuousOnInterval (energy seed observation M F radius start finish ordered) start finish := by
  let co:=LinearMap.toContinuousLinearMap (coefficients (modes M))
  let B:=(innerSL ℝ).bilinearComp (co.comp (inverse seed M F radius observation)) co
  have read (u v : physicalSpace (modes M)) :
      B u v=pairing (modes M) (inverse seed M F radius observation u) v := rfl
  have actual:=diagonal_ac B (combined_ac seed observation M F radius start finish ordered)
  simpa only [read] using! actual

theorem terminal_energy (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (actual : (mass seed M F radius observation).IsInvertible) :
    energy seed observation M F radius start finish ordered finish=
      pairing (modes M) (value seed M finish) (mass seed M F radius observation (value seed M finish)) := by
  have original:=completed_energy seed observation M F radius start finish ordered finish actual
  rw [NativeWindowTraceAdjoint.response_terminal,NativeWindowTraceDualEvolution.energy,lifted,map_zero,
    map_zero,mul_zero,add_zero,add_zero] at original
  exact original.symm

def netRate (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (time : ℝ) : ℝ :=
  -lyapunov seed observation M F radius time (q seed observation M F radius start finish ordered time)+
    2*pairing (modes M) (q seed observation M F radius start finish ordered time)
      (NativeWindowStageNineSource.lift (modes M) (input seed M time))

theorem source_write (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M F,FiniteModeNegClosed F →∀ observation∈Icc 0 horizon,
      ∀ start finish (ordered : start≤finish),0 ≤ start →
      IntervalIntegrable (netRate seed observation M F radius start finish ordered) volume start finish ∧
      pairing (modes M) (value seed M finish) (mass seed M F radius observation (value seed M finish))-
        energy seed observation M F radius start finish ordered start=
          ∫t in start..finish,netRate seed observation M F radius start finish ordered t := by
  obtain ⟨inverseLow,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  obtain ⟨derivativeLow,generated⟩ := source_energy_derivative seed horizon nonnegative
  refine ⟨max inverseLow derivativeLow,fun radius above M F closed observation observed start finish ordered start0 => ?_⟩
  have continuous:=energy_ac seed observation M F radius start finish ordered
  have actual:∀ᵐ t : ℝ,t∈uIcc start finish →HasDerivAt (energy seed observation M F radius start finish ordered)
      (netRate seed observation M F radius start finish ordered t) t := by
    filter_upwards [generated radius ((le_max_right _ _).trans above) M F closed observation observed start finish ordered start0,
      (volume : Measure ℝ).ae_ne start,(volume : Measure ℝ).ae_ne finish] with t derivative left right ht
    rw [uIcc_of_le ordered] at ht
    exact derivative ⟨lt_of_le_of_ne ht.1 (Ne.symm left),lt_of_le_of_ne ht.2 right⟩
  have normed:IntervalIntegrable (netRate seed observation M F radius start finish ordered) volume start finish := by
    apply (intervalIntegrable_iff').mpr
    refine ((intervalIntegrable_iff').mp continuous.intervalIntegrable_deriv).congr ?_
    filter_upwards [ae_restrict_of_ae actual,ae_restrict_mem measurableSet_uIcc] with t derivative ht
    exact (derivative ht).deriv
  have written:=integral_of_ac_derivative _ _ continuous normed actual
  rw [terminal_energy seed observation M F radius start finish ordered
    (inverted radius ((le_max_left _ _).trans above) M F closed observation observed)] at written
  exact ⟨normed,written⟩

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCoupled
