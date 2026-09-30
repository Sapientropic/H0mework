import H0mework.Versions.X.NavierStokes.WindowEnergyTraceCoupled.CoupledAction

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCoupled
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceAdjoint (value forward dual propagated response)
open NativeWindowTraceDualEvolution (mass inverse lifted)
noncomputable section
variable {nu : Viscosity}

theorem forcing_cancellation (M : Finset IntegerWavevector) (T : Module.End ℝ (physicalSpace M))
    (symmetric : ∀ x y,pairing M x (T y)=pairing M y (T x))
    (z eta f : physicalSpace M) (same : T z=eta) :
    pairing M z (((LinearMap.id : Module.End ℝ (physicalSpace M))-T) f)+pairing M f eta=pairing M z f := by
  simp only [LinearMap.sub_apply,LinearMap.id_apply,map_sub,symmetric z f,same]
  ring

theorem square_completion (M : Finset IntegerWavevector) (T : Module.End ℝ (physicalSpace M))
    (symmetric : ∀ x y,pairing M x (T y)=pairing M y (T x))
    (u z eta : physicalSpace M) (same : T z=eta) :
    pairing M u (T u)+2*pairing M u eta+pairing M z eta=pairing M (u+z) (T (u+z)) := by
  simp only [map_add,LinearMap.add_apply,same,symmetric z u]
  ring

def q (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (time : ℝ) :=
  lifted seed M F radius observation (combined seed observation M F radius start finish ordered time)

def energy (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (time : ℝ) : ℝ :=
  NativeWindowTraceDualEvolution.energy seed M F radius observation (combined seed observation M F radius start finish ordered time)

def lyapunov (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) (z : physicalSpace (modes M)) : ℝ :=
  pairing (modes M) (forward seed M time z) (mass seed M F radius observation z)+
    pairing (modes M) z (mass seed M F radius observation (forward seed M time z))

theorem completed_energy (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (time : ℝ)
    (actual : (mass seed M F radius observation).IsInvertible) :
    pairing (modes M) (value seed M time) (mass seed M F radius observation (value seed M time))+
      2*pairing (modes M) (value seed M time) (response seed observation M F radius start finish ordered time)+
        NativeWindowTraceDualEvolution.energy seed M F radius observation (response seed observation M F radius start finish ordered time)=
      energy seed observation M F radius start finish ordered time := by
  let u:=value seed M time
  let eta:=response seed observation M F radius start finish ordered time
  let z:=lifted seed M F radius observation eta
  have restored:mass seed M F radius observation z=eta := actual.self_apply_inverse _
  have original:=square_completion (modes M) (mass seed M F radius observation).toLinearMap
    (NativeWindowTraceDualEvolution.mass_symmetric seed M F radius observation) u z eta restored
  have full:=combined_identity seed observation M F radius start finish ordered time actual
  have inverseFull:lifted seed M F radius observation (combined seed observation M F radius start finish ordered time)=u+z := by
    rw [← full]
    exact actual.inverse_apply_self _
  simp only [energy,NativeWindowTraceDualEvolution.energy]
  rw [inverseFull,← full]
  exact original

private theorem inverse_symmetric (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (actual : (mass seed M F radius observation).IsInvertible) (x y : physicalSpace (modes M)) :
    pairing (modes M) (inverse seed M F radius observation x) y=pairing (modes M) (inverse seed M F radius observation y) x := by
  have original:=NativeWindowTraceDualEvolution.mass_symmetric seed M F radius observation
    (inverse seed M F radius observation x) (inverse seed M F radius observation y)
  simp only [inverse] at original ⊢
  rw [actual.self_apply_inverse,actual.self_apply_inverse] at original
  exact original

private theorem fixed_energy_derivative (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (actual : (mass seed M F radius observation).IsInvertible)
    {w : ℝ →physicalSpace (modes M)} {w' : physicalSpace (modes M)} {time : ℝ} (derivative : HasDerivAt w w' time) :
    HasDerivAt (fun t => NativeWindowTraceDualEvolution.energy seed M F radius observation (w t))
      (2*pairing (modes M) (lifted seed M F radius observation (w time)) w') time := by
  let co:=LinearMap.toContinuousLinearMap (coefficients (modes M))
  have first:=(co.comp (inverse seed M F radius observation)).hasFDerivAt.comp_hasDerivAt time derivative
  have last:=co.hasFDerivAt.comp_hasDerivAt time derivative
  have original:=first.inner ℝ last
  convert! original using 1
  change 2*pairing (modes M) (inverse seed M F radius observation (w time)) w'=
    pairing (modes M) (inverse seed M F radius observation (w time)) w'+pairing (modes M) (inverse seed M F radius observation w') (w time)
  rw [inverse_symmetric seed observation M F radius actual w' (w time)]
  ring

theorem energy_derivative_ae (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (nonnegative : 0 ≤ start)
    (actual : (mass seed M F radius observation).IsInvertible) : ∀ᵐ time : ℝ,time∈Ioo start finish →
    HasDerivAt (energy seed observation M F radius start finish ordered)
      (-lyapunov seed observation M F radius time (q seed observation M F radius start finish ordered time)+
        2*pairing (modes M) (q seed observation M F radius start finish ordered time) (drive seed M time)) time := by
  filter_upwards [combined_derivative_ae seed observation M F radius start finish ordered nonnegative] with time derivative inside
  have original:=fixed_energy_derivative seed observation M F radius actual (derivative inside)
  have restored:mass seed M F radius observation (q seed observation M F radius start finish ordered time)=
      combined seed observation M F radius start finish ordered time := actual.self_apply_inverse _
  change HasDerivAt (energy seed observation M F radius start finish ordered)
    (2*pairing (modes M) (q seed observation M F radius start finish ordered time)
      (drive seed M time-dual seed M time (combined seed observation M F radius start finish ordered time))) time at original
  rw [map_sub,← NativeWindowTraceAdjoint.adjoint_pairing,← restored] at original
  convert! original using 1
  rw [lyapunov,NativeWindowTraceDualEvolution.mass_symmetric seed M F radius observation
    (q seed observation M F radius start finish ordered time) (forward seed M time (q seed observation M F radius start finish ordered time))]
  ring

theorem source_energy_derivative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M F,FiniteModeNegClosed F →∀ observation∈Icc 0 horizon,
      ∀ start finish (ordered : start≤finish),0 ≤ start →∀ᵐ time : ℝ,time∈Ioo start finish →
      HasDerivAt (energy seed observation M F radius start finish ordered)
        (-lyapunov seed observation M F radius time (q seed observation M F radius start finish ordered time)+
          2*pairing (modes M) (q seed observation M F radius start finish ordered time)
            (NativeWindowStageNineSource.lift (modes M) (input seed M time))) time := by
  obtain ⟨low,paid⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  refine ⟨low,fun radius above M F closed observation observed start finish ordered start0 => ?_⟩
  filter_upwards [energy_derivative_ae seed observation M F radius start finish ordered start0
    (paid radius above M F closed observation observed),input_original_ae seed M] with time derivative inputRead inside
  rw [inputRead (start0.trans inside.1.le)]
  exact derivative inside

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCoupled
