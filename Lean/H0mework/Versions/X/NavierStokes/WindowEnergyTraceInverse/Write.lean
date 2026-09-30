import H0mework.Versions.X.NavierStokes.WindowEnergyTraceInverse.Mass

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceDualEvolution
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceOperatorTime (quadraticJet)
open NativeWindowTraceAdjoint (forward dual propagated response responseRate)
noncomputable section
variable {nu : Viscosity}

private theorem pair_derivative (M : ℕ) {f g : ℝ →physicalSpace (modes M)}
    {f' g' : physicalSpace (modes M)} {time : ℝ} (first : HasDerivAt f f' time) (last : HasDerivAt g g' time) :
    HasDerivAt (fun t => pairing (modes M) (f t) (g t))
      (pairing (modes M) f' (g time)+pairing (modes M) (f time) g') time := by
  have generated:=((LinearMap.toContinuousLinearMap (coefficients (modes M))).hasFDerivAt.comp_hasDerivAt time first).inner ℝ
    ((LinearMap.toContinuousLinearMap (coefficients (modes M))).hasFDerivAt.comp_hasDerivAt time last)
  convert! generated using 1
  exact add_comm _ _

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (horizon time : ℝ) (inside : time∈Ioo 0 horizon)
    (generated : ∀ t∈Icc 0 horizon,(mass seed M F radius t).IsInvertible)
    {w : ℝ →physicalSpace (modes M)} {w' : physicalSpace (modes M)} (actual : HasDerivAt w w' time) :
    HasDerivAt (fun t => energy seed M F radius t (w t))
      (2*pairing (modes M) (lifted seed M F radius time (w time)) w'-
        quadraticJet seed (modes M) F radius 1 time (lifted seed M F radius time (w time))) time := by
  let q:=fun t => lifted seed M F radius t (w t)
  have invertible:=generated time (Ioo_subset_Icc_self inside)
  have qDeriv:DifferentiableAt ℝ q time := (inverse_differentiableAt seed M F radius time invertible).clm_apply actual.differentiableAt
  have mDeriv:=((mass_contDiff seed M F radius).differentiable (by norm_num) time).hasDerivAt
  have relation:(fun t => mass seed M F radius t (q t)) =ᶠ[𝓝 time] w := by
    filter_upwards [Icc_mem_nhds inside.1 inside.2] with t ht
    exact (generated t ht).self_apply_inverse (w t)
  have equation:mass seed M F radius time (deriv q time)+deriv (mass seed M F radius) time (q time)=w' := by
    have product:=(mDeriv.clm_apply qDeriv.hasDerivAt).congr_of_eventuallyEq relation.symm
    simpa only [add_comm] using product.unique actual
  have paired:=congrArg (fun z => pairing (modes M) (q time) z) equation
  rw [map_add,mass_rate_pair] at paired
  have liftEq:mass seed M F radius time (q time)=w time := invertible.self_apply_inverse _
  have first:pairing (modes M) (deriv q time) (w time)=
      pairing (modes M) (q time) w'-quadraticJet seed (modes M) F radius 1 time (q time) := by
    rw [← liftEq,mass_symmetric]
    linarith only [paired]
  have scalar:=pair_derivative M qDeriv.hasDerivAt actual
  rw [first] at scalar
  convert! scalar using 1
  change 2*pairing (modes M) (q time) w'-_=(pairing (modes M) (q time) w'-_)+pairing (modes M) (q time) w'
  ring

def lyapunov (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (z : physicalSpace (modes M)) : ℝ :=
  pairing (modes M) (forward seed M time z) (mass seed M F radius time z)+
    pairing (modes M) z (mass seed M F radius time (forward seed M time z))

theorem lyapunov_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (z : physicalSpace (modes M)) : lyapunov seed M F radius time z=
      pairing (modes M) z (NativeWindowOperatorGreen.lyapunov (modes M) (modes_zero M) (modes_closed M) nu
        (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time)
        (mass seed M F radius time).toLinearMap z) :=
  NativeWindowOperatorGreen.whole_green _ _ _ _ _ _ _ _

theorem adjoint_generator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (actual : (mass seed M F radius time).IsInvertible) (w forcing : physicalSpace (modes M)) :
    2*pairing (modes M) (lifted seed M F radius time w) (forcing-dual seed M time w)=
      -lyapunov seed M F radius time (lifted seed M F radius time w)+
        2*pairing (modes M) (lifted seed M F radius time w) forcing := by
  let z:=lifted seed M F radius time w
  have restore:mass seed M F radius time z=w := actual.self_apply_inverse _
  rw [map_sub,← NativeWindowTraceAdjoint.adjoint_pairing]
  rw [lyapunov,mass_symmetric seed M F radius time z (forward seed M time z),restore]
  ring

theorem transported_energy_derivative (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (horizon : ℝ)
    (generated : ∀ t∈Icc 0 horizon,(mass seed M F radius t).IsInvertible) (time : ℝ)
    (clock : time∈Ioo 0 horizon) (inside : time∈Ioo start finish) :
    HasDerivAt (fun t => energy seed M F radius t (propagated seed observation M F radius start finish ordered t))
      (-quadraticJet seed (modes M) F radius 1 time
        (lifted seed M F radius time (propagated seed observation M F radius start finish ordered time))-
          lyapunov seed M F radius time (lifted seed M F radius time (propagated seed observation M F radius start finish ordered time))) time := by
  have original:HasDerivAt (propagated seed observation M F radius start finish ordered)
      (-dual seed M time (propagated seed observation M F radius start finish ordered time)) time :=
    (NativeWindowTraceAdjoint.backward_derivative seed M start finish ordered _ time (Ioo_subset_Icc_self inside)).hasDerivAt
      (Icc_mem_nhds inside.1 inside.2)
  have written:=energy_hasDerivAt seed M F radius horizon time clock generated original
  have green:=adjoint_generator seed M F radius time (generated time (Ioo_subset_Icc_self clock))
    (propagated seed observation M F radius start finish ordered time) 0
  simp only [zero_sub,map_zero,mul_zero,add_zero] at green
  rw [green] at written
  convert! written using 1
  ring

theorem response_energy_derivative_ae (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (nonnegative : 0 ≤ start) (horizon : ℝ)
    (generated : ∀ t∈Icc 0 horizon,(mass seed M F radius t).IsInvertible) : ∀ᵐ time : ℝ,
    time∈Ioo 0 horizon →time∈Ioo start finish →
    HasDerivAt (fun t => energy seed M F radius t (response seed observation M F radius start finish ordered t))
      (-quadraticJet seed (modes M) F radius 1 time
        (lifted seed M F radius time (response seed observation M F radius start finish ordered time))-
          lyapunov seed M F radius time (lifted seed M F radius time (response seed observation M F radius start finish ordered time))+
            2*pairing (modes M) (lifted seed M F radius time (response seed observation M F radius start finish ordered time))
              (responseRate seed observation M F radius time)) time := by
  filter_upwards [NativeWindowTraceAdjoint.response_derivative_ae seed observation M F radius start finish ordered nonnegative] with time actual clock inside
  have written:=energy_hasDerivAt seed M F radius horizon time clock generated (actual inside)
  rw [adjoint_generator seed M F radius time (generated time (Ioo_subset_Icc_self clock))] at written
  convert! written using 1
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowTraceDualEvolution
