import H0mework.Versions.X.NavierStokes.WindowEnergyTraceInverse.Control

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeResponseClockPayment
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceDualEvolution (mass lifted energy)
noncomputable section
variable {nu : Viscosity}

theorem mass_derivative_symmetric (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) (x y : physicalSpace (modes M)) :
    pairing (modes M) x (deriv (mass seed M F radius) time y)=
      pairing (modes M) y (deriv (mass seed M F radius) time x) := by
  have rate := ((NativeWindowTraceDualEvolution.mass_contDiff seed M F radius).differentiable
    (by norm_num) time).hasDerivAt
  have paired (u v : physicalSpace (modes M)) :
      HasDerivAt (fun t => pairing (modes M) u (mass seed M F radius t v))
        (pairing (modes M) u (deriv (mass seed M F radius) time v)) time := by
    have actual := (LinearMap.toContinuousLinearMap (pairing (modes M) u)).hasFDerivAt.comp_hasDerivAt
      time (rate.clm_apply (hasDerivAt_const time v))
    simpa only [map_zero,add_zero] using! actual
  have first := paired x y
  have same : (fun t => pairing (modes M) x (mass seed M F radius t y))=
      (fun t => pairing (modes M) y (mass seed M F radius t x)) :=
    funext fun t => NativeWindowTraceDualEvolution.mass_symmetric seed M F radius t x y
  rw [same] at first
  exact first.unique (paired y x)

private theorem relative_pair (M : ℕ)
    (T A : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M)) (C : ℝ)
    (symmetric : ∀ x y, pairing (modes M) x (A y)=pairing (modes M) y (A x))
    (diagonal : ∀ x, |pairing (modes M) x (A x)| ≤ C*pairing (modes M) x (T x))
    (x y : physicalSpace (modes M)) :
    2*pairing (modes M) x (A y) ≤
      C*(pairing (modes M) x (T x)+pairing (modes M) y (T y)) := by
  have plus := (le_abs_self _).trans (diagonal (x+y))
  have minus := (neg_le_abs _).trans (diagonal (x-y))
  simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply] at plus minus
  rw [← symmetric x y] at plus minus
  linarith only [plus,minus]

private theorem inverse_clock (M : ℕ)
    (T A : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M))
    (invertible : T.IsInvertible) (C : ℝ) (positive : 0 < C)
    (symmetric : ∀ x y, pairing (modes M) x (A y)=pairing (modes M) y (A x))
    (diagonal : ∀ x, |pairing (modes M) x (A x)| ≤ C*pairing (modes M) x (T x))
    (w : physicalSpace (modes M)) :
    pairing (modes M) (T.inverse (A (T.inverse w))) (A (T.inverse w)) ≤
      C^2*pairing (modes M) (T.inverse w) w := by
  let z := T.inverse w
  let q := T.inverse (A z)
  have restore : T z=w := invertible.self_apply_inverse w
  have clock : T q=A z := invertible.self_apply_inverse (A z)
  have paid := relative_pair M T A C symmetric diagonal q (C • z)
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,restore,clock] at paid
  change pairing (modes M) q (A z) ≤ C^2*pairing (modes M) z w
  apply (mul_le_mul_iff_right₀ positive).mp
  nlinarith only [paid]

theorem source_inverse_clock_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M,
      ∀ time ∈ Icc 0 horizon, ∀ w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      let z := lifted seed M F radius time w
      energy seed M F radius time (deriv (mass seed M F radius) time z) ≤
        C^2*energy seed M F radius time w := by
  obtain ⟨low,K,K0,source⟩ := NativeWindowTraceDualEvolution.source_control seed horizon nonnegative
  have positive : 0 < K+1 := by positivity
  refine ⟨low,K+1,positive.le,fun radius above outerRadius M time inside w => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let T := mass seed M F radius time
  let A := deriv (mass seed M F radius) time
  have actual := source radius above outerRadius M time inside
  have same (v : physicalSpace (modes M)) : lifted seed M F radius time (T v)=v :=
    actual.1.inverse_apply_self v
  have diagonal (v : physicalSpace (modes M)) :
      |pairing (modes M) v (A v)| ≤ (K+1)*pairing (modes M) v (T v) := by
    have raw := actual.2 (T v)
    have q0 := raw.1
    change 0 ≤ pairing (modes M) (lifted seed M F radius time (T v)) (T v) at q0
    rw [same v] at q0
    have bound := raw.2.2
    change |NativeWindowTraceOperatorTime.quadraticJet seed (modes M) F radius 1 time
      (lifted seed M F radius time (T v))| ≤ K*pairing (modes M)
        (lifted seed M F radius time (T v)) (T v) at bound
    rw [same v] at bound
    rw [← NativeWindowTraceDualEvolution.mass_rate_pair] at bound
    change |pairing (modes M) v (A v)| ≤ _ at bound
    nlinarith only [bound,q0]
  exact inverse_clock M T A actual.1 (K+1) positive
    (mass_derivative_symmetric seed M F radius time) diagonal w

end
end SaturationMonoid.NavierStokes.NativeResponseClockPayment
