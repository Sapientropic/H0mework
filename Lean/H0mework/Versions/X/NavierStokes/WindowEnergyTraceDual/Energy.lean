import H0mework.Versions.X.NavierStokes.WindowEnergyTraceOperator.Action

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceDualEnergy
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint
open NativeWindowTraceOperator (test jointTest test_pairing form_symmetric)
noncomputable section
variable {nu : Viscosity}

private theorem mass_nonnegative (M : Finset IntegerWavevector) (v : physicalSpace M) : 0≤pairing M v v := by
  change (0 : ℝ) ≤ inner ℝ (coefficients M v) (coefficients M v)
  exact real_inner_self_nonneg

private theorem inverse_joint_bound (M : Finset IntegerWavevector) (T : Module.End ℝ (physicalSpace M))
    (same : ∀ x y,pairing M x (T y)=pairing M y (T x))
    (coercive : ∀ v,pairing M v v≤pairing M v (T v)) (equiv : physicalSpace M ≃ₗ[ℝ] physicalSpace M)
    (original : ∀ v,equiv v=T v) (v : physicalSpace M) :
    0≤pairing M (equiv.symm (v-T v)) (v-T v) ∧
      pairing M (equiv.symm (v-T v)) (v-T v)≤pairing M v (T v)-pairing M v v := by
  have inverse (z : physicalSpace M) : T (equiv.symm z)=z := by
    rw [← original,equiv.apply_symm_apply]
  have lower := (mass_nonnegative M (equiv.symm (v-T v))).trans (coercive (equiv.symm (v-T v)))
  rw [inverse] at lower
  refine ⟨lower,?_⟩
  let w:=equiv.symm v
  have first := coercive w
  rw [inverse] at first
  have square := mass_nonnegative M (w-v)
  simp only [map_sub,LinearMap.sub_apply,pairing_symmetric M v w] at square
  have inverseBound : pairing M w v≤pairing M v v := by linarith only [first,square]
  have endpoint : equiv.symm (v-T v)=w-v := by
    rw [map_sub,← original,equiv.symm_apply_apply]
  have cross : pairing M w (T v)=pairing M v v := by rw [same,inverse]
  rw [endpoint]
  simp only [map_sub,LinearMap.sub_apply,cross]
  linarith only [inverseBound]

theorem source_inverse (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M F : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →FiniteModeNegClosed F →
      ∀ time∈Icc 0 horizon,∃ generated : physicalSpace M ≃ₗ[ℝ] physicalSpace M,
        (∀ v,generated v=test seed time M M F radius v) ∧
        ∀ v,0≤pairing M (generated.symm (jointTest seed time M F radius v)) (jointTest seed time M F radius v) ∧
          pairing M (generated.symm (jointTest seed time M F radius v)) (jointTest seed time M F radius v)≤
            pairing M v (test seed time M M F radius v)-pairing M v v := by
  obtain ⟨low,paid⟩ := NativeWindowTraceOperator.source_coercivity seed horizon nonnegative
  refine ⟨low,fun radius above M F zero closedM closedF time inside => ?_⟩
  let T:=test seed time M M F radius
  have coercive (v : physicalSpace M) : pairing M v v≤pairing M v (T v) := by
    have gradient : 0≤curlPair M v.1 v.1 := by
      unfold curlPair
      apply Finset.sum_nonneg
      intro wave _
      rw [complexCoordinateRealInner_self]
      exact complexCoordinateVectorNormSq_nonneg _
    have full := paid radius above M F zero closedM closedF time inside v
    exact (le_add_of_nonneg_right (mul_nonneg (by positivity [nu.coeff_pos]) gradient)).trans full
  have injective : Function.Injective T := by
    intro x y same
    apply sub_eq_zero.mp
    apply pairing_faithful M
    have bound:=coercive (x-y)
    have gone : T (x-y)=0 := by rw [map_sub,same,sub_self]
    rw [gone,map_zero] at bound
    exact bound
  let generated:=LinearEquiv.ofInjectiveEndo T injective
  refine ⟨generated,fun _ => rfl,fun v => ?_⟩
  have symmetric (x y : physicalSpace M) : pairing M x (T y)=pairing M y (T x) := by
    rw [test_pairing,test_pairing,form_symmetric]
  simpa only [jointTest,LinearMap.sub_apply,LinearMap.id_apply] using
    inverse_joint_bound M T symmetric coercive generated (fun _ => rfl) v

end
end SaturationMonoid.NavierStokes.NativeWindowTraceDualEnergy
