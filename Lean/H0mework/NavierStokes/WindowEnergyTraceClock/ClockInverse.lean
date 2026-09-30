import H0mework.NavierStokes.WindowEnergyTraceClock.ClockForm
import H0mework.NavierStokes.WindowEnergyTraceDual.Energy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceInverseComparison
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint
open NativeWindowTraceOperator (test test_pairing form_symmetric)
noncomputable section
variable {nu : Viscosity}

private theorem inverse_order (M : Finset IntegerWavevector) (A B : Module.End ℝ (physicalSpace M))
    (K : ℝ) (positive : 0<K) (symmetric : ∀ x y,pairing M x (A y)=pairing M y (A x))
    (nonnegative : ∀ x,0≤pairing M x (A x)) (bounded : ∀ x,pairing M x (A x)≤K*pairing M x (B x))
    (a b : physicalSpace M ≃ₗ[ℝ] physicalSpace M) (left : ∀ v,a v=A v) (right : ∀ v,b v=B v)
    (w : physicalSpace M) : pairing M (b.symm w) w≤K*pairing M (a.symm w) w := by
  let x:=b.symm w
  let z:=a.symm w
  have ax : A z=w := by rw [← left,a.apply_symm_apply]
  have bx : B x=w := by rw [← right,b.apply_symm_apply]
  have cross : pairing M z (A x)=pairing M x w := by rw [symmetric,ax]
  have square:=nonnegative (K • z-x)
  simp only [map_sub,LinearMap.sub_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,ax,cross] at square
  have cost:=bounded x
  rw [bx] at cost
  apply (mul_le_mul_iff_right₀ positive).mp
  change K*pairing M x w≤K*(K*pairing M z w)
  nlinarith only [square,cost]

theorem source_inverse_comparison (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius,∀ M : Finset IntegerWavevector,
      0∉M →FiniteModeNegClosed M →∀ s∈Icc 0 horizon,∀ t∈Icc 0 horizon,
        ∃ left right : physicalSpace M ≃ₗ[ℝ] physicalSpace M,
          (∀ v,left v=test seed s M M (integerWaveFrequencyCube outerRadius) radius v) ∧
          (∀ v,right v=test seed t M M (integerWaveFrequencyCube outerRadius) radius v) ∧
          ∀ w,pairing M (right.symm w) w≤Real.exp (C*|t-s|)*pairing M (left.symm w) w := by
  obtain ⟨temporal,C,C0,compare⟩ := NativeWindowTraceTimeComparison.source_form_comparison seed horizon nonnegative
  obtain ⟨invertible,inverse⟩ := NativeWindowTraceDualEnergy.source_inverse seed horizon nonnegative
  obtain ⟨positive,coercive⟩ := NativeWindowTraceOperator.source_coercivity seed horizon nonnegative
  refine ⟨max temporal (max invertible positive),C,C0,fun radius above outerRadius M zero closed s hs t ht => ?_⟩
  let F:=integerWaveFrequencyCube outerRadius
  have inverseAbove : invertible≤radius := (le_max_left _ _).trans ((le_max_right _ _).trans above)
  obtain ⟨left,leftOriginal,_⟩ := inverse radius inverseAbove M F zero closed (NativeWindowFiniteGramFourier.cube_closed outerRadius) s hs
  obtain ⟨right,rightOriginal,_⟩ := inverse radius inverseAbove M F zero closed (NativeWindowFiniteGramFourier.cube_closed outerRadius) t ht
  refine ⟨left,right,leftOriginal,rightOriginal,fun w => ?_⟩
  have symmetric (x y : physicalSpace M) : pairing M x (test seed s M M F radius y)=pairing M y (test seed s M M F radius x) := by
    rw [test_pairing,test_pairing,form_symmetric]
  have first (x : physicalSpace M) : 0≤pairing M x (test seed s M M F radius x) := by
    have mass : 0≤pairing M x x := by
      change (0 : ℝ) ≤ inner ℝ (coefficients M x) (coefficients M x)
      exact real_inner_self_nonneg
    have gradient : 0≤curlPair M x.1 x.1 := by
      unfold curlPair
      apply Finset.sum_nonneg
      intro wave _
      rw [complexCoordinateRealInner_self]
      exact complexCoordinateVectorNormSq_nonneg _
    exact (add_nonneg mass (mul_nonneg (by positivity [nu.coeff_pos]) gradient)).trans
      (coercive radius ((le_max_right _ _).trans ((le_max_right _ _).trans above)) M F zero closed
        (NativeWindowFiniteGramFourier.cube_closed outerRadius) s hs x)
  have bound (x : physicalSpace M) : pairing M x (test seed s M M F radius x)≤
      Real.exp (C*|t-s|)*pairing M x (test seed t M M F radius x) := by
    simpa only [abs_sub_comm] using compare radius ((le_max_left _ _).trans above) outerRadius M zero closed t ht s hs x
  exact inverse_order M _ _ _ (Real.exp_pos _) symmetric first bound left right leftOriginal rightOriginal w

theorem source_actual_inverse_comparison (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius,∀ M : Finset IntegerWavevector,
      0∉M →FiniteModeNegClosed M →∀ s∈Icc 0 horizon,∀ t∈Icc 0 horizon,
        ∀ left right : Module.End ℝ (physicalSpace M),
          (∀ v,test seed s M M (integerWaveFrequencyCube outerRadius) radius (left v)=v) →
          (∀ v,test seed t M M (integerWaveFrequencyCube outerRadius) radius (right v)=v) →
          ∀ w,pairing M (right w) w≤Real.exp (C*|t-s|)*pairing M (left w) w := by
  obtain ⟨low,C,C0,paid⟩ := source_inverse_comparison seed horizon nonnegative
  refine ⟨low,C,C0,fun radius above outerRadius M zero closed s hs t ht left right leftOriginal rightOriginal w => ?_⟩
  obtain ⟨a,b,first,last,compare⟩ := paid radius above outerRadius M zero closed s hs t ht
  have leftSame : left w=a.symm w := by
    apply a.injective
    rw [a.apply_symm_apply,first,leftOriginal]
  have rightSame : right w=b.symm w := by
    apply b.injective
    rw [b.apply_symm_apply,last,rightOriginal]
  rw [leftSame,rightSame]
  exact compare w

end
end SaturationMonoid.NavierStokes.NativeWindowTraceInverseComparison
