import H0mework.NavierStokes.WindowEnergyConvection.CutoffOperatorRelative
import H0mework.NavierStokes.WindowEnergyTraceClock.ClockInverse

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCutInverse
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint
open NativeWindowTraceCutOperator (test jointTest)
noncomputable section
variable {nu : Viscosity}

theorem mass_nonnegative (M : Finset IntegerWavevector) (v : physicalSpace M) : 0≤pairing M v v := by
  change (0 : ℝ) ≤ inner ℝ (coefficients M v) (coefficients M v)
  exact real_inner_self_nonneg

theorem gradient_nonnegative (M : Finset IntegerWavevector) (v : physicalSpace M) : 0≤curlPair M v.1 v.1 := by
  unfold curlPair
  apply Finset.sum_nonneg
  intro wave _
  rw [complexCoordinateRealInner_self]
  exact complexCoordinateVectorNormSq_nonneg _

theorem inverse_joint_bound (M : Finset IntegerWavevector) (T : Module.End ℝ (physicalSpace M))
    (same : ∀ x y,pairing M x (T y)=pairing M y (T x))
    (coercive : ∀ v,pairing M v v≤pairing M v (T v)) (equiv : physicalSpace M ≃ₗ[ℝ] physicalSpace M)
    (original : ∀ v,equiv v=T v) (v : physicalSpace M) :
    0≤pairing M (equiv.symm (v-T v)) (v-T v) ∧
      pairing M (equiv.symm (v-T v)) (v-T v)≤pairing M v (T v)-pairing M v v := by
  have inverse (z : physicalSpace M) : T (equiv.symm z)=z := by rw [← original,equiv.apply_symm_apply]
  have lower := (mass_nonnegative M (equiv.symm (v-T v))).trans (coercive (equiv.symm (v-T v)))
  rw [inverse] at lower
  refine ⟨lower,?_⟩
  let w:=equiv.symm v
  have first := coercive w
  rw [inverse] at first
  have square := mass_nonnegative M (w-v)
  simp only [map_sub,LinearMap.sub_apply,pairing_symmetric M v w] at square
  have inverseBound : pairing M w v≤pairing M v v := by linarith only [first,square]
  have endpoint : equiv.symm (v-T v)=w-v := by rw [map_sub,← original,equiv.symm_apply_apply]
  have cross : pairing M w (T v)=pairing M v v := by rw [same,inverse]
  rw [endpoint]
  simp only [map_sub,LinearMap.sub_apply,cross]
  linarith only [inverseBound]

theorem inverse_order (M : Finset IntegerWavevector) (A B : Module.End ℝ (physicalSpace M))
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

theorem test_symmetric (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (radius : ℕ)
    (x y : physicalSpace M) : pairing M x (test seed time M M F radius y)=pairing M y (test seed time M M F radius x) := by
  have old : pairing M x (NativeWindowTraceOperator.test seed time M M F radius y)=
      pairing M y (NativeWindowTraceOperator.test seed time M M F radius x) := by
    rw [NativeWindowTraceOperator.test_pairing,NativeWindowTraceOperator.test_pairing,NativeWindowTraceOperator.form_symmetric]
  simp only [NativeWindowTraceCutOperator.test,LinearMap.sub_apply,map_sub,old,NativeWindowTraceCutOperator.difference_pairing]
  congr 1
  unfold NativeWindowTraceCutOperator.differenceForm
  simp only [LinearMap.mk₂_apply]
  exact Finset.sum_congr rfl fun i _ => congrArg (NativeWindowTraceCutOperator.differenceRead seed time F) (mul_comm _ _)

theorem source_inverse (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ cutoff≥low,∀ M : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →
      ∀ time∈Icc 0 horizon,∃ generated : physicalSpace M ≃ₗ[ℝ] physicalSpace M,
        (∀ v,generated v=test seed time M M (integerWaveFrequencyCube cutoff) radius v) ∧
        ∀ v,0≤pairing M (generated.symm (jointTest seed time M (integerWaveFrequencyCube cutoff) radius v))
            (jointTest seed time M (integerWaveFrequencyCube cutoff) radius v) ∧
          pairing M (generated.symm (jointTest seed time M (integerWaveFrequencyCube cutoff) radius v))
              (jointTest seed time M (integerWaveFrequencyCube cutoff) radius v)≤
            pairing M v (test seed time M M (integerWaveFrequencyCube cutoff) radius v)-pairing M v v := by
  obtain ⟨low,paid⟩ := NativeWindowTraceCutOperator.source_coercivity seed horizon nonnegative
  refine ⟨low,fun radius above cutoff covered M zero closed time inside => ?_⟩
  let T:=test seed time M M (integerWaveFrequencyCube cutoff) radius
  have coercive (v : physicalSpace M) : pairing M v v≤pairing M v (T v) :=
    (le_add_of_nonneg_right (mul_nonneg (by positivity [nu.coeff_pos]) (gradient_nonnegative M v))).trans
      (paid radius above cutoff covered M zero closed time inside v)
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
  simpa only [NativeWindowTraceCutOperator.jointTest,LinearMap.sub_apply,LinearMap.id_apply] using
    inverse_joint_bound M T (test_symmetric seed time M (integerWaveFrequencyCube cutoff) radius) coercive generated (fun _ => rfl) v

theorem inverse_unique (M : Finset IntegerWavevector) (T : Module.End ℝ (physicalSpace M))
    (generated : physicalSpace M ≃ₗ[ℝ] physicalSpace M) (original : ∀ v,generated v=T v)
    (candidate : Module.End ℝ (physicalSpace M)) (right : ∀ v,T (candidate v)=v) : candidate=generated.symm.toLinearMap := by
  ext v : 1
  apply generated.injective
  rw [original,right,LinearEquiv.coe_coe,generated.apply_symm_apply]

theorem source_inverse_comparison (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ cutoff≥low,∀ M : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →
      ∀ time∈Icc 0 horizon,∃ old generated : physicalSpace M ≃ₗ[ℝ] physicalSpace M,
        (∀ v,old v=NativeWindowTraceOperator.test seed time M M (integerWaveFrequencyCube cutoff) radius v) ∧
        (∀ v,generated v=test seed time M M (integerWaveFrequencyCube cutoff) radius v) ∧
        ∀ w,(2/3 : ℝ)*pairing M (old.symm w) w≤pairing M (generated.symm w) w ∧
          pairing M (generated.symm w) w≤2*pairing M (old.symm w) w := by
  obtain ⟨first,oldInverse⟩ := NativeWindowTraceDualEnergy.source_inverse seed horizon nonnegative
  obtain ⟨last,newInverse⟩ := source_inverse seed horizon nonnegative
  obtain ⟨compare,comparison⟩ := NativeWindowTraceCutRelative.source_equivalent seed horizon nonnegative
  refine ⟨max first (max last compare),fun radius above cutoff covered M zero closed time inside => ?_⟩
  let F:=integerWaveFrequencyCube cutoff
  have newR : last≤radius := (le_max_left _ _).trans ((le_max_right _ _).trans above)
  have newN : last≤cutoff := (le_max_left _ _).trans ((le_max_right _ _).trans covered)
  have cmpR : compare≤radius := (le_max_right _ _).trans ((le_max_right _ _).trans above)
  have cmpN : compare≤cutoff := (le_max_right _ _).trans ((le_max_right _ _).trans covered)
  obtain ⟨old,oldOriginal,oldPaid⟩ := oldInverse radius ((le_max_left _ _).trans above) M F zero closed
    (NativeWindowFiniteGramFourier.cube_closed cutoff) time inside
  obtain ⟨generated,original,paid⟩ := newInverse radius newR cutoff newN M zero closed time inside
  have oldSymmetric (x y : physicalSpace M) : pairing M x (NativeWindowTraceOperator.test seed time M M F radius y)=
      pairing M y (NativeWindowTraceOperator.test seed time M M F radius x) := by
    rw [NativeWindowTraceOperator.test_pairing,NativeWindowTraceOperator.test_pairing,NativeWindowTraceOperator.form_symmetric]
  have oldPositive (v : physicalSpace M) : 0≤pairing M v (NativeWindowTraceOperator.test seed time M M F radius v) := by
    have bound:=oldPaid v
    linarith only [bound.1,bound.2,mass_nonnegative M v]
  have newPositive (v : physicalSpace M) : 0≤pairing M v (test seed time M M F radius v) := by
    have bound:=paid v
    linarith only [bound.1,bound.2,mass_nonnegative M v]
  refine ⟨old,generated,oldOriginal,original,fun w => ?_⟩
  have upper := inverse_order M _ _ 2 (by norm_num) oldSymmetric oldPositive
    (fun v => by have bound:=(comparison radius cmpR cutoff cmpN M zero closed time inside v).1; linarith only [bound])
    old generated oldOriginal original w
  have lower := inverse_order M _ _ (3/2) (by norm_num) (test_symmetric seed time M F radius) newPositive
    (fun v => (comparison radius cmpR cutoff cmpN M zero closed time inside v).2)
    generated old original oldOriginal w
  exact ⟨by linarith only [lower],upper⟩

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCutInverse
