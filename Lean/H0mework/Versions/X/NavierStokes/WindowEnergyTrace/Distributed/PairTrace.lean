import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.PotentialHalf
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.ConvectionTensor

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeResponsePairTrace
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceDualEvolution (mass lifted energy)
open NativeWindowDistributedAdjoint (testAction)
open NativeCommonAdvectorAction (curlPair)
open NativeResponseTensorPayment (pairTensor mixed_half_square_bound)
open NativeWindowHistorySpatialTransport (finite)
noncomputable section
variable {nu : Viscosity}

private theorem projection (M : ℕ) (v : physicalSpace (modes M)) :
    complexSharpSupportProjection (modes M) v.1=v.1 := by
  apply lp.ext
  funext k
  by_cases inside : k∈modes M
  · simp only [complexSharpSupportProjection_apply,if_pos inside]
  · simp only [complexSharpSupportProjection_apply,if_neg inside,physical_supported v k inside]

theorem pair_curl_square (M : ℕ) (v z : physicalSpace (modes M)) :
    ‖pairTensor M v z‖^2 ≤ (144*NativeUnheatedRieszKernel.constant/(2*Real.pi)^4)*
      curlPair (modes M) v.1 v.1*curlPair (modes M) z.1 z.1 := by
  have source : ‖pairTensor M v z‖^2 ≤144*NativeUnheatedRieszKernel.constant*
      NativeUnheatedStressProduct.gradientMass v.1*NativeUnheatedStressProduct.gradientMass z.1 := by
    unfold pairTensor
    exact mixed_half_square_bound ..
  have first := NativeWindowAugmentedTestProduct.curl_original (modes M) v (modes_zero M)
  have last := NativeWindowAugmentedTestProduct.curl_original (modes M) z (modes_zero M)
  rw [projection] at first last
  apply source.trans_eq
  rw [first,last]
  field_simp

private theorem norm_equation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (positive : 0<c) (w z p l : E) (equation : w=z+c • l+p) :
    c*‖l‖ ≤ ‖w‖+‖z‖+‖p‖ := by
  have restored : c • l=w-z-p := by rw [equation]; abel
  calc
    _ = ‖c • l‖ := by rw [norm_smul,Real.norm_of_nonneg positive.le]
    _ = ‖w-z-p‖ := congrArg norm restored
    _ ≤ ‖w-z‖+‖p‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (norm_sub_le w z) le_rfl

theorem source_inverse_graph (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ radius ≥ low,∀ outerRadius ≤ radius,∀ M,
      ∀ time∈Icc 0 horizon,∀ w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      let z := lifted seed M F radius time w
      ‖coefficients (modes M) (testAction (nu := nu) M z)‖^2 ≤ C*‖coefficients (modes M) w‖^2 := by
  obtain ⟨first,K,K0,potential⟩ := NativeTracePotentialHalf.source_potential_square seed horizon nonnegative
  obtain ⟨last,D,D0,control⟩ := NativeWindowTraceDualEvolution.source_control seed horizon nonnegative
  refine ⟨max first last,3*(2+K)/nu.coeff^2,by positivity [nu.coeff_pos],
    fun radius above outerRadius covered M time inside w => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let z := lifted seed M F radius time w
  let P := NativeDistributedLyapunov.potential seed M F radius time z
  let L := testAction (nu := nu) M z
  let E := energy seed M F radius time w
  let a := ‖coefficients (modes M) z‖
  let b := ‖coefficients (modes M) w‖
  have a0 : 0≤a := norm_nonneg _
  have b0 : 0≤b := norm_nonneg _
  have curl0 : 0≤curlPair (modes M) z.1 z.1 := by
    unfold curlPair
    simp only [complexCoordinateRealInner_self]
    exact Finset.sum_nonneg fun _ _ => complexCoordinateVectorNormSq_nonneg _
  have controlled := control radius ((le_max_right first last).trans above) outerRadius M time inside
  have coerced := controlled.2 w |>.2.1
  have normed : pairing (modes M) z z=a^2 := by
    change inner ℝ (coefficients (modes M) z) (coefficients (modes M) z)=_
    exact real_inner_self_eq_norm_sq _
  rw [normed] at coerced
  have lower : a^2≤E := by nlinarith only [coerced,curl0,nu.coeff_pos]
  have upper : E≤a*b := (le_abs_self _).trans
    (abs_real_inner_le_norm (coefficients (modes M) z) (coefficients (modes M) w))
  have small : a≤b := by
    by_cases zero : a=0
    · simpa only [zero] using b0
    · have positive : 0<a := lt_of_le_of_ne a0 (Ne.symm zero)
      nlinarith only [lower,upper,positive]
  have energyBound : E≤b^2 := upper.trans ((mul_le_mul_of_nonneg_right small b0).trans_eq (by ring))
  have paid := potential radius ((le_max_left first _).trans above) outerRadius covered M time inside w
  have Pbound : ‖coefficients (modes M) P‖^2≤K*b^2 :=
    paid.trans (mul_le_mul_of_nonneg_left energyBound K0)
  have generated := controlled.1
  have source : mass seed M F radius time z=w := generated.self_apply_inverse w
  rw [NativeDistributedLyapunov.mass_split] at source
  have triangle : nu.coeff*‖coefficients (modes M) L‖ ≤ b+a+‖coefficients (modes M) P‖ := by
    change z+nu.coeff • L+P=w at source
    have read := congrArg (coefficients (modes M)) source.symm
    simp only [map_add,map_smul] at read
    exact norm_equation nu.coeff nu.coeff_pos _ _ _ _ read
  have squared := pow_le_pow_left₀ (by positivity [nu.coeff_pos]) triangle 2
  have bound : nu.coeff^2*‖coefficients (modes M) L‖^2 ≤ 3*(2+K)*b^2 := by
    have za := pow_le_pow_left₀ a0 small 2
    rw [mul_pow] at squared
    nlinarith only [squared,za,Pbound,sq_nonneg (b-a),
      sq_nonneg (b-‖coefficients (modes M) P‖),sq_nonneg (a-‖coefficients (modes M) P‖)]
  have divided := (le_div_iff₀ (sq_pos_of_pos nu.coeff_pos)).mpr
    (show ‖coefficients (modes M) L‖^2*nu.coeff^2≤3*(2+K)*b^2 by nlinarith only [bound])
  exact divided.trans_eq (by ring)

theorem source_pair_trace (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ radius ≥ low,∀ outerRadius ≤ radius,∀ M,
      ∀ time∈Icc 0 horizon,∀ v w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      let z := lifted seed M F radius time w
      (∑ j : Coordinate,‖pairTensor M v (finite M j z)‖^2) ≤
        C*curlPair (modes M) v.1 v.1*‖coefficients (modes M) w‖^2 := by
  obtain ⟨low,C,C0,graph⟩ := source_inverse_graph seed horizon nonnegative
  let K := 144*NativeUnheatedRieszKernel.constant/(2*Real.pi)^4
  have K0 : 0≤K := by dsimp only [K]; positivity [NativeUnheatedRieszKernel.constant_nonnegative]
  refine ⟨low,K*C,by positivity,fun radius above outerRadius covered M time inside v w => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let z := lifted seed M F radius time w
  have rows := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun j _ =>
    pair_curl_square M v (finite M j z)
  rw [← Finset.mul_sum,NativeResponseConvectionTensor.second_gradient_square (nu := nu)] at rows
  have curl0 : 0≤curlPair (modes M) v.1 v.1 := by
    unfold curlPair
    simp only [complexCoordinateRealInner_self]
    exact Finset.sum_nonneg fun _ _ => complexCoordinateVectorNormSq_nonneg _
  have scaled := mul_le_mul_of_nonneg_left (graph radius above outerRadius covered M time inside w)
    (mul_nonneg K0 curl0)
  exact rows.trans (scaled.trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeResponsePairTrace
