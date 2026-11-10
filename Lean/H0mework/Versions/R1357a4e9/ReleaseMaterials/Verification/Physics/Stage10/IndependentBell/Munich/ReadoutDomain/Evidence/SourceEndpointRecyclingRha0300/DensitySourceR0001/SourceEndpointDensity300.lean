import H0mework.Versions.R4770e616.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceEndpointRecyclingRha0300.SourceR0009.SourceEndpointRecycling300
import H0mework.Versions.Ra4744604.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceOpenFieldKernelRha0299.SourceR0006.SourceExactDensityFlow299
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.InnerProductSpace.Trace

/-! The open initial atomic operator and its generated full-word trace.
The primal density IVP and the actual291 endpoint observable are paired by
the original finite-atomic trace. No completed kernel equality is an input.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ComplexOrder

namespace SourceEndpointDensity300
open SourceKrausSurvival285 SourceHiddenWordFlow286 SourceNativeKrausWindow292
open SourceOpenFieldKernel299 SourceEndpointWords300 SourceEndpointRecycling300
open SaturationMonoid.PhysicsCore.StageNineDiracMatterGalerkinEvolution

private def forgetContinuous :
    AtomicOperator →ₗ[ℂ] (AtomicHilbert →ₗ[ℂ] AtomicHilbert) :=
  (LinearMap.toContinuousLinearMap :
    (AtomicHilbert →ₗ[ℂ] AtomicHilbert) ≃ₗ[ℂ] AtomicOperator).symm.toLinearMap

def atomicTrace : AtomicOperator →L[ℂ] ℂ :=
  ((LinearMap.trace ℂ AtomicHilbert).comp forgetContinuous).toContinuousLinearMap

theorem atomicTrace_apply (A : AtomicOperator) :
    atomicTrace A = LinearMap.trace ℂ AtomicHilbert A.toLinearMap := rfl

def tracePairing : AtomicOperator →L[ℂ] AtomicOperator →L[ℂ] ℂ :=
  (ContinuousLinearMap.compL ℂ AtomicOperator AtomicOperator ℂ atomicTrace).comp
    (ContinuousLinearMap.compL ℂ AtomicHilbert AtomicHilbert AtomicHilbert)

theorem tracePairing_apply (density observable : AtomicOperator) :
    tracePairing density observable = atomicTrace (density * observable) := rfl

theorem atomicTrace_mul_comm (left right : AtomicOperator) :
    atomicTrace (left*right) = atomicTrace (right*left) := by
  change LinearMap.trace ℂ AtomicHilbert (left.toLinearMap*right.toLinearMap) =
    LinearMap.trace ℂ AtomicHilbert (right.toLinearMap*left.toLinearMap)
  exact LinearMap.trace_mul_comm _ _ _

theorem tracePairing_rankOne (density : AtomicOperator) (x : AtomicHilbert) :
    tracePairing density (InnerProductSpace.rankOne ℂ x x) = inner ℂ x (density x) := by
  rw [tracePairing_apply, ContinuousLinearMap.mul_def,
    InnerProductSpace.comp_rankOne, atomicTrace_apply]
  exact InnerProductSpace.trace_rankOne _ _

theorem tracePairing_nonnegative (density observable : AtomicOperator)
    (positiveDensity : density.IsPositive) (positiveObservable : observable.IsPositive) :
    0 ≤ tracePairing density observable := by
  obtain ⟨m,vectors,formed⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp positiveDensity
  simp only [formed, map_sum, sum_apply]
  apply Finset.sum_nonneg
  intro i _
  rw [tracePairing_apply, atomicTrace_mul_comm, ← tracePairing_apply, tracePairing_rankOne]
  exact positiveObservable.inner_nonneg_right _

variable {ι : Type*} [Fintype ι]
variable (source : RawKrausWindow AtomicHilbert ι) (hidden : Finset ι)

def densityGenerator (time : ℝ) : DensityAction :=
  bilateral (source.clampedCoefficient time) 1 + bilateral 1 (source.clampedCoefficient time) +
    ∑ j : Letters hidden, bilateral (source.chartJump j.val time) (source.chartJump j.val time)

theorem densityGenerator_apply (time : ℝ) (density : AtomicOperator) :
    densityGenerator source hidden time density =
      source.clampedCoefficient time * density + density * (source.clampedCoefficient time).adjoint +
        ∑ j : Letters hidden, source.chartJump j.val time * density *
          (source.chartJump j.val time).adjoint := by
  simp only [densityGenerator, add_apply, sum_apply,
    bilateral_apply, ContinuousLinearMap.adjoint_one, mul_one, one_mul]

theorem densityGenerator_continuous : Continuous (densityGenerator source hidden) := by
  have paired (left right : ℝ → AtomicOperator) (hl : Continuous left) (hr : Continuous right) :
      Continuous (fun time => bilateral (left time) (right time)) := by
    have same : (fun time => bilateral (left time) (right time)) =
        (fun time => compositionAction (left time) (right time).adjoint) := by
      funext time
      ext density x
      rfl
    rw [same]
    exact compositionAction_continuous left (fun time => (right time).adjoint) hl
      ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := AtomicHilbert)
        (F := AtomicHilbert)).continuous.comp hr)
  exact ((paired _ _ source.clampedCoefficient_continuous continuous_const).add
    (paired _ _ continuous_const source.clampedCoefficient_continuous)).add
      (continuous_finsetSum Finset.univ fun j _ => paired _ _
        (source.chartJump_continuous j.val) (source.chartJump_continuous j.val))

/-- This is the actual trace dual of the same selected primitive generator. -/
theorem generator_trace_duality (time : ℝ) (density observable : AtomicOperator) :
    tracePairing (densityGenerator source hidden time density) observable =
      tracePairing density (heisenberg source hidden time observable) := by
  let K := source.clampedCoefficient time
  let J := fun j : Letters hidden => source.chartJump j.val time
  have coherent : atomicTrace (K * density * observable) =
      atomicTrace (density * observable * K) := by
    simpa only [mul_assoc] using atomicTrace_mul_comm K (density*observable)
  have recycled (j : Letters hidden) :
      atomicTrace (J j * density * (J j).adjoint * observable) =
        atomicTrace (density * ((J j).adjoint * observable * J j)) := by
    simpa only [mul_assoc] using
      atomicTrace_mul_comm (J j) (density * (J j).adjoint * observable)
  simp only [tracePairing_apply, densityGenerator_apply, heisenberg_apply]
  simp only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum, map_add, map_sum]
  change atomicTrace (K * density * observable) +
      atomicTrace (density * K.adjoint * observable) +
      (∑ j, atomicTrace (J j * density * (J j).adjoint * observable)) =
    atomicTrace (density * (K.adjoint * observable)) +
      atomicTrace (density * (observable * K)) +
      ∑ j, atomicTrace (density * ((J j).adjoint * observable * J j))
  rw [coherent]
  have summed : (∑ j : Letters hidden,
      atomicTrace (J j * density * (J j).adjoint * observable)) =
        ∑ j : Letters hidden, atomicTrace (density * ((J j).adjoint * observable * J j)) :=
    Finset.sum_congr rfl (fun j _ => recycled j)
  rw [summed]
  simp only [mul_assoc]
  abel

/-- The primal operator flow is generated from identity on the full open rho slot. -/
def densityFlow (start : ℝ) (inside : start ∈ Icc source.left source.right) : ℝ → DensityAction :=
  SourceOpenFieldKernel299.BanachOperatorFlow.operatorFlow (B := AtomicOperator)
    (densityGenerator source hidden) (densityGenerator_continuous source hidden)
    start source.right inside.2

theorem densityFlow_initial (start : ℝ) (inside : start ∈ Icc source.left source.right) :
    densityFlow source hidden start inside start = 1 :=
  SourceOpenFieldKernel299.BanachOperatorFlow.operatorFlow_initial (B := AtomicOperator)
    (densityGenerator source hidden) (densityGenerator_continuous source hidden)
    start source.right inside.2

theorem densityFlow_derivative (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (time : ℝ) (ht : time ∈ Icc start source.right) :
    HasDerivWithinAt (densityFlow source hidden start inside)
      ((densityGenerator source hidden time).comp (densityFlow source hidden start inside time))
      (Icc start source.right) time :=
  SourceOpenFieldKernel299.BanachOperatorFlow.operatorFlow_derivative (B := AtomicOperator)
    (densityGenerator source hidden) (densityGenerator_continuous source hidden)
    start source.right inside.2 time ht

theorem densityFlow_applied_derivative (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (density : AtomicOperator)
    (time : ℝ) (ht : time ∈ Icc start source.right) :
    HasDerivWithinAt (fun r => densityFlow source hidden start inside r density)
      (densityGenerator source hidden time (densityFlow source hidden start inside time density))
      (Icc start source.right) time := by
  exact SourceOpenFieldKernel299.BanachOperatorFlow.applied_flow_derivative (B := AtomicOperator)
    (densityGenerator source hidden) (densityGenerator_continuous source hidden)
    start source.right inside.2 density time ht

/-- Forward rho and backward A are generated from the same original K/J occurrence. -/
theorem generated_trace_pairing (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (density observable : AtomicOperator) :
    tracePairing (densityFlow source hidden start inside source.right density) observable =
      tracePairing density (coflow source hidden observable start) := by
  let rho : ℝ → AtomicOperator := fun time => densityFlow source hidden start inside time density
  let effect : ℝ → AtomicOperator := coflow source hidden observable
  let F : ℝ → ℂ := fun time => tracePairing (rho time) (effect time)
  have included : Icc start source.right ⊆ Icc source.left source.right :=
    Icc_subset_Icc inside.1 le_rfl
  have derivative (time : ℝ) (ht : time ∈ Icc start source.right) :
      HasDerivWithinAt F 0 (Icc start source.right) time := by
    have drho := densityFlow_applied_derivative source hidden start inside density time ht
    have deffect := (coflow_derivative source hidden observable time (included ht)).mono included
    have paired : HasDerivWithinAt F
        (tracePairing (rho time) (-(heisenberg source hidden time (effect time))) +
          tracePairing (densityGenerator source hidden time (rho time)) (effect time))
        (Icc start source.right) time :=
      ContinuousLinearMap.hasDerivWithinAt_of_bilinear
        (B := tracePairing.bilinearRestrictScalars ℝ) drho deffect
    apply paired.congr_deriv
    rw [generator_trace_duality, map_neg, neg_add_cancel]
  have continuous : ContinuousOn F (Icc start source.right) :=
    fun time ht => (derivative time ht).continuousWithinAt
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.2 continuous
    (fun time ht => (derivative time (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)) (intervalIntegrable_const (c := (0 : ℂ)))
  rw [intervalIntegral.integral_zero] at paid
  have endpoints : F source.right = F start := sub_eq_zero.mp paid.symm
  simpa only [F,rho,effect,densityFlow_initial, coflow_terminal,
    _root_.one_apply_eq_self] using endpoints

/-- Genuine complete Born trace equals the generated selected recycling IVP. -/
theorem whole_word_trace_eq_recycling_IVP (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (density observable : AtomicOperator) :
    tracePairing (densityFlow source hidden start inside source.right density) observable =
      tracePairing density (endpointEffect source hidden start inside observable) := by
  rw [endpointEffect_eq_coflow]
  exact generated_trace_pairing source hidden start inside density observable

/-- The all-N, all-real-time source series has this same physical open-rho value. -/
theorem whole_word_trace_hasSum (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (density observable : AtomicOperator) :
    HasSum (fun n => tracePairing density (endpointWord source hidden observable n start))
      (tracePairing (densityFlow source hidden start inside source.right density) observable) := by
  have paid := (tracePairing density).hasSum
    (endpointWord_hasSum_coflow source hidden observable start inside)
  rw [← generated_trace_pairing source hidden start inside density observable] at paid
  exact paid

theorem whole_bath_trace_identity (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (density : AtomicOperator) :
    atomicTrace (densityFlow source Finset.univ start inside source.right density) =
      atomicTrace density := by
  have paid := whole_word_trace_eq_recycling_IVP source Finset.univ start inside density 1
  rw [endpointEffect_univ_identity] at paid
  simpa only [tracePairing_apply,mul_one] using paid

theorem densityFlow_positive (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (density : AtomicOperator) (positive : density.IsPositive) :
    (densityFlow source hidden start inside source.right density).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have tested := whole_word_trace_eq_recycling_IVP source hidden start inside density
    (InnerProductSpace.rankOne ℂ x x)
  rw [tracePairing_rankOne] at tested
  have nonnegative : 0 ≤ inner ℂ x (densityFlow source hidden start inside source.right density x) := by
    rw [tested]
    exact tracePairing_nonnegative density _ positive
      (endpointEffect_positive source hidden start inside _ (InnerProductSpace.isPositive_rankOne_self _))
  have parts := RCLike.nonneg_iff.mp nonnegative
  have left : inner ℂ (densityFlow source hidden start inside source.right density x) x =
      ((inner ℂ x (densityFlow source hidden start inside source.right density x)).re : ℂ) := by
    apply Complex.ext
    · change RCLike.re (inner ℂ (densityFlow source hidden start inside source.right density x) x) =
        RCLike.re (inner ℂ x (densityFlow source hidden start inside source.right density x))
      exact inner_re_symm _ _
    · change RCLike.im (inner ℂ (densityFlow source hidden start inside source.right density x) x) = 0
      rw [inner_im_symm]
      exact neg_eq_zero.mpr parts.2
  let value : ℝ := (inner ℂ x (densityFlow source hidden start inside source.right density x)).re
  constructor
  · rw [left]
    change (Complex.re (Complex.ofReal value) : ℂ) = Complex.ofReal value
    exact congrArg Complex.ofReal (Complex.ofReal_re value)
  · rw [left]
    change (0 : ℝ) ≤ Complex.re (Complex.ofReal value)
    rw [Complex.ofReal_re]
    have diagonal := parts.1
    change (0 : ℝ) ≤ value at diagonal
    exact diagonal

theorem densityFlow_trace_nonincreasing (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (density : AtomicOperator)
    (positive : density.IsPositive) :
    (atomicTrace (densityFlow source hidden start inside source.right density)).re ≤
      (atomicTrace density).re := by
  have paired := whole_word_trace_eq_recycling_IVP source hidden start inside density 1
  have traced : atomicTrace (densityFlow source hidden start inside source.right density) =
      tracePairing density (endpointEffect source hidden start inside 1) := by
    simpa only [tracePairing_apply,mul_one] using paired
  rw [traced]
  obtain ⟨m,vectors,formed⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp positive
  simp only [formed,map_sum,sum_apply,Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have tested : tracePairing (InnerProductSpace.rankOne ℂ (vectors i) (vectors i))
      (endpointEffect source hidden start inside 1) =
        inner ℂ (vectors i) (endpointEffect source hidden start inside 1 (vectors i)) := by
    rw [tracePairing_apply,atomicTrace_mul_comm,← tracePairing_apply,tracePairing_rankOne]
  have diagonal : (atomicTrace (InnerProductSpace.rankOne ℂ (vectors i) (vectors i))).re =
      ‖vectors i‖^2 := by
    rw [atomicTrace_apply, InnerProductSpace.trace_rankOne]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (vectors i : AtomicHilbert)
  rw [tested,diagonal]
  exact endpointEffect_subunital source hidden start inside (vectors i)

end SourceEndpointDensity300
