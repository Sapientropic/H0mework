import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.KernelBudget

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeKernelIntegralComparison
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint NativeDistributedWeightedBudget
open NativeWindowTraceDualEvolution (lifted)
open NativeCenteredResponseTensor (centered)
open NativeCenteredResponsePayment (heatWork potentialWork)
open NativeDistributedHistoryPayment (centeredWork)
open NativeResponseTensorPayment (pairTensor pairTensorCLM)
open NativeWindowHistorySpatialTransport (finite)
open NativeResponseKernelLift (traceCost)
noncomputable section
variable {nu : Viscosity}

private theorem pair_continuous {M : ℕ} {v z : ℝ→physicalSpace (modes M)} {S : Set ℝ}
    (vc : ContinuousOn v S) (zc : ContinuousOn z S) :
    ContinuousOn (fun t => pairTensor M (v t) (z t)) S :=
  ((pairTensorCLM M).continuous.comp_continuousOn vc).clm_apply zc

private theorem heat_continuous {M : ℕ} {v z : ℝ→physicalSpace (modes M)} {S : Set ℝ}
    (vc : ContinuousOn v S) (zc : ContinuousOn z S) :
    ContinuousOn (fun t => heatWork nu M (v t) (z t)) S := by
  let L := LinearMap.toContinuousLinearMap (testAction (nu := nu) M)
  exact ((pair_continuous vc zc).inner (𝕜 := ℝ)
    ((pair_continuous ((L.continuous.comp_continuousOn vc).const_smul (-nu.coeff)) zc).add
      (pair_continuous vc ((L.continuous.comp_continuousOn zc).const_smul nu.coeff)))).const_mul (2 : ℝ)

theorem source_centered_heat_integral (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) (eta : ℝ) (positive : 0<eta) :
    ∃ low : ℕ,∃ A : ℝ,0≤A ∧∀ radius≥low,∀ outerRadius M observation frame C,
      ∀ test : physicalSpace (modes M),∀ b,∀ ordered : 0≤b,b≤horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test 0 b ordered
      let v := fun t => centered seed M frame t
      let z := fun t => lifted seed M F radius t (p t)
      (∫ t in (0 : ℝ)..b,Real.exp (C*t)*centeredWork seed M F radius frame t (z t))+
        (A/(2*nu.coeff))*(∫ t in (0 : ℝ)..b,Real.exp (C*t)*heatWork nu M (v t) (z t)) ≤
        eta*(∫ t in (0 : ℝ)..b,Real.exp (C*t)*‖coefficients (modes M) (testAction (nu := nu) M (z t))‖^2)+
        A*(∫ t in (0 : ℝ)..b,Real.exp (C*t)*traceCost seed M F radius frame t (p t))+
        (∫ t in (0 : ℝ)..b,Real.exp (C*t)*potentialWork seed M F radius frame t (z t)) := by
  obtain ⟨low,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  obtain ⟨A,A0,point⟩ := NativeCenteredResponsePayment.centered_work_heat_paid nu eta positive
  refine ⟨low,A,A0,fun radius above outerRadius M observation frame C test b ordered within => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let p := response seed M observation test 0 b ordered
  let v := fun t => centered seed M frame t
  let z := fun t => lifted seed M F radius t (p t)
  let weight := fun t => Real.exp (C*t)
  let G := fun t => ‖coefficients (modes M) (testAction (nu := nu) M (z t))‖^2
  let Q := fun t => centeredWork seed M F radius frame t (z t)
  let H := fun t => heatWork nu M (v t) (z t)
  let J := fun t => traceCost seed M F radius frame t (p t)
  let P := fun t => potentialWork seed M F radius frame t (z t)
  let alpha := A/(2*nu.coeff)
  have generated := inverted radius above M F (NativeWindowFiniteGramFourier.cube_closed outerRadius)
  have zc := response_lift_continuous seed M F radius observation test b ordered
    (fun t ht => generated t (Icc_subset_Icc le_rfl within ht))
  have vc : ContinuousOn v (Icc 0 b) :=
    (NativeWindowTraceAdjoint.value_continuous seed M).continuousOn.sub continuousOn_const
  have wc : ContinuousOn weight (Icc 0 b) := by dsimp only [weight]; fun_prop
  have gc : ContinuousOn G (Icc 0 b) :=
    ((LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp_continuousOn
      ((LinearMap.toContinuousLinearMap (testAction (nu := nu) M)).continuous.comp_continuousOn zc)).norm.pow 2
  have qc := NativeDistributedSourceTest.centered_continuous seed M F radius frame zc
  have hc := heat_continuous (nu := nu) vc zc
  have jc : ContinuousOn J (Icc 0 b) := continuousOn_finsetSum _ fun j _ =>
    (pair_continuous vc ((finite M j).continuous.comp_continuousOn zc)).norm.pow 2
  have pc := NativeCenteredResponsePayment.potential_continuousOn seed M F radius frame zc
  have gi := (wc.mul gc).intervalIntegrable_of_Icc (μ := volume) ordered
  have qi := (wc.mul qc).intervalIntegrable_of_Icc (μ := volume) ordered
  have hi := (wc.mul hc).intervalIntegrable_of_Icc (μ := volume) ordered
  have ji := (wc.mul jc).intervalIntegrable_of_Icc (μ := volume) ordered
  have pi := (wc.mul pc).intervalIntegrable_of_Icc (μ := volume) ordered
  have paid := intervalIntegral.integral_mono_on ordered (qi.add (hi.const_mul alpha))
    (((gi.const_mul eta).add (ji.const_mul A)).add pi) (fun t _ => ?_)
  · rw [intervalIntegral.integral_add qi (hi.const_mul alpha),
      intervalIntegral.integral_add ((gi.const_mul eta).add (ji.const_mul A)) pi,
      intervalIntegral.integral_add (gi.const_mul eta) (ji.const_mul A),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at paid
    exact paid
  · have localPaid := point seed M F radius frame t (p t)
    change Q t+alpha*H t ≤ eta*G t+A*J t+P t at localPaid
    have scaled := mul_le_mul_of_nonneg_left localPaid (Real.exp_pos (C*t)).le
    change weight t*Q t+alpha*(weight t*H t) ≤ eta*(weight t*G t)+A*(weight t*J t)+weight t*P t
    dsimp only [weight] at *
    nlinarith only [scaled]

end
end SaturationMonoid.NavierStokes.NativeKernelIntegralComparison
