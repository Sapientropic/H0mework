import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.IntegralComparison
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.PotentialBudget

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeKernelAbsorption
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint NativeDistributedWeightedBudget
open NativeWindowTraceDualEvolution (lifted energy)
open NativeCenteredResponseTensor (centered tensor)
open NativeCenteredResponsePayment (heatWork potentialWork)
open NativeCenteredResponseRate (remainingRate)
open NativeCenteredResponseClock (clockWork)
open NativeDistributedHistoryPayment (centeredWork)
open NativeResponseKernelLift (kernelLift traceCost)
open NativeDistributedSourceTest (sourceTest)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section

theorem source_test_kernel_absorbed (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C epsilon D A K : ℝ,0≤C ∧0<epsilon ∧0≤D ∧0≤A ∧0≤K ∧
      ∀ outerRadius M observation,∀ observation0 : 0≤observation,observation+2≤horizon →
      let radius := max low outerRadius
      let F := integerWaveFrequencyCube outerRadius
      let test := sourceTest stackedShortCurrent M observation
      let p := response stackedShortCurrent M observation test 0 (observation+2) (by linarith)
      let q := kernelLift stackedShortCurrent M observation test 0 (observation+2) (by linarith)
      let z := fun t => lifted stackedShortCurrent M F radius t (p t)
      let Q := fun t => tensor stackedShortCurrent M F radius observation t (p t)
      (1/4 : ℝ)*‖coefficients (modes M) test‖^2+
        epsilon*(butterflyGainViscosity.coeff^2/16)*
          (∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
            ‖coefficients (modes M) (testAction (nu := butterflyGainViscosity) M (z t))‖^2) ≤
      D+(∫ t in (0 : ℝ)..(observation+2),
        pairing (modes M) (NativeWindowStageNineSource.forcing stackedShortCurrent M t) (p t))+
        2*epsilon*A*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          traceCost stackedShortCurrent M F radius observation t (q t))+
        epsilon*K*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          (1+NativeUnheatedSourceGradient.mass stackedShortCurrent t)*energy stackedShortCurrent M F radius t (p t))+
        epsilon*(A/(2*butterflyGainViscosity.coeff))*‖Q 0‖^2+
        epsilon*(A/(2*butterflyGainViscosity.coeff))*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          (2*inner ℝ (Q t) (remainingRate stackedShortCurrent M F radius observation t (p t)
            (load (nu := butterflyGainViscosity) observation M test t))+
          clockWork stackedShortCurrent M F radius observation t (p t)+C*‖Q t‖^2)) := by
  obtain ⟨first,C,C0,graph⟩ := NativeDistributedSourceTest.source_centered_weighted_graph
    stackedShortCurrent horizon nonnegative
  obtain ⟨second,A,A0,compare⟩ := NativeKernelIntegralComparison.source_centered_heat_integral
    stackedShortCurrent horizon nonnegative (butterflyGainViscosity.coeff^2/8)
      (by positivity [butterflyGainViscosity.coeff_pos])
  obtain ⟨third,write⟩ := NativeCenteredCompensated.source_weighted_heat_write stackedShortCurrent horizon nonnegative
  obtain ⟨fourth,K,K0,potential⟩ := NativeCenteredPotentialBudget.source_potential_integral_paid
    stackedShortCurrent horizon nonnegative (butterflyGainViscosity.coeff^2/16)
      (by positivity [butterflyGainViscosity.coeff_pos])
  obtain ⟨fifth,Kk,Kk0,correction⟩ := NativeResponseKernelLift.source_test_trace_recovery
    stackedShortCurrent horizon nonnegative C C0
  let B := kernelBudget butterflyGainViscosity horizon C
  have B0 : 0≤B := kernelBudget_nonnegative butterflyGainViscosity nonnegative C
  let epsilon := 1/(4*(B+A*Kk+1))
  have positive : 0<epsilon := by dsimp only [epsilon]; positivity
  have absorb : epsilon*(B+A*Kk)≤(3/4 : ℝ) := by
    have written : epsilon*(4*(B+A*Kk+1))=1 := by
      dsimp only [epsilon]
      exact div_mul_cancel₀ _ (by positivity : 4*(B+A*Kk+1)≠0)
    nlinarith only [written,positive,mul_nonneg A0 Kk0,B0]
  obtain ⟨sixth,D,D0,initial⟩ := source_initial_pair_paid horizon nonnegative epsilon positive
  let low := max first (max second (max third (max fourth (max fifth sixth))))
  refine ⟨low,C,epsilon,D,A,K,C0,positive,D0,A0,K0,
    fun outerRadius M observation observation0 within => ?_⟩
  let radius := max low outerRadius
  have above1 : first≤radius := by dsimp only [radius,low]; omega
  have above2 : second≤radius := by dsimp only [radius,low]; omega
  have above3 : third≤radius := by dsimp only [radius,low]; omega
  have above4 : fourth≤radius := by dsimp only [radius,low]; omega
  have above5 : fifth≤radius := by dsimp only [radius,low]; omega
  have above6 : sixth≤radius := by dsimp only [radius,low]; omega
  have covered : outerRadius≤radius := le_max_right _ _
  let F := integerWaveFrequencyCube outerRadius
  let test := sourceTest stackedShortCurrent M observation
  let b := observation+2
  have ordered : 0≤b := by dsimp only [b]; linarith
  have framed : observation∈Icc 0 horizon := ⟨observation0,by linarith⟩
  let p := response stackedShortCurrent M observation test 0 b ordered
  let q := kernelLift stackedShortCurrent M observation test 0 b ordered
  let z := fun t => lifted stackedShortCurrent M F radius t (p t)
  let Q := fun t => tensor stackedShortCurrent M F radius observation t (p t)
  let N := ‖coefficients (modes M) test‖^2
  let E := energy stackedShortCurrent M F radius 0 (p 0)
  let G := ∫ t in (0 : ℝ)..b,Real.exp (C*t)*
    ‖coefficients (modes M) (testAction (nu := butterflyGainViscosity) M (z t))‖^2
  let W := ∫ t in (0 : ℝ)..b,Real.exp (C*t)*centeredWork stackedShortCurrent M F radius observation t (z t)
  let H := ∫ t in (0 : ℝ)..b,Real.exp (C*t)*heatWork butterflyGainViscosity M
    (centered stackedShortCurrent M observation t) (z t)
  let Jp := ∫ t in (0 : ℝ)..b,Real.exp (C*t)*traceCost stackedShortCurrent M F radius observation t (p t)
  let Jq := ∫ t in (0 : ℝ)..b,Real.exp (C*t)*traceCost stackedShortCurrent M F radius observation t (q t)
  let P := ∫ t in (0 : ℝ)..b,Real.exp (C*t)*potentialWork stackedShortCurrent M F radius observation t (z t)
  let Y := ∫ t in (0 : ℝ)..b,Real.exp (C*t)*(1+NativeUnheatedSourceGradient.mass stackedShortCurrent t)*
    energy stackedShortCurrent M F radius t (p t)
  let R := ∫ t in (0 : ℝ)..b,Real.exp (C*t)*
    (2*inner ℝ (Q t) (remainingRate stackedShortCurrent M F radius observation t (p t)
      (load (nu := butterflyGainViscosity) observation M test t))+
      clockWork stackedShortCurrent M F radius observation t (p t)+C*‖Q t‖^2)
  let Fwork := ∫ t in (0 : ℝ)..b,pairing (modes M) (NativeWindowStageNineSource.forcing stackedShortCurrent M t) (p t)
  let alpha := A/(2*butterflyGainViscosity.coeff)
  have g := graph radius above1 outerRadius M observation observation framed test b ordered within
  have h := compare radius above2 outerRadius M observation observation C test b ordered within
  have w := write radius above3 outerRadius M observation observation C test b ordered within
  have pot := potential radius above4 outerRadius covered M observation observation C framed test b ordered within
  have corr := correction radius above5 outerRadius covered M observation observation0 within
  change E+(butterflyGainViscosity.coeff^2/4)*G≤W+B*N at g
  change W+alpha*H≤(butterflyGainViscosity.coeff^2/8)*G+A*Jp+P at h
  change H= -‖Q 0‖^2-R at w
  change P≤(butterflyGainViscosity.coeff^2/16)*G+K*Y at pot
  change Jp≤2*Jq+Kk*N at corr
  rw [w] at h
  have jp := mul_le_mul_of_nonneg_left corr A0
  have joint : E+(butterflyGainViscosity.coeff^2/16)*G≤
      2*A*Jq+K*Y+alpha*‖Q 0‖^2+alpha*R+(B+A*Kk)*N := by
    nlinarith only [g,h,pot,jp]
  have scaled := mul_le_mul_of_nonneg_left joint positive.le
  have paid := (le_abs_self _).trans (initial radius above6 outerRadius M (p 0))
  have green := window_source_green stackedShortCurrent M observation observation0 test
  rw [NativeDistributedSourceTest.source_pair] at green
  change N=pairing (modes M) (NativeWindowTraceAdjoint.value stackedShortCurrent M 0) (p 0)+Fwork at green
  change pairing (modes M) (NativeWindowTraceAdjoint.value stackedShortCurrent M 0) (p 0)≤epsilon*E+D at paid
  have kernel := mul_le_mul_of_nonneg_right absorb (sq_nonneg ‖coefficients (modes M) test‖)
  change (1/4 : ℝ)*N+epsilon*(butterflyGainViscosity.coeff^2/16)*G≤
    D+Fwork+2*epsilon*A*Jq+epsilon*K*Y+epsilon*alpha*‖Q 0‖^2+epsilon*alpha*R
  nlinarith only [green,paid,scaled,kernel]

end
end SaturationMonoid.NavierStokes.NativeKernelAbsorption
