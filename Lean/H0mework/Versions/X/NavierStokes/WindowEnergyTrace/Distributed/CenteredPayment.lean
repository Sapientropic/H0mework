import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.CenteredTensor
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.ConvectionTensor
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.SourceTest

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeCenteredResponsePayment
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeCenteredResponseTensor NativeResponseTensorPayment
open NativeWindowTraceDualEvolution (mass lifted)
open NativeWindowHistoryCreationGeometry (transport)
open NativeWindowOperatorGreen (laplacian)
open NativeDistributedHistoryPayment (centeredWork)
open NativeWindowHistorySpatialTransport (finite)
noncomputable section
variable {nu : Viscosity}

def potentialWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ) (z : physicalSpace (modes M)) : ℝ :=
  2*pairing (modes M) (NativeDistributedLyapunov.potential seed M F radius time z)
    (transport (modes M) (modes_zero M) (modes_closed M) nu (centered seed M frame time) z)

def heatWork (nu : Viscosity) (M : ℕ) (v z : physicalSpace (modes M)) : ℝ :=
  let L := laplacian (modes M) (modes_zero M) (modes_closed M) nu
  2*inner ℝ (pairTensor M v z)
    (pairTensor M ((-nu.coeff) • L v) z+pairTensor M v (nu.coeff • L z))

theorem centered_work_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ) (z : physicalSpace (modes M)) :
    centeredWork seed M F radius frame time z =
      2*nu.coeff*pairing (modes M)
        (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)
        (transport (modes M) (modes_zero M) (modes_closed M) nu (centered seed M frame time) z)+
      potentialWork seed M F radius frame time z := by
  let v := centered seed M frame time
  have skew := NativeWindowHistoryJacobianForm.transport_skew nu M v z z
  have zero : pairing (modes M) z (transport (modes M) (modes_zero M) (modes_closed M) nu v z)=0 := by
    linarith only [skew]
  rw [NativeDistributedHistoryPayment.centeredWork_actual,NativeDistributedLyapunov.mass_split]
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  change 2*(pairing (modes M) z (transport _ _ _ nu v z)+
    nu.coeff*pairing (modes M) (laplacian _ _ _ nu z) (transport _ _ _ nu v z)+
    pairing (modes M) (NativeDistributedLyapunov.potential seed M F radius time z)
      (transport _ _ _ nu v z)) = _
  rw [zero]
  dsimp only [potentialWork,v]
  ring

theorem centered_work_heat_paid (nu : Viscosity) (eta : ℝ) (positive : 0 < eta) :
    ∃ C : ℝ,0 ≤ C ∧∀ (seed : GeneratedWholeRestartCurrent nu) M F radius frame time
      (w : physicalSpace (modes M)),
      let v := centered seed M frame time
      let z := lifted seed M F radius time w
      centeredWork seed M F radius frame time z+(C/(2*nu.coeff))*heatWork nu M v z ≤
        eta*‖coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)‖^2+
          C*(∑ j : Coordinate,‖pairTensor M v (finite M j z)‖^2)+
            potentialWork seed M F radius frame time z := by
  obtain ⟨C,C0,paid⟩ := NativeResponseConvectionTensor.convection_heat_paid nu eta positive
  refine ⟨C,C0,fun seed M F radius frame time w => ?_⟩
  let v := centered seed M frame time
  let z := lifted seed M F radius time w
  have combined := paid M v z
  have signed := le_abs_self (2*nu.coeff*pairing (modes M)
    (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)
    (transport (modes M) (modes_zero M) (modes_closed M) nu v z))
  dsimp only at combined ⊢
  rw [centered_work_split]
  change _+(C/(2*nu.coeff))*heatWork nu M v z ≤ _
  dsimp only [heatWork]
  nlinarith only [combined,signed]

theorem source_test_heat_paid (nu : Viscosity) (eta : ℝ) (positive : 0 < eta) :
    ∃ C : ℝ,0 ≤ C ∧∀ (seed : GeneratedWholeRestartCurrent nu) M F radius observation
      (observation0 : 0 ≤ observation) time,
      let p := NativeWindowDistributedAdjoint.response seed M observation
        (NativeDistributedSourceTest.sourceTest seed M observation) 0 (observation+2)
          (by linarith [observation0])
      let v := centered seed M observation time
      let z := lifted seed M F radius time (p time)
      centeredWork seed M F radius observation time z+(C/(2*nu.coeff))*heatWork nu M v z ≤
        eta*‖coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu z)‖^2+
          C*(∑ j : Coordinate,‖pairTensor M v (finite M j z)‖^2)+
            potentialWork seed M F radius observation time z := by
  obtain ⟨C,C0,paid⟩ := centered_work_heat_paid nu eta positive
  exact ⟨C,C0,fun seed M F radius observation observation0 time => paid seed M F radius observation time _⟩

private theorem pair_continuousOn (M : ℕ) {v z : ℝ → physicalSpace (modes M)} {S : Set ℝ}
    (vc : ContinuousOn v S) (zc : ContinuousOn z S) :
    ContinuousOn (fun t => pairTensor M (v t) (z t)) S := by
  change ContinuousOn (fun t => pairTensorCLM M (v t) (z t)) S
  exact ((pairTensorCLM M).continuous.comp_continuousOn vc).clm_apply zc

private theorem heat_continuousOn (nu : Viscosity) (M : ℕ)
    {v z : ℝ → physicalSpace (modes M)} {S : Set ℝ}
    (vc : ContinuousOn v S) (zc : ContinuousOn z S) :
    ContinuousOn (fun t => heatWork nu M (v t) (z t)) S := by
  let L := LinearMap.toContinuousLinearMap (laplacian (modes M) (modes_zero M) (modes_closed M) nu)
  have left := pair_continuousOn M ((L.continuous.comp_continuousOn vc).const_smul (-nu.coeff)) zc
  have right := pair_continuousOn M vc ((L.continuous.comp_continuousOn zc).const_smul nu.coeff)
  exact ((pair_continuousOn M vc zc).inner (𝕜 := ℝ) (left.add right)).const_mul (2 : ℝ)

theorem potential_continuousOn (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame : ℝ)
    {z : ℝ → physicalSpace (modes M)} {S : Set ℝ} (zc : ContinuousOn z S) :
    ContinuousOn (fun t => potentialWork seed M F radius frame t (z t)) S := by
  let L := LinearMap.toContinuousLinearMap (laplacian (modes M) (modes_zero M) (modes_closed M) nu)
  let read := LinearMap.toContinuousLinearMap (coefficients (modes M))
  have mc := ((NativeWindowTraceDualEvolution.mass_contDiff seed M F radius).continuous.continuousOn).clm_apply zc
  have pc : ContinuousOn (fun t => NativeDistributedLyapunov.potential seed M F radius t (z t)) S := by
    apply ((mc.sub zc).sub ((L.continuous.comp_continuousOn zc).const_smul nu.coeff)).congr
    intro t _
    change NativeDistributedLyapunov.potential seed M F radius t (z t) =
      mass seed M F radius t (z t)-z t-nu.coeff • L (z t)
    rw [NativeDistributedLyapunov.mass_split]
    change NativeDistributedLyapunov.potential seed M F radius t (z t) =
      z t+nu.coeff • laplacian (modes M) (modes_zero M) (modes_closed M) nu (z t)+
        NativeDistributedLyapunov.potential seed M F radius t (z t)-z t-
        nu.coeff • laplacian (modes M) (modes_zero M) (modes_closed M) nu (z t)
    abel
  have kc : ContinuousOn (fun t =>
      transport (modes M) (modes_zero M) (modes_closed M) nu (centered seed M frame t) (z t)) S := by
    have first := (NativeWindowTraceAdjoint.forward_continuous seed M).continuousOn.clm_apply zc
    have last := (NativeWindowHistoryMeanAction.frozen nu M
      (NativeWindowHistoryMeanAction.meanValue seed M frame)).continuous.comp_continuousOn zc
    apply (first.sub last).congr
    intro t _
    change transport (modes M) (modes_zero M) (modes_closed M) nu
      (centered seed M frame t) (z t) =NativeWindowTraceAdjoint.forward seed M t (z t)-
        NativeWindowHistoryMeanAction.frozen nu M (NativeWindowHistoryMeanAction.meanValue seed M frame) (z t)
    rw [← NativeWindowHistoryMeanAction.frozen_source]
    exact (NativeWindowHistoryCreationSource.frozen_transport nu M _ _ (z t)).symm
  exact ((read.continuous.comp_continuousOn pc).inner (𝕜 := ℝ)
    (read.continuous.comp_continuousOn kc)).const_mul (2 : ℝ)

open NativeWindowDistributedAdjoint NativeDistributedWeightedBudget
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)

theorem source_test_compensated_budget (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C epsilon D A : ℝ,0 ≤ C ∧0 < epsilon ∧0 ≤ D ∧0 ≤ A ∧
      ∀ radius ≥ low,∀ outerRadius M observation (observation0 : 0 ≤ observation),
      observation+2 ≤ horizon →
      let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
      let p := response stackedShortCurrent M observation
        (NativeDistributedSourceTest.sourceTest stackedShortCurrent M observation)
        0 (observation+2) (by linarith [observation0])
      let v := fun t => centered stackedShortCurrent M observation t
      let z := fun t => lifted stackedShortCurrent M F radius t (p t)
      (1/2 : ℝ)*‖coefficients (modes M) (NativeDistributedSourceTest.sourceTest stackedShortCurrent M observation)‖^2+
        epsilon*(butterflyGainViscosity.coeff^2/8)*
          (∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*‖coefficients (modes M)
            (testAction (nu := butterflyGainViscosity) M (z t))‖^2)+
        epsilon*(A/(2*butterflyGainViscosity.coeff))*
          (∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*heatWork butterflyGainViscosity M (v t) (z t)) ≤
      D+(∫ t in (0 : ℝ)..(observation+2),pairing (modes M)
        (NativeWindowStageNineSource.forcing stackedShortCurrent M t) (p t))+
        epsilon*A*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          (∑ j : Coordinate,‖pairTensor M (v t) (finite M j (z t))‖^2))+
        epsilon*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          potentialWork stackedShortCurrent M F radius observation t (z t)) := by
  obtain ⟨first,C,epsilon,D,C0,ep,D0,source⟩ :=
    NativeDistributedSourceTest.source_test_budget horizon nonnegative
  obtain ⟨last,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible stackedShortCurrent horizon nonnegative
  obtain ⟨A,A0,heatPaid⟩ := centered_work_heat_paid butterflyGainViscosity
    (butterflyGainViscosity.coeff^2/8) (by positivity [butterflyGainViscosity.coeff_pos])
  refine ⟨max first last,C,epsilon,D,A,C0,ep,D0,A0,
    fun radius above outerRadius M observation observation0 within => ?_⟩
  let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let b := observation+2
  have ordered : 0 ≤ b := by dsimp only [b]; linarith
  let p := response stackedShortCurrent M observation
    (NativeDistributedSourceTest.sourceTest stackedShortCurrent M observation) 0 b ordered
  let v := fun t => centered stackedShortCurrent M observation t
  let z := fun t => lifted stackedShortCurrent M F radius t (p t)
  let weight := fun t => Real.exp (C*t)
  let G := fun t => ‖coefficients (modes M) (testAction (nu := butterflyGainViscosity) M (z t))‖^2
  let Q := fun t => centeredWork stackedShortCurrent M F radius observation t (z t)
  let H := fun t => heatWork butterflyGainViscosity M (v t) (z t)
  let J := fun t => ∑ j : Coordinate,‖pairTensor M (v t) (finite M j (z t))‖^2
  let P := fun t => potentialWork stackedShortCurrent M F radius observation t (z t)
  let alpha := A/(2*butterflyGainViscosity.coeff)
  let eta := butterflyGainViscosity.coeff^2/8
  have generated := inverted radius ((le_max_right first last).trans above) M F
    (NativeWindowFiniteGramFourier.cube_closed outerRadius)
  have zc := response_lift_continuous stackedShortCurrent M F radius observation
    (NativeDistributedSourceTest.sourceTest stackedShortCurrent M observation) b ordered
    (fun t ht => generated t (Icc_subset_Icc le_rfl within ht))
  change ContinuousOn z (Icc 0 b) at zc
  have vc : ContinuousOn v (Icc 0 b) :=
    (NativeWindowTraceAdjoint.value_continuous stackedShortCurrent M).continuousOn.sub continuousOn_const
  have wc : ContinuousOn weight (Icc 0 b) := by dsimp only [weight]; fun_prop
  have gc : ContinuousOn G (Icc 0 b) :=
    ((LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp_continuousOn
      ((LinearMap.toContinuousLinearMap (testAction (nu := butterflyGainViscosity) M)).continuous.comp_continuousOn zc)).norm.pow 2
  have qc := NativeDistributedSourceTest.centered_continuous stackedShortCurrent M F radius observation zc
  have hc := heat_continuousOn butterflyGainViscosity M vc zc
  have jc : ContinuousOn J (Icc 0 b) :=
    continuousOn_finsetSum _ (fun j _ =>
      (pair_continuousOn M vc ((finite M j).continuous.comp_continuousOn zc)).norm.pow 2)
  have pc := potential_continuousOn stackedShortCurrent M F radius observation zc
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
    have original := source radius ((le_max_left first last).trans above)
      outerRadius M observation observation0 within
    have scaled := mul_le_mul_of_nonneg_left paid ep.le
    change (1/2 : ℝ)*‖coefficients (modes M)
      (NativeDistributedSourceTest.sourceTest stackedShortCurrent M observation)‖^2+
      epsilon*(butterflyGainViscosity.coeff^2/4)*(∫ t in (0 : ℝ)..b,weight t*G t) ≤
      D+(∫ t in (0 : ℝ)..b,pairing (modes M)
        (NativeWindowStageNineSource.forcing stackedShortCurrent M t) (p t))+
        epsilon*(∫ t in (0 : ℝ)..b,weight t*Q t) at original
    dsimp only [alpha,eta] at scaled
    change epsilon*((∫ t in (0 : ℝ)..b,weight t*Q t)+
      (A/(2*butterflyGainViscosity.coeff))*(∫ t in (0 : ℝ)..b,weight t*H t)) ≤
      epsilon*((butterflyGainViscosity.coeff^2/8)*(∫ t in (0 : ℝ)..b,weight t*G t)+
        A*(∫ t in (0 : ℝ)..b,weight t*J t)+(∫ t in (0 : ℝ)..b,weight t*P t)) at scaled
    change (1/2 : ℝ)*‖coefficients (modes M)
      (NativeDistributedSourceTest.sourceTest stackedShortCurrent M observation)‖^2+
      epsilon*(butterflyGainViscosity.coeff^2/8)*(∫ t in (0 : ℝ)..b,weight t*G t)+
      epsilon*(A/(2*butterflyGainViscosity.coeff))*(∫ t in (0 : ℝ)..b,weight t*H t) ≤
      D+(∫ t in (0 : ℝ)..b,pairing (modes M)
        (NativeWindowStageNineSource.forcing stackedShortCurrent M t) (p t))+
      epsilon*A*(∫ t in (0 : ℝ)..b,weight t*J t)+epsilon*(∫ t in (0 : ℝ)..b,weight t*P t)
    nlinarith only [original,scaled]
  · have localPaid := heatPaid stackedShortCurrent M F radius observation t (p t)
    change Q t+alpha*H t ≤ eta*G t+A*J t+P t at localPaid
    have scaled := mul_le_mul_of_nonneg_left localPaid (Real.exp_pos (C*t)).le
    change weight t*Q t+alpha*(weight t*H t) ≤ eta*(weight t*G t)+A*(weight t*J t)+weight t*P t
    dsimp only [weight] at *
    nlinarith only [scaled]

end
end SaturationMonoid.NavierStokes.NativeCenteredResponsePayment
