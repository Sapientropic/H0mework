import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.CenteredRate

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeCenteredCompensated
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint NativeDistributedWeightedBudget
open NativeWindowTraceDualEvolution (mass inverse lifted energy)
open NativeCenteredResponseTensor (centered tensor)
open NativeCenteredResponsePayment (heatWork potentialWork)
open NativeCenteredResponseRate (remainingRate)
open NativeCenteredResponseClock (clockWork)
open NativeResponseTensorPayment (pairTensor pairTensorCLM)
open NativeUnheatedIntegralBilinear (diagonal_ac dominated integral_of_ac_derivative)
noncomputable section
variable {nu : Viscosity}

private theorem product_ac {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {x : ℝ → E} {y : ℝ → F} {a b : ℝ}
    (first : AbsolutelyContinuousOnInterval x a b) (last : AbsolutelyContinuousOnInterval y a b) :
    AbsolutelyContinuousOnInterval (fun t => (x t,y t)) a b := by
  unfold AbsolutelyContinuousOnInterval at first last ⊢
  apply squeeze_zero' (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg) _
    (by simpa using first.add last)
  filter_upwards with intervals
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Prod.dist_eq]
  exact max_le (le_add_of_nonneg_right dist_nonneg) (le_add_of_nonneg_left dist_nonneg)

private theorem bilinear_ac {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {x : ℝ → E} {y : ℝ → F} {a b : ℝ}
    (first : AbsolutelyContinuousOnInterval x a b) (last : AbsolutelyContinuousOnInterval y a b) :
    AbsolutelyContinuousOnInterval (fun t => B (x t) (y t)) a b := by
  let D : (E×F) →L[ℝ] (E×F) →L[ℝ] G :=
    B.bilinearComp (ContinuousLinearMap.fst ℝ E F) (ContinuousLinearMap.snd ℝ E F)
  have read (u v : E×F) : D u v=B u.1 v.2 := rfl
  have actual := diagonal_ac D (product_ac first last)
  simpa only [read] using actual

private theorem linear_ac {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {x : ℝ → E} {a b : ℝ}
    (actual : AbsolutelyContinuousOnInterval x a b) : AbsolutelyContinuousOnInterval (fun t => L (x t)) a b := by
  apply dominated actual ‖L‖
  intro s _ t _
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  exact L.le_opNorm _

private theorem square_ac (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame b : ℝ)
    (generated : ∀ t∈uIcc 0 b,(mass seed M F radius t).IsInvertible)
    {p : ℝ → physicalSpace (modes M)} (pa : AbsolutelyContinuousOnInterval p 0 b) :
    AbsolutelyContinuousOnInterval (fun t => ‖tensor seed M F radius frame t (p t)‖^2) 0 b := by
  have ia : ContDiffOn ℝ 1 (inverse seed M F radius) (uIcc 0 b) :=
    fun t ht => ((generated t ht).contDiffAt_map_inverse.comp t
      (NativeWindowTraceDualEvolution.mass_contDiff seed M F radius).contDiffAt).contDiffWithinAt
  have za := bilinear_ac (ContinuousLinearMap.apply ℝ (physicalSpace (modes M))) pa ia.absolutelyContinuousOnInterval
  have ua := linear_ac (NativeWindowStageNineSource.lift (modes M))
    (NativeWindowHierarchyPairWindow.state_ac_total seed 0 b)
  have ma : AbsolutelyContinuousOnInterval (fun _ : ℝ => NativeWindowHistoryMeanAction.meanValue seed M frame) 0 b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => NativeWindowHistoryMeanAction.meanValue seed M frame)).contDiffOn.absolutelyContinuousOnInterval
  have qa := bilinear_ac (pairTensorCLM M) (ua.sub ma) za
  have sa := diagonal_ac (innerSL ℝ) qa
  change AbsolutelyContinuousOnInterval (fun t => inner ℝ
    (tensor seed M F radius frame t (p t)) (tensor seed M F radius frame t (p t))) 0 b at sa
  simpa only [real_inner_self_eq_norm_sq] using sa

private theorem heat_continuous (nu : Viscosity) (M : ℕ)
    {v z : ℝ → physicalSpace (modes M)} {S : Set ℝ}
    (vc : ContinuousOn v S) (zc : ContinuousOn z S) : ContinuousOn (fun t => heatWork nu M (v t) (z t)) S := by
  let L := LinearMap.toContinuousLinearMap (testAction (nu := nu) M)
  have pair {x y : ℝ → physicalSpace (modes M)} (xc : ContinuousOn x S) (yc : ContinuousOn y S) :
      ContinuousOn (fun t => pairTensor M (x t) (y t)) S :=
    ((pairTensorCLM M).continuous.comp_continuousOn xc).clm_apply yc
  exact ((pair vc zc).inner (𝕜 := ℝ)
    ((pair ((L.continuous.comp_continuousOn vc).const_smul (-nu.coeff)) zc).add
      (pair vc ((L.continuous.comp_continuousOn zc).const_smul nu.coeff)))).const_mul (2 : ℝ)

theorem source_weighted_heat_write (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∀ radius ≥ low,∀ outerRadius M observation frame C
      (test : physicalSpace (modes M)) b (ordered : 0 ≤ b),b ≤ horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test 0 b ordered
      let v := fun t => centered seed M frame t
      let z := fun t => lifted seed M F radius t (p t)
      let Q := fun t => tensor seed M F radius frame t (p t)
      (∫ t in (0 : ℝ)..b,Real.exp (C*t)*heatWork nu M (v t) (z t)) =
        -‖Q 0‖^2-(∫ t in (0 : ℝ)..b,Real.exp (C*t)*
          (2*inner ℝ (Q t) (remainingRate seed M F radius frame t (p t) (load (nu := nu) observation M test t))+
            clockWork seed M F radius frame t (p t)+C*‖Q t‖^2)) := by
  obtain ⟨first,rate⟩ := NativeCenteredResponseRate.source_tensor_square_rate seed horizon nonnegative
  obtain ⟨last,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  refine ⟨max first last,fun radius above outerRadius M observation frame C test b ordered within => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let p := response seed M observation test 0 b ordered
  let v := fun t => centered seed M frame t
  let z := fun t => lifted seed M F radius t (p t)
  let Q := fun t => tensor seed M F radius frame t (p t)
  let R := fun t => heatWork nu M (v t) (z t)+
    2*inner ℝ (Q t) (remainingRate seed M F radius frame t (p t) (load (nu := nu) observation M test t))+
      clockWork seed M F radius frame t (p t)
  let weight := fun t => Real.exp (C*t)
  have generated := inverted radius ((le_max_right first last).trans above) M F
    (NativeWindowFiniteGramFourier.cube_closed outerRadius)
  have inside : uIcc 0 b⊆Icc 0 horizon := by rw [uIcc_of_le ordered]; exact Icc_subset_Icc le_rfl within
  have qa := square_ac seed M F radius frame b (fun t ht => generated t (inside ht))
    (response_ac seed M observation test 0 b ordered)
  change AbsolutelyContinuousOnInterval (fun t => ‖Q t‖^2) 0 b at qa
  have wa : ContDiff ℝ 1 weight := (contDiff_const.mul contDiff_id).exp
  have actual := wa.contDiffOn.absolutelyContinuousOnInterval.mul qa
  have derivative : ∀ᵐ t : ℝ,t∈uIcc 0 b →
      HasDerivAt (fun t => weight t*‖Q t‖^2) (weight t*(R t+C*‖Q t‖^2)) t := by
    filter_upwards [rate radius ((le_max_left first last).trans above) outerRadius M observation frame test 0 b ordered,
      (volume : Measure ℝ).ae_ne 0,(volume : Measure ℝ).ae_ne b] with t source left right ht
    rw [uIcc_of_le ordered] at ht
    have physical : t∈Ioo 0 b := ⟨lt_of_le_of_ne ht.1 (Ne.symm left),lt_of_le_of_ne ht.2 right⟩
    have sqr := source physical ⟨physical.1,physical.2.trans_le within⟩
    have wr : HasDerivAt weight (weight t*C) t := by
      simpa only [weight,id_eq,mul_one] using ((hasDerivAt_id t).const_mul C).exp
    apply (wr.mul sqr).congr_deriv
    change weight t*C*‖Q t‖^2+weight t*R t=weight t*(R t+C*‖Q t‖^2)
    ring
  have ri : IntervalIntegrable (fun t => weight t*(R t+C*‖Q t‖^2)) volume 0 b := by
    apply (intervalIntegrable_iff').mpr
    refine ((intervalIntegrable_iff').mp actual.intervalIntegrable_deriv).congr ?_
    filter_upwards [ae_restrict_of_ae derivative,ae_restrict_mem measurableSet_uIcc] with t dt ht
    exact (dt ht).deriv
  have written := integral_of_ac_derivative _ _ actual ri derivative
  simp only [Pi.mul_apply] at written
  have terminal : Q b=0 := by
    change pairTensorCLM M (v b) (lifted seed M F radius b (p b))=0
    simp only [p,response_terminal,lifted,map_zero]
  rw [terminal,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),mul_zero] at written
  have start : weight 0=1 := by simp only [weight,mul_zero,Real.exp_zero]
  rw [start,one_mul,zero_sub] at written
  have zc := response_lift_continuous seed M F radius observation test b ordered
    (fun t ht => generated t (Icc_subset_Icc le_rfl within ht))
  have vc : ContinuousOn v (Icc 0 b) :=
    (NativeWindowTraceAdjoint.value_continuous seed M).continuousOn.sub continuousOn_const
  have hi := (wa.continuous.continuousOn.mul (heat_continuous nu M vc zc)).intervalIntegrable_of_Icc
    (μ := volume) ordered
  have split := intervalIntegral.integral_sub ri hi
  change (∫ t in (0 : ℝ)..b,weight t*(R t+C*‖Q t‖^2)-weight t*heatWork nu M (v t) (z t)) =
    (∫ t in (0 : ℝ)..b,weight t*(R t+C*‖Q t‖^2))-
      (∫ t in (0 : ℝ)..b,weight t*heatWork nu M (v t) (z t)) at split
  have same (t : ℝ) : weight t*(R t+C*‖Q t‖^2)-weight t*heatWork nu M (v t) (z t)=
      weight t*(2*inner ℝ (Q t) (remainingRate seed M F radius frame t (p t) (load (nu := nu) observation M test t))+
        clockWork seed M F radius frame t (p t)+C*‖Q t‖^2) := by dsimp only [R]; ring
  simp_rw [same] at split
  rw [← written] at split
  dsimp only [F,p,v,z,Q,weight] at split ⊢
  linarith only [split]

theorem source_clock_and_weight_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) (C : ℝ) (C0 : 0 ≤ C) :
    ∃ low : ℕ,∃ K : ℝ,0 ≤ K ∧∀ radius ≥ low,∀ outerRadius M,∀ frame∈Icc 0 horizon,
      ∀ᵐ time : ℝ,time∈Icc 0 horizon →∀ w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      clockWork seed M F radius frame time w+C*‖tensor seed M F radius frame time w‖^2 ≤
        K*(1+NativeUnheatedSourceGradient.mass seed time)*energy seed M F radius time w := by
  obtain ⟨first,A,A0,mixed⟩ := NativeCenteredResponseTensor.source_tensor_paid seed horizon nonnegative
  obtain ⟨last,B,B0,clock⟩ := NativeCenteredResponseClock.source_clock_work_paid seed horizon nonnegative
  refine ⟨max first last,B+C*A,by positivity,fun radius above outerRadius M frame framed => ?_⟩
  filter_upwards [mixed radius ((le_max_left first last).trans above) outerRadius M frame framed,
    clock radius ((le_max_right first last).trans above) outerRadius M frame framed] with time qm qc ht w
  have paid := (le_abs_self _).trans (qc ht w)
  have weighted := mul_le_mul_of_nonneg_left (qm ht w) C0
  dsimp only
  nlinarith only [paid,weighted]

open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)

theorem source_test_actual_budget (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C epsilon D A : ℝ,0 ≤ C ∧0 < epsilon ∧0 ≤ D ∧0 ≤ A ∧
      ∀ radius ≥ low,∀ outerRadius M observation (observation0 : 0 ≤ observation),observation+2 ≤ horizon →
      let F := integerWaveFrequencyCube outerRadius
      let test := NativeDistributedSourceTest.sourceTest stackedShortCurrent M observation
      let p := response stackedShortCurrent M observation test 0 (observation+2) (by linarith [observation0])
      let v := fun t => centered stackedShortCurrent M observation t
      let z := fun t => lifted stackedShortCurrent M F radius t (p t)
      let Q := fun t => tensor stackedShortCurrent M F radius observation t (p t)
      (1/2 : ℝ)*‖coefficients (modes M) test‖^2+epsilon*(butterflyGainViscosity.coeff^2/8)*
        (∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*‖coefficients (modes M)
          (testAction (nu := butterflyGainViscosity) M (z t))‖^2) ≤
      D+(∫ t in (0 : ℝ)..(observation+2),pairing (modes M)
        (NativeWindowStageNineSource.forcing stackedShortCurrent M t) (p t))+
        epsilon*A*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          (∑ j : Coordinate,‖pairTensor M (v t) (NativeWindowHistorySpatialTransport.finite M j (z t))‖^2))+
        epsilon*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          potentialWork stackedShortCurrent M F radius observation t (z t))+
        epsilon*(A/(2*butterflyGainViscosity.coeff))*‖Q 0‖^2+
        epsilon*(A/(2*butterflyGainViscosity.coeff))*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          (2*inner ℝ (Q t) (remainingRate stackedShortCurrent M F radius observation t (p t)
            (load (nu := butterflyGainViscosity) observation M test t))+
            clockWork stackedShortCurrent M F radius observation t (p t)+C*‖Q t‖^2)) := by
  obtain ⟨first,C,epsilon,D,A,C0,ep,D0,A0,budget⟩ :=
    NativeCenteredResponsePayment.source_test_compensated_budget horizon nonnegative
  obtain ⟨last,write⟩ := source_weighted_heat_write stackedShortCurrent horizon nonnegative
  refine ⟨max first last,C,epsilon,D,A,C0,ep,D0,A0,
    fun radius above outerRadius M observation observation0 within => ?_⟩
  have paid := budget radius ((le_max_left first last).trans above) outerRadius M observation observation0 within
  have actual := write radius ((le_max_right first last).trans above) outerRadius M observation observation C
    (NativeDistributedSourceTest.sourceTest stackedShortCurrent M observation) (observation+2)
    (by linarith) within
  dsimp only at paid actual ⊢
  rw [actual] at paid
  nlinarith only [paid]

end
end SaturationMonoid.NavierStokes.NativeCenteredCompensated
