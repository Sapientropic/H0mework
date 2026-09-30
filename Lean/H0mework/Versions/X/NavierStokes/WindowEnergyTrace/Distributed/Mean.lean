import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Weighted
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWholeRelative

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeDistributedHistoryPayment
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint (response testAction)
open NativeWindowTraceDualEvolution (mass lifted energy)
open NativeWindowHistoryMeanAction (frozen meanValue)
open NativePhysicalPairing (includeCLM include_norm restrict_include)
noncomputable section
variable {nu : Viscosity}

theorem meanValue_window (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame : ℝ) :
    meanValue seed M frame = NativeWindowDistributedAdjoint.window seed M frame := by
  rw [meanValue,NativeWindowHistoryMeanProjection.mean_original]
  rfl

def meanDrift (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :=
  frozen nu M (meanValue seed M time)-frozen nu M 0

def meanWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ) (z : physicalSpace (modes M)) : ℝ :=
  2*pairing (modes M) (mass seed M F radius time z) (meanDrift seed M frame z)

def centeredWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ) (z : physicalSpace (modes M)) : ℝ :=
  2*pairing (modes M) (mass seed M F radius time z)
    ((NativeWindowTraceAdjoint.forward seed M time-frozen nu M (meanValue seed M frame)) z)

theorem meanDrift_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (z : physicalSpace (modes M)) :
    NativeWindowHistoryMeanDrift.drift seed M time (includeCLM (modes M) (modes_closed M) z)=
      includeCLM (modes M) (modes_closed M) (meanDrift seed M time z) := by
  rw [NativeWindowHistoryMeanDrift.drift_original,restrict_include,meanDrift,
    NativeWindowHistoryCreationSource.frozen_transport,sub_zero]

private theorem zero_frozen (M : ℕ) (z : physicalSpace (modes M)) :
    frozen nu M 0 z=(-nu.coeff) • testAction (nu := nu) M z := by
  have source := congrArg (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M))
    (NativeWindowMetricGraphMean.diffusion_laplacian nu M (includeCLM (modes M) (modes_closed M) z))
  simpa only [NativeWindowHistoryMeanBlocks.diffusion,NativeWindowHistoryOseen.lift,
    NativeWindowHistoryAnnihilationControl.laplacianFiber,ContinuousLinearMap.comp_apply,
    restrict_include,map_smul,testAction] using! source

theorem convection_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ) (z : physicalSpace (modes M)) :
    NativeDistributedLyapunov.convectionWork seed M F radius time z=
      meanWork seed M F radius frame time z+centeredWork seed M F radius frame time z := by
  have action := NativeDistributedLyapunov.forward_split seed M time z
  have split : meanDrift seed M frame z+
      (NativeWindowTraceAdjoint.forward seed M time-frozen nu M (meanValue seed M frame)) z=
      NativeWindowOperatorGreen.convection (modes M) (modes_zero M) (modes_closed M) nu
        (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time) z := by
    simp only [meanDrift,sub_apply,zero_frozen]
    rw [action]
    dsimp only [testAction]
    module
  simp only [NativeDistributedLyapunov.convectionWork,meanWork,centeredWork,← mul_add,← map_add,split]

theorem centeredWork_actual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ) (z : physicalSpace (modes M)) :
    centeredWork seed M F radius frame time z=
      2*pairing (modes M) (mass seed M F radius time z)
        (NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M) nu
          (NativeWindowTraceAdjoint.value seed M time-meanValue seed M frame) z) := by
  rw [centeredWork,← NativeWindowHistoryMeanAction.frozen_source,
    NativeWindowHistoryCreationSource.frozen_transport]

theorem source_mass_graph (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ radius ≥ low, ∀ outerRadius M,
      ∀ time ∈ Icc 0 horizon, ∀ z : physicalSpace (modes M),
      ‖coefficients (modes M) (mass seed M (integerWaveFrequencyCube outerRadius) radius time z)‖^2 ≤
        K*(‖coefficients (modes M) (testAction (nu := nu) M z)‖^2+‖coefficients (modes M) z‖^2) := by
  obtain ⟨low,D,D0,source⟩ := NativeDistributedLyapunov.source_potential_relative seed horizon nonnegative 1 zero_lt_one
  let K := 2*(nu.coeff+1)^2+2*(D+1)^2
  refine ⟨low,K,by positivity,fun radius above outerRadius M time inside z => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let d := ‖coefficients (modes M) (testAction (nu := nu) M z)‖
  let m := ‖coefficients (modes M) z‖
  have potential := source radius above outerRadius M time inside z
  have normed : ‖coefficients (modes M) (mass seed M F radius time z)‖ ≤ (nu.coeff+1)*d+(D+1)*m := by
    rw [NativeDistributedLyapunov.mass_split]
    simp only [map_add,map_smul]
    have first := norm_add_le (coefficients (modes M) z)
      (nu.coeff • coefficients (modes M) (testAction (nu := nu) M z))
    have last := norm_add_le
      (coefficients (modes M) z+nu.coeff • coefficients (modes M) (testAction (nu := nu) M z))
      (coefficients (modes M) (NativeDistributedLyapunov.potential seed M F radius time z))
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos nu.coeff_pos] at first
    dsimp only [F,d,m,testAction] at potential first last ⊢
    linarith only [potential,first,last]
  have squared := pow_le_pow_left₀ (norm_nonneg _) normed 2
  have a := sq_nonneg ((nu.coeff+1)*d-(D+1)*m)
  have padding := add_nonneg
    (mul_nonneg (sq_nonneg (nu.coeff+1)) (sq_nonneg m))
    (mul_nonneg (sq_nonneg (D+1)) (sq_nonneg d))
  change _ ≤ K*(d^2+m^2)
  dsimp only [K]
  nlinarith only [squared,a,padding]

private theorem paired_relative (x y d m K D epsilon : ℝ)
    (K0 : 0 ≤ K) (positive : 0 < epsilon)
    (first : x^2 ≤ K*(d^2+m^2))
    (last : y^2 ≤ (epsilon^2/(4*(K+1)))*d^2+D*m^2) :
    2*x*y ≤ epsilon*d^2+(epsilon*K/(2*(K+1))+2*(K+1)*D/epsilon)*m^2 := by
  let delta := epsilon/(2*(K+1))
  have delta0 : 0 < delta := by dsimp only [delta]; positivity
  have young : 2*x*y ≤ delta*x^2+y^2/delta := by
    apply (mul_le_mul_iff_left₀ delta0).mp
    have cancel : delta*(y^2/delta)=y^2 := mul_div_cancel₀ _ delta0.ne'
    nlinarith only [sq_nonneg (delta*x-y),cancel]
  have scaled := mul_le_mul_of_nonneg_left first delta0.le
  have divided := div_le_div_of_nonneg_right last delta0.le
  have leading : delta*K+(epsilon^2/(4*(K+1)))/delta ≤ epsilon := by
    have half : (epsilon^2/(4*(K+1)))/delta=epsilon/2 := by
      dsimp only [delta]
      field_simp
      ring
    rw [half]
    have small : delta*K ≤ epsilon/2 := by
      dsimp only [delta]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 2*(K+1))).mpr
      nlinarith
    linarith
  have paid := mul_le_mul_of_nonneg_right leading (sq_nonneg d)
  have same : delta*K+D/delta=epsilon*K/(2*(K+1))+2*(K+1)*D/epsilon := by
    dsimp only [delta]
    field_simp
  have distribute : (epsilon^2/(4*(K+1))*d^2+D*m^2)/delta=
      ((epsilon^2/(4*(K+1)))/delta)*d^2+(D/delta)*m^2 := by ring
  rw [distribute] at divided
  nlinarith only [young,scaled,divided,paid,same]

theorem source_mean_paid (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M,
      ∀ frame ∈ Icc 0 horizon, ∀ time ∈ Icc 0 horizon, ∀ w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      let z := lifted seed M F radius time w
      |meanWork seed M F radius frame time z| ≤
        epsilon*‖coefficients (modes M) (testAction (nu := nu) M z)‖^2+C*energy seed M F radius time w := by
  obtain ⟨first,K,K0,massBound⟩ := source_mass_graph seed horizon nonnegative
  let eta := epsilon^2/(4*(K+1))
  have eta0 : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨D,D0,driftBound⟩ := NativeStageNineWindowEnergy.source_drift_relative seed horizon eta eta0
  obtain ⟨last,liftBound⟩ := NativeDistributedLyapunov.source_lifted_control seed horizon nonnegative
  let C := epsilon*K/(2*(K+1))+2*(K+1)*D/epsilon
  have C0 : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨max first last,C,C0,fun radius above outerRadius M frame framed time inside w => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let z := lifted seed M F radius time w
  have firstPaid := massBound radius ((le_max_left first last).trans above) outerRadius M time inside z
  have lastPaid := driftBound M frame framed (includeCLM (modes M) (modes_closed M) z)
  simp only [meanDrift_original,
    NativeWindowHistoryAnnihilationControl.laplacianFiber,NativeWindowHistoryOseen.lift,ContinuousLinearMap.comp_apply,
    restrict_include,
    include_norm (modes M) (modes_zero M) (modes_closed M)] at lastPaid
  have lastForm : ‖coefficients (modes M) (meanDrift seed M frame z)‖^2 ≤
      eta*‖coefficients (modes M) (testAction (nu := nu) M z)‖^2+D*‖coefficients (modes M) z‖^2 := by
    simpa only [testAction] using! lastPaid
  have estimated := paired_relative
    ‖coefficients (modes M) (mass seed M F radius time z)‖
    ‖coefficients (modes M) (meanDrift seed M frame z)‖
    ‖coefficients (modes M) (testAction (nu := nu) M z)‖
    ‖coefficients (modes M) z‖ K D epsilon K0 positive firstPaid lastForm
  have paired : |meanWork seed M F radius frame time z| ≤
      2*‖coefficients (modes M) (mass seed M F radius time z)‖*
        ‖coefficients (modes M) (meanDrift seed M frame z)‖ := by
    rw [meanWork,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm
      (coefficients (modes M) (mass seed M F radius time z))
      (coefficients (modes M) (meanDrift seed M frame z)))
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have energyPaid := mul_le_mul_of_nonneg_left
    (liftBound radius ((le_max_right first last).trans above) outerRadius M time inside w) C0
  exact paired.trans (estimated.trans (add_le_add le_rfl energyPaid))

theorem source_centered_response_graph_gate (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M observation,
      ∀ frame ∈ Icc 0 horizon, ∀ (test : physicalSpace (modes M)) a b (ordered : a ≤ b),
      ∀ time ∈ Ioo a b, time ∈ Ioo 0 horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test a b ordered
      let z := lifted seed M F radius time (p time)
      (nu.coeff^2/4)*‖coefficients (modes M) (testAction (nu := nu) M z)‖^2 ≤
        deriv (fun t => energy seed M F radius t (p t)) time+
          centeredWork seed M F radius frame time z+C*energy seed M F radius time (p time)+
          (2/nu.coeff^2)*NativeForwardWindowSource.kernel (observation-time)^2*
            ‖coefficients (modes M) test‖^2 := by
  obtain ⟨first,C,C0,gate⟩ := NativeWindowDistributedAdjoint.source_response_graph_gate seed horizon nonnegative
  obtain ⟨last,D,D0,meanPaid⟩ := source_mean_paid seed horizon nonnegative
    (nu.coeff^2/4) (by positivity [nu.coeff_pos])
  refine ⟨max first last,C+D,add_nonneg C0 D0,
    fun radius above outerRadius M observation frame framed test a b ordered time inside valid => ?_⟩
  have original := gate radius ((le_max_left first last).trans above) outerRadius M observation test
    a b ordered time inside valid
  have paid := (le_abs_self _).trans (meanPaid radius ((le_max_right first last).trans above)
    outerRadius M frame framed time (Ioo_subset_Icc_self valid)
      (response seed M observation test a b ordered time))
  dsimp only at original paid ⊢
  rw [convection_split seed M (integerWaveFrequencyCube outerRadius) radius frame time] at original
  nlinarith only [original,paid]

end
end SaturationMonoid.NavierStokes.NativeDistributedHistoryPayment
