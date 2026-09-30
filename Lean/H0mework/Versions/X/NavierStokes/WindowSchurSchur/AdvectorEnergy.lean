import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorAction
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Mean

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurAdvectorEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM)
open NativeWindowHistoryOseen (H action forcingHistory)
open NativeWindowHistoryMeanProjection (embed mean projection)
open NativeWindowHistoryMeanAction (meanOperator)
open NativeWindowHistoryMeanBlocks (diffusion)
open NativeWindowHistoryMeanDrift (drift)
open NativeWindowTraceWholeHistory (metric metricAction finiteHistory)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

private theorem young (x y eta : ℝ) (positive : 0 < eta) : 2*x*y ≤ eta*x^2+y^2/eta := by
  have cancel : eta*(y^2/eta)=y^2 := mul_div_cancel₀ _ positive.ne'
  apply (mul_le_mul_iff_left₀ positive).mp
  nlinarith only [sq_nonneg (eta*x-y),cancel]

private theorem multiplier_bound (K B epsilon t a d m : ℝ) (K0 : 0 ≤ K) (positive : 0 < epsilon)
    (first : t^2 ≤ K*(d^2+m^2))
    (last : a^2 ≤ (epsilon^2/(16*(K+1)))*d^2+B*m*d) :
    2*t*a ≤ epsilon*d^2+
      (epsilon*K/(4*(K+1))+(16*(K+1)^2*B^2)/epsilon^3)*m^2 := by
  let eta := epsilon/(4*(K+1))
  let z := epsilon^2/(16*(K+1))
  have e0 : 0 < eta := by dsimp only [eta]; positivity
  have z0 : 0 < z := by dsimp only [z]; positivity
  have y := young d (B*m) (2*z) (by positivity)
  have square : a^2 ≤ 2*z*d^2+(B^2/(4*z))*m^2 := by
    have same : (B*m)^2/(2*z)=2*(B^2/(4*z))*m^2 := by ring
    nlinarith only [last,y,same]
  have scaled := div_le_div_of_nonneg_right square e0.le
  have normed := mul_le_mul_of_nonneg_left first e0.le
  have prod := young t a eta e0
  have used : 2*t*a ≤ (eta*K+2*z/eta)*d^2+(eta*K+B^2/(4*z*eta))*m^2 := by
    have distribute : (2*z*d^2+(B^2/(4*z))*m^2)/eta=(2*z/eta)*d^2+(B^2/(4*z*eta))*m^2 := by ring
    nlinarith only [scaled,normed,prod,distribute]
  have lead : eta*K+2*z/eta ≤ epsilon := by
    have same : 2*z/eta=epsilon/2 := by dsimp only [z,eta]; field_simp; ring
    have small : eta*K ≤ epsilon/4 := by
      dsimp only [eta]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0<4*(K+1))).mpr
      nlinarith
    rw [same]
    linarith
  have coefficient : eta*K+B^2/(4*z*eta)=epsilon*K/(4*(K+1))+(16*(K+1)^2*B^2)/epsilon^3 := by
    dsimp only [eta,z]
    field_simp
  have paid := mul_le_mul_of_nonneg_right lead (sq_nonneg d)
  nlinarith only [used,paid,coefficient]

open NativeWindowHistorySchurAdvectorAction (xAction wAction)
open NativeWindowMetricGraphHistory (gradient_bound source_history_bound action_symmetric)

private theorem norm_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : |2*inner ℝ x y| ≤ 2*‖x‖*‖y‖ := by
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x y) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

def xWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : H) : ℝ :=
  2*inner ℝ (metricAction seed frame M F R v) (xAction seed M time v)

theorem source_x_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M ≥ low,
      ∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,∀ v : H,
      |xWork seed M frame time (integerWaveFrequencyCube cutoff) radius v| ≤
        epsilon*‖laplacianAction nu M v‖^2+C*‖v‖^2 := by
  have first := @source_history_bound nu seed horizon nonnegative
  rcases first with ⟨one,K,K0,metricBound⟩
  let z := epsilon^2/(16*(K+1))
  have z0 : 0 < z := by dsimp only [z]; positivity
  obtain ⟨two,B,B0,driftBound⟩ := NativeWindowHistorySchurAdvectorAction.source_graph_bound seed horizon nonnegative z z0
  refine ⟨max one two,epsilon*K/(4*(K+1))+(16*(K+1)^2*B^2)/epsilon^3,by positivity,
    fun radius above cutoff covered M included frame frameInside time timeInside v => ?_⟩
  have t := (metricBound radius ((le_max_left _ _).trans above) cutoff ((le_max_left _ _).trans covered) M frame frameInside v).1
  have a := driftBound M ((le_max_right _ _).trans included) time timeInside v
  have g := mul_le_mul_of_nonneg_left (gradient_bound nu M v) B0
  have small : ‖xAction seed M time v‖^2 ≤ z*‖laplacianAction nu M v‖^2+B*‖v‖*‖laplacianAction nu M v‖ := by
    nlinarith only [a,g]
  have paired : |xWork seed M frame time (integerWaveFrequencyCube cutoff) radius v| ≤
      2*‖metricAction seed frame M (integerWaveFrequencyCube cutoff) radius v‖*‖xAction seed M time v‖ := by
    exact norm_pair (E := H) _ _
  exact paired.trans (multiplier_bound K B epsilon _ _ _ _ K0 positive t small)

theorem diffusion_history (nu : Viscosity) (M : ℕ) (v : H) :
    (diffusion nu M).compLpL 2 averageMeasure v=(-nu.coeff) • laplacianAction nu M v := by
  apply Lp.ext
  filter_upwards [(diffusion nu M).coeFn_compLpL v,(laplacianFiber nu M).coeFn_compLpL v,
    Lp.coeFn_smul (-nu.coeff) (laplacianAction nu M v)] with lag first last scaled
  change ((diffusion nu M).compLpL 2 averageMeasure v) lag=((-nu.coeff) • laplacianAction nu M v) lag
  rw [first,scaled,Pi.smul_apply]
  change diffusion nu M (v lag)=(-nu.coeff) • (((laplacianFiber nu M).compLpL 2 averageMeasure v) lag)
  rw [last,NativeWindowMetricGraphMean.diffusion_laplacian]

theorem source_action_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    action seed M time v=(-nu.coeff) • laplacianAction nu M v+xAction seed M time v+wAction seed M time v := by
  have actual := congrArg (fun A : H →L[ℝ] H => A v)
    (NativeWindowHistorySchurAdvectorAction.source_action_split seed M time)
  change action seed M time v=(diffusion nu M).compLpL 2 averageMeasure v+xAction seed M time v+wAction seed M time v at actual
  exact actual.trans (congrArg (fun u : H => u+xAction seed M time v+wAction seed M time v)
    (diffusion_history nu M v))

/-- The actual joint temporal-response drift and complete shadow forcing. -/
def responseWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset IntegerWavevector) (R : ℕ) : ℝ :=
  let h:=finiteHistory seed time M
  2*inner ℝ (metricAction seed frame M F R h) (wAction seed M time h+forcingHistory seed M time)

private theorem paired_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t l x w f : E) (nu : ℝ) :
    2*inner ℝ t ((-nu) • l+x+w+f)=
      -2*nu*inner ℝ t l+2*inner ℝ t x+2*inner ℝ t (w+f) := by
  simp only [inner_add_right,real_inner_smul_right]
  ring

theorem source_rate_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset IntegerWavevector) (R : ℕ) :
    NativeWindowMetricGraphGreen.sourceRate seed frame M F R time=
      -2*nu.coeff*inner ℝ (metricAction seed frame M F R (finiteHistory seed time M))
        (laplacianAction nu M (finiteHistory seed time M))+
      xWork seed M frame time F R (finiteHistory seed time M)+responseWork seed M frame time F R := by
  have symmetric := congrArg (fun x : ℝ => 2*x) (action_symmetric seed frame M F R (finiteHistory seed time M)
    (action seed M time (finiteHistory seed time M)+forcingHistory seed M time)).symm
  change NativeWindowMetricGraphGreen.sourceRate seed frame M F R time=
    2*inner ℝ (metricAction seed frame M F R (finiteHistory seed time M))
      (action seed M time (finiteHistory seed time M)+forcingHistory seed M time) at symmetric
  have read := source_action_read seed M time (finiteHistory seed time M)
  have actual := congrArg (fun v : H => 2*inner ℝ (metricAction seed frame M F R (finiteHistory seed time M))
    (v+forcingHistory seed M time)) read
  exact symmetric.trans (actual.trans (paired_split (E := H) _ _ _ _ _ nu.coeff))

theorem source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M ≥ low,
      ∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,
      NativeWindowMetricGraphGreen.sourceRate seed frame M (integerWaveFrequencyCube cutoff) radius time ≤
        -(nu.coeff^2/2)*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C*‖finiteHistory seed time M‖^2+
          responseWork seed M frame time (integerWaveFrequencyCube cutoff) radius := by
  have first := @source_history_bound nu seed horizon nonnegative
  rcases first with ⟨one,C1,C10,heat⟩
  obtain ⟨two,C2,C20,drift⟩ := source_x_bound seed horizon nonnegative (nu.coeff^2/2) (by positivity [nu.coeff_pos])
  refine ⟨max one two,C1+C2,add_nonneg C10 C20,
    fun radius above cutoff covered M included frame frameInside time timeInside => ?_⟩
  have h := (heat radius ((le_max_left _ _).trans above) cutoff ((le_max_left _ _).trans covered)
    M frame frameInside (finiteHistory seed time M)).2
  have x := drift radius ((le_max_right _ _).trans above) cutoff ((le_max_right _ _).trans covered)
    M ((le_max_right _ _).trans included) frame frameInside time timeInside (finiteHistory seed time M)
  have signed := le_abs_self (xWork seed M frame time (integerWaveFrequencyCube cutoff) radius (finiteHistory seed time M))
  have original := source_rate_split seed M frame time (integerWaveFrequencyCube cutoff) radius
  linarith only [h,x,signed,original]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem responseWork_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) (frame time : ℝ)
    (frame0 : 0 ≤ frame) (time0 : 0 ≤ time) :
    responseWork seed M (step.2.clockAdvance+frame) (step.2.clockAdvance+time) F R=
      responseWork step.1 M frame time F R := by
  have actions := NativeWindowHistorySchurAdvectorAction.actions_next seed M step generated time time0
  have w : wAction seed M (step.2.clockAdvance+time)=wAction step.1 M time := congrArg Prod.snd actions
  simp only [responseWork,w,NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time time0,
    NativeWindowTraceWholeHistory.metricAction_next seed step generated frame frame0,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time time0]

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurAdvectorEnergy
