import H0mework.NavierStokes.WindowHistoryMetricGraph.Green
import H0mework.NavierStokes.WindowSchurMean.Drift

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowMetricGraphMean
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

def meanWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset IntegerWavevector) (R : ℕ) (u : wholePhysical) : ℝ :=
  2*inner ℝ u (metric seed frame M F R (drift seed M time u))

private theorem drift_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (u : wholePhysical) :
    ‖drift seed M time u‖^2≤epsilon*‖laplacianFiber nu M u‖^2+
      NativeWindowHistoryCreationSource.budget seed horizon epsilon*‖u‖*‖laplacianFiber nu M u‖ := by
  have source := NativeWindowHistoryMeanDrift.source_whole_bound seed horizon epsilon positive M time inside u
  dsimp only at source
  have normed := real_inner_self_eq_norm_sq (coefficients (modes M) (NativeWindowOperatorGreen.laplacian
    (modes M) (modes_zero M) (modes_closed M) nu (restrictCLM (modes M) (modes_zero M) (modes_closed M) u)))
  change pairing (modes M) _ _=‖coefficients (modes M) _‖^2 at normed
  rw [normed,← NativeWindowMetricGraphHistory.laplacian_norm,← NativeWindowMetricGraphHistory.fiber_gradient] at source
  have bounded := mul_le_mul_of_nonneg_left (real_inner_le_norm u (laplacianFiber nu M u))
    (NativeWindowHistoryCreationSource.budget_nonnegative seed horizon epsilon positive)
  nlinarith only [source,bounded]

theorem source_mean_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M : ℕ,
      ∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,∀ u : wholePhysical,
      |meanWork seed M frame time (integerWaveFrequencyCube cutoff) radius u| ≤
        epsilon*‖laplacianFiber nu M u‖^2+C*‖u‖^2 := by
  have fact := @NativeWindowMetricGraphHistory.source_point_bound nu seed horizon nonnegative
  rcases fact with ⟨low,K,K0,source⟩
  let z := epsilon^2/(16*(K+1))
  have z0 : 0<z := by dsimp only [z]; positivity
  let B := NativeWindowHistoryCreationSource.budget seed horizon z
  refine ⟨low,epsilon*K/(4*(K+1))+(16*(K+1)^2*B^2)/epsilon^3,by positivity,
    fun radius above cutoff covered M frame frameInside time timeInside u => ?_⟩
  have t := (source radius above cutoff covered M frame frameInside u).1
  have a := drift_bound seed horizon z z0 M time timeInside u
  have paired : |meanWork seed M frame time (integerWaveFrequencyCube cutoff) radius u|≤
      2*‖metric seed frame M (integerWaveFrequencyCube cutoff) radius u‖*‖drift seed M time u‖ := by
    unfold meanWork
    rw [← NativeWindowMetricGraphHistory.metric_symmetric,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
  exact paired.trans (multiplier_bound K B epsilon _ _ _ _ K0 positive t a)

theorem diffusion_laplacian (nu : Viscosity) (M : ℕ) (u : wholePhysical) :
    diffusion nu M u=(-nu.coeff) • laplacianFiber nu M u := by
  let v:=restrictCLM (modes M) (modes_zero M) (modes_closed M) u
  have zero : NativeWindowHistoryMeanAction.frozen nu M 0 v=
      NativeWindowOperatorGreen.dissipative (modes M) (modes_zero M) (modes_closed M) nu v := by
    apply Subtype.ext
    change NativeCommonAdvectorAction.frozenOperator (modes M) nu (NativeWindowTraceAdjoint.curlMap M 0) v.1=_
    rw [map_zero]
    rfl
  change includeCLM (modes M) (modes_closed M) (NativeWindowHistoryMeanAction.frozen nu M 0 v)=
    (-nu.coeff) • includeCLM (modes M) (modes_closed M)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)
  rw [zero,NativeWindowOperatorGreen.dissipative_laplacian,LinearMap.smul_apply,map_smul]

theorem drift_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u : wholePhysical) :
    meanOperator seed M time u+nu.coeff • laplacianFiber nu M u=drift seed M time u := by
  simp only [drift,sub_apply,diffusion_laplacian,neg_smul,sub_neg_eq_add]

private theorem mean_pair (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset IntegerWavevector) (R : ℕ) (u : wholePhysical) :
    inner ℝ (embed u) (metricAction seed frame M F R
      (action seed M time (embed u)+nu.coeff • laplacianAction nu M (embed u)))=
      inner ℝ u (metric seed frame M F R (drift seed M time u)) := by
  let w : H := action seed M time (embed u)+nu.coeff • laplacianAction nu M (embed u)
  have linear : mean w=mean (action seed M time (embed u))+nu.coeff • mean (laplacianAction nu M (embed u)) := by
    simp only [w,map_add,map_smul]
  have lap : mean (laplacianAction nu M (embed u))=laplacianFiber nu M u := by
    simpa only [NativeWindowHistoryMeanProjection.mean_embed] using!
      NativeWindowHistoryMeanProjection.mean_comp (laplacianFiber nu M) (embed u)
  have actual : mean w=drift seed M time u := linear.trans
    ((congrArg₂ (fun x y : wholePhysical => x+nu.coeff • y)
      (NativeWindowHistoryMeanAction.mean_action seed M time u) lap).trans (drift_read seed M time u))
  have first := NativeWindowHistoryMeanProjection.embed_pairing u (metricAction seed frame M F R w)
  have last := congrArg (fun x : wholePhysical => inner ℝ u x)
    (NativeWindowHistoryMeanProjection.mean_comp (metric seed frame M F R) w)
  have final := congrArg (fun x : wholePhysical => inner ℝ u (metric seed frame M F R x)) actual
  simpa only [w] using! first.trans (last.trans final)

private theorem residual_square (v : H) :
    NativeWindowHistoryMeanProjection.residual (NativeWindowHistoryMeanProjection.residual v)=
      NativeWindowHistoryMeanProjection.residual v := by
  change NativeWindowHistoryMeanProjection.residual v-projection (NativeWindowHistoryMeanProjection.residual v)=_
  rw [NativeWindowHistoryMeanProjection.projection_residual,sub_zero]

private theorem residual_pair (T : wholePhysical →L[ℝ] wholePhysical) (v w : H) :
    inner ℝ (NativeWindowHistoryMeanProjection.residual v) (T.compLpL 2 averageMeasure w)=
      inner ℝ (NativeWindowHistoryMeanProjection.residual v)
        (T.compLpL 2 averageMeasure (NativeWindowHistoryMeanProjection.residual w)) := by
  have first := NativeWindowHistoryMeanProjection.residual_symmetric v (T.compLpL 2 averageMeasure w)
  have last := NativeWindowHistoryMeanProjection.residual_symmetric v
    (T.compLpL 2 averageMeasure (NativeWindowHistoryMeanProjection.residual w))
  have one := congrArg (fun x : H => inner ℝ v x) (NativeWindowHistoryMeanProjection.residual_comp T w)
  have two := congrArg (fun x : H => inner ℝ v x)
    (NativeWindowHistoryMeanProjection.residual_comp T (NativeWindowHistoryMeanProjection.residual w))
  have three := congrArg (fun x : H => inner ℝ v (T.compLpL 2 averageMeasure x)) (residual_square w)
  exact (first.trans one).trans ((last.trans two).trans three).symm

/-- The original residual-residual advection, with its entire pressure projection. -/
def bathWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : H) : ℝ :=
  2*inner ℝ (NativeWindowHistoryMeanProjection.residual v) (metricAction seed frame M F R
    (NativeWindowHistoryMeanBlocks.bath seed M time v+
      nu.coeff • laplacianAction nu M (NativeWindowHistoryMeanProjection.residual v)))

private theorem paired_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (x y z : E) : inner ℝ x (T (y+z))=inner ℝ x (T y)+inner ℝ x (T z) := by
  rw [map_add,inner_add_right]

theorem diagonal_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : H) :
    NativeWindowMetricGraphGreen.diagonalWork seed M frame time F R v=
      meanWork seed M frame time F R (mean v)+bathWork seed M frame time F R v := by
  have first : inner ℝ (projection v) (metricAction seed frame M F R
      (action seed M time (projection v)+nu.coeff • laplacianAction nu M (projection v)))=
      inner ℝ (mean v) (metric seed frame M F R (drift seed M time (mean v))) := mean_pair seed M frame time F R (mean v)
  have last := residual_pair (metric seed frame M F R) v (action seed M time (NativeWindowHistoryMeanProjection.residual v))
  have split1 := paired_add (E := H) (metricAction seed frame M F R) (NativeWindowHistoryMeanProjection.residual v)
    (action seed M time (NativeWindowHistoryMeanProjection.residual v))
    (nu.coeff • laplacianAction nu M (NativeWindowHistoryMeanProjection.residual v))
  have split2 := paired_add (E := H) (metricAction seed frame M F R) (NativeWindowHistoryMeanProjection.residual v)
    (NativeWindowHistoryMeanBlocks.bath seed M time v)
    (nu.coeff • laplacianAction nu M (NativeWindowHistoryMeanProjection.residual v))
  change inner ℝ (NativeWindowHistoryMeanProjection.residual v)
    (metricAction seed frame M F R (action seed M time (NativeWindowHistoryMeanProjection.residual v)))=
      inner ℝ (NativeWindowHistoryMeanProjection.residual v)
        (metricAction seed frame M F R (NativeWindowHistoryMeanBlocks.bath seed M time v)) at last
  unfold NativeWindowMetricGraphGreen.diagonalWork meanWork bathWork
  linarith only [first,last,split1,split2]

theorem source_bath_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M : ℕ,
      ∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,∀ v : H,
      2*inner ℝ v (metricAction seed frame M (integerWaveFrequencyCube cutoff) radius (action seed M time v)) ≤
        -(nu.coeff^2/4)*‖laplacianAction nu M v‖^2+C*‖v‖^2+
          bathWork seed M frame time (integerWaveFrequencyCube cutoff) radius v := by
  have one := @NativeWindowMetricGraphGreen.source_green_bound nu seed horizon nonnegative
  rcases one with ⟨first,C1,C10,green⟩
  have two := @source_mean_bound nu seed horizon nonnegative (nu.coeff^2/4) (by positivity [nu.coeff_pos])
  rcases two with ⟨last,C2,C20,drift⟩
  refine ⟨max first last,C1+C2,add_nonneg C10 C20,fun radius above cutoff covered M frame frameInside time timeInside v => ?_⟩
  have full := green radius ((le_max_left _ _).trans above) cutoff ((le_max_left _ _).trans covered)
    M frame frameInside time timeInside v
  have small := drift radius ((le_max_right _ _).trans above) cutoff ((le_max_right _ _).trans covered)
    M frame frameInside time timeInside (mean v)
  have signed := le_abs_self (meanWork seed M frame time (integerWaveFrequencyCube cutoff) radius (mean v))
  have graph := NativeWindowMetricGraphGreen.graph_split nu M v
  have mass := NativeWindowMetricGraphGreen.mass_split v
  have positive := mul_nonneg C20 (sq_nonneg ‖NativeWindowHistoryMeanProjection.residual v‖)
  have lapPositive := mul_nonneg (sq_nonneg nu.coeff) (sq_nonneg ‖laplacianAction nu M (NativeWindowHistoryMeanProjection.residual v)‖)
  have same := diagonal_read seed M frame time (integerWaveFrequencyCube cutoff) radius v
  have graphScaled := congrArg (fun x : ℝ => nu.coeff^2*x) graph
  have massScaled := congrArg (fun x : ℝ => C2*x) mass
  nlinarith only [full,small,signed,graphScaled,massScaled,positive,lapPositive,same]

private theorem rate_upper (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time b : ℝ)
    (bound : 2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M F R
      (action seed M time (finiteHistory seed time M))) ≤ b) :
    NativeWindowMetricGraphGreen.sourceRate seed frame M F R time ≤ b+
      2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M F R (forcingHistory seed M time)) := by
  have split := congrArg (fun x : ℝ => 2*x) (paired_add (E := H) (metricAction seed frame M F R)
    (finiteHistory seed time M) (action seed M time (finiteHistory seed time M)) (forcingHistory seed M time))
  have actual : NativeWindowMetricGraphGreen.sourceRate seed frame M F R time=
    2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M F R (action seed M time (finiteHistory seed time M)))+
      2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M F R (forcingHistory seed M time)) := by
    simpa only [NativeWindowMetricGraphGreen.sourceRate,mul_add] using! split
  exact actual.trans_le (add_le_add bound le_rfl)

theorem source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M : ℕ,
      ∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,
      NativeWindowMetricGraphGreen.sourceRate seed frame M (integerWaveFrequencyCube cutoff) radius time ≤
        -(nu.coeff^2/4)*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C*‖finiteHistory seed time M‖^2+
          bathWork seed M frame time (integerWaveFrequencyCube cutoff) radius (finiteHistory seed time M)+
          2*inner ℝ (finiteHistory seed time M) (metricAction seed frame M (integerWaveFrequencyCube cutoff) radius
            (forcingHistory seed M time)) := by
  have fact := @source_bath_bound nu seed horizon nonnegative
  rcases fact with ⟨low,C,C0,paid⟩
  exact ⟨low,C,C0,fun radius above cutoff covered M frame frameInside time timeInside =>
    rate_upper seed frame M _ radius time _
      (paid radius above cutoff covered M frame frameInside time timeInside (finiteHistory seed time M))⟩

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem bath_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) (frame time : ℝ)
    (frame0 : 0 ≤ frame) (time0 : 0 ≤ time) (v : H) :
    bathWork seed M (step.2.clockAdvance+frame) (step.2.clockAdvance+time) F R v=
      bathWork step.1 M frame time F R v := by
  have blocks := NativeWindowHistoryMeanBlocks.blocks_next seed M step generated time time0
  simp only [Prod.mk.injEq] at blocks
  simp only [bathWork,blocks.2.2.2,NativeWindowTraceWholeHistory.metricAction_next seed step generated frame frame0]

end
end SaturationMonoid.NavierStokes.NativeWindowMetricGraphMean
