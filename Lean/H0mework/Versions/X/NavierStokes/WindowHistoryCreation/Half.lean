import H0mework.Versions.X.NavierStokes.WindowSchurSchur.WeakPairing
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.FeedbackSource
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.HilbertHalfProduct

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCreationHalf
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeFiniteActionResolvent (physicalSpace)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowStressOseenTest (evaluate)
open NativeWindowHistoryCreationGeometry (square)
open NativeWindowHistoryCreationCovariance (centered)
open NativeWindowHistorySchurWeakPairing (potential)
open NativeWindowHistoryAdjointSpatialHalf (moment cap)
open NativeWindowHistoryAdjointSpatialFeedback (read lift historyBudget)
open NativeWindowAbsoluteTimeFourier (polynomial)
open NativeUnheatedSexticLatticePower (radical)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}
local notation "Q" => NativeWindowHistoryMeanProjection.residual

theorem component_product (M : Finset IntegerWavevector) (closed : ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.FiniteModeNegClosed M)
    (u v : physicalSpace M) (j i : Coordinate) :
    (∫x : Torus,(evaluate M M j u x)^2*(evaluate M M i v x)^2) ≤
      cap^2*(∑k∈M,radical k^4*‖u.1 k j‖^2)*(∑k∈M,radical k^2*‖v.1 k i‖^2) := by
  have source:=NativeWindowHilbertHalfProduct.finite_product_bound (E := ℂ) M M
    (fun k => u.1 k j) (fun k => v.1 k i)
  have original (w : physicalSpace M) (d : Coordinate) (x : Torus) :
      polynomial M (fun k => w.1 k d) x=(evaluate M M d w x : ℂ) := by
    simpa only [polynomial,ContinuousMap.coe_mk,smul_eq_mul] using
      (NativeWindowHistoryCreationGeometry.evaluate_complex M closed w d x).symm
  have same : (∫x : Torus,‖polynomial M (fun k => v.1 k i) x • polynomial M (fun k => u.1 k j) x‖^2)=
      ∫x : Torus,(evaluate M M j u x)^2*(evaluate M M i v x)^2 := by
    apply integral_congr_ae
    filter_upwards with x
    rw [original,original,norm_smul,mul_pow,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,sq_abs,sq_abs]
    ring
  exact same.symm.trans_le source

theorem square_product (M : Finset IntegerWavevector) (closed : ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.FiniteModeNegClosed M)
    (u v : physicalSpace M) : (∫x : Torus,square M u x*square M v x) ≤ cap^2*moment M 2 u*moment M 1 v := by
  have regular (j i : Coordinate) : Integrable (fun x : Torus => (evaluate M M j u x)^2*(evaluate M M i v x)^2) :=
    (((evaluate M M j u).continuous.pow 2).mul ((evaluate M M i v).continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have point (x : Torus) : square M u x*square M v x=
      ∑j : Coordinate,∑i : Coordinate,(evaluate M M j u x)^2*(evaluate M M i v x)^2 := by
    simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply,Finset.sum_mul,Finset.mul_sum,pow_two]
    rw [Finset.sum_comm]
  have original : (∫x : Torus,square M u x*square M v x)=
      ∑j : Coordinate,∑i : Coordinate,∫x : Torus,(evaluate M M j u x)^2*(evaluate M M i v x)^2 := by
    simp_rw [point]
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => regular j i))]
    exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ (fun i _ => regular j i)
  rw [original]
  apply (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => component_product M closed u v j i).trans_eq
  simp only [moment,NativeWindowHistoryAdjointSpatialHalf.input_square]
  norm_num only
  simp only [← Finset.mul_sum,← Finset.sum_mul]

open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM restrict_include)
open NativeWindowHistoryAdjointSpatialFeedback (sample)

theorem mean_restrict (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    restrictCLM (modes M) (modes_zero M) (modes_closed M) (mean (finiteHistory seed time M))=
      NativeWindowHistoryMeanAction.meanValue seed M time := by
  have original:=congrArg (restrictCLM (modes M) (modes_zero M) (modes_closed M))
    (NativeWindowHistoryMeanProjection.mean_comp (NativeWindowTraceWholeHistory.projection M)
      (NativeWindowTraceWholeHistory.history seed time))
  change restrictCLM (modes M) (modes_zero M) (modes_closed M) (mean (finiteHistory seed time M))=
    restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (includeCLM (modes M) (modes_closed M) (NativeWindowHistoryMeanAction.meanValue seed M time)) at original
  exact original.trans (restrict_include (modes M) (modes_zero M) (modes_closed M) _)

theorem sample_centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (fun lag => sample M (Q (finiteHistory seed time M)) lag)=ᵐ[averageMeasure]
      fun lag => centered seed M time (time-lag) := by
  let h:=finiteHistory seed time M
  filter_upwards [Lp.coeFn_sub h (embed (mean h)),NativeWindowTraceWholeHistory.finiteHistory_ae seed time M,
    NativeWindowTraceWholeHistory.constant_ae (mean h)] with lag split original averaged
  change Q h lag=h lag-embed (mean h) lag at split
  change restrictCLM (modes M) (modes_zero M) (modes_closed M) (Q h lag)=_
  rw [split,show h lag=NativeWindowTraceWholeHistory.projection M (NativeWindowTraceWholeHistory.original seed (time-lag)) from original,
    show embed (mean h) lag=mean h from averaged,map_sub]
  change restrictCLM (modes M) (modes_zero M) (modes_closed M)
    (includeCLM (modes M) (modes_closed M) (restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (NativeWindowTraceWholeHistory.original seed (time-lag))))-
      restrictCLM (modes M) (modes_zero M) (modes_closed M) (mean (finiteHistory seed time M))=_
  rw [restrict_include,NativeWindowHistoryOseen.restrict_original_total,mean_restrict]
  rfl

theorem potential_history (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    potential seed M time v=∫lag,(∫x : Torus,square (modes M) (sample M (Q (finiteHistory seed time M)) lag) x*
      square (modes M) v x) ∂averageMeasure := by
  exact (NativeWindowHistorySchurWeakPairing.potential_original seed M time v).symm.trans
    (integral_congr_ae ((sample_centered seed M time).fun_comp
      (fun w : physicalSpace (modes M) => ∫x : Torus,square (modes M) w x*square (modes M) v x)).symm)

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ := 4*cap^2*historyBudget seed horizon

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ budget seed horizon := by
  unfold budget
  positivity [NativeWindowHistoryAdjointSpatialFeedback.historyBudget_nonnegative seed horizon]

theorem potential_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    potential seed M time v ≤ budget seed horizon*moment (modes M) 1 v := by
  let h:=Q (finiteHistory seed time M)
  let a:=fun k => radical k^2
  have integrable:=((NativeWindowHistorySchurWeakPairing.potential_integrable seed M time v).congr
    (((sample_centered seed M time).fun_comp
      (fun w : physicalSpace (modes M) => ∫x : Torus,square (modes M) w x*square (modes M) v x)).symm))
  have point (lag : ℝ) : (∫x : Torus,square (modes M) (sample M h lag) x*square (modes M) v x) ≤
      (cap^2*moment (modes M) 1 v)*‖read M a (h lag)‖^2 := by
    have paid:=square_product (modes M) (modes_closed M) (sample M h lag) v
    have recognized:=NativeWindowHistoryAdjointSpatialFeedback.read_moment M 2 (h lag)
    exact paid.trans_eq (by rw [recognized]; dsimp only [sample]; ring)
  rw [potential_history]
  have integrated:=integral_mono_ae integrable
    ((NativeWindowHistoryAdjointSpatialFeedback.read_integrable M a h).const_mul _)
    (Eventually.of_forall point)
  apply integrated.trans
  rw [integral_const_mul,← NativeWindowHistoryAdjointSpatialFeedback.lift_square]
  have cost:=(NativeWindowHistoryAdjointSpatialFeedback.lift_residual_bound M a (finiteHistory seed time M)).trans
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryAdjointSpatialFeedback.history_bound seed horizon M time inside) (by norm_num : (0:ℝ) ≤ 4))
  exact (mul_le_mul_of_nonneg_left cost (mul_nonneg (sq_nonneg _)
    (NativeWindowHistoryAdjointSpatialHalf.moment_nonnegative (modes M) 1 v))).trans_eq (by unfold budget; ring)

theorem source_potential_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ M time,time∈Icc 0 horizon → ∀ v : physicalSpace (modes M),
      potential seed M time v ≤ C*moment (modes M) 1 v :=
  ⟨budget seed horizon,budget_nonnegative seed horizon,fun M time inside v => potential_bound seed horizon M time inside v⟩

theorem source_creation_young (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) (r : H) (a : ℝ) :
    2*a*inner ℝ (NativeWindowHistoryMeanAction.creation seed M time (includeCLM (modes M) (modes_closed M) v)) r ≤
      a^2*budget seed horizon*moment (modes M) 1 v+NativeWindowTraceWholeHistory.gradient M r := by
  exact (NativeWindowHistorySchurWeakPairing.creation_young seed M time v r a).trans
    (add_le_add ((mul_le_mul_of_nonneg_left (potential_bound seed horizon M time inside v) (sq_nonneg a)).trans_eq
      (mul_assoc _ _ _).symm) (le_refl _))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem potential_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (v : physicalSpace (modes M)) :
    potential seed M (step.2.clockAdvance+time) v=potential step.1 M time v := by
  rw [potential_history,potential_history,
    NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCreationHalf
