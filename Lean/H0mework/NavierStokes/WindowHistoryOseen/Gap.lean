import H0mework.NavierStokes.WindowHistoryOseen.Action
import H0mework.NavierStokes.WindowEnergyTraceWhole.Control
import H0mework.NavierStokes.WindowEnergyTraceAdjoint.Gap

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryOseenGap
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeCommonAdvectorAction NativeResolventAdjoint
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_inner include_norm restrict_include)
open NativeWindowHistoryOseen (H lift forwardFiber dualFiber action adjoint)
open NativeWindowTraceWholeHistory (projection projected gradient)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceAdjointGap (gap)
noncomputable section
variable {nu : Viscosity}

theorem projection_lift (M : ℕ) (A : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M))
    (v : wholePhysical) : projection M (lift M A v)=lift M A v := by
  simp only [projection,lift,ContinuousLinearMap.comp_apply,restrict_include]

theorem lift_projection (M : ℕ) (A : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M))
    (v : wholePhysical) : lift M A (projection M v)=lift M A v := by
  simp only [projection,lift,ContinuousLinearMap.comp_apply,restrict_include]

theorem projected_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    projected M (action seed M time v)=action seed M time v := by
  apply Lp.ext
  filter_upwards [(projection M).coeFn_compLpL (action seed M time v),
    NativeWindowHistoryOseen.action_ae seed M time v] with lag projectRead actionRead
  change (((projection M).compLpL 2 averageMeasure (action seed M time v)) lag)=_
  rw [projectRead,actionRead]
  exact projection_lift M _ _

theorem action_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    action seed M time (projected M v)=action seed M time v := by
  apply Lp.ext
  filter_upwards [NativeWindowHistoryOseen.action_ae seed M time (projected M v),
    NativeWindowHistoryOseen.action_ae seed M time v,(projection M).coeFn_compLpL v]
    with lag first last projectRead
  have project : projected M v lag=projection M (v lag) := projectRead
  rw [first,last,project]
  exact lift_projection M _ _

theorem projected_adjoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    projected M (adjoint seed M time v)=adjoint seed M time v := by
  apply Lp.ext
  filter_upwards [(projection M).coeFn_compLpL (adjoint seed M time v),
    NativeWindowHistoryOseen.adjoint_ae seed M time v] with lag projectRead actionRead
  change (((projection M).compLpL 2 averageMeasure (adjoint seed M time v)) lag)=_
  rw [projectRead,actionRead]
  exact projection_lift M _ _

theorem adjoint_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    adjoint seed M time (projected M v)=adjoint seed M time v := by
  apply Lp.ext
  filter_upwards [NativeWindowHistoryOseen.adjoint_ae seed M time (projected M v),
    NativeWindowHistoryOseen.adjoint_ae seed M time v,(projection M).coeFn_compLpL v]
    with lag first last projectRead
  have project : projected M v lag=projection M (v lag) := projectRead
  rw [first,last,project]
  exact lift_projection M _ _

private theorem project_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P A : E →L[ℝ] E) (commutes : ∀ v,P (A v)=A (P v)) (p : ℝ → E) (domain : Set ℝ) (time : ℝ)
    (derivative : HasDerivWithinAt p (-(A (p time))) domain time) :
    HasDerivWithinAt (fun t => P (p t)) (-(A (P (p time)))) domain time := by
  simpa only [Function.comp_def,map_neg,commutes] using P.hasFDerivAt.comp_hasDerivWithinAt time derivative

theorem projected_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (p : ℝ → H)
    (domain : Set ℝ) (time : ℝ) (derivative : HasDerivWithinAt p (-adjoint seed M time (p time)) domain time) :
    HasDerivWithinAt (fun t => projected M (p t)) (-adjoint seed M time (projected M (p time))) domain time := by
  exact project_derivative (E := H) ((projection M).compLpL 2 averageMeasure) (adjoint seed M time)
    (fun v => (projected_adjoint seed M time v).trans (adjoint_projected seed M time v).symm)
    p domain time derivative

theorem fiber_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) (v : wholePhysical) :
    inner ℝ v (forwardFiber seed M sample v)=-nu.coeff*curlPair (modes M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v).1
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v).1 := by
  rw [real_inner_comm]
  change inner ℝ (includeCLM (modes M) (modes_closed M)
    (NativeWindowTraceAdjoint.forward seed M sample
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))) v=_
  rw [include_inner _ (modes_zero M),pairing_symmetric]
  exact physicalOperator_pairing (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceAdjoint.advector seed M sample) (NativeWindowTraceAdjoint.advector_reality seed M sample) _

theorem action_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    inner ℝ v (action seed M time v)=-nu.coeff*gradient M v := by
  rw [L2.inner_def,NativeWindowTraceWholeHistory.gradient,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryOseen.action_ae seed M time v] with lag actual
  rw [actual,fiber_energy]

theorem gradient_gap (nu : Viscosity) (M : ℕ) (v : H) :
    (2*Real.pi)^2*‖projected M v‖^2 ≤ gradient M v := by
  have mass := ((Lp.memLp (projected M v)).integrable_norm_pow (by norm_num : (2 : ℕ)≠0)).const_mul ((2*Real.pi)^2)
  have estimate := integral_mono_ae mass (NativeWindowTraceWholeHistory.gradient_integrable nu M v) (by
    filter_upwards [(projection M).coeFn_compLpL v] with lag actual
    change (2*Real.pi)^2*‖projected M v lag‖^2 ≤ _
    have project : projected M v lag=projection M (v lag) := actual
    rw [project,projection,ContinuousLinearMap.comp_apply,include_norm (modes M) (modes_zero M)]
    exact NativeWindowTraceAdjointGap.spectral_gap (modes M) (modes_zero M) _)
  simpa only [integral_const_mul,← NativeWindowTraceWholeHistory.norm_square,NativeWindowTraceWholeHistory.gradient] using estimate

theorem action_gap (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    inner ℝ v (action seed M time v) ≤ -gap nu*‖projected M v‖^2 := by
  rw [action_energy]
  have paid := mul_le_mul_of_nonneg_left (gradient_gap nu M v) nu.coeff_pos.le
  dsimp only [gap]
  nlinarith only [paid]

theorem adjoint_gap (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    inner ℝ v (-adjoint seed M time v) ≥ gap nu*‖projected M v‖^2 := by
  rw [inner_neg_right (𝕜 := ℝ) v,← NativeWindowHistoryOseen.action_adjoint,real_inner_comm v (action seed M time v)]
  linarith only [action_gap seed M time v]

theorem projected_finiteHistory (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M : ℕ) :
    projected M (NativeWindowTraceWholeHistory.finiteHistory seed time M)=
      NativeWindowTraceWholeHistory.finiteHistory seed time M :=
  NativeWindowTraceWholeHistory.projected_idempotent M (NativeWindowTraceWholeHistory.history seed time)

theorem projected_jointHistory (seed : GeneratedWholeRestartCurrent nu) (frame time : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) :
    projected M (NativeWindowTraceWholeHistory.jointHistory seed frame time M F R)=
      NativeWindowTraceWholeHistory.jointHistory seed frame time M F R := by
  apply Lp.ext
  filter_upwards [(projection M).coeFn_compLpL (NativeWindowTraceWholeHistory.jointHistory seed frame time M F R),
    NativeWindowTraceWholeHistory.jointHistory_ae seed frame time M F R] with lag first last
  change (((projection M).compLpL 2 averageMeasure (NativeWindowTraceWholeHistory.jointHistory seed frame time M F R)) lag)=_
  rw [first,last]
  simp only [projection,NativeWindowTraceWholeHistory.joint,ContinuousLinearMap.comp_apply,restrict_include]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryOseenGap
