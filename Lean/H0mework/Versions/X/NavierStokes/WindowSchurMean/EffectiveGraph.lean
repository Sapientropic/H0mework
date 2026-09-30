import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.Effective
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Mean
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.FeedbackSource

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowMeanEffectiveGraph
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_norm)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistorySchurAction (effective feedback)
open NativeWindowHistoryMeanDrift (drift)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
noncomputable section
variable {nu : Viscosity}

def load (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (u : wholePhysical) : wholePhysical := u-effective seed M time u

private theorem coercive_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u f : E) (positive : ‖u‖^2 ≤ inner ℝ u f) : ‖u‖ ≤ ‖f‖ := by
  have bound:=positive.trans (real_inner_le_norm u f)
  by_cases zero : ‖u‖=0
  · rw [zero]; exact norm_nonneg f
  · have up : 0 < ‖u‖:=lt_of_le_of_ne (norm_nonneg _) (Ne.symm zero)
    nlinarith only [bound,up]

theorem load_mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (u : wholePhysical) : ‖u‖ ≤ ‖load seed M time u‖ := by
  apply coercive_norm (E:=wholePhysical)
  have grad:=NativeWindowHistoryMeanGradient.gradient_nonnegative seed M
    (NativeWindowHistoryMeanProjection.embed u)
  have cost:=NativeWindowHistorySchurAction.cost_nonnegative seed M time u
  have positive:=mul_nonneg nu.coeff_pos.le grad
  change ‖u‖^2 ≤ inner ℝ u (u-effective seed M time u)
  rw [inner_sub_right,real_inner_self_eq_norm_sq,
    NativeWindowHistorySchurAction.effective_energy]
  linarith only [positive,cost]

theorem load_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (u : wholePhysical) :
    nu.coeff • laplacianFiber nu M u=
      load seed M time u-u+drift seed M time u+feedback seed M time u := by
  have original:=NativeWindowMetricGraphMean.drift_read seed M time u
  change NativeWindowHistoryMeanAction.meanOperator seed M time u+
    nu.coeff • laplacianFiber nu M u=drift seed M time u at original
  unfold load effective
  simp only [add_apply]
  rw [← original]
  abel

private theorem four_square {E : Type*} [SeminormedAddCommGroup E] (f u a b : E) :
    ‖f-u+a+b‖^2 ≤ 4*(‖f‖^2+‖u‖^2+‖a‖^2+‖b‖^2) := by
  have triangle:=norm_add_le (f-u+a) b
  have first:=norm_add_le (f-u) a
  have last:=norm_sub_le f u
  have upper:‖f-u+a+b‖ ≤ ‖f‖+‖u‖+‖a‖+‖b‖:=by linarith only [triangle,first,last]
  have squared:=pow_le_pow_left₀ (norm_nonneg _) upper 2
  nlinarith only [squared,sq_nonneg (‖f‖-‖u‖),sq_nonneg (‖f‖-‖a‖),
    sq_nonneg (‖f‖-‖b‖),sq_nonneg (‖u‖-‖a‖),sq_nonneg (‖u‖-‖b‖),sq_nonneg (‖a‖-‖b‖)]

private theorem scalar_graph (nu B D l m f a b : ℝ) (nu0 : 0 < nu) (B0 : 0 ≤ B)
    (D0 : 0 ≤ D) (l0 : 0 ≤ l) (m0 : 0 ≤ m) (mass : m ≤ f)
    (equation : nu^2*l^2 ≤ 4*(f^2+m^2+a^2+b^2))
    (advection : a^2 ≤ (nu^2/16)*l^2+D*m*l)
    (reaction : b^2 ≤ B*(m^2+nu*m*l)) :
    l^2 ≤ ((16+8*B+32*(D+B*nu)^2/nu^2)/nu^2)*f^2 := by
  have ms:=pow_le_pow_left₀ m0 mass 2
  have ml:=mul_le_mul_of_nonneg_right mass l0
  have dml:=mul_le_mul_of_nonneg_left ml D0
  have bms:=mul_le_mul_of_nonneg_left ms B0
  have bml:=mul_le_mul_of_nonneg_left ml (mul_nonneg B0 nu0.le)
  have bound:3*nu^2*l^2 ≤ (32+16*B)*f^2+16*(D+B*nu)*f*l := by
    nlinarith only [equation,advection,reaction,ms,dml,bms,bml]
  have young:16*(D+B*nu)*f*l ≤ nu^2*l^2+64*(D+B*nu)^2/nu^2*f^2 := by
    have raw : 2*(nu*l)*(8*(D+B*nu)*f/nu) ≤
        (nu*l)^2+(8*(D+B*nu)*f/nu)^2 := by
      nlinarith only [sq_nonneg (nu*l-8*(D+B*nu)*f/nu)]
    calc
      _=2*(nu*l)*(8*(D+B*nu)*f/nu) := by field_simp; ring
      _≤(nu*l)^2+(8*(D+B*nu)*f/nu)^2 := raw
      _=_ := by ring
  have coefficient : ((16+8*B+32*(D+B*nu)^2/nu^2)/nu^2)*f^2=
      ((16+8*B+32*(D+B*nu)^2/nu^2)*f^2)/nu^2 := by ring
  rw [coefficient]
  apply (le_div_iff₀ (sq_pos_of_pos nu0)).mpr
  ring_nf at bound young ⊢
  linarith only [bound,young]

def graphBudget (seed : GeneratedWholeRestartCurrent nu) (horizon B : ℝ) : ℝ :=
  (16+8*B+32*(NativeWindowHistoryCreationSource.budget seed horizon (nu.coeff^2/16)+
    B*nu.coeff)^2/nu.coeff^2)/nu.coeff^2

theorem graph_of_feedback (seed : GeneratedWholeRestartCurrent nu) (horizon B : ℝ)
    (B0 : 0 ≤ B) (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon)
    (v : NativeFiniteActionResolvent.physicalSpace (modes M))
    (paid : ‖feedback seed M time (includeCLM (modes M) (modes_closed M) v)‖^2 ≤
      B*NativeWindowHistoryHeatDual.energy nu M v) :
    ‖laplacianFiber nu M (includeCLM (modes M) (modes_closed M) v)‖^2 ≤
      graphBudget seed horizon B*‖load seed M time (includeCLM (modes M) (modes_closed M) v)‖^2 := by
  let u:=includeCLM (modes M) (modes_closed M) v
  let D:=NativeWindowHistoryCreationSource.budget seed horizon (nu.coeff^2/16)
  have small : 0 < nu.coeff^2/16 := div_pos (sq_pos_of_pos nu.coeff_pos) (by norm_num)
  have D0 : 0 ≤ D:=NativeWindowHistoryCreationSource.budget_nonnegative seed horizon _ small
  have grad : inner ℝ u (laplacianFiber nu M u)=NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1 := by
    rw [NativeWindowMetricGraphHistory.fiber_gradient]
    simp only [u,NativePhysicalPairing.restrict_include]
  have energy : NativeWindowHistoryHeatDual.energy nu M v=
      ‖u‖^2+nu.coeff*inner ℝ u (laplacianFiber nu M u) := by
    rw [grad]
    simp only [NativeWindowHistoryHeatDual.energy,u,include_norm (modes M) (modes_zero M)]
  have pairing:=real_inner_le_norm u (laplacianFiber nu M u)
  have reaction : ‖feedback seed M time u‖^2 ≤
      B*(‖u‖^2+nu.coeff*‖u‖*‖laplacianFiber nu M u‖) := by
    rw [energy] at paid
    exact paid.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (by nlinarith only [mul_le_mul_of_nonneg_left pairing nu.coeff_pos.le])) B0)
  have advection := NativeWindowHistoryMeanDrift.source_whole_bound seed horizon
    (nu.coeff^2/16) small M time inside u
  dsimp only at advection
  have normed := real_inner_self_eq_norm_sq (NativeFiniteActionResolvent.coefficients (modes M)
    (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) u)))
  change NativeFiniteActionResolvent.pairing (modes M) _ _=‖NativeFiniteActionResolvent.coefficients (modes M) _‖^2 at normed
  rw [normed,← NativeWindowMetricGraphHistory.laplacian_norm,
    ← NativeWindowMetricGraphHistory.fiber_gradient] at advection
  have advected : ‖drift seed M time u‖^2 ≤ (nu.coeff^2/16)*‖laplacianFiber nu M u‖^2+
      D*‖u‖*‖laplacianFiber nu M u‖ := by
    have extra:=mul_le_mul_of_nonneg_left pairing D0
    change _ ≤ (nu.coeff^2/16)*‖laplacianFiber nu M u‖^2+D*inner ℝ u (laplacianFiber nu M u) at advection
    nlinarith only [advection,extra]
  have original:=congrArg (fun x : wholePhysical => ‖x‖^2) (load_split seed M time u)
  rw [norm_smul,Real.norm_of_nonneg nu.coeff_pos.le,mul_pow] at original
  have equation:=original.trans_le (four_square (load seed M time u) u
    (drift seed M time u) (feedback seed M time u))
  exact scalar_graph nu.coeff B D _ _ _ _ _ nu.coeff_pos B0 D0
    (norm_nonneg _) (norm_nonneg _) (load_mass seed M time u) equation advected reaction

theorem source_graph_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time∈Icc 0 horizon,
      ∀ v : NativeFiniteActionResolvent.physicalSpace (modes M),
        ‖laplacianFiber nu M (includeCLM (modes M) (modes_closed M) v)‖^2 ≤
          C*‖load seed M time (includeCLM (modes M) (modes_closed M) v)‖^2 := by
  obtain ⟨B,B0,paid⟩:=NativeWindowHistoryAdjointSpatialFeedback.source_feedback_bound seed horizon
  refine ⟨graphBudget seed horizon B,?_,fun M time inside v =>
    graph_of_feedback seed horizon B B0 M time inside v (paid M time inside v)⟩
  unfold graphBudget
  positivity

theorem source_load (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    load seed M time (NativeWindowHistoryMeanProjection.mean
      (NativeWindowTraceWholeHistory.finiteHistory seed time M))=
        NativeWindowHistorySchurCompletion.commonForce seed M time := by
  unfold load NativeWindowHistorySchurCompletion.commonForce
  rw [NativeWindowHistorySchurAction.source_rate]
  abel

theorem source_mean_graph (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time∈Icc 0 horizon,
      ‖laplacianFiber nu M (NativeWindowHistoryMeanProjection.mean
        (NativeWindowTraceWholeHistory.finiteHistory seed time M))‖^2 ≤
          C*‖NativeWindowHistorySchurCompletion.commonForce seed M time‖^2 := by
  obtain ⟨C,C0,paid⟩:=source_graph_bound seed horizon
  refine ⟨C,C0,fun M time inside => ?_⟩
  have projected:=congrArg NativeWindowHistoryMeanProjection.mean
    (NativeWindowHistoryMeanGradient.source_projection seed M time)
  have source:NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)=
      includeCLM (modes M) (modes_closed M) (NativeWindowHistoryMeanGradient.meanValue M
        (NativeWindowTraceWholeHistory.finiteHistory seed time M)) := by
    simpa only [NativeWindowHistoryMeanProjection.projection,ContinuousLinearMap.comp_apply,
      NativeWindowHistoryMeanProjection.mean_embed] using projected
  have bound:=paid M time inside (NativeWindowHistoryMeanGradient.meanValue M
    (NativeWindowTraceWholeHistory.finiteHistory seed time M))
  rw [← source,source_load] at bound
  exact bound

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem load_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0 ≤ time) (u : wholePhysical) :
    load seed M (step.2.clockAdvance+time) u=load step.1 M time u := by
  have same:=NativeWindowHistorySchurAction.action_next seed M step generated time nonnegative
  exact congrArg (fun A : wholePhysical →L[ℝ] wholePhysical => u-A u) (congrArg Prod.fst same)

end
end SaturationMonoid.NavierStokes.NativeWindowMeanEffectiveGraph
