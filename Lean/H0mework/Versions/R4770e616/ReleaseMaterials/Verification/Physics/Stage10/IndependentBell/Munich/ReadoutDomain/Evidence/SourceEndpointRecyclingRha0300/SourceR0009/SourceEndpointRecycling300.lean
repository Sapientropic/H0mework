import H0mework.Versions.Ra4744604.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceEndpointRecyclingRha0300.SourceR0006.SourceEndpointWords300
import H0mework.Versions.Ra4744604.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceOpenFieldKernelRha0299.SourceR0006.SourceExactDensityFlow299
import H0mework.Versions.R75d8419e.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceTerminalBanachFlowRha0303.SourceR0003.SourceTerminalBanachFlow303

/-! The same complete word source and the selected recycling IVP coincide.
The endpoint observable is arbitrary. The source identity Gram is consumed
through291's entire L² source; it is not substituted for this weighted theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace SourceEndpointRecycling300
open SourceKrausSurvival285 SourceHiddenWordFlow286 SourceKrausWordMass289
open SourceEndpointWords300
open SaturationMonoid.PhysicsCore.StageNineDiracMatterGalerkinEvolution

universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
variable {ι : Type v} [Fintype ι]
variable (source : RawKrausWindow E ι) (hidden : Finset ι)

abbrev EffectAction := Operator (E := E) →L[ℂ] Operator (E := E)

-- Select only the existing normed additive/scalar topology, avoiding the ring search branch.
omit [CompleteSpace E] [Nontrivial E] in
private instance effectActionTopologicalAddGroup : IsTopologicalAddGroup (EffectAction (E := E)) :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup (E := EffectAction (E := E))

omit [CompleteSpace E] [Nontrivial E] in
private instance effectActionContinuousAdd : ContinuousAdd (EffectAction (E := E)) :=
  effectActionTopologicalAddGroup.toContinuousAdd

omit [CompleteSpace E] [Nontrivial E] in
private instance effectActionContinuousSMulReal : ContinuousSMul ℝ (EffectAction (E := E)) := by
  let _ : IsBoundedSMul ℝ (EffectAction (E := E)) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := EffectAction (E := E))
  exact IsBoundedSMul.continuousSMul (α := ℝ) (β := EffectAction (E := E))

def compositionAction (left right : Operator (E := E)) : EffectAction (E := E) :=
  (ContinuousLinearMap.compL ℂ E E E left).comp ((ContinuousLinearMap.compL ℂ E E E).flip right)

omit [CompleteSpace E] [Nontrivial E] in
theorem compositionAction_apply (left right A : Operator (E := E)) :
    compositionAction left right A = left * A * right := rfl

omit [CompleteSpace E] [Nontrivial E] in
theorem compositionAction_continuous (left right : ℝ → Operator (E := E))
    (hl : Continuous left) (hr : Continuous right) :
    Continuous (fun time => compositionAction (left time) (right time)) :=
  ((ContinuousLinearMap.compL ℂ (Operator (E := E)) (Operator (E := E))
      (Operator (E := E))).continuous.comp
        ((ContinuousLinearMap.compL ℂ E E E).continuous.comp hl)).clm_apply
    ((ContinuousLinearMap.compL ℂ E E E).flip.continuous.comp hr)

def heisenberg (time : ℝ) : EffectAction (E := E) :=
  compositionAction (source.clampedCoefficient time).adjoint 1 +
    compositionAction 1 (source.clampedCoefficient time) +
      ∑ j : Letters hidden, compositionAction
        (source.chartJump j.val time).adjoint (source.chartJump j.val time)

theorem heisenberg_apply (time : ℝ) (A : Operator (E := E)) :
    heisenberg source hidden time A =
      (source.clampedCoefficient time).adjoint * A + A * source.clampedCoefficient time +
        ∑ j : Letters hidden, (source.chartJump j.val time).adjoint * A * source.chartJump j.val time := by
  simp only [heisenberg, add_apply, sum_apply, compositionAction_apply, mul_one, one_mul]

theorem heisenberg_continuous : Continuous (heisenberg source hidden) := by
  have paired (left right : ℝ → Operator (E := E)) (hl : Continuous left) (hr : Continuous right) :
      Continuous (fun time => compositionAction
        (left time) (right time)) :=
    compositionAction_continuous left right hl hr
  exact ((paired _ _ ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
      source.clampedCoefficient_continuous) continuous_const).add
    (paired _ _ continuous_const source.clampedCoefficient_continuous)).add
      (continuous_finsetSum Finset.univ fun j _ => paired _ _
        ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
          (source.chartJump_continuous j.val)) (source.chartJump_continuous j.val))

def reflect (time : ℝ) : ℝ := source.left + source.right - time

theorem reflect_reflect (time : ℝ) : reflect source (reflect source time) = time := by
  unfold reflect
  ring

theorem reflect_inside (time : ℝ) (inside : time ∈ Icc source.left source.right) :
    reflect source time ∈ Icc source.left source.right := by
  unfold reflect
  constructor <;> linarith [inside.1,inside.2]

def rawCoflow (time : ℝ) : EffectAction (E := E) :=
  SourceTerminalBanachFlow303.terminalOperatorFlow (B := Operator (E := E))
    (heisenberg source hidden) (heisenberg_continuous source hidden)
    source.left source.right source.ordered time

theorem rawCoflow_terminal : rawCoflow source hidden source.right = 1 :=
  SourceTerminalBanachFlow303.terminalOperatorFlow_terminal (B := Operator (E := E))
    (heisenberg source hidden) (heisenberg_continuous source hidden)
    source.left source.right source.ordered

theorem rawCoflow_derivative (time : ℝ) (inside : time ∈ Icc source.left source.right) :
    HasDerivWithinAt (rawCoflow source hidden)
      (-((heisenberg source hidden time).comp (rawCoflow source hidden time)))
      (Icc source.left source.right) time :=
  SourceTerminalBanachFlow303.terminalOperatorFlow_derivative (B := Operator (E := E))
    (heisenberg source hidden) (heisenberg_continuous source hidden)
    source.left source.right source.ordered time inside

theorem rawCoflow_continuousOn :
    ContinuousOn (rawCoflow source hidden) (Icc source.left source.right) :=
  SourceTerminalBanachFlow303.terminalOperatorFlow_continuousOn (B := Operator (E := E))
    (heisenberg source hidden) (heisenberg_continuous source hidden)
    source.left source.right source.ordered

/-- Clamping only supplies a continuous extension; it does not change a source time. -/
def coflow (A : Operator (E := E)) (time : ℝ) : Operator (E := E) :=
  rawCoflow source hidden (source.timeProjection time) A

theorem coflow_original (A : Operator (E := E)) (time : ℝ)
    (inside : time ∈ Icc source.left source.right) :
    coflow source hidden A time = rawCoflow source hidden time A := by
  simp only [coflow, RawKrausWindow.timeProjection, projIcc_of_mem source.ordered inside]

theorem coflow_continuous (A : Operator (E := E)) : Continuous (coflow source hidden A) :=
  (((ContinuousLinearMap.apply ℂ (Operator (E := E)) A).continuous.comp_continuousOn
    (rawCoflow_continuousOn source hidden)).comp_continuous
      (continuous_subtype_val.comp (continuous_projIcc (h := source.ordered))))
        (fun time => (source.timeProjection time).property)

theorem coflow_terminal (A : Operator (E := E)) : coflow source hidden A source.right = A := by
  rw [coflow_original source hidden A source.right (right_mem_Icc.mpr source.ordered),
    rawCoflow_terminal]
  rfl

theorem coflow_derivative (A : Operator (E := E)) (time : ℝ)
    (inside : time ∈ Icc source.left source.right) :
    HasDerivWithinAt (coflow source hidden A)
      (-(heisenberg source hidden time (coflow source hidden A time)))
      (Icc source.left source.right) time := by
  have applied := SourceTerminalBanachFlow303.applied_terminal_flow_derivative
    (B := Operator (E := E)) (heisenberg source hidden) (heisenberg_continuous source hidden)
    source.left source.right source.ordered A time inside
  change HasDerivWithinAt (fun r => rawCoflow source hidden r A)
    (-(heisenberg source hidden time (rawCoflow source hidden time A)))
    (Icc source.left source.right) time at applied
  have same := applied.congr (fun t ht => coflow_original source hidden A t ht)
    (coflow_original source hidden A time inside)
  simpa only [← coflow_original source hidden A time inside] using same

private theorem chartPropagator_original (s r : ℝ)
    (hs : s ∈ Icc source.left source.right) (hr : r ∈ Icc source.left source.right) :
    source.chartPropagator s r = source.propagate s r := by
  simp only [RawKrausWindow.chartPropagator, RawKrausWindow.timeProjection,
    projIcc_of_mem source.ordered hs, projIcc_of_mem source.ordered hr]

omit [CompleteSpace E] [Nontrivial E] in
private theorem ext_matrixElement (A B : Operator (E := E))
    (same : ∀ x, matrixElement x x A = matrixElement x x B) : A = B := by
  have written : A.toLinearMap = B.toLinearMap :=
    (ext_inner_map A.toLinearMap B.toLinearMap).mp (fun x => by
      change inner ℂ (A x) x = inner ℂ (B x) x
      have polarized := congrArg (starRingEnd ℂ) (same x)
      change (starRingEnd ℂ) (inner ℂ x (A x)) =
        (starRingEnd ℂ) (inner ℂ x (B x)) at polarized
      calc
        inner ℂ (A x) x = (starRingEnd ℂ) (inner ℂ x (A x)) :=
          (inner_conj_symm (𝕜 := ℂ) (A x) x).symm
        _ = (starRingEnd ℂ) (inner ℂ x (B x)) := polarized
        _ = inner ℂ (B x) x := inner_conj_symm (𝕜 := ℂ) (B x) x)
  ext x
  exact congrArg (fun T : E →ₗ[ℂ] E => T x) written

/-- The backward equation itself generates the Volterra identity for arbitrary A. -/
theorem coflow_volterra (A : Operator (E := E)) (s : ℝ)
    (inside : s ∈ Icc source.left source.right) :
    coflow source hidden A s = endpointSeed source A s +
      SourceEndpointWords300.advance source hidden (coflow source hidden A) s := by
  apply ext_matrixElement
  intro x
  let u : ℝ → E := fun r => source.propagate s r x
  let B : ℝ → Operator (E := E) := coflow source hidden A
  let F : ℝ → ℂ := fun r => inner ℂ (u r) (B r (u r))
  have included : Icc s source.right ⊆ Icc source.left source.right :=
    Icc_subset_Icc inside.1 le_rfl
  have du (r : ℝ) (hr : r ∈ Icc s source.right) :
      HasDerivWithinAt u (source.clampedCoefficient r (u r)) (Icc s source.right) r :=
    (source.propagate_derivative s x r (included hr)).mono included
  have dB (r : ℝ) (hr : r ∈ Icc s source.right) :
      HasDerivWithinAt B (-(heisenberg source hidden r (B r))) (Icc s source.right) r :=
    (coflow_derivative source hidden A r (included hr)).mono included
  have Fcontinuous : ContinuousOn F (Icc s source.right) := by
    have uc : ContinuousOn u (Icc s source.right) := fun r hr => (du r hr).continuousWithinAt
    exact uc.inner (𝕜 := ℂ) ((coflow_continuous source hidden A).continuousOn.clm_apply uc)
  have first (r : ℝ) (hr : r ∈ Icc s source.right) :
      source.chartPropagator s r = source.propagate s r :=
    chartPropagator_original source s r inside (included hr)
  have derivative (r : ℝ) (hr : r ∈ Ioo s source.right) :
      HasDerivAt F
        (-matrixElement x x (SourceEndpointWords300.insertion source hidden B s r)) r := by
    have closed : r ∈ Icc s source.right := Ioo_subset_Icc_self hr
    have applied : HasDerivWithinAt (fun time => B time (u time))
        ((-(heisenberg source hidden r (B r))) (u r) +
          B r (source.clampedCoefficient r (u r))) (Icc s source.right) r :=
      ContinuousLinearMap.hasDerivWithinAt_of_bilinear
        (B := (ContinuousLinearMap.apply ℂ E).bilinearRestrictScalars ℝ)
        (du r closed) (dB r closed)
    have product := (du r closed).inner ℂ applied
    apply (product.congr_deriv ?_).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
    simp only [heisenberg_apply, neg_apply, add_apply,
      sum_apply, mul_apply_eq_comp, inner_add_right, inner_neg_right,
      inner_sum, ContinuousLinearMap.adjoint_inner_right,
      matrixElement, innerSL_apply_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      SourceEndpointWords300.insertion, map_sum, firstBranch, first r closed, u]
    abel
  have integrable : IntervalIntegrable (fun r =>
      -matrixElement x x (SourceEndpointWords300.insertion source hidden B s r))
      volume s source.right :=
    ((matrixElement x x).continuous.comp
      ((SourceEndpointWords300.insertion_continuous source hidden B
        (coflow_continuous source hidden A)).comp
          (continuous_const.prodMk continuous_id))).neg.intervalIntegrable _ _
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.2
    Fcontinuous derivative integrable
  have atStart : F s = matrixElement x x (coflow source hidden A s) := by
    dsimp [F,u,B,matrixElement]
    rw [source.propagate_initial s inside]
    rfl
  have atEnd : F source.right = matrixElement x x (endpointSeed source A s) := by
    dsimp [F,u,B,matrixElement]
    rw [coflow_terminal, endpointSeed,
      chartPropagator_original source s source.right inside (right_mem_Icc.mpr source.ordered)]
    exact (ContinuousLinearMap.adjoint_inner_right (source.propagate s source.right)
      x (A (source.propagate s source.right x))).symm
  have insertionIntegral :
      (∫ r in s..source.right,
        matrixElement x x (SourceEndpointWords300.insertion source hidden B s r)) =
        matrixElement x x (SourceEndpointWords300.advance source hidden B s) :=
    (matrixElement x x).intervalIntegral_comp_comm
      (((SourceEndpointWords300.insertion_continuous source hidden B
        (coflow_continuous source hidden A)).comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg, insertionIntegral, atEnd, atStart] at paid
  rw [map_add]
  have combined := eq_sub_iff_add_eq.mp paid
  calc
    _ = (-matrixElement x x (SourceEndpointWords300.advance source hidden B s) +
          matrixElement x x (coflow source hidden A s)) +
        matrixElement x x (SourceEndpointWords300.advance source hidden B s) := by abel
    _ = _ := congrArg (fun value : ℂ =>
      value + matrixElement x x (SourceEndpointWords300.advance source hidden B s)) combined

theorem endpointWord_tail_difference (A : Operator (E := E)) (n : ℕ) (s : ℝ)
    (inside : s ∈ Icc source.left source.right) :
    endpointWord source hidden A n s =
      SourceEndpointWords300.iterate source hidden (coflow source hidden A) n s -
        SourceEndpointWords300.iterate source hidden (coflow source hidden A) (n+1) s := by
  induction n generalizing s with
  | zero =>
    change endpointSeed source A s = coflow source hidden A s -
      SourceEndpointWords300.advance source hidden (coflow source hidden A) s
    exact eq_sub_iff_add_eq.mpr (coflow_volterra source hidden A s inside).symm
  | succ n ih =>
    change SourceEndpointWords300.advance source hidden (endpointWord source hidden A n) s =
      SourceEndpointWords300.advance source hidden
        (SourceEndpointWords300.iterate source hidden (coflow source hidden A) n) s -
      SourceEndpointWords300.advance source hidden
        (SourceEndpointWords300.iterate source hidden (coflow source hidden A) (n+1)) s
    rw [← SourceEndpointWords300.advance_sub source hidden _ _
      (iterate_continuous source hidden _ (coflow_continuous source hidden A) n)
      (iterate_continuous source hidden _ (coflow_continuous source hidden A) (n+1))]
    exact SourceEndpointWords300.advance_congr source hidden _ _ (fun r hr => ih r hr) s inside

theorem finite_endpoint_balance (A : Operator (E := E)) (n : ℕ) (s : ℝ)
    (inside : s ∈ Icc source.left source.right) :
    (∑ k ∈ Finset.range n, endpointWord source hidden A k s) +
      SourceEndpointWords300.iterate source hidden (coflow source hidden A) n s =
        coflow source hidden A s := by
  induction n with
  | zero => simp [SourceEndpointWords300.iterate]
  | succ n ih =>
    rw [Finset.sum_range_succ, endpointWord_tail_difference source hidden A n s inside,
      add_assoc, sub_add_cancel]
    exact ih

private theorem endpointSeed_norm (A : Operator (E := E)) (s : ℝ)
    (inside : s ∈ Icc source.left source.right) : ‖endpointSeed source A s‖ ≤ ‖A‖ := by
  rw [endpointSeed, chartPropagator_original source s source.right inside
    (right_mem_Icc.mpr source.ordered)]
  have bounded := propagate_opNorm_le_one source s source.right inside.1 inside.2 le_rfl
  calc
    _ ≤ (‖(source.propagate s source.right).adjoint‖ * ‖A‖) *
        ‖source.propagate s source.right‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = (‖source.propagate s source.right‖ * ‖A‖) * ‖source.propagate s source.right‖ := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ (1 * ‖A‖) * 1 := by gcongr
    _ = _ := by ring

theorem endpointWord_norm_summable (A : Operator (E := E)) (s : ℝ)
    (inside : s ∈ Icc source.left source.right) :
    Summable (fun n => ‖endpointWord source hidden A n s‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_) ((Real.summable_pow_div_factorial
      (activity source hidden * (source.right-s))).mul_left ‖A‖)
  simpa only [endpointWord, mul_pow, mul_assoc, mul_div_assoc] using
    iterate_norm source hidden (endpointSeed source A) ‖A‖
      (endpointSeed_norm source A) n s inside

/-- The source factorial tail closes the whole operator-valued observable series. -/
theorem endpointWord_hasSum_coflow (A : Operator (E := E)) (s : ℝ)
    (inside : s ∈ Icc source.left source.right) :
    HasSum (fun n => endpointWord source hidden A n s) (coflow source hidden A s) := by
  obtain ⟨peak,_,maximal⟩ := isCompact_Icc.exists_isMaxOn
    ⟨source.left,left_mem_Icc.mpr source.ordered⟩ (coflow_continuous source hidden A).norm.continuousOn
  have bound : ∀ r ∈ Icc source.left source.right,
      ‖coflow source hidden A r‖ ≤ ‖coflow source hidden A peak‖ := maximal
  have tail := iterate_tendsto_zero source hidden (coflow source hidden A)
    ‖coflow source hidden A peak‖ bound s inside
  apply (hasSum_iff_tendsto_nat_of_summable_norm
    (endpointWord_norm_summable source hidden A s inside)).mpr
  have limit : Tendsto (fun n => coflow source hidden A s -
      SourceEndpointWords300.iterate source hidden (coflow source hidden A) n s)
      atTop (𝓝 (coflow source hidden A s)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub tail
  apply limit.congr'
  exact Filter.Eventually.of_forall fun n =>
    (eq_sub_iff_add_eq.mpr (finite_endpoint_balance source hidden A n s inside)).symm

section ActualSourceTrace

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- This is an equality of the291 source compression and the generated recycling IVP. -/
theorem endpointEffect_eq_coflow (A : Operator (E := E)) (s : ℝ)
    (inside : s ∈ Icc source.left source.right) :
    endpointEffect source hidden s inside A = coflow source hidden A s := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  exact ((matrixElement x y).hasSum (endpointWord_hasSum_coflow source hidden A s inside)).unique
    (endpointWord_pairing_hasSum source hidden s inside A x y) |>.symm

def completeObservable (A : Operator (E := E)) (time : ℝ) : Operator (E := E) :=
  endpointEffect source hidden (source.timeProjection time) (source.timeProjection time).property A

theorem completeObservable_eq_coflow (A : Operator (E := E)) :
    completeObservable source hidden A = coflow source hidden A := by
  funext time
  rw [completeObservable, endpointEffect_eq_coflow]
  change coflow source hidden A (source.timeProjection time) =
    rawCoflow source hidden (source.timeProjection time) A
  exact coflow_original source hidden A (source.timeProjection time)
    (source.timeProjection time).property

theorem completeObservable_terminal (A : Operator (E := E)) :
    completeObservable source hidden A source.right = A := by
  rw [completeObservable_eq_coflow, coflow_terminal]

theorem completeObservable_derivative (A : Operator (E := E)) (time : ℝ)
    (inside : time ∈ Icc source.left source.right) :
    HasDerivWithinAt (completeObservable source hidden A)
      (-(heisenberg source hidden time (completeObservable source hidden A time)))
      (Icc source.left source.right) time := by
  rw [completeObservable_eq_coflow]
  exact coflow_derivative source hidden A time inside

/-- The completed Born observable obeys the original selected raw recycling equation. -/
theorem completeObservable_raw_recycling (A : Operator (E := E)) (time : ℝ)
    (inside : time ∈ Icc source.left source.right) :
    HasDerivWithinAt (completeObservable source hidden A)
      (-((source.coefficient time).adjoint * completeObservable source hidden A time +
        completeObservable source hidden A time * source.coefficient time +
          ∑ j : Letters hidden, (source.jumps time j.val).adjoint *
            completeObservable source hidden A time * source.jumps time j.val))
      (Icc source.left source.right) time := by
  have actual := completeObservable_derivative source hidden A time inside
  rw [heisenberg_apply, source.clampedCoefficient_original time inside] at actual
  simpa only [RawKrausWindow.chartJump, RawKrausWindow.timeProjection,
    projIcc_of_mem source.ordered inside] using actual

end ActualSourceTrace
end SourceEndpointRecycling300
