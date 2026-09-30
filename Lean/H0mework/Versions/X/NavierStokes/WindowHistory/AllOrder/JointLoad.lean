import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.JointControl
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.CreatedLoadBudget

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderJointLoad
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H gradient)
open NativeWindowHistorySpatialWords (history)
open NativeWindowHistoryAllOrderWord (value)
open NativeWindowHistoryAllOrderCausal (created remaining load)
open NativeWindowHistoryAllOrderJointEnergy (energy mixedLoad)
open NativeWindowHistoryAllOrderCreatedLoadBudget (history_continuous load_integrable)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

private theorem inner_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f p : ℝ → E) (a b : ℝ) (ab : a ≤ b) (fi : IntervalIntegrable f volume a b) (pc : ContinuousOn p (Icc a b)) :
    IntervalIntegrable (fun t => inner ℝ (p t) (f t)) volume a b := by
  obtain ⟨C,bounded⟩:=isCompact_Icc.exists_bound_of_continuousOn pc
  have first:=(intervalIntegrable_iff_integrableOn_Icc_of_le ab).mp fi
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le ab).mpr
  refine (first.norm.const_mul C).mono' (pc.aestronglyMeasurable measurableSet_Icc |>.inner first.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (mul_le_mul_of_nonneg_right (bounded t ht) (norm_nonneg _))

theorem energy_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) : ContinuousOn (energy seed M word a B aB) (Icc a B) := fun t ht =>
  (NativeWindowHistoryAllOrderJointEnergy.source_derivative seed M word a B aB t ht).continuousWithinAt

theorem created_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) : ContinuousOn (created seed M word a B aB) (Icc a B) := fun t ht =>
  (NativeWindowHistoryAllOrderCausal.created_derivative seed M word a B aB t ht).continuousWithinAt

theorem mixed_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (inside : b∈Icc a B) :
    (∫t in a..b,mixedLoad seed M word a B aB t)=
      (∫t in a..b,2*inner ℝ (history seed M word t) (load seed M word t))-
        ∫t in a..b,2*inner ℝ (created seed M word a B aB t) (load seed M word t) := by
  have subset:Icc a b ⊆ Icc a B:=Icc_subset_Icc le_rfl inside.2
  have x:= (inner_integrable (E := H) (load seed M word) (history seed M word) a b inside.1
    (load_integrable seed M word a b) (history_continuous seed M word).continuousOn).const_mul 2
  have y:= (inner_integrable (E := H) (load seed M word) (created seed M word a B aB) a b inside.1
    (load_integrable seed M word a b) ((created_continuous seed M word a B aB).mono subset)).const_mul 2
  rw [← intervalIntegral.integral_sub x y]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le inside.1] at ht
  rw [NativeWindowHistoryAllOrderJointEnergy.mixedLoad_original seed M word a B aB t (subset ht)]
  have split : inner ℝ (history seed M word t-created seed M word a B aB t) (load seed M word t)=
      inner ℝ (history seed M word t) (load seed M word t)-inner ℝ (created seed M word a B aB t) (load seed M word t) := by
    simpa only [] using! (inner_sub_left (𝕜 := ℝ) (E := H) (history seed M word t)
      (created seed M word a B aB t) (load seed M word t))
  rw [split]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem source_integral (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M (word : List Coordinate) (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
    energy seed M word a horizon start.2 b+
      (nu.coeff/2)*(∫t in a..b,gradient M (history seed M word t))≤
        energy seed M word a horizon start.2 a+C*(∫t in a..b,energy seed M word a horizon start.2 t)+
          ∫t in a..b,mixedLoad seed M word a horizon start.2 t := by
  obtain ⟨C,C0,paid⟩:=NativeWindowHistoryAllOrderJointControl.source_generator seed horizon
  refine ⟨C,C0,fun M word a start b inside => ?_⟩
  let E:=energy seed M word a horizon start.2
  let g:=fun t => gradient M (history seed M word t)
  let L:=mixedLoad seed M word a horizon start.2
  have subset:Icc a b ⊆ Icc a horizon:=Icc_subset_Icc le_rfl inside.2
  have ec:ContinuousOn E (Icc a b):=(energy_continuous seed M word a horizon start.2).mono subset
  have ei:=ec.intervalIntegrable_of_Icc (μ := volume) inside.1
  have gi : IntervalIntegrable g volume a b:=
    ((NativeWindowHistoryCausalDissipation.gradient_continuous nu M).comp (history_continuous seed M word)).intervalIntegrable a b
  have yc:=((history_continuous seed M word).continuousOn (s := Icc a b)).sub
    ((created_continuous seed M word a horizon start.2).mono subset)
  have li:IntervalIntegrable L volume a b :=
    ((inner_integrable (E := H) (load seed M word) (fun t=>history seed M word t-created seed M word a horizon start.2 t)
      a b inside.1 (load_integrable seed M word a b) yc).const_mul 2).congr (fun t ht => by
        rw [uIoc_of_le inside.1] at ht
        exact (NativeWindowHistoryAllOrderJointEnergy.mixedLoad_original seed M word a horizon start.2 t (subset ⟨ht.1.le,ht.2⟩)).symm)
  have integrable := ((ei.const_mul C).add li).sub (gi.const_mul (nu.coeff/2))
  have derivative (t : ℝ) (ht : t∈Ioo a b) : HasDerivAt E (deriv E t) t :=
    ((NativeWindowHistoryAllOrderJointEnergy.source_derivative seed M word a horizon start.2 t
      ⟨ht.1.le,ht.2.le.trans inside.2⟩).hasDerivAt (Icc_mem_nhds ht.1 (ht.2.trans_le inside.2))).differentiableAt.hasDerivAt
  have bound (t : ℝ) (ht : t∈Ioo a b) : deriv E t≤C*E t+L t-(nu.coeff/2)*g t := by
    have source:=paid M word a start t ⟨ht.1,ht.2.trans_le inside.2⟩
    linarith only [source]
  have integrated:=intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le inside.1 ec
    (fun t ht => (derivative t ht).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le inside.1).mp integrable) bound
  rw [intervalIntegral.integral_sub ((ei.const_mul C).add li) (gi.const_mul (nu.coeff/2)),
    intervalIntegral.integral_add (ei.const_mul C) li,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at integrated
  linarith only [integrated]


set_option backward.isDefEq.respectTransparency false in
theorem energy_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) : energy seed M word a B aB a=‖history seed M word a‖^2 := by
  have split:=NativeWindowHistoryMeanProjection.energy_split (history seed M word a)
  have meanRead:=NativeWindowHistoryAllOrderWord.value_original seed M word a
  rw [energy,NativeWindowHistoryAllOrderCausalEnergy.energy_initial]
  dsimp only [remaining]
  rw [NativeWindowHistoryAllOrderCausalEnergy.created_initial,sub_zero,meanRead]
  change ‖NativeWindowHistoryMeanProjection.mean (history seed M word a)‖^2+
    ‖NativeWindowHistoryMeanProjection.residual (history seed M word a)‖^2=_
  rw [split]
  change _=‖NativeWindowHistoryMeanProjection.embed (NativeWindowHistoryMeanProjection.mean (history seed M word a))‖^2+_
  exact congrArg (fun q : ℝ => q^2+‖NativeWindowHistoryMeanProjection.residual (history seed M word a)‖^2)
    (NativeWindowHistoryMeanProjection.embed_norm (NativeWindowHistoryMeanProjection.mean (history seed M word a))).symm

set_option backward.isDefEq.respectTransparency false in
theorem source_first_word (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ C K : ℝ,0≤C ∧ 0≤K ∧ ∀ M (j : Coordinate) (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      energy seed M [j] a horizon start.2 b+
        (nu.coeff/4)*(∫t in a..b,gradient M (history seed M [j] t))≤
          C+K*(∫t in a..b,energy seed M [j] a horizon start.2 t)+
            ∫t in a..b,2*inner ℝ (history seed M [j] t) (load seed M [j] t) := by
  obtain ⟨K,K0,whole⟩:=source_integral seed horizon
  obtain ⟨C,C0,paid⟩:=NativeWindowHistoryAllOrderCreatedLoadBudget.source seed horizon (nu.coeff/4)
    nonnegative (by positivity [nu.coeff_pos])
  obtain ⟨X,X0,initial⟩:=NativeWindowHistoryAllOrderCreatedLoadBudget.first_history_bound seed horizon
  refine ⟨X+C,K,add_nonneg X0 C0,K0,fun M j a start b inside => ?_⟩
  have full:=whole M [j] a start b inside
  rw [mixed_write seed M [j] a horizon start.2 b inside,energy_initial] at full
  have createdPaid:=paid M j a start b inside
  have initialPaid:=initial M j a start
  have lower:=neg_abs_le (∫t in a..b,2*inner ℝ (created seed M [j] a horizon start.2 t) (load seed M [j] t))
  linarith only [full,createdPaid,initialPaid,lower]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderJointLoad
