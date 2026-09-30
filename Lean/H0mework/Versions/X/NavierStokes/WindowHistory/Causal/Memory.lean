import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Flow
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.Resolvent

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalMean
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H action forcingHistory)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryMeanAction (creation meanOperator)
open NativeWindowHistoryMeanBlocks (bath annihilation)
open NativeWindowHistoryCausalBath (kernel dual)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}
local notation "Q" => NativeWindowHistoryMeanProjection.residual

def residual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  Q (finiteHistory seed time M)

def input (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  creation seed M time (mean (finiteHistory seed time M))+Q (forcingHistory seed M time)

private theorem derivative_reordered {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b c d : E} {time : ℝ} (evolves : HasDerivAt f (a+b+c) time)
    (same : b=d) : HasDerivAt f (d+(a+c)) time := by
  have rate : a+b+c=d+(a+c) := by rw [same]; abel
  exact evolves.congr_deriv rate

theorem source_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (residual seed M)
      (bath seed M time (residual seed M time)+input seed M time) time := by
  simpa only [residual,input] using! derivative_reordered (E := H)
    (NativeWindowHistoryMeanBlocks.source_residual_derivative seed M time)
    (NativeWindowHistoryBathResolvent.bath_residual seed M time (finiteHistory seed time M)).symm

private theorem creation_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    Continuous (creation seed M) :=
  Continuous.clm_comp (𝕜 := ℝ) (E := NativeWholeResolvent.wholePhysical) (F := H) (G := H) continuous_const
    (Continuous.clm_comp (𝕜 := ℝ) (E := NativeWholeResolvent.wholePhysical) (F := H) (G := H)
      (NativeWindowHistoryOseen.action_continuous seed M) continuous_const)

theorem input_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    IntervalIntegrable (input seed M) volume a b := by
  have history : Continuous (fun t => finiteHistory seed t M) := NativeWindowHistoryOseen.history_continuous seed M
  have formed : Continuous (fun t => creation seed M t (mean (finiteHistory seed t M))) :=
    Continuous.clm_apply (𝕜 := ℝ) (E := NativeWholeResolvent.wholePhysical) (F := H)
      (creation_continuous seed M) (mean.continuous.comp history)
  have forced := NativeWindowHistoryOseen.forcingHistory_integrable seed M a b
  have mapped : IntervalIntegrable (fun t => Q (forcingHistory seed M t)) volume a b :=
    ⟨by simpa only [] using! (Q).integrable_comp (H := H) (E := H) (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ) forced.1,
      by simpa only [] using! (Q).integrable_comp (H := H) (E := H) (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ) forced.2⟩
  exact (formed.intervalIntegrable a b).add mapped

private theorem inner_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f p : ℝ → E) (a b : ℝ) (ab : a ≤ b)
    (integrable : IntervalIntegrable f volume a b) (continuous : ContinuousOn p (Icc a b)) :
    IntervalIntegrable (fun t => inner ℝ (f t) (p t)) volume a b := by
  obtain ⟨C,bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn continuous
  have first := (intervalIntegrable_iff_integrableOn_Icc_of_le ab).mp integrable
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le ab).mpr
  refine (first.norm.mul_const C).mono' (first.aestronglyMeasurable.inner
    (continuous.aestronglyMeasurable measurableSet_Icc)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (norm_inner_le_norm (f t) (p t)).trans
    (mul_le_mul_of_nonneg_left (bounded t ht) (norm_nonneg _))

private theorem green_write {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A D : ℝ → E → E)
    (dual : ∀ t u v,inner ℝ (A t u) v=inner ℝ u (D t v))
    (x p f : ℝ → E) (a b : ℝ) (ab : a ≤ b)
    (dx : ∀ t∈Icc a b,HasDerivWithinAt x (A t (x t)+f t) (Icc a b) t)
    (dp : ∀ t∈Icc a b,HasDerivWithinAt p (-D t (p t)) (Icc a b) t)
    (integrable : IntervalIntegrable f volume a b) :
    inner ℝ (x b) (p b)-inner ℝ (x a) (p a)=∫ t in a..b,inner ℝ (f t) (p t) := by
  have xc : ContinuousOn x (Icc a b) := fun t ht => (dx t ht).continuousWithinAt
  have pc : ContinuousOn p (Icc a b) := fun t ht => (dp t ht).continuousWithinAt
  have derivative (t : ℝ) (ht : t∈Ioo a b) :
      HasDerivAt (fun s => inner ℝ (x s) (p s)) (inner ℝ (f t) (p t)) t := by
    have first := (dx t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have last := (dp t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    convert! first.inner ℝ last using 1
    rw [inner_neg_right,inner_add_left,dual]
    ring
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ab (xc.inner (𝕜 := ℝ) pc)
    derivative (inner_integrable f p a b ab integrable pc)).symm

theorem source_green (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (inside : b∈Icc a B) (terminal : H) :
    inner ℝ (residual seed M b) terminal-
      inner ℝ (residual seed M a) (kernel seed M a B aB a b terminal)=
        ∫ t in a..b,inner ℝ (input seed M t) (kernel seed M a B aB t b terminal) := by
  have subset : Icc a b ⊆ Icc a B := Icc_subset_Icc le_rfl inside.2
  have dx (t : ℝ) (_ht : t∈Icc a b) : HasDerivWithinAt (residual seed M)
      (bath seed M t (residual seed M t)+input seed M t) (Icc a b) t := by
    simpa only [] using! (source_derivative seed M t).hasDerivWithinAt (s := Icc a b)
  have dp (t : ℝ) (ht : t∈Icc a b) :
      HasDerivWithinAt (fun s => kernel seed M a B aB s b terminal)
        (-dual seed M t (kernel seed M a B aB t b terminal)) (Icc a b) t := by
    exact (NativeWindowHistoryCausalBath.kernel_derivative seed M a B aB b terminal t (subset ht)).mono subset
  have written := green_write (E := H) (fun t v => bath seed M t v) (fun t v => dual seed M t v)
    (NativeWindowHistoryCausalBath.bath_dual seed M) (residual seed M)
    (fun t => kernel seed M a B aB t b terminal) (input seed M) a b inside.1
    dx dp (input_integrable seed M a b)
  simpa only [NativeWindowHistoryCausalBath.kernel_terminal seed M a B aB b inside terminal] using! written

def memory (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (u : NativeWholeResolvent.wholePhysical) : ℝ :=
  ∫ t in a..b,inner ℝ (input seed M t)
    (kernel seed M a B aB t b (creation seed M b u))

theorem memory_decomposition (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (b : ℝ) (inside : b∈Icc a B)
    (u : NativeWholeResolvent.wholePhysical) :
    memory seed M a B aB b u=
      (∫ t in a..b,inner ℝ (creation seed M t (mean (finiteHistory seed t M)))
        (kernel seed M a B aB t b (creation seed M b u)))+
      ∫ t in a..b,inner ℝ (Q (forcingHistory seed M t))
        (kernel seed M a B aB t b (creation seed M b u)) := by
  let p := fun t => kernel seed M a B aB t b (creation seed M b u)
  have pc : ContinuousOn p (Icc a b) := fun t ht =>
    (NativeWindowHistoryCausalBath.kernel_derivative seed M a B aB b (creation seed M b u) t
      ⟨ht.1,ht.2.trans inside.2⟩).continuousWithinAt.mono (Icc_subset_Icc le_rfl inside.2)
  have formed : Continuous (fun t => creation seed M t (mean (finiteHistory seed t M))) :=
    Continuous.clm_apply (𝕜 := ℝ) (E := NativeWholeResolvent.wholePhysical) (F := H)
      (creation_continuous seed M) (mean.continuous.comp (NativeWindowHistoryOseen.history_continuous seed M))
  have forced := NativeWindowHistoryOseen.forcingHistory_integrable seed M a b
  have mapped : IntervalIntegrable (fun t => Q (forcingHistory seed M t)) volume a b :=
    ⟨by simpa only [] using! (Q).integrable_comp (H := H) (E := H) (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ) forced.1,
      by simpa only [] using! (Q).integrable_comp (H := H) (E := H) (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ) forced.2⟩
  have first := inner_integrable (E := H) _ p a b inside.1 (formed.intervalIntegrable a b) pc
  have last := inner_integrable (E := H) _ p a b inside.1 mapped pc
  unfold memory input
  calc
    _ = ∫ t in a..b,(inner ℝ (creation seed M t (mean (finiteHistory seed t M))) (p t)+
        inner ℝ (Q (forcingHistory seed M t)) (p t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact inner_add_left (𝕜 := ℝ) (E := H) _ _ _
    _ = _ := intervalIntegral.integral_add first last

theorem source_annihilation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (inside : b∈Icc a B)
    (u : NativeWholeResolvent.wholePhysical) :
    inner ℝ u (annihilation seed M b (finiteHistory seed b M))=
      -inner ℝ (residual seed M a) (kernel seed M a B aB a b (creation seed M b u))-
        memory seed M a B aB b u := by
  have written := source_green seed M a B aB b inside (creation seed M b u)
  have coupling := NativeWindowHistoryMeanBlocks.coupling_green seed M b u (residual seed M b)
  have centered : annihilation seed M b (residual seed M b)=annihilation seed M b (finiteHistory seed b M) := by
    simp only [annihilation,residual,ContinuousLinearMap.comp_apply,NativeWindowHistoryBathResolvent.residual_square]
  have centeredRead:=congrArg (fun v : NativeWholeResolvent.wholePhysical => inner ℝ u v) centered
  have paired:=congrArg₂ (fun x y : ℝ => x+y) centeredRead
    (real_inner_comm (creation seed M b u) (residual seed M b)).symm
  have coupled:=paired.symm.trans coupling
  change _=memory seed M a B aB b u at written
  linarith only [coupled,written]

theorem source_memory_law (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (inside : b∈Icc a B)
    (u : NativeWholeResolvent.wholePhysical) :
    inner ℝ u (deriv (fun t => mean (finiteHistory seed t M)) b)=
      inner ℝ u (meanOperator seed M b (mean (finiteHistory seed b M))+mean (forcingHistory seed M b))-
      inner ℝ (residual seed M a) (kernel seed M a B aB a b (creation seed M b u))-
        memory seed M a B aB b u := by
  rw [(NativeWindowHistoryMeanBlocks.source_mean_derivative seed M b).deriv]
  simp only [inner_add_right]
  linarith only [source_annihilation seed M a B aB b inside u]

theorem prepared_memory (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (B : ℝ) (horizon : -2≤B) (b : ℝ) (inside : b∈Icc (-2) B)
    (u : NativeWholeResolvent.wholePhysical) :
    inner ℝ u (annihilation seed M b (finiteHistory seed b M))=
      -memory seed M (-2) B horizon b u := by
  have actual := source_annihilation seed M (-2) B horizon b inside u
  have prepared : residual seed M (-2)=0 := NativeWindowHistoryMeanBlocks.source_initial seed M
  have zero : inner ℝ (residual seed M (-2))
      (kernel seed M (-2) B horizon (-2) b (creation seed M b u))=0 := by
    rw [prepared]
    exact inner_zero_left (𝕜 := ℝ) (E := H) _
  rw [zero,neg_zero,zero_sub] at actual
  exact actual


open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem residual_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0≤time) :
    residual seed M (step.2.clockAdvance+time)=residual step.1 M time :=
  congrArg Q (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M)

theorem input_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0≤time) :
    input seed M (step.2.clockAdvance+time)=input step.1 M time := by
  have created:=congrArg₂ (fun (A : NativeWholeResolvent.wholePhysical →L[ℝ] H) (v : H) => A (mean v))
    (NativeWindowHistoryMeanBlocks.creation_next seed M step generated time nonnegative)
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M)
  have forced:=congrArg Q (NativeWindowHistoryOseen.forcingHistory_next seed M step generated time nonnegative)
  exact congrArg₂ (fun x y : H => x+y) created forced

theorem memory_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (b : ℝ) (inside : b∈Icc a B)
    (u : NativeWholeResolvent.wholePhysical) :
    memory seed M (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+b) u = memory step.1 M a B aB b u := by
  unfold memory
  rw [← intervalIntegral.integral_comp_add_left _ step.2.clockAdvance]
  apply intervalIntegral.integral_congr
  intro t ht
  have sample : t∈Icc a b := by simpa only [uIcc_of_le inside.1] using ht
  have force:=input_next seed M step generated t (a0.trans sample.1)
  have source:=congrArg (fun A : NativeWholeResolvent.wholePhysical →L[ℝ] H => A u)
    (NativeWindowHistoryMeanBlocks.creation_next seed M step generated b (a0.trans inside.1))
  have moved:=congrArg₂ (fun (A : H →L[ℝ] H) (v : H) => A v)
    (NativeWindowHistoryCausalBath.kernel_next seed M step generated a B aB a0 b inside t sample) source
  exact congrArg₂ (inner ℝ) force moved

theorem source_mean_rate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0≤time) :
    deriv (fun t => mean (finiteHistory seed t M)) (step.2.clockAdvance+time) =
      deriv (fun t => mean (finiteHistory step.1 t M)) time := by
  have blocks:=NativeWindowHistoryMeanBlocks.blocks_next seed M step generated time nonnegative
  have state:=NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M
  have drift:=congrArg₂ (fun (A : NativeWholeResolvent.wholePhysical →L[ℝ] NativeWholeResolvent.wholePhysical)
      (v : H) => A (mean v)) (congrArg Prod.fst blocks) state
  have feedback:=congrArg₂ (fun (A : H →L[ℝ] NativeWholeResolvent.wholePhysical) (v : H) => A v)
    (congrArg (fun blocks => blocks.2.2.1) blocks) state
  have forcing:=congrArg mean (NativeWindowHistoryOseen.forcingHistory_next seed M step generated time nonnegative)
  have total:=congrArg₂ (fun x y : NativeWholeResolvent.wholePhysical => x+y)
    (congrArg₂ (fun x y : NativeWholeResolvent.wholePhysical => x+y) drift feedback) forcing
  exact (NativeWindowHistoryMeanBlocks.source_mean_derivative seed M (step.2.clockAdvance+time)).deriv.trans
    (total.trans (NativeWindowHistoryMeanBlocks.source_mean_derivative step.1 M time).deriv.symm)

/-- The actual old-clock mean derivative is consumed by the same newly generated memory law. -/
theorem source_memory_law_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (b : ℝ) (inside : b∈Icc a B)
    (u : NativeWholeResolvent.wholePhysical) :
    inner ℝ u (deriv (fun t => mean (finiteHistory seed t M)) (step.2.clockAdvance+b)) =
      inner ℝ u (meanOperator step.1 M b (mean (finiteHistory step.1 b M))+mean (forcingHistory step.1 M b))-
        inner ℝ (residual step.1 M a) (kernel step.1 M a B aB a b (creation step.1 M b u))-
          memory step.1 M a B aB b u := by
  exact (congrArg (fun v : NativeWholeResolvent.wholePhysical => inner ℝ u v)
    (source_mean_rate_next seed M step generated b (a0.trans inside.1))).trans
      (source_memory_law step.1 M a B aB b inside u)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalMean
