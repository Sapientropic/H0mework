import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.FullStatisticalFiber.Trainingchart
import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.FullStatisticalFiber.Phaseconsumer

/-! Full single-error membership and joint phase slabs consume one original source. -/

set_option autoImplicit false

namespace P23.ObservableClosure.TrainingChart.Consumer

open PhaseFiber
open P23.ObservableClosure.Consumer

noncomputable section

structure FullTrainingMembership (raw : RawSource) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (a0 a1 : ℝ) (bounds : MeanIntervals)
    (lo0 hi0 lo1 hi1 : ℝ) : Prop where
  singles : SingleMembership (raw.withPhase lam h0 h1) a0 a1 bounds
  joints : TrainingQualified raw lam h0 h1 (mirror a0) (mirror a1) lo0 hi0 lo1 hi1

structure FullTrainingChart (raw : RawSource) (a0 a1 : ℝ) (bounds : MeanIntervals)
    (lo0 hi0 lo1 hi1 k : ℝ) : Prop where
  polytope : SourcePolytope raw.baseline a0 a1 bounds
  phase : PhaseQualified raw (mirror a0) (mirror a1) lo0 hi0 lo1 hi1 k

theorem phase_polytope_iff_baseline (raw : RawSource) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (a0 a1 : ℝ) (bounds : MeanIntervals) :
    SourcePolytope (raw.withPhase lam h0 h1) a0 a1 bounds ↔
      SourcePolytope raw.baseline a0 a1 bounds := by
  constructor <;> intro hp <;> exact ⟨hp.alpha0,hp.alpha1,hp.beta0,hp.beta1⟩

theorem full_training_iff_chart (raw : RawSource) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (a0 a1 : ℝ) (bounds : MeanIntervals)
    (lo0 hi0 lo1 hi1 : ℝ) :
    FullTrainingMembership raw lam h0 h1 a0 a1 bounds lo0 hi0 lo1 hi1 ↔
      FullTrainingChart raw a0 a1 bounds lo0 hi0 lo1 hi1
        (interference (raw.withPhase lam h0 h1)) := by
  constructor
  · intro hm
    have hp := (single_membership_iff_polytope _ a0 a1 bounds).1 hm.singles
    exact ⟨(phase_polytope_iff_baseline raw lam h0 h1 a0 a1 bounds).1 hp,
      (training_qualified_iff_phase raw lam h0 h1 _ _ _ _ _ _).1 hm.joints⟩
  · intro hc
    refine ⟨?_,(training_qualified_iff_phase raw lam h0 h1 _ _ _ _ _ _).2 hc.phase⟩
    apply (single_membership_iff_polytope _ a0 a1 bounds).2
    exact (phase_polytope_iff_baseline raw lam h0 h1 a0 a1 bounds).2 hc.polytope

def nativeWindow (raw : RawSource) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (cell : Cell) (bgA bgB : ℝ) : Outcomes :=
  generatedWindow (raw.withPhase lam h0 h1) cell bgA bgB

theorem original_window_phase_readback (raw : RawSource) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (cell : Cell) (bgA bgB : ℝ) :
    nativeWindow raw lam h0 h1 cell bgA bgB=
      PhaseFiber.Consumer.phaseWindow raw (interference (raw.withPhase lam h0 h1))
        cell bgA bgB := by
  unfold nativeWindow generatedWindow
  rw [with_phase_affine_readback]
  rfl

structure SourceChartReadout (raw : RawSource) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (a0 a1 : ℝ) (bounds : MeanIntervals) (lo0 hi0 lo1 hi1 bgA bgB : ℝ) : Prop where
  physical : PhysicalCovariance raw.baseline
  chart : FullTrainingChart raw a0 a1 bounds lo0 hi0 lo1 hi1
    (interference (raw.withPhase lam h0 h1))
  pulse : ∀ cell, pulse00 (raw.withPhase lam h0 h1) cell=
    affinePulse raw cell (interference (raw.withPhase lam h0 h1))
  window : ∀ cell, nativeWindow raw lam h0 h1 cell bgA bgB=
    PhaseFiber.Consumer.phaseWindow raw (interference (raw.withPhase lam h0 h1))
      cell bgA bgB

/-- Every full-training legal source generates its physical chart, shared phase and all windows. -/
theorem source_generates_full_training_chart (raw : RawSource) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (a0 a1 : ℝ) (bounds : MeanIntervals)
    (lo0 hi0 lo1 hi1 bgA bgB : ℝ)
    (hm : FullTrainingMembership raw lam h0 h1 a0 a1 bounds lo0 hi0 lo1 hi1) :
    SourceChartReadout raw lam h0 h1 a0 a1 bounds lo0 hi0 lo1 hi1 bgA bgB :=
  ⟨source_physical_covariance raw.baseline,
    (full_training_iff_chart raw lam h0 h1 a0 a1 bounds lo0 hi0 lo1 hi1).1 hm,
    fun cell => with_phase_affine_readback raw lam h0 h1 cell,
    fun cell => original_window_phase_readback raw lam h0 h1 cell bgA bgB⟩

/-- Conversely the complete chart generates a legal source without a supplied source endpoint. -/
theorem chart_generates_full_training_source (raw : RawSource) (a0 a1 : ℝ)
    (bounds : MeanIntervals) (lo0 hi0 lo1 hi1 k : ℝ)
    (hc : FullTrainingChart raw a0 a1 bounds lo0 hi0 lo1 hi1 k) :
    FullTrainingMembership raw (phaseRecipe raw k)
      (phase_recipe_bounds raw k hc.phase.physical).1
      (phase_recipe_bounds raw k hc.phase.physical).2
      a0 a1 bounds lo0 hi0 lo1 hi1 := by
  apply (full_training_iff_chart raw _ _ _ a0 a1 bounds lo0 hi0 lo1 hi1).2
  change FullTrainingChart raw a0 a1 bounds lo0 hi0 lo1 hi1
    (interference (generatedSnapshot raw k hc.phase.physical))
  simpa [generated_interference] using hc

structure RegularTrainingReadout (s : Snapshot) (a0 a1 : ℝ) : Prop where
  inverse_chart : ChartReadback s a0 a1
  z_positive : 0 < covarianceZ s
  radius_positive : 0 < covarianceR2 s

/-- The full intervals, not their centres, pay the nonzero covariance chart. -/
theorem full_interval_members_recover_regular_chart (raw : RawSource) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (a0 a1 : ℝ) (bounds : MeanIntervals)
    (lo0 hi0 lo1 hi1 : ℝ)
    (hm : FullTrainingMembership raw lam h0 h1 a0 a1 bounds lo0 hi0 lo1 hi1)
    (hs0 : 0 < sinDouble a0) (hs1 : sinDouble a1 < 0)
    (hb0 : 0 < bounds.beta0lo) (hb1 : 0 < bounds.beta1lo)
    (hc : cosDouble a1 < cosDouble a0)
    (hA : bounds.alpha0hi < bounds.alpha1lo) (hB : bounds.beta0hi < bounds.beta1lo) :
    RegularTrainingReadout (raw.withPhase lam h0 h1) a0 a1 := by
  have hx := training_intervals_exclude_equal_modes _ a0 a1 bounds hm.singles hA hB hc
  exact ⟨interval_members_recover_chart _ a0 a1 bounds hm.singles hs0 hs1 hb0 hb1 hc,
    hx.1,hx.2⟩

end
end P23.ObservableClosure.TrainingChart.Consumer
