import H0mework.Versions.R9c73a630.Chemistry.LAlanineGradient.Bounds
import Mathlib.Analysis.ODE.ExistUnique

/-! Flow parameters vary inside the frozen M3 density field; they are not the physical MD clock. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousFlow

open SourceGaussianModel ContinuousGradient
open Set Metric ODE
open scoped NNReal Topology

noncomputable section

def outerRadius : ℝ≥0 := ⟨sourceRadius, sourceRadius_positive.le⟩
def initialRadius : ℝ≥0 := 3 * outerRadius / 4
def timeRadius : ℝ := sourceRadius / (4 * ((sourceSpeedBound : ℝ) + 1))

theorem timeRadius_positive : 0 < timeRadius := by
  have positive := sourceRadius_positive
  unfold timeRadius
  positivity

def zeroTime : Icc (-timeRadius) timeRadius :=
  ⟨0, by constructor <;> linarith [timeRadius_positive]⟩

theorem travel_budget : (sourceSpeedBound : ℝ) * timeRadius ≤ sourceRadius / 4 := by
  have positive := sourceRadius_positive
  have ratio : (sourceSpeedBound : ℝ) / ((sourceSpeedBound : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  calc
    (sourceSpeedBound : ℝ) * timeRadius =
        (sourceRadius / 4) * ((sourceSpeedBound : ℝ) / ((sourceSpeedBound : ℝ) + 1)) := by
      unfold timeRadius
      field_simp [show (sourceSpeedBound : ℝ) + 1 ≠ 0 by positivity]
    _ ≤ (sourceRadius / 4) * 1 :=
      mul_le_mul_of_nonneg_left ratio (by positivity : 0 ≤ sourceRadius / 4)
    _ = sourceRadius / 4 := mul_one _

theorem sourcePicard : IsPicardLindelof (fun _ => sourceGradient) zeroTime sourceCentre
    outerRadius initialRadius sourceSpeedBound sourceLipschitzBound where
  lipschitzOnWith := fun _ _ => by
    change LipschitzOnWith sourceLipschitzBound sourceGradient (closedBall sourceCentre sourceRadius)
    rw [← sourceCube_eq_closedBall]
    exact sourceGradient_lipschitzOn_cube
  continuousOn := fun _ _ => continuous_const.continuousOn
  norm_le := fun _ _ x inside => by
    apply sourceGradient_norm_le
    rw [sourceCube_eq_closedBall]
    exact inside
  mul_max_le := by
    change (sourceSpeedBound : ℝ) * max (timeRadius - 0) (0 - -timeRadius) ≤
      sourceRadius - (3 * sourceRadius / 4)
    simp only [sub_zero, zero_sub, neg_neg, max_self]
    have positive := sourceRadius_positive
    linarith [travel_budget]

abbrev InitialPoint := closedBall sourceCentre (initialRadius : ℝ)

theorem halfBall_subset_initialBall :
    closedBall sourceCentre (sourceRadius / 2) ⊆ closedBall sourceCentre (initialRadius : ℝ) := by
  apply closedBall_subset_closedBall
  change sourceRadius / 2 ≤ 3 * sourceRadius / 4
  linarith [sourceRadius_positive]

def centreInitial : InitialPoint := ⟨sourceCentre, mem_closedBall_self initialRadius.2⟩

def fixedPoint (initial : InitialPoint) : FunSpace zeroTime sourceCentre initialRadius sourceSpeedBound :=
  Classical.choose (FunSpace.exists_isFixedPt_next sourcePicard initial.property)

theorem fixedPoint_isFixed (initial : InitialPoint) :
    Function.IsFixedPt (FunSpace.next sourcePicard initial.property) (fixedPoint initial) :=
  Classical.choose_spec (FunSpace.exists_isFixedPt_next sourcePicard initial.property)

/-- This extension is clamped outside the generated time window; the ODE is asserted on the window. -/
def sourceFlow (initial : InitialPoint) : ℝ → Point := (fixedPoint initial).compProj

theorem sourceFlow_starts (initial : InitialPoint) : sourceFlow initial 0 = initial.val := by
  change (fixedPoint initial).compProj (zeroTime : ℝ) = _
  rw [FunSpace.compProj_val, ← fixedPoint_isFixed initial, FunSpace.next_apply₀]

theorem sourceFlow_stays (initial : InitialPoint) (time : ℝ) : sourceFlow initial time ∈ sourceCube := by
  rw [sourceCube_eq_closedBall]
  exact (fixedPoint initial).compProj_mem_closedBall sourcePicard.mul_max_le

theorem sourceFlow_continuous (initial : InitialPoint) : Continuous (sourceFlow initial) :=
  (fixedPoint initial).continuous_compProj

theorem sourceFlow_integral (initial : InitialPoint) (time : ℝ)
    (inside : time ∈ Icc (-timeRadius) timeRadius) :
    sourceFlow initial time = initial.val + ∫ t in (0 : ℝ)..time, sourceGradient (sourceFlow initial t) := by
  have equation := (FunSpace.isFixedPt_next_iff sourcePicard initial.property).mp
    (fixedPoint_isFixed initial) ⟨time, inside⟩
  simpa only [sourceFlow, FunSpace.compProj_of_mem inside, ODE.picard, zeroTime] using equation

theorem sourceFlow_hasDerivWithinAt (initial : InitialPoint) (time : ℝ)
    (inside : time ∈ Icc (-timeRadius) timeRadius) :
    HasDerivWithinAt (sourceFlow initial) (sourceGradient (sourceFlow initial time))
      (Icc (-timeRadius) timeRadius) time := by
  apply (hasDerivWithinAt_picard_Icc zeroTime.property sourcePicard.continuousOn_uncurry
    (sourceFlow_continuous initial).continuousOn
    (fun t _ => (fixedPoint initial).compProj_mem_closedBall sourcePicard.mul_max_le)
    initial.val inside).congr_of_mem _ inside
  intro t ht
  exact sourceFlow_integral initial t ht

theorem sourceFlow_evolves (initial : InitialPoint) (time : ℝ)
    (inside : time ∈ Ioo (-timeRadius) timeRadius) :
    HasDerivAt (sourceFlow initial) (sourceGradient (sourceFlow initial time)) time :=
  (sourceFlow_hasDerivWithinAt initial time (Ioo_subset_Icc_self inside)).hasDerivAt
    (Icc_mem_nhds inside.1 inside.2)

theorem sourceFlow_time_distance (initial : InitialPoint) (s t : ℝ)
    (hs : s ∈ Icc (-timeRadius) timeRadius) (ht : t ∈ Icc (-timeRadius) timeRadius) :
    dist (sourceFlow initial s) (sourceFlow initial t) ≤ (sourceSpeedBound : ℝ) * |s - t| := by
  simpa only [sourceFlow, FunSpace.compProj_of_mem hs, FunSpace.compProj_of_mem ht,
    Subtype.dist_eq, Real.dist_eq] using
      (fixedPoint initial).lipschitzWith.dist_le_mul ⟨s, hs⟩ ⟨t, ht⟩

theorem sourceFlow_displacement (initial : InitialPoint) (time : ℝ)
    (inside : time ∈ Icc (-timeRadius) timeRadius) :
    dist (sourceFlow initial time) initial.val ≤ (sourceSpeedBound : ℝ) * |time| := by
  simpa only [sourceFlow_starts, sub_zero] using
    sourceFlow_time_distance initial time 0 inside zeroTime.property

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousFlow
