import H0mework.Versions.R9c73a630.Chemistry.LAlanineFlow.Stability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousFlow

open SourceGaussianModel ContinuousGradient Set Metric

noncomputable section

theorem halfTime_inside (time : ℝ) (inside : time ∈ Icc (-timeRadius / 2) (timeRadius / 2)) :
    time ∈ Ioo (-timeRadius) timeRadius := by
  constructor <;> linarith [timeRadius_positive, inside.1, inside.2]

theorem shifted_halfTime_inside (start time : ℝ)
    (hs : start ∈ Icc (-timeRadius / 2) (timeRadius / 2))
    (ht : time ∈ Ioo (-timeRadius / 2) (timeRadius / 2)) :
    start + time ∈ Ioo (-timeRadius) timeRadius := by
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

theorem restart_remains_initial (initial : InitialPoint)
    (margin : initial.val ∈ closedBall sourceCentre (sourceRadius / 2)) (start : ℝ)
    (inside : start ∈ Icc (-timeRadius / 2) (timeRadius / 2)) :
    sourceFlow initial start ∈ closedBall sourceCentre (initialRadius : ℝ) := by
  rw [mem_closedBall] at margin ⊢
  have ht := halfTime_inside start inside
  have absolute : |start| ≤ timeRadius := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
  calc
    dist (sourceFlow initial start) sourceCentre ≤
        dist (sourceFlow initial start) initial.val + dist initial.val sourceCentre := dist_triangle _ _ _
    _ ≤ (sourceSpeedBound : ℝ) * |start| + sourceRadius / 2 :=
      add_le_add (sourceFlow_displacement initial start (Ioo_subset_Icc_self ht)) margin
    _ ≤ (sourceSpeedBound : ℝ) * timeRadius + sourceRadius / 2 := by gcongr
    _ ≤ (initialRadius : ℝ) := by
      change _ ≤ 3 * sourceRadius / 4
      linarith [travel_budget]

def restartInitial (initial : InitialPoint)
    (margin : initial.val ∈ closedBall sourceCentre (sourceRadius / 2)) (start : ℝ)
    (inside : start ∈ Icc (-timeRadius / 2) (timeRadius / 2)) : InitialPoint :=
  ⟨sourceFlow initial start, restart_remains_initial initial margin start inside⟩

theorem safe_restart (initial : InitialPoint)
    (margin : initial.val ∈ closedBall sourceCentre (sourceRadius / 2)) (start : ℝ)
    (inside : start ∈ Icc (-timeRadius / 2) (timeRadius / 2)) :
    EqOn (sourceFlow (restartInitial initial margin start inside))
      (fun time => sourceFlow initial (start + time)) (Ioo (-timeRadius / 2) (timeRadius / 2)) := by
  apply ODE_solution_unique_of_mem_Ioo (v := fun _ => sourceGradient) (s := fun _ => sourceCube)
    (fun _ _ => sourceGradient_lipschitzOn_cube)
    (show (0 : ℝ) ∈ Ioo (-timeRadius / 2) (timeRadius / 2) by
      constructor <;> linarith [timeRadius_positive])
  · intro time ht
    exact ⟨sourceFlow_evolves _ time (halfTime_inside time (Ioo_subset_Icc_self ht)), sourceFlow_stays _ time⟩
  · intro time ht
    refine ⟨?_, sourceFlow_stays initial (start + time)⟩
    have shift : HasDerivAt (fun t : ℝ => start + t) 1 time := by
      simpa only [id_eq] using (hasDerivAt_id time).const_add start
    convert! (sourceFlow_evolves initial (start + time) (shifted_halfTime_inside start time inside ht)).scomp
      time shift using 1
    simp only [one_smul]
  · simp only [sourceFlow_starts, restartInitial, add_zero]

theorem centre_has_uniform_flow :
    ∃ initial : InitialPoint, initial.val = sourceCentre ∧
      ∀ time ∈ Ioo (-timeRadius) timeRadius,
        HasDerivAt (sourceFlow initial) (sourceGradient (sourceFlow initial time)) time ∧
        sourceFlow initial time ∈ sourceCube :=
  ⟨centreInitial, rfl, fun time ht => ⟨sourceFlow_evolves _ time ht, sourceFlow_stays _ time⟩⟩

def sourceFlowClosure : Prop :=
  0 < timeRadius ∧ type_of% sourceFlow_starts ∧ type_of% sourceFlow_stays ∧
  type_of% sourceFlow_integral ∧ type_of% sourceFlow_evolves ∧ type_of% sourceFlow_displacement ∧
  type_of% initial_dist_bound ∧ type_of% forward_gronwall ∧ type_of% injective_at ∧
  type_of% same_field_unique ∧ type_of% densityAlongFlow_derivative ∧
  type_of% restart_remains_initial ∧ type_of% safe_restart ∧ type_of% centre_has_uniform_flow

theorem sourceGeneratedContinuousGradientFlow : sourceFlowClosure :=
  ⟨timeRadius_positive, sourceFlow_starts, sourceFlow_stays, sourceFlow_integral, sourceFlow_evolves,
    sourceFlow_displacement, initial_dist_bound, forward_gronwall, injective_at, same_field_unique,
    densityAlongFlow_derivative, restart_remains_initial, safe_restart, centre_has_uniform_flow⟩

example : sourceFlow centreInitial 0 = sourceCentre := sourceFlow_starts centreInitial
example (time : ℝ) (inside : time ∈ Icc (-timeRadius / 2) (timeRadius / 2)) :
    Function.Injective (fun initial : InitialPoint => sourceFlow initial time) :=
  injective_at time (halfTime_inside time inside)


end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousFlow
