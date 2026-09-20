import H0mework.Physics.LowEnergyMatterSpace.GlobalWindow
import H0mework.Physics.LowEnergyMatterSpace.PerturbedFlow

/-! Uniqueness glues the source-generated finite windows into an all-real-time development. -/
set_option autoImplicit false
open Set Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section

theorem perturbed_global_exists (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (epsilon start : ℝ) (initial : MatterL2) :
    ∃ curve : ℝ → MatterL2, curve start=initial ∧
      ∀ t, HasDerivAt curve (interactionGenerator perturbation epsilon t (curve t)) t := by
  have windows (radius : ℝ) : ∃ curve : ℝ → MatterL2,
      0<radius → start ∈ Ioo (-radius) radius → curve start=initial ∧
        ∀ t ∈ Ioo (-radius) radius,
          HasDerivAt curve (interactionGenerator perturbation epsilon t (curve t)) t := by
    by_cases positive : 0<radius
    · by_cases located : start ∈ Ioo (-radius) radius
      · obtain ⟨curve,starts,evolves⟩ := perturbed_finite_interval_exists perturbation continuousPerturbation
          symmetric epsilon radius start positive located initial
        exact ⟨curve,fun _ _ => ⟨starts,evolves⟩⟩
      · exact ⟨fun _ => initial,fun _ impossible => False.elim (located impossible)⟩
    · exact ⟨fun _ => initial,fun impossible _ => False.elim (positive impossible)⟩
  choose window generated using windows
  let radius (t : ℝ) := |start|+|t|+1
  have positive (t : ℝ) : 0<radius t := by dsimp [radius]; positivity
  have startInside (t : ℝ) : start ∈ Ioo (-radius t) (radius t) := by
    apply abs_lt.mp
    dsimp [radius]
    linarith [abs_nonneg t]
  have timeInside (t : ℝ) : t ∈ Ioo (-radius t) (radius t) := by
    apply abs_lt.mp
    dsimp [radius]
    linarith [abs_nonneg start]
  let curve (t : ℝ) := window (radius t) t
  have agrees (r : ℝ) (pos : 0<r) (located : start ∈ Ioo (-r) r) :
      EqOn curve (window r) (Ioo (-r) r) := by
    intro t inside
    let common := min (radius t) r
    have initialCommon : start ∈ Ioo (-common) common :=
      abs_lt.mp (lt_min (abs_lt.mpr (startInside t)) (abs_lt.mpr located))
    have timeCommon : t ∈ Ioo (-common) common :=
      abs_lt.mp (lt_min (abs_lt.mpr (timeInside t)) (abs_lt.mpr inside))
    have left (s : ℝ) (member : s ∈ Ioo (-common) common) : s ∈ Ioo (-radius t) (radius t) :=
      abs_lt.mp ((abs_lt.mpr member).trans_le (min_le_left _ _))
    have right (s : ℝ) (member : s ∈ Ioo (-common) common) : s ∈ Ioo (-r) r :=
      abs_lt.mp ((abs_lt.mpr member).trans_le (min_le_right _ _))
    exact perturbed_curve_unique perturbation symmetric epsilon common start initialCommon
      (window (radius t)) (window r)
      (fun s member => (generated (radius t) (positive t) (startInside t)).2 s (left s member))
      (fun s member => (generated r pos located).2 s (right s member))
      ((generated (radius t) (positive t) (startInside t)).1.trans (generated r pos located).1.symm) timeCommon
  refine ⟨curve,(generated (radius start) (positive start) (startInside start)).1,fun t => ?_⟩
  have localEquation := (generated (radius t) (positive t) (startInside t)).2 t (timeInside t)
  have same : curve =ᶠ[𝓝 t] window (radius t) := by
    filter_upwards [Ioo_mem_nhds (timeInside t).1 (timeInside t).2] with s inside
    exact agrees (radius t) (positive t) (startInside t) inside
  exact localEquation.congr_of_eventuallyEq same

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
