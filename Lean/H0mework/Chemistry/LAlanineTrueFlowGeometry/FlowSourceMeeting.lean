import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceRawPath

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel TrueFlowDifferential TrueTubeWholeActual TrueTubeContinuation Set
noncomputable section

/-- A same-sign meeting identifies the longer trajectory's shifted point with the other seed. -/
theorem rawFlow_meeting_nonneg (p q : Point) (a b : Time)
    (nonnegative : 0 ≤ (b : ℝ)) (ordered : (b : ℝ) ≤ a)
    (meeting : rawFlow p a = rawFlow q b) :
    rawFlow p ((a : ℝ) - b) = rawFlow q 0 := by
  have shifted_mem : MapsTo (fun r : ℝ => r + ((a : ℝ) - b))
      (Icc 0 (b : ℝ)) (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    intro r hr
    constructor <;> linarith [a.property.2, hr.1, hr.2]
  have unshifted_mem : Icc (0 : ℝ) b ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) := by
    intro r hr
    exact ⟨by linarith [hr.1], hr.2.trans b.property.2⟩
  have shifted : IsIntegralCurveOn (fun r => rawFlow p (r + ((a : ℝ) - b)))
      (fun _ => globalField 1) (Icc 0 (b : ℝ)) := by
    intro r hr
    have derivative := (rawFlow_extended p _ (shifted_mem hr)).scomp r
      ((hasDerivAt_id r).add_const ((a : ℝ) - b)).hasDerivWithinAt shifted_mem
    simpa only [Function.comp_def, id_eq, one_smul] using derivative
  have plain := (rawFlow_extended q).mono unshifted_mem
  have same := ODE_solution_unique_of_mem_Icc_left
    (v := fun _ => globalField 1) (s := fun _ => univ) (a := (0 : ℝ)) (b := (b : ℝ))
    (fun _ _ => (globalField_lipschitz 1).lipschitzOnWith)
    shifted.continuousOn
    (fun r hr => (shifted r ⟨hr.1.le, hr.2⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem hr))
    (fun _ _ => mem_univ _)
    plain.continuousOn
    (fun r hr => (plain r ⟨hr.1.le, hr.2⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem hr))
    (fun _ _ => mem_univ _) (by
      rw [show (b : ℝ) + ((a : ℝ) - b) = (a : ℝ) by ring]
      exact meeting)
  simpa only [zero_add] using same ⟨le_rfl, nonnegative⟩

/-- The negative-time counterpart uses the same autonomous field and forward interval uniqueness. -/
theorem rawFlow_meeting_nonpos (p q : Point) (a b : Time)
    (nonpositive : (b : ℝ) ≤ 0) (ordered : (a : ℝ) ≤ b)
    (meeting : rawFlow p a = rawFlow q b) :
    rawFlow p ((a : ℝ) - b) = rawFlow q 0 := by
  have shifted_mem : MapsTo (fun r : ℝ => r + ((a : ℝ) - b))
      (Icc (b : ℝ) 0) (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    intro r hr
    constructor <;> linarith [a.property.1, hr.1, hr.2]
  have unshifted_mem : Icc (b : ℝ) 0 ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) := by
    intro r hr
    exact ⟨b.property.1.trans hr.1, by linarith [hr.2]⟩
  have shifted : IsIntegralCurveOn (fun r => rawFlow p (r + ((a : ℝ) - b)))
      (fun _ => globalField 1) (Icc (b : ℝ) 0) := by
    intro r hr
    have derivative := (rawFlow_extended p _ (shifted_mem hr)).scomp r
      ((hasDerivAt_id r).add_const ((a : ℝ) - b)).hasDerivWithinAt shifted_mem
    simpa only [Function.comp_def, id_eq, one_smul] using derivative
  have plain := (rawFlow_extended q).mono unshifted_mem
  have same := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => globalField 1) (s := fun _ => univ) (a := (b : ℝ)) (b := (0 : ℝ))
    (fun _ _ => (globalField_lipschitz 1).lipschitzOnWith)
    shifted.continuousOn
    (fun r hr => (shifted r ⟨hr.1, hr.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hr))
    (fun _ _ => mem_univ _)
    plain.continuousOn
    (fun r hr => (plain r ⟨hr.1, hr.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hr))
    (fun _ _ => mem_univ _) (by
      rw [show (b : ℝ) + ((a : ℝ) - b) = (a : ℝ) by ring]
      exact meeting)
  simpa only [zero_add] using same ⟨nonpositive, le_rfl⟩

/-- Fixed-time source flow never identifies two different initial points. -/
theorem rawFlow_timeSlice_injective (t : Time) :
    Function.Injective (fun p : Point => rawFlow p t) := by
  intro p q meeting
  have same : rawFlow p 0 = rawFlow q 0 := by
    by_cases nonnegative : 0 ≤ (t : ℝ)
    · simpa only [sub_self] using rawFlow_meeting_nonneg p q t t nonnegative le_rfl meeting
    · simpa only [sub_self] using rawFlow_meeting_nonpos p q t t
        (le_of_lt (lt_of_not_ge nonnegative)) le_rfl meeting
  simpa only [rawFlow_starts] using same

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
