import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceEvolution

/-!
The original Hessian bound and interval ODE uniqueness make every actual initial-value
response injective. Comparison at the requested time is transported back to time zero.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual TrueFlowDifferential Set
noncomputable section

/-- The generated initial-value differential has no kernel at any actual time, including endpoints. -/
theorem initialFlowDerivative_injective (p : BandPoint) (s : Time) :
    Function.Injective (initialFlowDerivative p s) := by
  intro h₁ h₂ equal
  let field (t : ℝ) : Space →L[ℝ] Space := sourceHessianLinear (extendPath (actualPath p) t)
  have field_lipschitz (t : ℝ) :
      LipschitzWith TrueTubeHull.lipschitzConstant (field t) := by
    apply ContinuousLinearMap.lipschitzWith_of_opNorm_le
    exact actualPath_hessian_bound p (projIcc (-(1 / 2)) (1 / 2) (by norm_num) t)
  have derivative (h : Space) (t : ℝ) (ht : t ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
      HasDerivAt (responseCurve p h) (field t (responseCurve p h t)) t := by
    let time : Time := ⟨t, ht⟩
    change HasDerivAt (responseCurve p h)
      (sourceHessianLinear (extendPath (actualPath p) time) (responseCurve p h time)) (time : ℝ)
    rw [extendPath_coe, responseCurve_is_actual]
    exact sourceResponse_variational p h time
  have regular (h : Space) : Continuous (responseCurve p h) :=
    continuous_const.add (continuous_pathPrimitive (pathHessian p (sourceResponse p h)))
  have target : responseCurve p h₁ s = responseCurve p h₂ s := by
    rw [responseCurve_is_actual, responseCurve_is_actual]
    exact equal
  have at_zero : responseCurve p h₁ 0 = responseCurve p h₂ 0 := by
    by_cases hs : 0 ≤ (s : ℝ)
    · have within (t : ℝ) (ht : t ∈ Ioc 0 (s : ℝ)) :
          t ∈ Icc (-(1 / 2) : ℝ) (1 / 2) :=
        ⟨le_trans (by norm_num) ht.1.le, le_trans ht.2 s.property.2⟩
      have same := ODE_solution_unique_of_mem_Icc_left
        (v := fun t => field t) (s := fun _ => univ) (a := (0 : ℝ)) (b := (s : ℝ))
        (fun t _ => (field_lipschitz t).lipschitzOnWith)
        (regular h₁).continuousOn
        (fun t ht => (derivative h₁ t (within t ht)).hasDerivWithinAt)
        (fun _ _ => mem_univ _)
        (regular h₂).continuousOn
        (fun t ht => (derivative h₂ t (within t ht)).hasDerivWithinAt)
        (fun _ _ => mem_univ _) target
      exact same ⟨le_rfl, hs⟩
    · have hs' : (s : ℝ) ≤ 0 := le_of_lt (lt_of_not_ge hs)
      have within (t : ℝ) (ht : t ∈ Ico (s : ℝ) 0) :
          t ∈ Icc (-(1 / 2) : ℝ) (1 / 2) :=
        ⟨le_trans s.property.1 ht.1, le_trans ht.2.le (by norm_num)⟩
      have same := ODE_solution_unique_of_mem_Icc_right
        (v := fun t => field t) (s := fun _ => univ) (a := (s : ℝ)) (b := (0 : ℝ))
        (fun t _ => (field_lipschitz t).lipschitzOnWith)
        (regular h₁).continuousOn
        (fun t ht => (derivative h₁ t (within t ht)).hasDerivWithinAt)
        (fun _ _ => mem_univ _)
        (regular h₂).continuousOn
        (fun t ht => (derivative h₂ t (within t ht)).hasDerivWithinAt)
        (fun _ _ => mem_univ _) target
      exact same ⟨hs', le_rfl⟩
  calc
    h₁ = sourceResponse p h₁ zeroTime := (sourceResponse_starts p h₁).symm
    _ = responseCurve p h₁ zeroTime := (responseCurve_is_actual p h₁ zeroTime).symm
    _ = responseCurve p h₂ zeroTime := at_zero
    _ = sourceResponse p h₂ zeroTime := responseCurve_is_actual p h₂ zeroTime
    _ = h₂ := sourceResponse_starts p h₂

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
