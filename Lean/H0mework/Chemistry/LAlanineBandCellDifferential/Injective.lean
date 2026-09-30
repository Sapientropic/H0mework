import H0mework.Chemistry.LAlanineBandCellDifferential.Evolution

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandGeometry WholeBandActual TrueFlowDifferential Set
noncomputable section

theorem cell0_initialFlowDerivative_injective (p : Cell0Point) (s : Time) :
    Function.Injective (cell0_initialFlowDerivative p s) := by
  intro h₁ h₂ equal
  let field (t : ℝ) : Space →L[ℝ] Space := sourceHessianLinear (extendPath (rawPath (cellSeed 0 p.val)) t)
  have field_lipschitz (t : ℝ) : LipschitzWith (17/20 : NNReal) (field t) := by
    apply ContinuousLinearMap.lipschitzWith_of_opNorm_le
    exact cell0_hessian_norm p (projIcc (-(1/2)) (1/2) (by norm_num) t)
  have derivative (h : Space) (t : ℝ) (ht : t ∈ Icc (-(1/2) : ℝ) (1/2)) :
      HasDerivAt (cell0_responseCurve p h) (field t (cell0_responseCurve p h t)) t := by
    let time : Time := ⟨t, ht⟩
    change HasDerivAt (cell0_responseCurve p h)
      (sourceHessianLinear (extendPath (rawPath (cellSeed 0 p.val)) time)
        (cell0_responseCurve p h time)) (time : ℝ)
    rw [extendPath_coe, cell0_responseCurve_is_actual]
    exact cell0_sourceResponse_variational p h time
  have regular (h : Space) : Continuous (cell0_responseCurve p h) :=
    continuous_const.add (continuous_pathPrimitive (cell0_pathHessian p (cell0_sourceResponse p h)))
  have target : cell0_responseCurve p h₁ s = cell0_responseCurve p h₂ s := by
    rw [cell0_responseCurve_is_actual, cell0_responseCurve_is_actual]
    exact equal
  have at_zero : cell0_responseCurve p h₁ zeroTime = cell0_responseCurve p h₂ zeroTime := by
    by_cases hs : 0 ≤ (s : ℝ)
    · have within (t : ℝ) (ht : t ∈ Ioc 0 (s : ℝ)) :
          t ∈ Icc (-(1/2) : ℝ) (1/2) :=
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
          t ∈ Icc (-(1/2) : ℝ) (1/2) :=
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
  simpa only [cell0_responseCurve_is_actual, cell0_sourceResponse_starts] using at_zero

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
