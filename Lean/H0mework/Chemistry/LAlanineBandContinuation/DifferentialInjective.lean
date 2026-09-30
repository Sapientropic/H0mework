import H0mework.Chemistry.LAlanineBandContinuation.DifferentialEvolution

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation TrueFlowDifferential Set
noncomputable section

theorem initialFlowDerivative_injective (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (s : Time) :
    Function.Injective (initialFlowDerivative c p s) := by
  intro h₁ h₂ equal
  let field (t : ℝ) : Space →L[ℝ] Space := sourceHessianLinear (extendPath (rawPath (cellSeed c p)) t)
  have field_lipschitz (t : ℝ) : LipschitzWith (17/20 : NNReal) (field t) := by
    apply ContinuousLinearMap.lipschitzWith_of_opNorm_le
    exact actual_hessian_norm c fields bounds p inside (projIcc (-(1/2)) (1/2) (by norm_num) t)
  have derivative (h : Space) (t : ℝ) (ht : t ∈ Icc (-(1/2) : ℝ) (1/2)) :
      HasDerivAt (responseCurve c p h) (field t (responseCurve c p h t)) t := by
    let time : Time := ⟨t, ht⟩
    change HasDerivAt (responseCurve c p h)
      (sourceHessianLinear (extendPath (rawPath (cellSeed c p)) time)
        (responseCurve c p h time)) (time : ℝ)
    rw [extendPath_coe, responseCurve_is_actual c fields bounds p inside]
    exact sourceResponse_variational c p h time
  have regular (h : Space) : Continuous (responseCurve c p h) :=
    continuous_const.add (continuous_pathPrimitive (pathHessian c p (sourceResponse c p h)))
  have target : responseCurve c p h₁ s = responseCurve c p h₂ s := by
    rw [responseCurve_is_actual c fields bounds p inside, responseCurve_is_actual c fields bounds p inside]
    exact equal
  have at_zero : responseCurve c p h₁ zeroTime = responseCurve c p h₂ zeroTime := by
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
  simpa only [responseCurve_is_actual c fields bounds p inside, sourceResponse_starts c fields bounds p inside] using at_zero

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
