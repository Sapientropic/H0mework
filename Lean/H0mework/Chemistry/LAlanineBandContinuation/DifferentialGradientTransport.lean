import H0mework.Chemistry.LAlanineBandContinuation.DifferentialEvolution

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation TrueFlowDifferential Set
noncomputable section

theorem gradient_transport (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (s : Time) :
    initialFlowDerivative c p s (sourceGradient (cellSeed c p)) =
      sourceGradient (rawPath (cellSeed c p) s) := by
  let direction := sourceGradient (cellSeed c p)
  have equal : EqOn (extendPath (sourceResponse c p direction))
      (fun t => sourceGradient (rawFlow (cellSeed c p) t)) (Icc (-(1/2) : ℝ) (1/2)) := by
    apply ODE_solution_unique_of_mem_Icc
      (v := fun t h => sourceHessianLinear (rawFlow (cellSeed c p) t) h)
      (s := fun _ => Set.univ) (K := (17/20 : NNReal)) (t₀ := 0)
    · intro t ht
      exact ((sourceHessianLinear (rawFlow (cellSeed c p) t)).lipschitzWith_of_opNorm_le
        (K := (17/20 : NNReal))
        (actual_hessian_norm c fields bounds p inside ⟨t, Ioo_subset_Icc_self ht⟩)).lipschitzOnWith
    · constructor <;> norm_num
    · exact (continuous_extendPath (sourceResponse c p direction)).continuousOn
    · intro t ht
      have derivative := sourceResponse_actual_variational c fields bounds p inside direction ⟨t, Ioo_subset_Icc_self ht⟩
      have agrees := extendPath_coe (sourceResponse c p direction) ⟨t, Ioo_subset_Icc_self ht⟩
      change extendPath (sourceResponse c p direction) t =
        sourceResponse c p direction ⟨t, Ioo_subset_Icc_self ht⟩ at agrees
      rw [← agrees] at derivative
      exact derivative.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · intro t _
      trivial
    · exact (sourceGradient_contDiff 1).continuous.comp_continuousOn (full_original c fields p inside).continuousOn
    · intro t ht
      exact (sourceGradient_hasFDerivAt (rawFlow (cellSeed c p) t)).comp_hasDerivAt t
        ((full_original c fields p inside t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    · intro t _
      trivial
    · rw [rawFlow_starts]
      change extendPath (sourceResponse c p direction) (zeroTime : ℝ) = direction
      rw [extendPath_coe, sourceResponse_starts c fields bounds p inside]
  have result : extendPath (sourceResponse c p direction) (s : ℝ) =
      sourceGradient (rawFlow (cellSeed c p) s) := equal s.property
  rw [extendPath_coe] at result
  exact result

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
