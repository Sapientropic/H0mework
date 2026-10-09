import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.Evolution

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandGeometry WholeBandActual TrueFlowDifferential
open WholeBandCell0Continuation Set
noncomputable section

theorem cell0_gradient_transport (p : Cell0Point) (s : Time) :
    cell0_initialFlowDerivative p s (sourceGradient (cellSeed 0 p.val)) =
      sourceGradient (rawPath (cellSeed 0 p.val) s) := by
  let direction := sourceGradient (cellSeed 0 p.val)
  have equal : EqOn (extendPath (cell0_sourceResponse p direction))
      (fun t => sourceGradient (rawFlow (cellSeed 0 p.val) t)) (Icc (-(1/2) : ℝ) (1/2)) := by
    apply ODE_solution_unique_of_mem_Icc
      (v := fun t h => sourceHessianLinear (rawFlow (cellSeed 0 p.val) t) h)
      (s := fun _ => Set.univ) (K := (17/20 : NNReal)) (t₀ := 0)
    · intro t ht
      exact ((sourceHessianLinear (rawFlow (cellSeed 0 p.val) t)).lipschitzWith_of_opNorm_le
        (K := (17/20 : NNReal))
        (cell0_hessian_norm p ⟨t, Ioo_subset_Icc_self ht⟩)).lipschitzOnWith
    · constructor <;> norm_num
    · exact (continuous_extendPath (cell0_sourceResponse p direction)).continuousOn
    · intro t ht
      have derivative := cell0_sourceResponse_actual_variational p direction ⟨t, Ioo_subset_Icc_self ht⟩
      have agrees := extendPath_coe (cell0_sourceResponse p direction) ⟨t, Ioo_subset_Icc_self ht⟩
      change extendPath (cell0_sourceResponse p direction) t =
        cell0_sourceResponse p direction ⟨t, Ioo_subset_Icc_self ht⟩ at agrees
      rw [← agrees] at derivative
      exact derivative.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · intro t _
      trivial
    · exact (sourceGradient_contDiff 1).continuous.comp_continuousOn (cell0_full_original p).continuousOn
    · intro t ht
      exact (sourceGradient_hasFDerivAt (rawFlow (cellSeed 0 p.val) t)).comp_hasDerivAt t
        ((cell0_full_original p t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    · intro t _
      trivial
    · rw [rawFlow_starts]
      change extendPath (cell0_sourceResponse p direction) (zeroTime : ℝ) = direction
      rw [extendPath_coe, cell0_sourceResponse_starts]
  have result : extendPath (cell0_sourceResponse p direction) (s : ℝ) =
      sourceGradient (rawFlow (cellSeed 0 p.val) s) := equal s.property
  rw [extendPath_coe] at result
  exact result

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
