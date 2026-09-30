import H0mework.Chemistry.LAlanineBandContinuation.DifferentialVariational

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation TrueFlowDifferential Set
noncomputable section

theorem sourceResponse_actual_variational (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (h : Space) (s : Time) :
    HasDerivWithinAt (extendPath (sourceResponse c p h))
      (sourceHessianLinear (rawPath (cellSeed c p) s) (sourceResponse c p h s))
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) := by
  apply (sourceResponse_variational c p h s).hasDerivWithinAt.congr_of_mem _ s.property
  intro t ht
  exact (extendPath_coe (sourceResponse c p h) ⟨t, ht⟩).trans
    (responseCurve_is_actual c fields bounds p inside h ⟨t, ht⟩).symm

theorem initialFlowDerivative_variational (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (h : Space) (s : Time) :
    HasDerivWithinAt (fun t => initialFlowDerivative c p (projIcc (-(1 / 2)) (1 / 2) (by norm_num) t) h)
      (sourceHessianLinear (rawPath (cellSeed c p) s) (initialFlowDerivative c p s h))
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) :=
  sourceResponse_actual_variational c fields bounds p inside h s

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
