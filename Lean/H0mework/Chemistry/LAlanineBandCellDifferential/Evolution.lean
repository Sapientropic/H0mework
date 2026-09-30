import H0mework.Chemistry.LAlanineBandCellDifferential.Variational

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandGeometry WholeBandActual TrueFlowDifferential Set
noncomputable section

theorem cell0_sourceResponse_actual_variational (p : Cell0Point) (h : Space) (s : Time) :
    HasDerivWithinAt (extendPath (cell0_sourceResponse p h))
      (sourceHessianLinear (rawPath (cellSeed 0 p.val) s) (cell0_sourceResponse p h s))
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) := by
  apply (cell0_sourceResponse_variational p h s).hasDerivWithinAt.congr_of_mem _ s.property
  intro t ht
  exact (extendPath_coe (cell0_sourceResponse p h) ⟨t, ht⟩).trans
    (cell0_responseCurve_is_actual p h ⟨t, ht⟩).symm

theorem cell0_initialFlowDerivative_variational (p : Cell0Point) (h : Space) (s : Time) :
    HasDerivWithinAt (fun t => cell0_initialFlowDerivative p (projIcc (-(1 / 2)) (1 / 2) (by norm_num) t) h)
      (sourceHessianLinear (rawPath (cellSeed 0 p.val) s) (cell0_initialFlowDerivative p s h))
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) :=
  cell0_sourceResponse_actual_variational p h s

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
