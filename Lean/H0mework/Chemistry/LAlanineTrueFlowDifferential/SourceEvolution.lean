import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceVariational

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual Set
noncomputable section

theorem sourceResponse_actual_variational (p : BandPoint) (h : Space) (s : Time) :
    HasDerivWithinAt (extendPath (sourceResponse p h))
      (sourceHessianLinear (actualPath p s) (sourceResponse p h s))
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) := by
  apply (sourceResponse_variational p h s).hasDerivWithinAt.congr_of_mem _ s.property
  intro t ht
  exact (extendPath_coe (sourceResponse p h) ⟨t, ht⟩).trans
    (responseCurve_is_actual p h ⟨t, ht⟩).symm

theorem initialFlowDerivative_variational (p : BandPoint) (h : Space) (s : Time) :
    HasDerivWithinAt (fun t => initialFlowDerivative p (projIcc (-(1 / 2)) (1 / 2) (by norm_num) t) h)
      (sourceHessianLinear (actualPath p s) (initialFlowDerivative p s h))
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) :=
  sourceResponse_actual_variational p h s

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
