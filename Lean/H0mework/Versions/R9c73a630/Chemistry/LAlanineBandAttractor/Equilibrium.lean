import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.Contraction
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandGlobalSource.FlowGlobal

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Attractor

open SourceGaussianModel ContinuousGradient
noncomputable section

theorem zero_is_original_flow_equilibrium (centre : Point) (radius : ℝ)
    (zero : ZeroInBall centre radius) (t : ℝ) : GlobalSource.flow zero.point t = zero.point := by
  have same : (fun _ : ℝ => zero.point) = GlobalSource.flow zero.point := by
    apply GlobalSource.flow_unique zero.point _ rfl
    intro s
    rw [zero.zero]
    exact hasDerivAt_const s zero.point
  exact (congrFun same t).symm

end
end LAlanine40K2025.BasinRefinement.Attractor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
