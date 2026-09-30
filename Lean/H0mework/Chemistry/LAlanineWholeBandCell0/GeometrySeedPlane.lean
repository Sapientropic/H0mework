import H0mework.Chemistry.LAlanineTrueFlowGeometry.FlowSourceMeeting
import H0mework.Chemistry.LAlanineTrueFlowGeometry.FlowPlane
import H0mework.Chemistry.LAlanineBandGeometry.Cells

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousSeed WholeBandSource TrueFlowGeometry TrueFlowDifferential
open ContinuousGradient Matrix Set
open scoped Matrix
noncomputable section

theorem cell_seed_plane_zero (c : FullBandCell) (p : Point) :
    planeCoordinate (cellSeed c p) = 0 := by
  rw [planeCoordinate, normalRead_apply]
  have offset : cellSeed c p - centre =
      bandU (cellSegment c) (Geometry.Source.epsilon 0) p • basisVector 0 + p 1 • basisVector 1 := by
    change centre + _ + _ - centre = _
    abel
  rw [offset, dotProduct_add, dotProduct_smul, dotProduct_smul,
    seedNormal_dot_basis, seedNormal_dot_basis, smul_zero, smul_zero, add_zero]

theorem source_timeSlice_classification (c d : FullBandCell) (p q : Point)
    (hp : p ∈ cellDomain c) (hq : q ∈ cellDomain d) (t : Time) :
    rawFlow (cellSeed c p) t = rawFlow (cellSeed d q) t ↔ p 0 = q 0 ∧ p 1 = q 1 :=
  (rawFlow_timeSlice_injective t).eq_iff.trans (cell_seed_eq_iff_coordinates c d p q hp hq)

theorem rawPlane_strictMono_of_actual (x : Point)
    (original : IsIntegralCurveOn (rawFlow x) (fun _ => sourceGradient) (Icc (-(1/2 : ℝ)) (1/2)))
    (transverse : ∀ t ∈ Icc (-(1/2 : ℝ)) (1/2), 0 < seedNormal ⬝ᵥ sourceGradient (rawFlow x t)) :
    StrictMonoOn (fun t => planeCoordinate (rawFlow x t)) (Icc (-(1/2 : ℝ)) (1/2)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
  · exact normalRead.continuous.comp_continuousOn (original.continuousOn.sub continuousOn_const)
  · intro t ht
    have derivative := (planeCoordinate_hasFDerivAt (rawFlow x t)).comp_hasDerivWithinAt t
      (original t (interior_subset ht))
    rw [normalRead_apply] at derivative
    exact derivative.mono interior_subset
  · intro t ht
    exact transverse t (interior_subset ht)

end
end LAlanine40K2025.BasinRefinement.WholeBandGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
