import H0mework.Chemistry.LAlanineBandContinuation.Full
import H0mework.Chemistry.LAlanineWholeBandCell0.GeometrySeedPlane
import H0mework.Chemistry.LAlanineWholeBandCell0.GeometryTransverse
import H0mework.Chemistry.LAlanineTrueFlowGeometry.FlowSourceNoFold

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandTransverse
open TrueFlowGeometry TrueFlowDifferential Set Matrix
noncomputable section

def PositiveNormalReports (c : FullBandCell) : Prop :=
  ∀ d : Direction, ∀ i : Step, 0 < normalLower (tubeCallAt c d i)

theorem actual_transverse (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c)
    (t : ℝ) (time : t ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    0 < seedNormal ⬝ᵥ sourceGradient (rawFlow (cellSeed c p) t) := by
  obtain ⟨d, i, _, actual⟩ := full_field_cover c fields p inside t time
  exact (Rat.cast_pos.mpr (positive d i)).trans_le (normal_dot_lower _ _ actual)

theorem actual_plane_strictMono (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) :
    StrictMonoOn (fun t => planeCoordinate (rawFlow (cellSeed c p) t)) (Icc (-(1/2 : ℝ)) (1/2)) :=
  rawPlane_strictMono_of_actual _ (full_original c fields p inside)
    (actual_transverse c fields positive p inside)

/-- Source field soundness and positive independent normal reports classify both actual occurrences. -/
theorem actual_meeting_classification (c d : FullBandCell)
    (leftFields : ∀ side, DirectionFields c side) (rightFields : ∀ side, DirectionFields d side)
    (leftPositive : PositiveNormalReports c) (rightPositive : PositiveNormalReports d)
    (p q : Point) (hp : p ∈ cellDomain c) (hq : q ∈ cellDomain d) (a b : Time) :
    rawFlow (cellSeed c p) a = rawFlow (cellSeed d q) b ↔
      p 0 = q 0 ∧ p 1 = q 1 ∧ (a : ℝ) = b := by
  rw [rawFlow_meeting_classification _ _ (cell_seed_plane_zero c p) (cell_seed_plane_zero d q)
    (actual_plane_strictMono c leftFields leftPositive p hp)
    (actual_plane_strictMono d rightFields rightPositive q hq) a b,
    cell_seed_eq_iff_coordinates c d p q hp hq]
  exact and_assoc

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
