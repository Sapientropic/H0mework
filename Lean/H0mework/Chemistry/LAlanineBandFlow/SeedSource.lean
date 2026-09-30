import H0mework.Chemistry.LAlanineBandGeometry.Cells
import H0mework.Chemistry.LAlanineContinuousSource.CellBounds

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSeed

open SourceGaussianModel SourceSignedEvaluator ContinuousSeed WholeBandSource
noncomputable section

def interpolateQ (values : Geometry.Data.Knot → ℚ) (s : Segment) (v : ℚ) : ℚ :=
  let t := (v-knotCoordinate (firstKnot s)) / (knotCoordinate (lastKnot s)-knotCoordinate (firstKnot s))
  (1-t)*values (firstKnot s)+t*values (lastKnot s)

theorem interpolateQ_cast (values : Geometry.Data.Knot → ℚ) (s : Segment) (v : ℚ) :
    (interpolateQ values s v : ℝ) = interpolate values s v := by
  simp [interpolateQ, interpolate, knotFraction]

theorem source_corners : ∀ c : FullBandCell, ∀ side : Fin 2,
    interpolateQ Geometry.Source.lower (cellSegment c) (cellV c side) = cellLowerCurve c side ∧
    interpolateQ Geometry.Source.upper (cellSegment c) (cellV c side) = cellUpperCurve c side := by
  decide +kernel

def uRange (c : FullBandCell) : Pair :=
  (min (cellLowerCurve c 0) (cellLowerCurve c 1) - Geometry.Source.epsilon 0,
   max (cellUpperCurve c 0) (cellUpperCurve c 1) + Geometry.Source.epsilon 0)
def vRange (c : FullBandCell) : Pair := (cellV c 0, cellV c 1)

theorem source_u_corners : ∀ c : FullBandCell, ∀ side : Fin 2,
    (uRange c).1 ≤ cellLowerCurve c side - Geometry.Source.epsilon 0 ∧
    cellLowerCurve c side - Geometry.Source.epsilon 0 ≤ (uRange c).2 ∧
    (uRange c).1 ≤ cellUpperCurve c side + Geometry.Source.epsilon 0 ∧
    cellUpperCurve c side + Geometry.Source.epsilon 0 ≤ (uRange c).2 := by
  decide +kernel

def positionBox (c : FullBandCell) (a : Fin 3) : Pair :=
  add (add (point (SourceFiniteData.boxCentre a))
    (mul (point (Geometry.Source.basis a 0)) (uRange c)))
    (mul (point (Geometry.Source.basis a 1)) (vRange c))

theorem source_initial_box : ∀ c : FullBandCell, ∀ a : Fin 3,
    positionBox c a = initialBox c 0 0 a := by
  decide +kernel

end
end LAlanine40K2025.BasinRefinement.WholeBandSeed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
