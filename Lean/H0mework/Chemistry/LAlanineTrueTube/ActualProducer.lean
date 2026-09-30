import H0mework.Chemistry.LAlanineTrueTube.ActualAssembly
import H0mework.Chemistry.LAlanineTrueTube.MatrixProducer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeActual

open SourceGaussianModel SourceSignedEvaluator TrueTubeSource TrueTubeTrace
open WholeCellPartition ContinuousParameterMap Set
noncomputable section

theorem actual_first_step (d : Direction) (initial : Point)
    (inside : InRectangle (initialBox d 0) initial) :
    ∃ curve : ℝ → Point, curve 0 = initial ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt curve (signedGradient (sign d) (curve t)) (Icc 0 (stepSize : ℝ)) t ∧
          InRectangle (tubeBox d 0) (curve t)) ∧
      InRectangle (endpointBox d 0) (curve stepSize) ∧
      InRectangle (initialBox d 1) (curve stepSize) :=
  firstStep_from_fields d (TrueTubeMatrix.actual_initial_at d) (TrueTubeMatrix.actual_first_tube d) initial inside

theorem actual_band_first_step (d : Direction) (p : Point) (inside : p ∈ fullDomain) :
    ∃ curve : ℝ → Point, curve 0 = initialMap 0 4 p ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt curve (signedGradient (sign d) (curve t)) (Icc 0 (stepSize : ℝ)) t ∧
          InRectangle (tubeBox d 0) (curve t)) ∧
      InRectangle (endpointBox d 0) (curve stepSize) ∧
      InRectangle (initialBox d 1) (curve stepSize) :=
  actual_first_step d (initialMap 0 4 p) (actual_seed_initial d p inside)

end
end LAlanine40K2025.BasinRefinement.TrueTubeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
