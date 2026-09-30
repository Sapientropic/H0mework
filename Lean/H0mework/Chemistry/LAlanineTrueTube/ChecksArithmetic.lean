import H0mework.Chemistry.LAlanineTrueTube.ChecksIncidence
import H0mework.Chemistry.LAlanineTrueTube.TraceSignedField

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeChecks

open TrueTubeSource TrueTubeTrace SourceGaussianModel SourceSignedEvaluator IntervalParameterMap
noncomputable section

def signedTubeGradient (d : Direction) : VectorPair :=
  signedGradientPair (sign d) (recordedField (firstTubeField d))
def signedInitialGradient (d : Direction) : VectorPair :=
  signedGradientPair (sign d) (recordedField 0)

def picardImage (d : Direction) : VectorPair :=
  vectorAdd (initialBox d 0) (vectorScale (0, stepSize) (signedTubeGradient d))

def eulerEndpoint (d : Direction) : VectorPair :=
  vectorAdd (initialBox d 0) (vectorScale (point stepSize) (signedTubeGradient d))

def secondEndpoint (d : Direction) : VectorPair :=
  vectorAdd (vectorAdd (initialBox d 0) (vectorScale (point stepSize) (signedInitialGradient d)))
    (vectorScale (point (stepSize ^ 2 / 2)) (accelerationPair (recordedField (firstTubeField d))))

def intersectEndpoints (d : Direction) : VectorPair := fun axis =>
  (max (eulerEndpoint d axis).1 (secondEndpoint d axis).1,
   min (eulerEndpoint d axis).2 (secondEndpoint d axis).2)

theorem first_picard_selfmap : ∀ d : Direction, ∀ axis : Fin 3,
    (tubeBox d 0 axis).1 ≤ (picardImage d axis).1 ∧
      (picardImage d axis).2 ≤ (tubeBox d 0 axis).2 := by decide +kernel

theorem first_endpoint_recomputed : ∀ d : Direction, ∀ axis : Fin 3,
    intersectEndpoints d axis = endpointBox d 0 axis := by decide +kernel

theorem endpoint_intersection_eq (d : Direction) : intersectEndpoints d = endpointBox d 0 :=
  funext (first_endpoint_recomputed d)

theorem signed_tube_ordered : ∀ d : Direction, ∀ axis : Fin 3,
    (signedTubeGradient d axis).1 ≤ (signedTubeGradient d axis).2 := by decide +kernel

theorem acceleration_ordered : ∀ d : Direction, ∀ axis : Fin 3,
    (accelerationPair (recordedField (firstTubeField d)) axis).1 ≤
      (accelerationPair (recordedField (firstTubeField d)) axis).2 := by decide +kernel

end
end LAlanine40K2025.BasinRefinement.TrueTubeChecks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
