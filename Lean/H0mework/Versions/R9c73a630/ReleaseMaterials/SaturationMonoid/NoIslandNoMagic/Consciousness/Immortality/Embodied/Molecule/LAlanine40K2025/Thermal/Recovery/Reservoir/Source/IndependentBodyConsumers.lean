import H0mework.Foundation.Relations.ConsumerQuotient
import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalLoad.GeneratedControllerEnvironment

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open Load.Source

/-- Coordinates of the incoming PCE matrix, declared without a target channel. -/
def bodyConsumers : IndependentConsumerSystem LoadedJoint where
  Consumer := (PairController × Fin 2) × (PairController × Fin 2)
  Output := fun _ => ℂ
  read := fun index rho => rho index.1 index.2
  positive := ⟨⟨⟨⟨0, 0⟩, 0⟩, 0⟩, ⟨⟨⟨0, 0⟩, 0⟩, 0⟩⟩

theorem bodyConsumers_exact (left right : LoadedJoint) :
    bodyConsumers.Indistinguishable left right ↔ left = right := by
  constructor
  · intro same
    ext i j
    exact same (i, j)
  · rintro rfl consumer
    rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
