import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.SourceData
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerNuclearForce

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open LAlanine40K2025.BasinRefinement.SourceFiniteData
noncomputable section

/-- Full rational target-frame coordinates, before the picobohr ledger readout. -/
def nucleus (a : Fin 13) (k : Fin 3) : ℚ :=
  LAlanine40K2025.Reentry.Source.stepReadout.nuclear.target.position a k

theorem same_reentry_target (a : Fin 13) (k : Fin 3) :
    nucleus a k =
      LAlanine40K2025.Reentry.Source.stepReadout.nuclear.target.position a k := rfl

theorem ledger_rounding_residual (a : Fin 13) (k : Fin 3) :
    |nucleus a k - Nuclear.nuclearPositionQ a k| < (1 : ℚ)/(2*10^12) := by
  exact LAlanine40K2025.Reentry.Producer.nuclearTargetPosition_resolution a k

/-- Every Gaussian AO term belongs exactly to one of the thirteen original
    full-precision target-frame nuclear positions. -/
theorem all_term_centres_precise :
    ∀ i : Basis, List.Forall (fun t => ∃ a : Fin 13, t.centre = nucleus a)
      (sourceTerms i) := by
  decide +kernel

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
