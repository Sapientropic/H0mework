import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.AO
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.Recorded

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceFiniteData SourceSignedEvaluator
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
noncomputable section

/-- Column 6 is the original target ledger's nuclear-attraction matrix
    element, scaled from picohartree. -/
def recordedAttraction (i j : Basis) : ℚ :=
  if i.val ≤ j.val then
    (((targetAORow (Kinetic.kineticPairIndex i j))[6]! : ℤ) : ℚ) / 10^12
  else
    (((targetAORow (Kinetic.kineticPairIndex j i))[6]! : ℤ) : ℚ) / 10^12

def AttractionResidual (i j : Basis) (error : ℚ) : Prop :=
  recordedAttraction i j - error ≤ (aoAttractionInterval i j).1 ∧
    (aoAttractionInterval i j).2 ≤ recordedAttraction i j + error

theorem actual_ao_attraction_error (i j : Basis) (error : ℚ)
    (residual : AttractionResidual i j error) :
    |Nuclear.aoAttraction i j - (recordedAttraction i j : ℝ)| ≤ (error : ℝ) := by
  have source := ao_attraction_interval_contains i j
  rcases residual with ⟨lower,upper⟩
  have lowerReal : (recordedAttraction i j : ℝ) - error ≤
      ((aoAttractionInterval i j).1 : ℝ) := by exact_mod_cast lower
  have upperReal : ((aoAttractionInterval i j).2 : ℝ) ≤
      (recordedAttraction i j : ℝ) + error := by exact_mod_cast upper
  rw [abs_le]
  constructor <;> linarith [source.1,source.2]

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
