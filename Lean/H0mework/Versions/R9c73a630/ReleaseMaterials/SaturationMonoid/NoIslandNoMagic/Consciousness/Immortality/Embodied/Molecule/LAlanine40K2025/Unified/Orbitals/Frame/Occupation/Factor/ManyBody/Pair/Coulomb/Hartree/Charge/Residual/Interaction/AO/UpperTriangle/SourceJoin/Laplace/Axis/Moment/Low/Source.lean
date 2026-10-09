import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceS

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData BasinRefinement.SourceGaussianModel
noncomputable section

def lowBasis (slot : Fin 11) : Basis := ⟨3+slot.val, by omega⟩

def sourceLow (term : Term) : Prop :=
  ∀ axis : Fin 3,
    term.powers axis < 3 ∧ term.centre axis = Axis.originalS.centre axis

theorem original_low_raw :
    ∀ slot : Fin 11,
      (sourceTerms (lowBasis slot)).all (fun term =>
        decide (∀ axis : Fin 3,
          term.powers axis < 3 ∧
          term.centre axis = Axis.originalS.centre axis)) = true := by
  decide +kernel

theorem original_low_source (slot : Fin 11) (term : Term)
    (member : term ∈ sourceTerms (lowBasis slot)) : sourceLow term := by
  have h := List.all_eq_true.mp (original_low_raw slot) term member
  simpa only [sourceLow,decide_eq_true_eq] using h

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
