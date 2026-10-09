import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceS

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData BasinRefinement.SourceGaussianModel
noncomputable section

def sourceP0 (term : Term) : Prop :=
  term.powers 0 = 1 ∧ term.powers 1 = 0 ∧ term.powers 2 = 0 ∧
    ∀ axis : Fin 3, term.centre axis = Axis.originalS.centre axis

theorem original_p0_raw :
    (sourceTerms (3 : Basis)).all (fun term =>
      decide (term.powers 0 = 1 ∧ term.powers 1 = 0 ∧
        term.powers 2 = 0 ∧
        ∀ axis : Fin 3, term.centre axis = Axis.originalS.centre axis)) = true := by
  decide +kernel

theorem original_p0_source (term : Term)
    (member : term ∈ sourceTerms (3 : Basis)) : sourceP0 term := by
  have h := List.all_eq_true.mp original_p0_raw term member
  simpa only [sourceP0,decide_eq_true_eq] using h

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
