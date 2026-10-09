import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceS

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData BasinRefinement.SourceGaussianModel
noncomputable section

def sourceLowDegree (term : Term) : Prop :=
  ∀ axis : Fin 3, term.powers axis < 3

theorem all_original_low_degree_raw :
    ∀ basis : Basis,
      (sourceTerms basis).all (fun term =>
        decide (∀ axis : Fin 3, term.powers axis < 3)) = true := by
  decide +kernel

theorem all_original_low_degree (basis : Basis) (term : Term)
    (member : term ∈ sourceTerms basis) : sourceLowDegree term := by
  have h := List.all_eq_true.mp (all_original_low_degree_raw basis) term member
  simpa only [sourceLowDegree, decide_eq_true_eq] using h

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
