import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceS

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData BasinRefinement.SourceGaussianModel
noncomputable section

def pBasis (axis : Fin 3) : Basis := ⟨3+axis.val, by omega⟩

def sourcePAxis (axis : Fin 3) (term : Term) : Prop :=
  term.powers axis = 1 ∧
    (∀ other : Fin 3, other ≠ axis → term.powers other = 0) ∧
      ∀ other : Fin 3, term.centre other = Axis.originalS.centre other

theorem original_p_axes_raw :
    ∀ axis : Fin 3,
      (sourceTerms (pBasis axis)).all (fun term =>
        decide (term.powers axis = 1 ∧
          (∀ other : Fin 3, other ≠ axis → term.powers other = 0) ∧
          ∀ other : Fin 3, term.centre other = Axis.originalS.centre other)) = true := by
  decide +kernel

theorem original_p_axes_source (axis : Fin 3) (term : Term)
    (member : term ∈ sourceTerms (pBasis axis)) : sourcePAxis axis term := by
  have h := List.all_eq_true.mp (original_p_axes_raw axis) term member
  simpa only [sourcePAxis,decide_eq_true_eq] using h

theorem original_p_axes_census :
    ∀ axis : Fin 3, (sourceTerms (pBasis axis)).length = 3 := by
  decide +kernel

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
