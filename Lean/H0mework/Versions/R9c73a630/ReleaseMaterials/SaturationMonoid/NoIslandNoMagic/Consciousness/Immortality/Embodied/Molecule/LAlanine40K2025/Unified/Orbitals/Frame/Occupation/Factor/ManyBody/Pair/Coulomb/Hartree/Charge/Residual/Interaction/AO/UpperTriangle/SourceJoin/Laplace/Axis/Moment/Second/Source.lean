import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceS

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData BasinRefinement.SourceGaussianModel
noncomputable section

def dAxis (term : Term) : Fin 3 :=
  if term.powers 0 = 2 then 0
  else if term.powers 1 = 2 then 1
  else 2

def sourceDAxis (term : Term) : Prop :=
  term.powers (dAxis term) = 2 ∧
    (∀ other : Fin 3, other ≠ dAxis term → term.powers other = 0) ∧
      ∀ other : Fin 3, term.centre other = Axis.originalS.centre other

theorem original_d11_raw :
    (sourceTerms (11 : Basis)).all (fun term =>
      decide (term.powers (dAxis term) = 2 ∧
        (∀ other : Fin 3, other ≠ dAxis term → term.powers other = 0) ∧
        ∀ other : Fin 3, term.centre other = Axis.originalS.centre other)) = true := by
  decide +kernel

theorem original_d11_source (term : Term)
    (member : term ∈ sourceTerms (11 : Basis)) : sourceDAxis term := by
  have h := List.all_eq_true.mp original_d11_raw term member
  simpa only [sourceDAxis,decide_eq_true_eq] using h

theorem original_d11_census : (sourceTerms (11 : Basis)).length = 3 := by
  decide +kernel

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
