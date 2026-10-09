import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Source

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData BasinRefinement.SourceGaussianModel
noncomputable section

def targetLinearPowers (term : Term) : Prop :=
  ∀ axis : Fin 3, term.powers axis < 2

def targetLinearChecker (basis : Basis) : Bool :=
  (sourceTerms basis).all (fun term =>
    decide (∀ axis : Fin 3, term.powers axis < 2))

def targetLinearBases : Finset Basis :=
  Finset.univ.filter (fun basis => targetLinearChecker basis = true)

theorem original_target_linear_card : targetLinearBases.card = 86 := by
  decide +kernel

theorem original_target_linear_sound (basis : Basis)
    (member : basis ∈ targetLinearBases) :
    ∀ term ∈ sourceTerms basis, targetLinearPowers term := by
  have checked := (Finset.mem_filter.mp member).2
  change (sourceTerms basis).all
    (fun term => decide (∀ axis : Fin 3, term.powers axis < 2)) = true at checked
  simpa only [targetLinearPowers,List.all_eq_true,decide_eq_true_eq]
    using checked

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
