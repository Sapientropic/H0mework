import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceQuartet

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

def sourceSChecker (i : Basis) : Bool :=
  (sourceTerms i).all (fun term => decide (∀ axis : Fin 3, term.powers axis = 0))

def sourceSBases : Finset Basis :=
  Finset.univ.filter (fun i => sourceSChecker i = true)

theorem source_s_bases_card : sourceSBases.card = 32 := by decide +kernel

theorem source_s_bases_sound (i : Basis) (member : i ∈ sourceSBases) :
    sourceS i := by
  have checked := (Finset.mem_filter.mp member).2
  change (sourceTerms i).all
    (fun term => decide (∀ axis : Fin 3, term.powers axis = 0)) = true at checked
  simpa only [sourceS,sPowers,List.all_eq_true,decide_eq_true_eq]
    using checked

theorem source_s_bases_quartet (i j k l : Basis)
    (hi : i ∈ sourceSBases) (hj : j ∈ sourceSBases)
    (hk : k ∈ sourceSBases) (hl : l ∈ sourceSBases) :
    electronRepulsion i j k l = sourceSQuartet i j k l :=
  source_s_quartet i j k l
    (source_s_bases_sound i hi) (source_s_bases_sound j hj)
    (source_s_bases_sound k hk) (source_s_bases_sound l hl)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
