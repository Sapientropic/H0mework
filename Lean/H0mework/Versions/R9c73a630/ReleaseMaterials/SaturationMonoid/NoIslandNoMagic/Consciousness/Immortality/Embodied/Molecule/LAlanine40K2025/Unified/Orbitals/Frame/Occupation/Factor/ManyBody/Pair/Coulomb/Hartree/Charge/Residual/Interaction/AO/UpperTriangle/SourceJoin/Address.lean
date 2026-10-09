import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.All
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.Sum
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open BasinRefinement.SourceFiniteData
noncomputable section

def targetPair (address : Fin 4851) : Basis × Basis :=
  (targetLeft address.val,targetRight address.val)

theorem target_pair_upper (address : Fin 4851) :
    targetPair address ∈ UpperTriangle.sourceUpperPairs := by
  rcases all_target_rows_certified address with ⟨_,_,_,_,ordered,_,_,_⟩
  simpa [targetPair,UpperTriangle.sourceUpperPairs] using ordered

theorem target_pair_index (address : Fin 4851) :
    pairIndex address.val = address.val := by
  rcases all_target_rows_certified address with ⟨_,_,_,_,_,index,_,_⟩
  exact index

theorem target_pair_injective : Function.Injective targetPair := by
  intro left right equal
  have sameLeft : targetLeft left.val = targetLeft right.val :=
    congrArg Prod.fst equal
  have sameRight : targetRight left.val = targetRight right.val :=
    congrArg Prod.snd equal
  have sameIndex : pairIndex left.val = pairIndex right.val := by
    simp only [pairIndex,sameLeft,sameRight]
  exact Fin.ext ((target_pair_index left).symm.trans
    (sameIndex.trans (target_pair_index right)))

def targetUpperPair (address : Fin 4851) : UpperTriangle.sourceUpperPairs :=
  ⟨targetPair address,target_pair_upper address⟩

theorem target_upper_pair_injective : Function.Injective targetUpperPair := by
  intro left right equal
  exact target_pair_injective (congrArg Subtype.val equal)

theorem target_upper_pair_surjective : Function.Surjective targetUpperPair := by
  have card : Fintype.card (Fin 4851) =
      Fintype.card UpperTriangle.sourceUpperPairs := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using
      UpperTriangle.source_upper_pair_count.symm
  exact target_upper_pair_injective.surjective_of_finite
    (Fintype.equivOfCardEq card)

def targetUpperEquiv : Fin 4851 ≃ UpperTriangle.sourceUpperPairs :=
  Equiv.ofBijective targetUpperPair
    ⟨target_upper_pair_injective,target_upper_pair_surjective⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
