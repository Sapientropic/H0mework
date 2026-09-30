import H0mework.Probability.Source.ConditionalNextImage

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNext.Image

noncomputable section
universe u v
variable {Source : Type u} [Fintype Source] {Next : Type v}
attribute [local instance] valuesFintype valuesMeasurable valuesSingleton

local notation "entropy" =>
  SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy

theorem entropy_injective (source : PMF Source) (nextRead : Source → Next)
    (injective : Function.Injective nextRead) :
    entropy (source.map (actual nextRead)) = entropy source := by
  classical
  have oneToOne : Function.Injective (actual nextRead) :=
    fun _ _ same => injective (congrArg Subtype.val same)
  have onto : Function.Surjective (actual nextRead) := by
    intro value
    obtain ⟨point, same⟩ := value.property
    exact ⟨point, Subtype.ext same⟩
  unfold SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy
  congr 1
  symm
  apply Fintype.sum_bijective (actual nextRead) ⟨oneToOne, onto⟩
  intro point
  have mass : source.map (actual nextRead) (actual nextRead point) = source point := by
    rw [PMF.map_apply, tsum_eq_single point]
    · exact if_pos rfl
    · intro other different
      exact if_neg (fun same => different (oneToOne same).symm)
  rw [mass]

end
end SourceConditionalNext.Image
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
