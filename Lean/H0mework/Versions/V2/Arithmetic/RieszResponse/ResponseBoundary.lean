import H0mework.Versions.V2.Arithmetic.RieszResponse.Material
import H0mework.Versions.V2.Arithmetic.MellinProjection.PaBoundaryCommutator

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteResponse

open Complex
noncomputable section

private theorem inverse_character (coordinate : ℂ) (shift : ℝ) :
    fullMellinTranslationCharacter coordinate (-shift) =
      reciprocalMellinTranslationCharacter coordinate shift := by
  unfold fullMellinTranslationCharacter reciprocalMellinTranslationCharacter
  congr 1
  push_cast
  ring

private theorem projection_self (value : BurnolPaAmbientCarrier) :
    burnolEvenAmbientProjection (value : BurnolL2) = value :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value

private theorem paired_action (value : BurnolPaAmbientCarrier) (shift : ℝ) :
    burnolPairedAmbientCompression shift value =
      (1 / 2 : ℂ) •
        (burnolEvenAmbientProjection (burnolMultiplicativeDilation shift (value : BurnolL2)) +
          burnolEvenAmbientProjection (burnolMultiplicativeDilation (-shift) (value : BurnolL2))) :=
  rfl

theorem original_boundary_material (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    burnolZeroPairedFixedAnnulusBoundary coordinate zero shift =
      (pairedMellinTranslationCharacter coordinate.value shift -
        pairedMellinTranslationCharacter (star coordinate.value) shift) •
          burnolCompletedMellinRieszVector coordinate -
      (1 / 2 : ℂ) • burnolEvenAmbientProjection
        (sourceMaterial coordinate shift + sourceMaterial coordinate (-shift)) := by
  have material : burnolEvenAmbientProjection
      (sourceMaterial coordinate shift + sourceMaterial coordinate (-shift)) =
      burnolEvenAmbientProjection (burnolMultiplicativeDilation shift
        (burnolCompletedMellinRieszVector coordinate : BurnolL2)) +
      burnolEvenAmbientProjection (burnolMultiplicativeDilation (-shift)
        (burnolCompletedMellinRieszVector coordinate : BurnolL2)) -
      (fullMellinTranslationCharacter (star coordinate.value) shift +
        reciprocalMellinTranslationCharacter (star coordinate.value) shift) •
          burnolCompletedMellinRieszVector coordinate := by
    simp only [sourceMaterial, map_add, map_sub, map_smul, projection_self, inverse_character]
    module
  change pairedMellinTranslationCharacter coordinate.value shift •
    burnolCompletedMellinRieszVector coordinate -
    burnolPairedAmbientCompression shift (burnolCompletedMellinRieszVector coordinate) = _
  rw [paired_action, material]
  unfold pairedMellinTranslationCharacter
  module

end
end OriginalRieszFiniteResponse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
