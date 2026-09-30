import H0mework.Versions.Y.Arithmetic.RieszFiniteSource.SourceKernel
import H0mework.Versions.Y.Arithmetic.RieszResponse.ResponseBoundary
import H0mework.Versions.Y.Arithmetic.RiemannSpectral.PaFixedShiftBoundaryRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSource

open Complex
open scoped InnerProductSpace
noncomputable section

theorem original_boundary (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    burnolZeroPairedFixedAnnulusBoundary coordinate zero shift =
      (pairedMellinTranslationCharacter coordinate.value shift -
        pairedMellinTranslationCharacter (star coordinate.value) shift) •
          burnolCompletedMellinRieszVector coordinate -
      (1 / 2 : ℂ) • burnolEvenAmbientProjection
        (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift)) := by
  rw [OriginalRieszFiniteResponse.original_boundary_material, original_material_eq_program,
    original_material_eq_program]

theorem original_boundary_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    burnolCompletedMellinEvaluator coordinate
        (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) =
      (pairedMellinTranslationCharacter coordinate.value shift -
        pairedMellinTranslationCharacter (star coordinate.value) shift) *
          inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
            (burnolCompletedMellinRieszVector coordinate : BurnolL2) -
      (1 / 2 : ℂ) * inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
        (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift)) := by
  rw [original_boundary, map_sub, map_smul, map_smul,
    ← burnolCompletedMellinRieszVector_readback, ← burnolCompletedMellinRieszVector_readback]
  simp only [burnolEvenAmbientProjection,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, smul_eq_mul]
  rfl

theorem original_fixed_residual (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    burnolPaFixedShiftResidual coordinate zero =
      (1 / 2 : ℂ) * inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
        (forcingIntegral coordinate (Real.log stageZeroSonineQ) +
          forcingIntegral coordinate (-Real.log stageZeroSonineQ)) -
      (pairedMellinTranslationCharacter coordinate.value (Real.log stageZeroSonineQ) -
        pairedMellinTranslationCharacter (star coordinate.value) (Real.log stageZeroSonineQ)) *
          inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
            (burnolCompletedMellinRieszVector coordinate : BurnolL2) := by
  have returned := fixedShiftBoundaryRead_eq_neg_residual coordinate zero
  rw [original_boundary_read] at returned
  linear_combination returned

end
end OriginalRieszFiniteSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
