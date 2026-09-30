import H0mework.Versions.Y.Arithmetic.RieszColumns.ColumnsRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteColumns

open Complex
open scoped InnerProductSpace
open OriginalRieszFiniteSource
noncomputable section

theorem original_boundary_source_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (bounded : |shift| ≤ Real.log 2) (value : BurnolPaAmbientCarrier)
    (inPa : value ∈ burnolCompactCoPoissonClosedRange) :
    inner ℂ (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift : BurnolL2)
        (value : BurnolL2) =
      -(1 / 2 : ℂ) * (firstSourceRead coordinate shift value +
        firstSourceRead coordinate (-shift) value) := by
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero
  have initial : inner ℂ (burnolCompletedMellinRieszVector coordinate) value = 0 :=
    (Submodule.mem_orthogonal' _ _).mp orthogonal value inPa
  have projected : inner ℂ
      (burnolEvenAmbientProjection (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift)))
      value = inner ℂ (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift))
        (value : BurnolL2) :=
    ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
      ).inner_orthogonalProjectionOnto_eq_of_mem_right value _
  change inner ℂ (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) value = _
  rw [original_boundary, inner_sub_left]
  have kernelScalar := inner_smul_left (𝕜 := ℂ)
    (burnolCompletedMellinRieszVector coordinate) value
    (pairedMellinTranslationCharacter coordinate.value shift -
      pairedMellinTranslationCharacter (star coordinate.value) shift)
  have sourceScalar := inner_smul_left (𝕜 := ℂ)
    (burnolEvenAmbientProjection (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift)))
    value (1 / 2 : ℂ)
  rw [kernelScalar, sourceScalar]
  rw [initial, mul_zero, zero_sub, projected, inner_add_left,
    forcing_firstSourceRead coordinate shift bounded value inPa,
    forcing_firstSourceRead coordinate (-shift) (by simpa only [abs_neg] using bounded) value inPa]
  norm_num [map_ofNat]

theorem fixed_boundary_source_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (value : BurnolPaAmbientCarrier)
    (inPa : value ∈ burnolCompactCoPoissonClosedRange) :
    inner ℂ (burnolZeroPairedFixedAnnulusBoundary coordinate zero
        (Real.log stageZeroSonineQ) : BurnolL2) (value : BurnolL2) =
      -(1 / 2 : ℂ) * (firstSourceRead coordinate (Real.log stageZeroSonineQ) value +
        firstSourceRead coordinate (-Real.log stageZeroSonineQ) value) :=
  original_boundary_source_read coordinate zero (Real.log stageZeroSonineQ) fixedShift_small value inPa

end
end OriginalRieszFiniteColumns
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
