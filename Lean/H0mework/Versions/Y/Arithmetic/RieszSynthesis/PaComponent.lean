import H0mework.Versions.Y.Arithmetic.RieszSynthesis.SynthesisSource
import H0mework.Versions.Y.Arithmetic.RieszColumns.ColumnsBoundary

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSynthesis

open Complex
open scoped InnerProductSpace
open OriginalRieszFiniteColumns
noncomputable section

local instance synthesisComponentAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The finite source programme generates a Pa component before it is identified with the original B. -/
def paComponent (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolPaAmbientCarrier :=
  -(1 / 2 : ℂ) • burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
    (sourceSynthesis coordinate shift + sourceSynthesis coordinate (-shift))

theorem paComponent_mem (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    paComponent coordinate shift ∈ burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _
    (Submodule.starProjection_apply_mem _ _)

theorem paComponent_eq_original (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (bounded : |shift| ≤ Real.log 2) :
    paComponent coordinate shift = burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) := by
  let part := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  have killed : part (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift +
      (1 / 2 : ℂ) • (sourceSynthesis coordinate shift + sourceSynthesis coordinate (-shift))) = 0 := by
    apply burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_apply_eq_zero_iff.mpr
    rw [Submodule.mem_orthogonal']
    intro value inPa
    have read : inner ℂ (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) value =
        -(1 / 2 : ℂ) * (firstSourceRead coordinate shift value +
          firstSourceRead coordinate (-shift) value) :=
      original_boundary_source_read coordinate zero shift bounded value inPa
    have scalar := inner_smul_left (𝕜 := ℂ)
      (sourceSynthesis coordinate shift + sourceSynthesis coordinate (-shift)) value (1 / 2 : ℂ)
    rw [inner_add_left, scalar, inner_add_left, sourceSynthesis_read, sourceSynthesis_read, read]
    norm_num [map_ofNat]
  rw [map_add, map_smul] at killed
  unfold paComponent
  rw [neg_smul]
  exact (eq_neg_of_add_eq_zero_left killed).symm

theorem paComponent_replay (coordinate : BurnolCompletedMellinCoordinate) (shift radius : ℝ) :
    burnolCoPoissonWindowReplay radius (paComponent coordinate shift) =
      burnolRadiusRestriction radius (paComponent coordinate shift : BurnolL2) :=
  burnolCoPoissonWindowReplay_Pa radius _ (paComponent_mem coordinate shift)

theorem original_residual_kept (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (bounded : |shift| ≤ Real.log 2) :
    burnolZeroPairedFixedAnnulusBoundary coordinate zero shift - paComponent coordinate shift =
      (burnolZeroPairedFixedAnnulusBoundaryOrthogonal coordinate zero shift : BurnolPaAmbientCarrier) := by
  rw [paComponent_eq_original coordinate zero shift bounded]
  exact (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_orthogonal_val _).symm

theorem original_evaluator_reads_residual (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (bounded : |shift| ≤ Real.log 2) :
    burnolCompletedMellinEvaluator coordinate
        (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) =
      inner ℂ (burnolCompletedMellinRieszVector coordinate)
        (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift - paComponent coordinate shift) := by
  rw [original_residual_kept coordinate zero shift bounded]
  exact burnolZeroPairedBoundary_read_eq_orthogonalProjection_inner coordinate zero shift

end
end OriginalRieszFiniteSynthesis
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
