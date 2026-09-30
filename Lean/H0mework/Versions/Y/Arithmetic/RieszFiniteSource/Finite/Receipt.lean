import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.Phi
import H0mework.Versions.Y.Arithmetic.RieszSynthesis.WholeSource
import H0mework.Versions.Y.Arithmetic.RieszSynthesis.PaComponent

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSource

open Complex MeasureTheory
open OriginalRieszFiniteColumns OriginalRieszFiniteSynthesis OriginalRieszFinitePairing
noncomputable section

local instance receiptAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- Complete finite action material retained before the root effect is emitted.
Every field is generated from one completed-Mellin coordinate and its zero. -/
structure Receipt where
  kernel : BurnolL2
  acted : ℝ → BurnolL2
  forcing : ℝ → BurnolL2
  position : ℝ → BurnolL2
  fourier : ℝ → BurnolL2
  positionMean : ℝ → ℂ
  fourierMean : ℝ → ℂ
  sourceSynthesis : ℝ → BurnolPaAmbientCarrier
  wholeSynthesis : ℝ → BurnolPaAmbientCarrier
  boundary : ℝ → BurnolPaAmbientCarrier
  pa : ℝ → BurnolPaAmbientCarrier
  orthogonal : ℝ → BurnolPaOrthogonalCarrier
  sourcePair : ℝ → ℂ
  fixedResidual : ℂ

def Receipt.generate (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) : Receipt where
  kernel := (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  acted := fun shift =>
    burnolMultiplicativeDilation shift (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  forcing := forcingIntegral coordinate
  position := positionColumn coordinate
  fourier := fourierColumn coordinate
  positionMean := fun shift => ∫ x : ℝ, positionColumn coordinate shift x
  fourierMean := fun shift => ∫ x : ℝ, fourierColumn coordinate shift x
  sourceSynthesis := OriginalRieszFiniteSynthesis.sourceSynthesis coordinate
  wholeSynthesis := OriginalRieszFiniteSynthesis.wholeSynthesis coordinate
  boundary := burnolZeroPairedFixedAnnulusBoundary coordinate zero
  pa := OriginalRieszFiniteSynthesis.paComponent coordinate
  orthogonal := burnolZeroPairedFixedAnnulusBoundaryOrthogonal coordinate zero
  sourcePair := OriginalRieszFinitePairing.sourcePairRead coordinate
  fixedResidual := burnolPaFixedShiftResidual coordinate zero

/-- Both directions of the original action are retained by one source function. -/
theorem Receipt.generate_action (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    (Receipt.generate coordinate zero).acted shift =
      fullMellinTranslationCharacter (star coordinate.value) shift •
        (Receipt.generate coordinate zero).kernel +
          (Receipt.generate coordinate zero).forcing shift := by
  exact original_finite_action coordinate shift

theorem Receipt.generate_whole_projection
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (shift : ℝ) (bounded : |shift| ≤ Real.log 2) :
    (Receipt.generate coordinate zero).wholeSynthesis shift =
      burnolEvenAmbientProjection
        ((Receipt.generate coordinate zero).forcing shift) := by
  exact OriginalRieszFiniteSynthesis.wholeSynthesis_eq_projection
    coordinate shift bounded

theorem Receipt.generate_keeps_fourier_defect
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    (Receipt.generate coordinate zero).wholeSynthesis shift =
      (Receipt.generate coordinate zero).sourceSynthesis shift +
        OriginalRieszFiniteSynthesis.defectTranspose
          (burnolAnnulusSamplingL2
            ((Receipt.generate coordinate zero).fourier shift) 0) := by
  exact OriginalRieszFiniteSynthesis.wholeSynthesis_keeps_defect
    coordinate shift

theorem Receipt.generate_pa_projection
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (shift : ℝ) (bounded : |shift| ≤ Real.log 2) :
    (Receipt.generate coordinate zero).pa shift =
      burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
        ((Receipt.generate coordinate zero).boundary shift) := by
  exact OriginalRieszFiniteSynthesis.paComponent_eq_original
    coordinate zero shift bounded

theorem Receipt.generate_fixedResidual_source
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    -(Receipt.generate coordinate zero).fixedResidual =
      (pairedMellinTranslationCharacter coordinate.value (Real.log stageZeroSonineQ) -
        pairedMellinTranslationCharacter (star coordinate.value)
          (Real.log stageZeroSonineQ)) *
        kernelSelfSource coordinate +
        (1 / 2 : ℂ) *
          star ((Receipt.generate coordinate zero).sourcePair
            (Real.log stageZeroSonineQ)) := by
  simpa only [Receipt.generate, evaluatorSource] using
    fixed_residual_source coordinate zero

theorem Receipt.generate_pa_orthogonal
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    (Receipt.generate coordinate zero).boundary (Real.log stageZeroSonineQ) -
        (Receipt.generate coordinate zero).pa (Real.log stageZeroSonineQ) =
      ((Receipt.generate coordinate zero).orthogonal
        (Real.log stageZeroSonineQ) : BurnolPaAmbientCarrier) := by
  exact OriginalRieszFiniteSynthesis.original_residual_kept
    coordinate zero (Real.log stageZeroSonineQ) fixedShift_small

end
end OriginalRieszFiniteSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
