import H0mework.Versions.V2.Arithmetic.RieszSynthesis.WholeSource
import H0mework.Versions.V2.Arithmetic.RieszSynthesis.PaComponent

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSynthesis

open Complex
open scoped InnerProductSpace
open OriginalRieszFiniteColumns OriginalRieszFiniteSource
noncomputable section

theorem original_evaluator_wholeRead (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (bounded : |shift| ≤ Real.log 2) :
    burnolCompletedMellinEvaluator coordinate
        (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) =
      (pairedMellinTranslationCharacter coordinate.value shift -
        pairedMellinTranslationCharacter (star coordinate.value) shift) *
          inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
            (burnolCompletedMellinRieszVector coordinate : BurnolL2) -
        (1 / 2 : ℂ) * star
          (wholeSourceRead coordinate shift (burnolCompletedMellinRieszVector coordinate) +
            wholeSourceRead coordinate (-shift) (burnolCompletedMellinRieszVector coordinate)) := by
  have swapped : inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift)) =
      star (wholeSourceRead coordinate shift (burnolCompletedMellinRieszVector coordinate) +
        wholeSourceRead coordinate (-shift) (burnolCompletedMellinRieszVector coordinate)) := by
    calc
      _ = star (inner ℂ (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift))
          (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := (inner_conj_symm _ _).symm
      _ = _ := by
        rw [inner_add_left, forcing_wholeSourceRead coordinate shift bounded,
          forcing_wholeSourceRead coordinate (-shift) (by simpa only [abs_neg] using bounded)]
  rw [OriginalRieszFiniteSource.original_boundary_read, swapped]

theorem original_evaluator_keeps_sourceDefect (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (bounded : |shift| ≤ Real.log 2) :
    burnolCompletedMellinEvaluator coordinate
        (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) =
      (pairedMellinTranslationCharacter coordinate.value shift -
        pairedMellinTranslationCharacter (star coordinate.value) shift) *
          inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
            (burnolCompletedMellinRieszVector coordinate : BurnolL2) -
        (1 / 2 : ℂ) * star
          (firstSourceRead coordinate shift (burnolCompletedMellinRieszVector coordinate) +
            firstSourceRead coordinate (-shift) (burnolCompletedMellinRieszVector coordinate) +
            inner ℂ (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0 +
              burnolAnnulusSamplingL2 (fourierColumn coordinate (-shift)) 0)
              (sourceFourierDefect (burnolCompletedMellinRieszVector coordinate))) := by
  let K := burnolCompletedMellinRieszVector coordinate
  have paired : wholeSourceRead coordinate shift K + wholeSourceRead coordinate (-shift) K =
      firstSourceRead coordinate shift K + firstSourceRead coordinate (-shift) K +
        inner ℂ (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0 +
          burnolAnnulusSamplingL2 (fourierColumn coordinate (-shift)) 0) (sourceFourierDefect K) := by
    simp only [wholeSourceRead_keeps_defect, inner_add_left]
    ring
  rw [original_evaluator_wholeRead coordinate zero shift bounded, paired]

theorem fixed_residual_wholeSourceRead (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    -burnolPaFixedShiftResidual coordinate zero =
      (pairedMellinTranslationCharacter coordinate.value (Real.log stageZeroSonineQ) -
        pairedMellinTranslationCharacter (star coordinate.value) (Real.log stageZeroSonineQ)) *
          inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
            (burnolCompletedMellinRieszVector coordinate : BurnolL2) -
        (1 / 2 : ℂ) * star
          (wholeSourceRead coordinate (Real.log stageZeroSonineQ) (burnolCompletedMellinRieszVector coordinate) +
            wholeSourceRead coordinate (-Real.log stageZeroSonineQ) (burnolCompletedMellinRieszVector coordinate)) := by
  rw [← fixedShiftBoundaryRead_eq_neg_residual]
  exact original_evaluator_wholeRead coordinate zero (Real.log stageZeroSonineQ) fixedShift_small

theorem source_evaluator_reads_original_residual (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (bounded : |shift| ≤ Real.log 2) :
    burnolCompletedMellinEvaluator coordinate (boundarySource coordinate shift) =
      inner ℂ (burnolCompletedMellinRieszVector coordinate)
        (boundarySource coordinate shift - paComponent coordinate shift) := by
  rw [boundarySource_eq_original coordinate zero shift bounded]
  exact original_evaluator_reads_residual coordinate zero shift bounded

end
end OriginalRieszFiniteSynthesis
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
