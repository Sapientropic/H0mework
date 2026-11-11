import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResolventReconstruction.Source
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.PaDiagonalBoundary

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResolventReconstruction
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open BurnolPhysicalState.OriginalRieszFiniteSource SourceGeneratedCompressedUnitaryDefectPort
open scoped InnerProductSpace

local instance actionAmbientComplete : CompleteSpace BurnolPaAmbientCarrier :=
 IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance actionOrthogonalComplete : CompleteSpace BurnolPaOrthogonalCarrier :=
 IsComplete.completeSpace_coe burnolPaOrthogonalClosedFace.isClosed.isComplete

/-- Both independently generated L2 source columns retain all resolvent, primitive and edge terms. -/
def sourceColumns (coordinate : BurnolCompletedMellinCoordinate) : Fin 2→BurnolL2 :=
 ![sourceY0 coordinate,sourceY1 coordinate]

def sourceCoefficients (coordinate : BurnolCompletedMellinCoordinate) : Fin 2→ℂ :=
 ![Kernel.A coordinate,Kernel.beta coordinate]

/-- The original finite shift acts on the full source columns before any physical projection. -/
def sourceFiniteGram (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) (i j : Fin 2) : ℂ :=
 (1/2:ℂ)*inner ℂ (sourceColumns coordinate i)
  (burnolMultiplicativeDilation shift (sourceColumns coordinate j)+
   burnolMultiplicativeDilation (-shift) (sourceColumns coordinate j))-
 pairedMellinTranslationCharacter coordinate.value shift *
  inner ℂ (sourceColumns coordinate i) (sourceColumns coordinate j)

theorem generatedK_finite_Gram (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
 (1/2:ℂ)*inner ℂ (generatedK coordinate)
  (burnolMultiplicativeDilation shift (generatedK coordinate)+
   burnolMultiplicativeDilation (-shift) (generatedK coordinate))-
 pairedMellinTranslationCharacter coordinate.value shift * inner ℂ (generatedK coordinate) (generatedK coordinate)=
 ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients coordinate i)*sourceCoefficients coordinate j*
  sourceFiniteGram coordinate shift i j := by
 simp only [Fin.sum_univ_two,sourceCoefficients,sourceFiniteGram,sourceColumns,
  Matrix.cons_val_zero,Matrix.cons_val_one,generatedK,map_add,map_smul,
  inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,starRingEnd_apply]
 ring

private theorem original_fixed_residual_full_L2 (coordinate : BurnolCompletedMellinCoordinate)
 (zero : riemannZeta coordinate.value=0) :
 burnolPaFixedShiftResidual coordinate zero=
 (1/2:ℂ)*inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  (burnolMultiplicativeDilation (Real.log stageZeroSonineQ) (burnolCompletedMellinRieszVector coordinate : BurnolL2)+
   burnolMultiplicativeDilation (-Real.log stageZeroSonineQ) (burnolCompletedMellinRieszVector coordinate : BurnolL2))-
 pairedMellinTranslationCharacter coordinate.value (Real.log stageZeroSonineQ)*
  inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
   (burnolCompletedMellinRieszVector coordinate : BurnolL2) := by
 unfold burnolPaFixedShiftResidual
 rw [burnolPaPairedDilationCompression]
 simp only [ContinuousLinearMap.comp_apply]
 rw [burnolPaOrthogonalClosedFace.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
 change inner ℂ (burnolCompletedMellinRieszVector coordinate)
  ((1/2:ℂ) •
   (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius (Real.log stageZeroSonineQ)
      (burnolCompletedMellinRieszVector coordinate)+
    evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius (-Real.log stageZeroSonineQ)
      (burnolCompletedMellinRieszVector coordinate)))-
  pairedMellinTranslationCharacter coordinate.value (Real.log stageZeroSonineQ)*
   inner ℂ (burnolCompletedMellinRieszVector coordinate) (burnolCompletedMellinRieszVector coordinate)=_
 have scaled := inner_smul_right (𝕜:=ℂ) (burnolCompletedMellinRieszVector coordinate)
  (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius (Real.log stageZeroSonineQ)
      (burnolCompletedMellinRieszVector coordinate)+
   evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius (-Real.log stageZeroSonineQ)
      (burnolCompletedMellinRieszVector coordinate)) (1/2:ℂ)
 rw [scaled,inner_add_right]
 have forward := compression_inner_right_readback
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
  (burnolMultiplicativeDilation (Real.log stageZeroSonineQ)).toLinearIsometry
  (burnolCompletedMellinRieszVector coordinate) (burnolCompletedMellinRieszVector coordinate)
 have backward := compression_inner_right_readback
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
  (burnolMultiplicativeDilation (-Real.log stageZeroSonineQ)).toLinearIsometry
  (burnolCompletedMellinRieszVector coordinate) (burnolCompletedMellinRieszVector coordinate)
 change inner ℂ (burnolCompletedMellinRieszVector coordinate)
  (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius (Real.log stageZeroSonineQ)
   (burnolCompletedMellinRieszVector coordinate))=
  inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
   (burnolMultiplicativeDilation (Real.log stageZeroSonineQ)
    (burnolCompletedMellinRieszVector coordinate : BurnolL2)) at forward
 change inner ℂ (burnolCompletedMellinRieszVector coordinate)
  (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius (-Real.log stageZeroSonineQ)
   (burnolCompletedMellinRieszVector coordinate))=
  inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
   (burnolMultiplicativeDilation (-Real.log stageZeroSonineQ)
    (burnolCompletedMellinRieszVector coordinate : BurnolL2)) at backward
 rw [forward,backward]
 simp only [inner_add_right]
 rfl

/-- Original diagonal residual, generated from the two source columns with every cross term retained. -/
theorem original_fixedResidual_source_Gram (coordinate : BurnolCompletedMellinCoordinate)
 (zero : riemannZeta coordinate.value=0) :
 burnolPaFixedShiftResidual coordinate zero=
 ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients coordinate i)*sourceCoefficients coordinate j*
  sourceFiniteGram coordinate (Real.log stageZeroSonineQ) i j := by
 rw [original_fixed_residual_full_L2,← generatedK_eq_original]
 exact generatedK_finite_Gram coordinate (Real.log stageZeroSonineQ)

theorem original_fixedResidual_source_four_terms (coordinate : BurnolCompletedMellinCoordinate)
 (zero : riemannZeta coordinate.value=0) :
 burnolPaFixedShiftResidual coordinate zero=
 star (Kernel.A coordinate)*Kernel.A coordinate*sourceFiniteGram coordinate (Real.log stageZeroSonineQ) 0 0+
 star (Kernel.A coordinate)*Kernel.beta coordinate*sourceFiniteGram coordinate (Real.log stageZeroSonineQ) 0 1+
 star (Kernel.beta coordinate)*Kernel.A coordinate*sourceFiniteGram coordinate (Real.log stageZeroSonineQ) 1 0+
 star (Kernel.beta coordinate)*Kernel.beta coordinate*sourceFiniteGram coordinate (Real.log stageZeroSonineQ) 1 1 := by
 rw [original_fixedResidual_source_Gram]
 simp only [Fin.sum_univ_two,sourceCoefficients,Matrix.cons_val_zero,Matrix.cons_val_one]
 ring

/-- Omitting the sourceRate*R(fourierPrimitive) term leaves exactly the indicated Euler forcing. -/
theorem omit_sourceY1_resolvent_changes_source (coordinate : BurnolCompletedMellinCoordinate) :
 GapEuler.euler
   ((-(1/2:ℂ) • sourceResolvent coordinate (Response.wholeU-fourierL2 Response.wholeV)+
      fourierPrimitive coordinate : BurnolL2) : TemperedDistribution ℝ ℂ)+
 sourceRate coordinate •
   ((-(1/2:ℂ) • sourceResolvent coordinate (Response.wholeU-fourierL2 Response.wholeV)+
      fourierPrimitive coordinate : BurnolL2) : TemperedDistribution ℝ ℂ)=
 FourierTransform.fourier Response.Psi+
  (2*sourceRate coordinate) • (fourierPrimitive coordinate : TemperedDistribution ℝ ℂ) := by
 have complete := sourceY1_euler coordinate
 have inverse := sourceResolvent_euler coordinate (fourierPrimitive coordinate)
 change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (sourceY1 coordinate))+
  sourceRate coordinate • (Lp.toTemperedDistributionCLM ℂ volume 2 (sourceY1 coordinate))=_ at complete
 change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
  (-(1/2:ℂ) • sourceResolvent coordinate (Response.wholeU-fourierL2 Response.wholeV)+fourierPrimitive coordinate))+
  sourceRate coordinate • (Lp.toTemperedDistributionCLM ℂ volume 2
   (-(1/2:ℂ) • sourceResolvent coordinate (Response.wholeU-fourierL2 Response.wholeV)+fourierPrimitive coordinate))=_
 simp only [sourceY1,map_add,map_smul,Lp.toTemperedDistributionCLM_apply] at complete ⊢
 linear_combination (norm := module) complete - sourceRate coordinate • inverse

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResolventReconstruction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
