import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnweightedCayleySource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
import H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementExactOrderPhysicalRead
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.ClozelBurnolPaZeroObservation

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.GammaOutsideDomain

open MeasureTheory BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KGamma OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.JointLogConductor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open scoped InnerProductSpace

open private gamma_pair_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
open private gamma_pair_inverse_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
open private conjugate_twice original_R_Fourier_adjoint from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open private physical_outside_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergySource

local notation "R" => burnolDirectRightResolventCLM
local notation "K" => burnolCompletedMellinRieszVector
local notation "F" => fourierL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Outside" => OriginalKCombPhysicalAction.physicalRemainder

private theorem kernel_ne_zero (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) : (K c : BurnolL2) ≠ 0 := by
  have evaluator := burnolAnalyticComplementCompletedMellinEvaluator_ne_zero_generated
    (burnolPaZeroObservation c zero) (burnolPaZeroObservation_nontrivial c zero) c.rightHalf
  intro vanished
  apply evaluator
  apply ContinuousLinearMap.ext
  intro value
  change burnolCompletedMellinEvaluator c value = 0
  rw [← burnolCompletedMellinRieszVector_readback]
  change inner ℂ (K c : BurnolL2) (value : BurnolL2) = 0
  rw [vanished, inner_zero_left]

private def columnScale (value : BurnolL2) : ℂ := 2 * ((‖value‖ ^ 2 : ℝ) : ℂ)

private theorem columnScale_ne_zero {value : BurnolL2} (nonzero : value ≠ 0) :
    columnScale value ≠ 0 := by
  exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr nonzero)))

private theorem adjoint_source (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    F (R (barC c) (fourierL2.symm v)) = sourceAdjoint c v := by
  have paid := original_R_Fourier_adjoint (barC c) (fourierL2.symm v)
  rw [conjugate_twice, fourierL2.apply_symm_apply] at paid
  exact paid

private theorem adjoint_graph (c : BurnolCompletedMellinCoordinate) {v gamma : BurnolL2}
    (source : GammaPair v gamma) : GammaPair (sourceAdjoint c v) (sourceAdjoint c gamma) := by
  have transported := gamma_pair_fourier _ _
    (actual_Gamma_R (barC c) _ _ (gamma_pair_inverse_fourier _ _ source))
  simpa only [adjoint_source] using transported

private theorem column_graph {acted target input column gammaActed gammaTarget gammaInput : BurnolL2}
    {ratio inverse scale : ℂ}
    (action : acted = ratio • target - inverse • input - scale • column)
    (actedGraph : GammaPair acted gammaActed) (targetGraph : GammaPair target gammaTarget)
    (inputGraph : GammaPair input gammaInput) (scaleNonzero : scale ≠ 0) :
    GammaPair column (scale⁻¹ • (ratio • gammaTarget - inverse • gammaInput - gammaActed)) := by
  intro test
  have read := actedGraph test
  simp only [action, inner_sub_right, inner_smul_right, targetGraph test, inputGraph test] at read
  have isolated := congrArg (fun price : ℂ =>
    ratio * inner ℂ (test.toLp 2 volume) gammaTarget -
      inverse * inner ℂ (test.toLp 2 volume) gammaInput - price) read
  simp only [sub_sub_cancel] at isolated
  simp only [inner_smul_right, inner_sub_right]
  calc
    _ = scale⁻¹ * (scale * inner ℂ (wholeConductorTest test) column) := by
      rw [← mul_assoc, inv_mul_cancel₀ scaleNonzero, one_mul]
    _ = _ := congrArg (scale⁻¹ * ·) isolated

/-- The whole original forward B-power column carries the conductor value from the unprojected FK action. -/
def forwardColumnGamma (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (columnScale (K c : BurnolL2))⁻¹ •
    ((sourceForwardRatio c / (sourceDamping c : ℂ)) • actualGammaKernel (barC c) -
      (sourceDamping c : ℂ)⁻¹ • F (actualGammaKernel c) - R c (F (actualGammaKernel c)))

/-- The independent adjoint B-power column carries its own unprojected conjugate-K conductor value. -/
def adjointColumnGamma (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (columnScale (K (barC c) : BurnolL2))⁻¹ •
    ((sourceAdjointRatio c / (sourceDamping c : ℂ)) • F (actualGammaKernel c) -
      (sourceDamping c : ℂ)⁻¹ • actualGammaKernel (barC c) -
      sourceAdjoint c (actualGammaKernel (barC c)))

theorem actual_forward_column_gamma (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    GammaPair (physicalOutsideColumn c) (forwardColumnGamma c) := by
  have input := gamma_pair_fourier _ _ (actual_gamma_original_kernel c)
  have acted := original_R_FK_generated c
  simp only [sourceFKAction, generatedK_eq_original] at acted
  change R c (F (K c : BurnolL2)) =
    (sourceForwardRatio c / (sourceDamping c : ℂ)) • (K (barC c) : BurnolL2) -
      (sourceDamping c : ℂ)⁻¹ • F (K c : BurnolL2) -
      columnScale (K c : BurnolL2) • physicalOutsideColumn c at acted
  exact column_graph acted (actual_Gamma_R c _ _ input) (actual_gamma_original_kernel (barC c))
    input (columnScale_ne_zero (kernel_ne_zero c zero))

theorem actual_adjoint_column_gamma (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    GammaPair (hPowerPhysicalCorrection c) (adjointColumnGamma c) := by
  have conjugateZero : riemannZeta (barC c).value = 0 := by
    change riemannZeta (star c.value) = 0
    rw [Complex.star_def, riemannZeta_conj, zero, map_zero]
  have input := actual_gamma_original_kernel (barC c)
  have acted := original_R_adjoint_conjugateK_generated c
  simp only [sourceConjugateAdjointAction, generatedK_eq_original] at acted
  change sourceAdjoint c (K (barC c) : BurnolL2) =
    (sourceAdjointRatio c / (sourceDamping c : ℂ)) • F (K c : BurnolL2) -
      (sourceDamping c : ℂ)⁻¹ • (K (barC c) : BurnolL2) -
      columnScale (K (barC c) : BurnolL2) • hPowerPhysicalCorrection c at acted
  exact column_graph acted (adjoint_graph c input) (gamma_pair_fourier _ _ (actual_gamma_original_kernel c))
    input (columnScale_ne_zero (kernel_ne_zero (barC c) conjugateZero))

/-- Every original physical input generates the conductor of its actual Cayley outside field. -/
theorem actual_physical_Cayley_outside_gamma (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (v : BurnolPaAmbientCarrier) :
    GammaPair (Outside (sourceCayley c (v : BurnolL2)))
      (((sourceDamping c : ℂ) * (-2 * inner ℂ (F (generatedK c)) (v : BurnolL2))) •
        forwardColumnGamma c) := by
  have outsideAction : Outside (sourceCayley c (v : BurnolL2)) =
      ((sourceDamping c : ℂ) * (-2 * inner ℂ (F (generatedK c)) (v : BurnolL2))) •
        physicalOutsideColumn c := by
    rw [sourceCayley_apply, map_add, map_smul, physical_outside_zero, zero_add,
      original_R_physical_outside_source, smul_smul]
  rw [outsideAction]
  intro test
  simp only [inner_smul_right, actual_forward_column_gamma c zero test]

end OriginalKCrossParameterRAdjointSource.GammaOutsideDomain
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
