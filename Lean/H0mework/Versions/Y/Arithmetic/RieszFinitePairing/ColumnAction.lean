import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.ColumnIntegral
import H0mework.Versions.Y.Arithmetic.RieszColumns.Columns
import H0mework.Versions.Y.Arithmetic.RieszGreen.GapGram

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Complex FourierTransform MeasureTheory
open scoped FourierTransform
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFiniteSource OriginalRieszFiniteColumns

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "TD" => TemperedDistribution ℝ ℂ

private def sourceLift : BurnolQuarterMeanZeroCarrier →L[ℂ] TD :=
  (Lp.toTemperedDistributionCLM ℂ volume 2).comp
    (burnolQuarterZeroExtension.comp
      (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))

private theorem source_euler_law (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : TD) =
      (star coordinate.value - 1 / 2) •
        (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : TD) +
      (burnolQuarterZeroExtension (Kernel.A coordinate • (Response.u : BurnolQuarterIntervalL2) -
        Kernel.beta coordinate • (Response.v : BurnolQuarterIntervalL2)) : TD) -
      Kernel.beta coordinate • GapEuler.edge q := by
  rw [Euler.source_euler]
  change sourceLift (Euler.sourceEuler coordinate) - Kernel.beta coordinate • GapEuler.edge q =
    (star coordinate.value - 1 / 2) • sourceLift (burnolRieszSingleFourierSource coordinate) +
      sourceLift (Kernel.A coordinate • Response.u - Kernel.beta coordinate • Response.v) -
      Kernel.beta coordinate • GapEuler.edge q
  rw [Euler.sourceEuler_eq]
  simp only [map_add, map_sub, map_smul]
  module

private theorem return_euler_law (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (burnolQuarterZeroExtension
      (Constructor.returnState coordinate : BurnolQuarterIntervalL2) : TD) +
      (star coordinate.value - 1 / 2) •
        (burnolQuarterZeroExtension (Constructor.returnState coordinate : BurnolQuarterIntervalL2) : TD) =
      (burnolQuarterZeroExtension (Kernel.beta coordinate • (Response.u : BurnolQuarterIntervalL2) -
        Kernel.A coordinate • (Response.v : BurnolQuarterIntervalL2)) : TD) -
      burnolRieszReturnRaw coordinate q • GapEuler.edge q := by
  rw [Euler.return_euler]
  change (sourceLift (Constructor.returnEuler coordinate) -
      burnolRieszReturnRaw coordinate q • GapEuler.edge q) +
      (star coordinate.value - 1 / 2) • sourceLift (Constructor.returnState coordinate) =
    sourceLift (Kernel.beta coordinate • Response.u - Kernel.A coordinate • Response.v) -
      burnolRieszReturnRaw coordinate q • GapEuler.edge q
  rw [Euler.returnEuler_eq]
  simp only [Constructor.returnState, map_add, map_sub, map_smul]
  module

private theorem gap_euler_law (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (gapState coordinate : TD) +
      (star coordinate.value - 1 / 2) • (gapState coordinate : TD) =
      (-star coordinate.value * GapEuler.gapMean q coordinate) • GapEuler.edge q := by
  exact GapEuler.even_gapTail_euler q (by norm_num) coordinate

theorem positionColumn_action (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    positionColumn coordinate endpoint =
      burnolMultiplicativeDilation endpoint
        (gapState coordinate + burnolQuarterZeroExtension
          (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) -
      fullMellinTranslationCharacter (star coordinate.value) endpoint •
        (gapState coordinate + burnolQuarterZeroExtension
          (Constructor.returnState coordinate : BurnolQuarterIntervalL2)) := by
  let base := gapState coordinate + burnolQuarterZeroExtension
    (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
  let forcing := burnolQuarterZeroExtension
    (Kernel.beta coordinate • (Response.u : BurnolQuarterIntervalL2) -
      Kernel.A coordinate • (Response.v : BurnolQuarterIntervalL2))
  let corrected := base + Kernel.A coordinate • edgePrimitive coordinate
  have correctedLaw : GapEuler.euler (corrected : TD) +
      (star coordinate.value - 1 / 2) • (corrected : TD) = (forcing : TD) := by
    have gap := gap_euler_law coordinate
    have returned := return_euler_law coordinate
    have primitive := congrArg (fun state : TD => Kernel.A coordinate • state)
      (edgePrimitive_euler coordinate)
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 corrected) +
      (star coordinate.value - 1 / 2) • Lp.toTemperedDistributionCLM ℂ volume 2 corrected = _
    dsimp only [corrected, base, forcing]
    simp only [map_add, map_smul, Lp.toTemperedDistributionCLM_apply]
    unfold Kernel.A at primitive returned ⊢
    linear_combination (norm := module) gap + returned + primitive
  have action := ColumnIntegral.action_of_euler coordinate corrected forcing correctedLaw endpoint
  dsimp only [corrected] at action
  simp only [map_add, map_smul] at action
  change nativeIntegral (star coordinate.value - 1 / 2) forcing endpoint -
    Kernel.A coordinate • edgeIntegral coordinate endpoint =
      burnolMultiplicativeDilation endpoint base -
        fullMellinTranslationCharacter (star coordinate.value) endpoint • base
  rw [edgeIntegral]
  linear_combination (norm := module) -action

theorem fourierColumn_action (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    fourierColumn coordinate endpoint =
      fullMellinTranslationCharacter (star coordinate.value) endpoint •
        burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) -
      burnolMultiplicativeDilation (-endpoint)
        (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) := by
  let value := burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  let forcing := burnolQuarterZeroExtension
    (Kernel.A coordinate • (Response.u : BurnolQuarterIntervalL2) -
      Kernel.beta coordinate • (Response.v : BurnolQuarterIntervalL2))
  let lambda := star coordinate.value - 1 / 2
  have source : GapEuler.euler (value : TD) = lambda • (value : TD) + (forcing : TD) -
      Kernel.beta coordinate • GapEuler.edge q := source_euler_law coordinate
  have transformed : GapEuler.euler (fourierL2 value : TD) +
      lambda • (fourierL2 value : TD) =
      -(fourierL2 forcing : TD) + Kernel.beta coordinate • 𝓕 (GapEuler.edge q) := by
    have actual := congrArg (fourierCLM ℂ TD) source
    simp only [map_add, map_sub, map_smul, fourierCLM_apply] at actual
    have valueFourier : (fourierL2 value : TD) = 𝓕 (value : TD) := by
      rw [Lp.fourier_toTemperedDistribution_eq]
      rfl
    have forcingFourier : (fourierL2 forcing : TD) = 𝓕 (forcing : TD) := by
      rw [Lp.fourier_toTemperedDistribution_eq]
      rfl
    rw [valueFourier, forcingFourier, GapEuler.euler_fourier, actual]
    module
  let corrected := fourierL2 value + Kernel.beta coordinate • fourierPrimitive coordinate
  let correctedForcing := (2 * lambda * Kernel.beta coordinate) • fourierPrimitive coordinate -
    fourierL2 forcing
  have correctedLaw : GapEuler.euler (corrected : TD) +
      (star coordinate.value - 1 / 2) • (corrected : TD) = (correctedForcing : TD) := by
    have primitive := congrArg (fun state : TD => Kernel.beta coordinate • state)
      (fourierPrimitive_euler coordinate)
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 corrected) +
      (star coordinate.value - 1 / 2) • Lp.toTemperedDistributionCLM ℂ volume 2 corrected =
        Lp.toTemperedDistributionCLM ℂ volume 2 correctedForcing
    dsimp only [corrected, correctedForcing]
    simp only [map_add, map_sub, map_smul, Lp.toTemperedDistributionCLM_apply]
    dsimp only [lambda] at transformed ⊢
    linear_combination (norm := module) transformed + primitive
  have action := ColumnIntegral.action_of_euler coordinate corrected correctedForcing correctedLaw endpoint
  dsimp only [corrected, correctedForcing] at action
  rw [ColumnIntegral.native_smul_sub] at action
  simp only [map_add, map_smul] at action
  apply fourierL2.injective
  change fourierL2 (backwardIntegral lambda forcing endpoint -
      Kernel.beta coordinate • reverseEdgeIntegral coordinate endpoint) =
    fourierL2 (fullMellinTranslationCharacter (star coordinate.value) endpoint • value -
      burnolMultiplicativeDilation (-endpoint) value)
  rw [map_sub, map_smul, fourier_backwardIntegral, fourier_reverseEdgeIntegral,
    map_sub, map_smul, fourierL2_burnolMultiplicativeDilation, neg_neg, fourierEdgeIntegral]
  dsimp only [lambda] at action ⊢
  linear_combination (norm := module) action

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
