import H0mework.Versions.V2.Arithmetic.RieszColumns.Window
import H0mework.Versions.V2.Arithmetic.RieszColumns.ReverseEdge
import H0mework.Versions.V2.Arithmetic.RieszFiniteSource.SourceKernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteColumns

open Complex MeasureTheory
open OriginalPaPhysicalGreen OriginalRieszFiniteSource OriginalRieszSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)

private theorem nativeIntegral_sub (lambda : ℂ) (left right : BurnolL2) (endpoint : ℝ) :
    nativeIntegral lambda (left - right) endpoint =
      nativeIntegral lambda left endpoint - nativeIntegral lambda right endpoint := by
  unfold nativeIntegral
  rw [← intervalIntegral.integral_sub (nativeIntegrand_integrable _ _ _)
    (nativeIntegrand_integrable _ _ _)]
  apply intervalIntegral.integral_congr
  intro time _
  simp only [nativeIntegrand, map_sub, smul_sub]

private theorem nativeIntegral_smul (lambda coefficient : ℂ) (value : BurnolL2) (endpoint : ℝ) :
    nativeIntegral lambda (coefficient • value) endpoint =
      coefficient • nativeIntegral lambda value endpoint := by
  unfold nativeIntegral
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro time _
  simp only [nativeIntegrand, map_smul]
  module

def positionColumn (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : BurnolL2 :=
  nativeIntegral (star coordinate.value - 1 / 2)
    (burnolQuarterZeroExtension (Kernel.beta coordinate • (Response.u : BurnolQuarterIntervalL2) -
      Kernel.A coordinate • (Response.v : BurnolQuarterIntervalL2))) endpoint -
    Kernel.A coordinate • edgeIntegral coordinate endpoint

def fourierColumn (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : BurnolL2 :=
  backwardIntegral (star coordinate.value - 1 / 2)
    (burnolQuarterZeroExtension (Kernel.A coordinate • (Response.u : BurnolQuarterIntervalL2) -
      Kernel.beta coordinate • (Response.v : BurnolQuarterIntervalL2))) endpoint -
    Kernel.beta coordinate • reverseEdgeIntegral coordinate endpoint

theorem forcingIntegral_columns (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    forcingIntegral coordinate endpoint =
      positionColumn coordinate endpoint + fourierL2 (fourierColumn coordinate endpoint) := by
  unfold forcingIntegral profileIntegral fourierProfileIntegral positionColumn fourierColumn
  simp only [map_sub, map_smul]
  rw [fourier_backwardIntegral, fourier_reverseEdgeIntegral]
  simp only [Response.wholeU, Response.wholeV, map_sub, map_smul,
    nativeIntegral_sub, nativeIntegral_smul]
  module

theorem edgeIntegral_cutoff_self (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    originalPhysicalCutoff (q * Real.exp |endpoint|) (edgeIntegral coordinate endpoint) =
      edgeIntegral coordinate endpoint := by
  apply cutoff_eq_self_of_ae_zero
  apply edgeIntegral_ae_zero
  · nlinarith [Real.one_le_exp_iff.mpr (abs_nonneg endpoint)]
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_abs endpoint)) (by norm_num)

theorem positionColumn_cutoff_self (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    originalPhysicalCutoff (q * Real.exp |endpoint|) (positionColumn coordinate endpoint) =
      positionColumn coordinate endpoint := by
  let radius := q * Real.exp |endpoint|
  have source := nativeIntegral_interval_cutoff_self (star coordinate.value - 1 / 2)
    (Kernel.beta coordinate • (Response.u : BurnolQuarterIntervalL2) -
      Kernel.A coordinate • (Response.v : BurnolQuarterIntervalL2)) endpoint
  have edge := edgeIntegral_cutoff_self coordinate endpoint
  change (burnolRadiusZeroExtension radius).comp (burnolRadiusRestriction radius)
    (positionColumn coordinate endpoint) = _
  unfold positionColumn
  rw [map_sub, map_smul]
  change originalPhysicalCutoff radius _ - Kernel.A coordinate • originalPhysicalCutoff radius _ = _
  rw [source, edge]

theorem fourierColumn_cutoff_self (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    originalPhysicalCutoff (q * Real.exp |endpoint|) (fourierColumn coordinate endpoint) =
      fourierColumn coordinate endpoint := by
  let radius := q * Real.exp |endpoint|
  have source := backwardIntegral_interval_cutoff_self (star coordinate.value - 1 / 2)
    (Kernel.A coordinate • (Response.u : BurnolQuarterIntervalL2) -
      Kernel.beta coordinate • (Response.v : BurnolQuarterIntervalL2)) endpoint
  have edge := reverseEdgeIntegral_cutoff_self coordinate endpoint
  change originalPhysicalCutoff radius (reverseEdgeIntegral coordinate endpoint) =
    reverseEdgeIntegral coordinate endpoint at edge
  change (burnolRadiusZeroExtension radius).comp (burnolRadiusRestriction radius)
    (fourierColumn coordinate endpoint) = _
  unfold fourierColumn
  rw [map_sub, map_smul]
  change originalPhysicalCutoff radius _ - Kernel.beta coordinate • originalPhysicalCutoff radius _ = _
  rw [source, edge]

theorem positionColumn_integrable (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    Integrable (positionColumn coordinate endpoint) :=
  integrable_of_cutoff_eq_self (q * Real.exp |endpoint|) _ (positionColumn_cutoff_self coordinate endpoint)

theorem fourierColumn_integrable (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    Integrable (fourierColumn coordinate endpoint) :=
  integrable_of_cutoff_eq_self (q * Real.exp |endpoint|) _ (fourierColumn_cutoff_self coordinate endpoint)

theorem positionColumn_firstMoment (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    MemLp (fun x : ℝ => (x : ℂ) * positionColumn coordinate endpoint x) 2 volume :=
  firstMoment_of_cutoff_eq_self (q * Real.exp |endpoint|) _ (positionColumn_cutoff_self coordinate endpoint)

theorem fourierColumn_firstMoment (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    MemLp (fun x : ℝ => (x : ℂ) * fourierColumn coordinate endpoint x) 2 volume :=
  firstMoment_of_cutoff_eq_self (q * Real.exp |endpoint|) _ (fourierColumn_cutoff_self coordinate endpoint)

end
end OriginalRieszFiniteColumns
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
