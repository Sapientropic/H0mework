import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Integral
import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource
local instance sourceComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "T2" => burnolMeanZeroTruncatedFourierSquare
local notation "K" => burnolCompletedMellinRieszVector
local notation "seed" => OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed

/-- The finite stock unfolds the original endpoint eta through its own Fourier-square action. -/
def actualSourceStock (N : ℕ) : BurnolQuarterMeanZeroCarrier :=
  (∑ n ∈ Finset.range N, T2 ^ n) Response.eta

def actualUStock (N : ℕ) : BurnolL2 :=
  burnolQuarterZeroExtension (actualSourceStock N : BurnolQuarterIntervalL2)

def actualVStock (N : ℕ) : BurnolL2 :=
  burnolQuarterZeroExtension (T (actualSourceStock N) : BurnolQuarterIntervalL2)

theorem actual_source_operator_sum : HasSum (fun n : ℕ => T2 ^ n) burnolMeanZeroBlockInverse := by
  simpa only [burnolMeanZeroBlockInverse,burnolMeanZeroOneMinusSquare] using
    hasSum_geom_series_inverse T2 burnolMeanZeroTruncatedFourierSquare_opNorm_lt_one

theorem actual_source_stock_tendsto : Tendsto actualSourceStock atTop (𝓝 Response.u) := by
  have source := actual_source_operator_sum.tendsto_sum_nat
  have evaluated := ((ContinuousLinearMap.apply ℂ BurnolQuarterMeanZeroCarrier Response.eta).continuous.tendsto _).comp source
  exact evaluated

theorem actual_source_stock_successor (N : ℕ) :
    actualSourceStock (N+1) = actualSourceStock N + (T2 ^ N) Response.eta := by
  simp only [actualSourceStock,Finset.sum_range_succ,add_apply]

theorem actual_source_stock_means (N : ℕ) :
    burnolQuarterMeanCoefficient (actualSourceStock N : BurnolQuarterIntervalL2) = 0 ∧
    burnolQuarterMeanCoefficient (T (actualSourceStock N) : BurnolQuarterIntervalL2) = 0 := by
  exact ⟨Constructor.mean_zero (actualSourceStock N), Constructor.mean_zero (T (actualSourceStock N))⟩

def actualStockExtension : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolL2 :=
  burnolQuarterZeroExtension.comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule)

theorem actual_UV_stock_tendsto :
    Tendsto actualUStock atTop (𝓝 Response.wholeU) ∧
    Tendsto actualVStock atTop (𝓝 Response.wholeV) := by
  constructor
  · exact (actualStockExtension.continuous.tendsto Response.u).comp actual_source_stock_tendsto
  · exact ((actualStockExtension.comp T).continuous.tendsto Response.u).comp actual_source_stock_tendsto

def actualVelocityStock (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  -(star coordinate.value - 1/2) • (K coordinate : BurnolL2) +
  Kernel.A coordinate • (fourierL2 (actualUStock N) - actualVStock N) +
  Kernel.beta coordinate • (actualUStock N - fourierL2 (actualVStock N)) +
  ((1/2:ℂ)*Kernel.A coordinate) • seed + ((1/2:ℂ)*Kernel.beta coordinate) • fourierL2 seed

theorem actual_velocity_stock_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (actualVelocityStock coordinate) atTop
      (𝓝 (OriginalKBoundarySourceAction.Source.velocity coordinate)) := by
  have u := actual_UV_stock_tendsto.1
  have v := actual_UV_stock_tendsto.2
  have fu := (fourierL2.continuous.tendsto Response.wholeU).comp u
  have fv := (fourierL2.continuous.tendsto Response.wholeV).comp v
  exact (((tendsto_const_nhds.add ((fu.sub v).const_smul (Kernel.A coordinate))).add
    ((u.sub fv).const_smul (Kernel.beta coordinate))).add tendsto_const_nhds).add tendsto_const_nhds

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
