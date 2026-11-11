import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Mean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelCompressedSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource
local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "q" => (1/4:ℝ)

/-- The actual negative physical action generates the quarter constant face before the source is cotested. -/
theorem actual_negative_physical_source_restriction (test : BurnolPaAmbientCarrier) (t : ℝ) (nonnegative : 0 ≤ t) :
    burnolQuarterRestriction (burnolMultiplicativeDilation (-t) (test : BurnolL2)) =
      ((Real.exp (-t/2):ℂ)*FiniteMobiusResolventFlux.actualMean (test : BurnolL2)) • intervalConstant q := by
  exact FiniteMobiusResolventFlux.source_negative_restriction test (-t) (neg_nonpos.mpr nonnegative)

/-- A source mean-zero quarter field annihilates the generated compressed physical cotest; no cancellation certificate is supplied. -/
theorem actual_compressed_meanZero_source_cotest (test : BurnolPaAmbientCarrier)
    (source : BurnolQuarterMeanZeroCarrier) (t : ℝ) (nonnegative : 0 ≤ t) :
    inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t
      (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2))) = 0 := by
  have unitary := (burnolMultiplicativeDilation t).inner_map_map
    (burnolMultiplicativeDilation (-t) (test : BurnolL2))
    (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2))
  rw [burnolMultiplicativeDilation_neg_eq_symm,(burnolMultiplicativeDilation t).apply_symm_apply] at unitary
  rw [unitary,←burnolMultiplicativeDilation_neg_eq_symm]
  change inner ℂ (burnolMultiplicativeDilation (-t) (test : BurnolL2))
    (burnolQuarterRestriction.adjoint (source : BurnolQuarterIntervalL2)) = 0
  rw [ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction,
    actual_negative_physical_source_restriction test t nonnegative,inner_smul_left]
  have zero := (Submodule.mem_orthogonal' (intervalConstantLine q) (source : BurnolQuarterIntervalL2)).mp source.property
    (intervalConstant q) (Submodule.mem_span_singleton_self (intervalConstant q))
  have actualZero : inner ℂ (intervalConstant q) (source : BurnolQuarterIntervalL2) = 0 := by
    rw [←inner_conj_symm,zero]
    exact map_zero _
  rw [actualZero,mul_zero]

theorem actual_compressed_UV_source_cotests (test : BurnolPaAmbientCarrier) (t : ℝ) (nonnegative : 0 ≤ t) :
    inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t Response.wholeU) = 0 ∧
    inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t Response.wholeV) = 0 :=
  ⟨actual_compressed_meanZero_source_cotest test Response.u t nonnegative,
    actual_compressed_meanZero_source_cotest test Response.v t nonnegative⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelCompressedSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
