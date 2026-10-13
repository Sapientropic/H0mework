import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKResponseCofinalSourceAction.Read
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKResponseCofinalSourceAction.Limit
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKResponseCofinalSourceAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The first source-owned reader independently consumes the actual cofinal U limit. -/
theorem actual_first_coefficient_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
 Tendsto (fun n:Nat=>actualFirstRead coordinate (actualU n)) atTop
  (𝓝 (actualFirstRead coordinate OriginalRieszSource.Response.u)) :=
 ((actualFirstRead coordinate).continuous.tendsto _).comp actual_source_tendsto

/-- The second reader consumes the same source limit in the exact original R/cut/Tate order. -/
theorem actual_second_coefficient_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
 Tendsto (fun n:Nat=>actualSecondRead coordinate (actualU n)) atTop
  (𝓝 (actualSecondRead coordinate OriginalRieszSource.Response.u)) :=
 ((actualSecondRead coordinate).continuous.tendsto _).comp actual_source_tendsto

/-- The actual V source has the matching two independent consumers, not a value-based sequence admission. -/
theorem actual_V_coefficients_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
 Tendsto (fun n:Nat=>actualFirstRead coordinate (actualV n)) atTop
  (𝓝 (actualFirstRead coordinate OriginalRieszSource.Response.v)) ∧
 Tendsto (fun n:Nat=>actualSecondRead coordinate (actualV n)) atTop
  (𝓝 (actualSecondRead coordinate OriginalRieszSource.Response.v)) :=
 ⟨((actualFirstRead coordinate).continuous.tendsto _).comp actual_V_source_tendsto,
  ((actualSecondRead coordinate).continuous.tendsto _).comp actual_V_source_tendsto⟩

theorem actual_first_coefficient_error_from_eta (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 ‖actualFirstRead coordinate OriginalRieszSource.Response.u-actualFirstRead coordinate (actualU n)‖≤
 ‖actualFirstRead coordinate‖*((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) :=
 (actual_first_coefficient_error coordinate n).trans
  (mul_le_mul_of_nonneg_left
   (mul_le_mul_of_nonneg_left actual_original_source_norm (by positivity)) (ContinuousLinearMap.opNorm_nonneg (actualFirstRead coordinate)))

theorem actual_second_coefficient_error_from_eta (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 ‖actualSecondRead coordinate OriginalRieszSource.Response.u-actualSecondRead coordinate (actualU n)‖≤
 ‖actualSecondRead coordinate‖*((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) :=
 (actual_second_coefficient_error coordinate n).trans
  (mul_le_mul_of_nonneg_left
   (mul_le_mul_of_nonneg_left actual_original_source_norm (by positivity)) (ContinuousLinearMap.opNorm_nonneg (actualSecondRead coordinate)))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKResponseCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
