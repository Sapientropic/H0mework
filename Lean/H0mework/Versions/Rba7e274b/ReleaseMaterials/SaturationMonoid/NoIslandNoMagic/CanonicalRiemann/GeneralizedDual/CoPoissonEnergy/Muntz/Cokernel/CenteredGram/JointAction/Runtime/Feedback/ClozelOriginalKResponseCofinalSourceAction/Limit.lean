import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKResponseCofinalSourceAction.Control
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

/-- The actual inverse source equation pays the source norm from eta itself. -/
theorem actual_original_source_norm : ‖OriginalRieszSource.Response.u‖≤(4/3:ℝ)*‖OriginalRieszSource.Response.eta‖ :=by
 have source:=norm_add_le OriginalRieszSource.Response.eta
  (burnolMeanZeroTruncatedFourierSquare OriginalRieszSource.Response.u)
 have controlled:=actual_square_source_norm OriginalRieszSource.Response.u
 rw [←actual_original_source_fixed] at source
 linarith

theorem actual_source_error_from_eta (n : Nat) :
 ‖OriginalRieszSource.Response.u-actualU n‖≤
 (1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖) :=
 (actual_source_error_bound n).trans
  (mul_le_mul_of_nonneg_left actual_original_source_norm (by positivity))

/-- The same genuine finite source converges to the already-generated inverse source in its complete carrier. -/
theorem actual_source_tendsto : Tendsto actualU atTop (𝓝 OriginalRieszSource.Response.u) :=by
 have shrink:Tendsto (fun n:Nat=>(1/4:ℝ)^n) atTop (𝓝 0):=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
 have controlled:Tendsto (fun n:Nat=>‖OriginalRieszSource.Response.u-actualU n‖) atTop (𝓝 0):=
  squeeze_zero (fun _=>norm_nonneg _) actual_source_error_from_eta
   (by simpa using shrink.mul_const ((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖))
 apply tendsto_iff_norm_sub_tendsto_zero.mpr
 simpa only [norm_sub_rev] using controlled

theorem actual_V_source_tendsto : Tendsto actualV atTop (𝓝 OriginalRieszSource.Response.v) :=
 (burnolMeanZeroTruncatedFourier.continuous.tendsto _).comp actual_source_tendsto

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKResponseCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
