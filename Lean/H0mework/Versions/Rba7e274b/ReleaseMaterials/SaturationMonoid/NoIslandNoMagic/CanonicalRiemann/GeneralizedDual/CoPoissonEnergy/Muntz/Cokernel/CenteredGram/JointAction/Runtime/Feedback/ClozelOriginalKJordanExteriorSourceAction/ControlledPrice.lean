import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanExteriorSourceAction.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanExteriorSourceAction
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

/-- Only an actual radius contained in the original protected q interval is priced by that physical input's original mean. -/
theorem actual_contained_radius_physical_price (radius : ℝ) (positive : 0<radius) (contained : radius≤q)
 (physical : BurnolPaAmbientCarrier) :
 inner ℂ (actualRadiusSeed radius) (physical : BurnolL2)=
 (((2*radius:ℝ):ℂ))*Paid.actualMean (physical : BurnolL2) :=by
 have subset : symmetricInterval radius⊆symmetricInterval q :=by
  intro x hx
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
 have original:=(ae_restrict_of_ae_restrict_of_subset subset (burnolAmbientGap_ae physical))
 unfold actualRadiusSeed burnolRadiusZeroExtension
 rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def]
 have source : (∫ x:ℝ,inner ℂ (intervalConstant radius x)
   (burnolRadiusRestriction radius (physical : BurnolL2) x) ∂volume.restrict (symmetricInterval radius))=
   ∫ x:ℝ,Paid.actualMean (physical : BurnolL2) ∂volume.restrict (symmetricInterval radius) :=by
  apply integral_congr_ae
  filter_upwards [intervalConstant_coeFn radius,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) (physical : BurnolL2),original]
   with x unit restricted actual
  change burnolRadiusRestriction radius (physical : BurnolL2) x=(physical : BurnolL2) x at restricted
  rw [unit,restricted,actual,FiniteMobiusResolventFlux.actual_mean_physical]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_one,mul_one]
 rw [source,integral_const]
 simp only [Measure.real,Measure.restrict_apply_univ,symmetricInterval,Real.volume_Icc]
 rw [ENNReal.toReal_ofReal (by linarith : 0≤radius- -radius)]
 rw [Complex.real_smul]
 push_cast
 ring

theorem actual_annulus_lower_endpoint_price (time shift : ℝ) (nonnegative : 0≤shift)
 (physical : BurnolPaAmbientCarrier) :
 inner ℂ (burnolMultiplicativeDilation shift (actualExteriorAnnulus time)) (physical : BurnolL2)=
 (Real.exp (shift/2):ℂ)*
 (inner ℂ (actualRadiusSeed (q*Real.exp (time/2-shift))) (physical : BurnolL2)-
 (((2*(q*Real.exp (-shift)):ℝ):ℂ))*Paid.actualMean (physical : BurnolL2)) :=by
 rw [actual_annulus_physical_action]
 rw [actual_contained_radius_physical_price (q*Real.exp (-shift))
   (mul_pos (by norm_num) (Real.exp_pos _))
   (by have small:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative);nlinarith) physical]

theorem actual_annulus_protected_band_price (time shift : ℝ) (nonnegative : 0≤shift)
 (inside : time≤2*shift) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (burnolMultiplicativeDilation shift (actualExteriorAnnulus time)) (physical : BurnolL2)=
 (Real.exp (shift/2):ℂ)*
 ((((2*(q*Real.exp (time/2-shift)):ℝ):ℂ))-(((2*(q*Real.exp (-shift)):ℝ):ℂ)))*
 Paid.actualMean (physical : BurnolL2) :=by
 rw [actual_annulus_lower_endpoint_price time shift nonnegative physical,
   actual_contained_radius_physical_price (q*Real.exp (time/2-shift)) (mul_pos (by norm_num) (Real.exp_pos _))
   (by have small:=Real.exp_le_one_iff.mpr (by linarith : time/2-shift≤0);nlinarith)]
 ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanExteriorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
