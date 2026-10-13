import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanExteriorSourceAction.FullResponse
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanExteriorSourceAction.Moment
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

private theorem actual_exterior_response_integrable (z : ℂ) (right : 1/4<z.re)
 (shift : ℝ) (physical : BurnolPaAmbientCarrier) :
 IntegrableOn (fun time:ℝ=>star ((time:ℂ)*Complex.exp (-z*(time:ℂ)))*
   inner ℂ (burnolMultiplicativeDilation shift (actualExteriorAnnulus time)) (physical : BurnolL2)) (Ioi 0) :=by
 let reader:BurnolL2→L[ℝ]ℂ:=Complex.conjCLE.toContinuousLinearMap.comp
   ((innerSL ℂ (physical : BurnolL2)).restrictScalars ℝ)
 have integrable:=(burnolMultiplicativeDilation shift).toLinearIsometry.toContinuousLinearMap.integrable_comp
   (actual_annulus_source_integrable z right)
 have generated:=reader.integrable_comp integrable
 apply generated.congr
 filter_upwards with time
 change reader (burnolMultiplicativeDilation shift
   (((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time))=_
 have pair (field:BurnolL2):reader field=inner ℂ field (physical : BurnolL2):=inner_conj_symm field _
 rw [pair,map_smul,inner_smul_left,starRingEnd_apply]

def actualBeyondBandPrice (z : ℂ) (shift : ℝ) (physical : BurnolPaAmbientCarrier) : ℂ :=
 ∫ time:ℝ in Ioi (2*shift),star ((time:ℂ)*Complex.exp (-z*(time:ℂ)))*
   inner ℂ (burnolMultiplicativeDilation shift (actualExteriorAnnulus time)) (physical : BurnolL2)

/-- Complete original exterior response consumes its source-paid finite protected band and retains all genuine beyond-band material. -/
theorem actual_complete_exterior_response (z : ℂ) (right : 1/4<z.re) (zNonzero : z≠0)
 (rateQualified : z-1/2≠0) (shift : ℝ) (nonnegative : 0≤shift) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (burnolMultiplicativeDilation shift (Source.actualJordanSeedExterior z)) (physical : BurnolL2)=
 actualProtectedBandPrice (star z) shift physical+actualBeyondBandPrice z shift physical :=by
 rw [actual_jordan_exterior_full_response z right shift physical]
 have integrable:=actual_exterior_response_integrable z right shift physical
 have tail:=integrable.mono_set (Ioi_subset_Ioi (by linarith : (0:ℝ)≤2*shift))
 have source:=intervalIntegral.integral_interval_add_Ioi integrable tail
 rw [actual_protected_band_moment z zNonzero rateQualified shift nonnegative physical] at source
 exact source.symm

def actualExteriorFiniteEffect (z : ℂ) (shift : ℝ) : BurnolL2 :=
 burnolMultiplicativeDilation shift (Source.actualJordanSeedExterior z)-Source.actualJordanSeedExterior z

/-- Original unshifted source price is paid by the generated complete response and its real finite effect, never a free price constructor. -/
theorem actual_original_exterior_from_finite_response (z : ℂ) (right : 1/4<z.re) (zNonzero : z≠0)
 (rateQualified : z-1/2≠0) (shift : ℝ) (nonnegative : 0≤shift) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (Source.actualJordanSeedExterior z) (physical : BurnolL2)=
 actualProtectedBandPrice (star z) shift physical+actualBeyondBandPrice z shift physical-
 inner ℂ (actualExteriorFiniteEffect z shift) (physical : BurnolL2) :=by
 rw [←actual_complete_exterior_response z right zNonzero rateQualified shift nonnegative physical]
 unfold actualExteriorFiniteEffect
 rw [inner_sub_left]
 ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanExteriorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
