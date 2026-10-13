import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanExteriorSourceAction.Response
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

def actualTwoRadiusFiniteField (z : ℂ) (shift : ℝ) : BurnolL2 :=
 ∫ time:ℝ in Ioi 0,((time:ℂ)*Complex.exp (-z*(time:ℂ))) •
  ((Real.exp (shift/2):ℂ) •
    (actualRadiusSeed (q*Real.exp (time/2-shift))-actualRadiusSeed (q*Real.exp (-shift)))-
   (actualRadiusSeed (q*Real.exp (time/2))-Source.seed))

/-- Actual source action minus its original material generates this entire two-endpoint finite field. -/
theorem actual_exterior_finite_effect_field (z : ℂ) (right : 1/4<z.re) (shift : ℝ) :
 actualExteriorFiniteEffect z shift=actualTwoRadiusFiniteField z shift :=by
 unfold actualExteriorFiniteEffect actualTwoRadiusFiniteField
 rw [actual_jordan_exterior_from_annulus z right]
 have mapped : burnolMultiplicativeDilation shift
  (∫ time:ℝ in Ioi 0,((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time)=
  ∫ time:ℝ in Ioi 0,burnolMultiplicativeDilation shift
    (((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time) :=
  (LinearIsometry.integral_comp_comm (burnolMultiplicativeDilation shift).toLinearIsometry _).symm
 have old:=actual_annulus_source_integrable z right
 have new:=(burnolMultiplicativeDilation shift).toLinearIsometry.toContinuousLinearMap.integrable_comp old
 change IntegrableOn (fun time:ℝ=>burnolMultiplicativeDilation shift
   (((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time)) (Ioi 0) at new
 rw [mapped,←integral_sub new old]
 apply setIntegral_congr_fun measurableSet_Ioi
 intro time _
 dsimp only
 rw [map_smul,←smul_sub,actual_annulus_finite_effect]

/-- The original response consumes the generated full finite field, keeping all beyond-band source material. -/
theorem actual_original_exterior_generated_price (z : ℂ) (right : 1/4<z.re) (zNonzero : z≠0)
 (rateQualified : z-1/2≠0) (shift : ℝ) (nonnegative : 0≤shift) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (Source.actualJordanSeedExterior z) (physical : BurnolL2)=
 actualProtectedBandPrice (star z) shift physical+actualBeyondBandPrice z shift physical-
 inner ℂ (actualTwoRadiusFiniteField z shift) (physical : BurnolL2) :=by
 have source:=actual_original_exterior_from_finite_response z right zNonzero rateQualified shift nonnegative physical
 rw [actual_exterior_finite_effect_field z right shift] at source
 exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanExteriorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
