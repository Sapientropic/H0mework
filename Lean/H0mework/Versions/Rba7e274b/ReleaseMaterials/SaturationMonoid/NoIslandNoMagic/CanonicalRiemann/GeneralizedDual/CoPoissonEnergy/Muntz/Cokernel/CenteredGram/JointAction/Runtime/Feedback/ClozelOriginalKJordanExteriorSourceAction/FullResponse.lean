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

/-- Actual source integrability is transported through its own exterior restriction before any full physics response is read. -/
theorem actual_annulus_source_integrable (z : ℂ) (right : 1/4<z.re) :
 IntegrableOn (fun time:ℝ=>((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time) (Ioi 0) :=by
 let outer:BurnolL2→L[ℂ]BurnolL2:=ContinuousLinearMap.id ℂ BurnolL2-
   (burnolRadiusZeroExtension q).comp (burnolRadiusRestriction q)
 have generated:=outer.integrable_comp (Source.actual_resonant_integrable z right Source.seed)
 apply generated.congr
 filter_upwards [ae_restrict_mem measurableSet_Ioi] with time positive
 change Source.actualResonantIntegrand z Source.seed time-
   burnolRadiusZeroExtension q (burnolRadiusRestriction q (Source.actualResonantIntegrand z Source.seed time))=_
 exact actual_annulus_integrand_from_outer_projection z time positive.le

/-- Whole exterior source action preserves both moving endpoint fields and the entire source integral. -/
theorem actual_jordan_exterior_dilation_field (z : ℂ) (right : 1/4<z.re) (shift : ℝ) :
 burnolMultiplicativeDilation shift (Source.actualJordanSeedExterior z)=
 (Real.exp (shift/2):ℂ) •
  (∫ time:ℝ in Ioi 0,((time:ℂ)*Complex.exp (-z*(time:ℂ))) •
    (actualRadiusSeed (q*Real.exp (time/2-shift))-actualRadiusSeed (q*Real.exp (-shift)))) :=by
 rw [actual_jordan_exterior_from_annulus z right]
 have mapped : burnolMultiplicativeDilation shift
  (∫ time:ℝ in Ioi 0,((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time)=
  ∫ time:ℝ in Ioi 0,burnolMultiplicativeDilation shift
    (((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time) :=
  (LinearIsometry.integral_comp_comm (burnolMultiplicativeDilation shift).toLinearIsometry _).symm
 rw [mapped]
 simp_rw [map_smul,actual_annulus_dilation,smul_comm _ (Real.exp (shift/2):ℂ)]
 rw [integral_smul]

/-- Original full source action, not a protected-band-only wrapper, is independently read on the actual physical input. -/
theorem actual_jordan_exterior_full_response (z : ℂ) (right : 1/4<z.re)
 (shift : ℝ) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (burnolMultiplicativeDilation shift (Source.actualJordanSeedExterior z)) (physical : BurnolL2)=
 ∫ time:ℝ in Ioi 0,star ((time:ℂ)*Complex.exp (-z*(time:ℂ)))*
   inner ℂ (burnolMultiplicativeDilation shift (actualExteriorAnnulus time)) (physical : BurnolL2) :=by
 rw [actual_jordan_exterior_from_annulus z right]
 have mapped : burnolMultiplicativeDilation shift
  (∫ time:ℝ in Ioi 0,((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time)=
  ∫ time:ℝ in Ioi 0,burnolMultiplicativeDilation shift
    (((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time) :=
  (LinearIsometry.integral_comp_comm (burnolMultiplicativeDilation shift).toLinearIsometry _).symm
 rw [mapped]
 let reader:BurnolL2→L[ℝ]ℂ:=Complex.conjCLE.toContinuousLinearMap.comp
   ((innerSL ℂ (physical : BurnolL2)).restrictScalars ℝ)
 have integrable:=(burnolMultiplicativeDilation shift).toLinearIsometry.toContinuousLinearMap.integrable_comp
   (actual_annulus_source_integrable z right)
 have read:=(reader.integral_comp_comm integrable).symm
 have pair (field:BurnolL2) : reader field=inner ℂ field (physical : BurnolL2) :=inner_conj_symm field _
 change reader (∫ time:ℝ in Ioi 0,burnolMultiplicativeDilation shift
    (((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time))=
  ∫ time:ℝ in Ioi 0,reader (burnolMultiplicativeDilation shift
    (((time:ℂ)*Complex.exp (-z*(time:ℂ))) • actualExteriorAnnulus time)) at read
 rw [pair] at read
 rw [read]
 apply setIntegral_congr_fun measurableSet_Ioi
 intro time _
 dsimp only
 rw [pair,map_smul,inner_smul_left,starRingEnd_apply]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanExteriorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
