import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanSeedFieldSource.Consumer
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

namespace Source
export OriginalKJordanSeedFieldSource (actual_seed_dilation_source actual_jordan_seed_integrand_source actual_jordan_seed_integrand_quarter actual_jordan_seed_exact_quarter_field actualJordanSeedExterior)
export OriginalKJordanSeedFieldSource.J (actualResonantIntegrand actualResonantField actual_resonant_integrable seed)
end Source

def actualRadiusSeed (radius : ℝ) : BurnolL2 :=
 burnolRadiusZeroExtension radius (intervalConstant radius)

def actualExteriorAnnulus (time : ℝ) : BurnolL2 :=
 actualRadiusSeed (q*Real.exp (time/2))-Source.seed

/-- The original radius unit is recovered from the same native gap-Riesz source norm, not substituted by equal prices. -/
theorem actual_radius_seed_gap_source (radius : ℝ) (positive : 0<radius) :
 actualRadiusSeed radius=(((2*radius:ℝ):ℂ)) • burnolAmbientGapRieszVector radius :=by
 unfold burnolAmbientGapRieszVector actualRadiusSeed
 rw [burnolIntervalConstant_norm_sq positive,smul_smul]
 have qualified : (((2*radius:ℝ):ℂ))≠0:=by exact_mod_cast (ne_of_gt (by positivity : 0<2*radius))
 rw [star_inv₀,←starRingEnd_apply,Complex.conj_ofReal,mul_inv_cancel₀ qualified,one_smul]
 rfl

/-- The whole original negative source action genuinely generates the expanding interval seed. -/
theorem actual_seed_expanding_radius_source (time : ℝ) :
 burnolMultiplicativeDilation (-time/2) Source.seed=
 (Real.exp (-time/4):ℂ) • actualRadiusSeed (q*Real.exp (time/2)) :=by
 rw [Source.actual_seed_dilation_source,
   actual_radius_seed_gap_source _ (mul_pos (by norm_num) (Real.exp_pos _)),smul_smul]
 rw [show -(-time/2)/2=time/4 by ring,show -(-time/2)=time/2 by ring]
 congr 1
 have coefficient : (2*q)*Real.exp (time/4)=Real.exp (-time/4)*(2*(q*Real.exp (time/2))) :=by
  have phase : Real.exp (-time/4)*Real.exp (time/2)=Real.exp (time/4) :=by
   rw [←Real.exp_add]
   congr 1
   ring
  nlinarith only [phase]
 exact_mod_cast coefficient

/-- The same literal J integrand generates the entire expanding annulus stock, before any exterior moment is read. -/
theorem actual_jordan_seed_annulus_integrand (z : ℂ) (time : ℝ) :
 Source.actualResonantIntegrand z Source.seed time=
 ((time:ℂ)*Complex.exp (-z*(time:ℂ))) • (Source.seed+actualExteriorAnnulus time) :=by
 unfold Source.actualResonantIntegrand burnolDirectRightResolventIntegrand
 rw [actual_seed_expanding_radius_source,←algebraMap_smul ℂ time,smul_smul,smul_smul,mul_assoc,
   Paid.source_weight_mean_phase]
 unfold actualExteriorAnnulus
 module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanExteriorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
