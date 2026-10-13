import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanExteriorSourceAction.Annulus
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

/-- Paid native gap-Riesz action keeps the real radius seed unit and generates both actual endpoints of every annulus. -/
theorem actual_radius_seed_dilation (radius : ℝ) (positive : 0<radius) (shift : ℝ) :
 burnolMultiplicativeDilation shift (actualRadiusSeed radius)=
 (Real.exp (shift/2):ℂ) • actualRadiusSeed (radius*Real.exp (-shift)) :=by
 rw [actual_radius_seed_gap_source radius positive,map_smul,
   burnolAmbientGapRiesz_dilation positive,
   actual_radius_seed_gap_source _ (mul_pos positive (Real.exp_pos _)),smul_smul,smul_smul]
 congr 1
 have phase : Real.exp (shift/2)*Real.exp (-shift)=Real.exp (-shift/2) :=by
  rw [←Real.exp_add]
  congr 1
  ring
 have coefficient : (2*radius)*Real.exp (-shift/2)=
   Real.exp (shift/2)*(2*(radius*Real.exp (-shift))) :=by
  rw [←phase]
  ring
 exact_mod_cast coefficient

/-- The actual exterior annulus action is a two-radius source field, preserving its moved inner endpoint. -/
theorem actual_annulus_dilation (time shift : ℝ) :
 burnolMultiplicativeDilation shift (actualExteriorAnnulus time)=
 (Real.exp (shift/2):ℂ) •
 (actualRadiusSeed (q*Real.exp (time/2-shift))-
   actualRadiusSeed (q*Real.exp (-shift))) :=by
 unfold actualExteriorAnnulus
 rw [map_sub,actual_radius_seed_dilation _ (mul_pos (by norm_num) (Real.exp_pos _))]
 change _-burnolMultiplicativeDilation shift (actualRadiusSeed q)=_
 rw [actual_radius_seed_dilation q (by norm_num),←smul_sub,mul_assoc,←Real.exp_add]
 rw [show time/2+-shift=time/2-shift by ring]

/-- The same generated annulus field gives its actual finite source difference, before any physical reader. -/
theorem actual_annulus_finite_effect (time shift : ℝ) :
 burnolMultiplicativeDilation shift (actualExteriorAnnulus time)-actualExteriorAnnulus time=
 (Real.exp (shift/2):ℂ) •
 (actualRadiusSeed (q*Real.exp (time/2-shift))-actualRadiusSeed (q*Real.exp (-shift)))-
 (actualRadiusSeed (q*Real.exp (time/2))-Source.seed) :=by
 rw [actual_annulus_dilation]
 rfl

/-- Both endpoints are paid by the same actual finite effect; no source physical membership or zero price is assumed. -/
theorem actual_annulus_physical_action (time shift : ℝ) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (burnolMultiplicativeDilation shift (actualExteriorAnnulus time)) (physical : BurnolL2)=
 (Real.exp (shift/2):ℂ)*
 (inner ℂ (actualRadiusSeed (q*Real.exp (time/2-shift))) (physical : BurnolL2)-
   inner ℂ (actualRadiusSeed (q*Real.exp (-shift))) (physical : BurnolL2)) :=by
 rw [actual_annulus_dilation,inner_smul_left,inner_sub_left]
 rw [Complex.conj_ofReal]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanExteriorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
