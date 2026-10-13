import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanExteriorSourceAction.ControlledPrice
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

elab "source182FinitePrimitive" : term => do
 let head:=("_private.H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanSeedFieldSource.Coefficient".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full:=("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanSeedFieldSource.actual_exponential_primitive_derivative".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full

def actualScalarMoment (z : ℂ) (endpoint : ℝ) : ℂ :=
 1/z^2-(endpoint/z+1/z^2)*Complex.exp (-z*(endpoint:ℂ))

/-- Existing actual source primitive generates the finite moment before protected-band physical pricing. -/
theorem actual_finite_scalar_moment (z : ℂ) (qualified : z≠0) (endpoint : ℝ) :
 (∫ time:ℝ in (0:ℝ)..endpoint,(time:ℂ)*Complex.exp (-z*(time:ℂ)))=
 actualScalarMoment z endpoint :=by
 have source:=intervalIntegral.integral_eq_sub_of_hasDerivAt
   (fun time _=>source182FinitePrimitive z qualified time)
   ((show Continuous (fun time:ℝ=>(time:ℂ)*Complex.exp (-z*(time:ℂ))) by fun_prop).intervalIntegrable 0 endpoint)
 change (∫ time:ℝ in (0:ℝ)..endpoint,(time:ℂ)*Complex.exp (-z*(time:ℂ)))=
  -(endpoint/z+1/z^2)*Complex.exp (-z*(endpoint:ℂ))-
  -((0:ℂ)/z+1/z^2)*Complex.exp (-z*(0:ℂ)) at source
 unfold actualScalarMoment
 rw [source]
 simp only [zero_div,zero_add,mul_zero,Complex.exp_zero,mul_one]
 ring

def actualProtectedBandPrice (z : ℂ) (shift : ℝ) (physical : BurnolPaAmbientCarrier) : ℂ :=
 (((2*q:ℝ):ℂ)*(Real.exp (-shift/2):ℂ))*Paid.actualMean (physical : BurnolL2)*
 (actualScalarMoment (z-1/2) (2*shift)-actualScalarMoment z (2*shift))

/-- Both real source radii remain within q on this finite band; their actual mean price is generated from the original source action. -/
theorem actual_protected_band_moment (z : ℂ) (zNonzero : z≠0) (rateQualified : z-1/2≠0)
 (shift : ℝ) (nonnegative : 0≤shift) (physical : BurnolPaAmbientCarrier) :
 (∫ time:ℝ in (0:ℝ)..2*shift,
    star ((time:ℂ)*Complex.exp (-z*(time:ℂ)))*
      inner ℂ (burnolMultiplicativeDilation shift (actualExteriorAnnulus time)) (physical : BurnolL2))=
 actualProtectedBandPrice (star z) shift physical :=by
 have pointwise : ∀ (time:ℝ),time∈Set.uIoc (0:ℝ) (2*shift) →
   star ((time:ℂ)*Complex.exp (-z*(time:ℂ)))*
    inner ℂ (burnolMultiplicativeDilation shift (actualExteriorAnnulus time)) (physical : BurnolL2)=
   (((2*q:ℝ):ℂ)*(Real.exp (-shift/2):ℂ))*Paid.actualMean (physical : BurnolL2)*
    ((time:ℂ)*Complex.exp (-(star z-1/2)*(time:ℂ))-
     (time:ℂ)*Complex.exp (-star z*(time:ℂ))) :=by
  intro time inside
  have bound : time≤2*shift :=by
   rw [uIoc_of_le (by linarith : (0:ℝ)≤2*shift)] at inside
   exact inside.2
  rw [actual_annulus_protected_band_price time shift nonnegative bound physical]
  have phase : star (Complex.exp (-z*(time:ℂ)))=Complex.exp (-star z*(time:ℂ)) :=by
   rw [←starRingEnd_apply,←Complex.exp_conj]
   congr 1
   simp only [map_mul,map_neg,Complex.conj_ofReal]
   rfl
  rw [star_mul,phase]
  have timeReal : star (time:ℂ)=(time:ℂ):=by simp only [Complex.star_def,Complex.conj_ofReal]
  rw [timeReal]
  push_cast
  have firstPhase : Complex.exp (-star z*(time:ℂ))*Complex.exp ((shift:ℂ)/2)*
    Complex.exp ((time:ℂ)/2-shift)=
    Complex.exp (-(shift:ℂ)/2)*Complex.exp (-(star z-1/2)*(time:ℂ)) :=by
   rw [←Complex.exp_add,←Complex.exp_add,←Complex.exp_add]
   congr 1
   ring
  have secondPhase : Complex.exp ((shift:ℂ)/2)*Complex.exp (-(shift:ℂ))=
    Complex.exp (-(shift:ℂ)/2) :=by
   rw [←Complex.exp_add]
   congr 1
   ring
  calc
   _=(((2*q:ℝ):ℂ)*Paid.actualMean (physical : BurnolL2)*(time:ℂ))*
     (Complex.exp (-star z*(time:ℂ))*Complex.exp ((shift:ℂ)/2)*
       Complex.exp ((time:ℂ)/2-shift)-
      Complex.exp (-star z*(time:ℂ))*(Complex.exp ((shift:ℂ)/2)*Complex.exp (-(shift:ℂ)))) :=by
      push_cast
      ring
   _=_:=by
    rw [firstPhase,secondPhase]
    push_cast
    ring
 have continuous (w:ℂ) : Continuous (fun time:ℝ=>(time:ℂ)*Complex.exp (-w*(time:ℂ))) :=by fun_prop
 rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall pointwise),intervalIntegral.integral_const_mul,
   intervalIntegral.integral_sub ((continuous _).intervalIntegrable _ _) ((continuous _).intervalIntegrable _ _),
   actual_finite_scalar_moment (star z-1/2) (by simpa only [star_sub,star_div₀,star_one,star_ofNat,star_star] using star_ne_zero.mpr rateQualified),
   actual_finite_scalar_moment (star z) (star_ne_zero.mpr zNonzero)]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanExteriorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
