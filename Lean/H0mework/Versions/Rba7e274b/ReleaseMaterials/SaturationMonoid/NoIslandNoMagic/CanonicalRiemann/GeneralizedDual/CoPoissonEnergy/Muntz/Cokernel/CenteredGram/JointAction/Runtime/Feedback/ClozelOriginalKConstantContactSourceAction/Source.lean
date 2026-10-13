import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierRegularMeanAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RieszEulerDomain
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantContactSourceAction
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


namespace ConstantSource
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward.RieszEulerDomain (value velocity strong_derivative)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual (seed)
end ConstantSource

/-- The already-generated two-contact corrected original K and actual R share one source unitary orbit. -/
theorem actual_constant_contact_R_ward (material : BurnolL2) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 inner ℂ (ConstantSource.velocity coordinate) acted+
 inner ℂ (ConstantSource.value coordinate)
   (-(coordinate.value-1/2) • acted-(2:ℂ) • material)=0 := by
 dsimp only
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let source:=ConstantSource.value coordinate
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 have generated:=(ConstantSource.strong_derivative coordinate).inner ℂ
   (OriginalKSourceBalance.source_R_ordinary_strong observation nontrivial half material)
 have same : (fun shift : ℝ=>inner ℂ
   (burnolMultiplicativeDilation shift source) (burnolMultiplicativeDilation shift acted))=
   fun _=>inner ℂ source acted :=funext fun shift=>(burnolMultiplicativeDilation shift).inner_map_map _ _
 change HasDerivAt (fun shift : ℝ=>inner ℂ
   (burnolMultiplicativeDilation shift source) (burnolMultiplicativeDilation shift acted)) _ 0 at generated
 rw [same] at generated
 have zero:=generated.unique (hasDerivAt_const (0:ℝ) (inner ℂ source acted))
 simp only [burnolMultiplicativeDilation_zero] at zero
 change inner ℂ (ConstantSource.value coordinate)
   (-(observation.coordinate-1/2) • acted-(2:ℂ) • material)+
   inner ℂ (ConstantSource.velocity coordinate) acted=0 at zero
 change inner ℂ (ConstantSource.velocity coordinate) acted+
   inner ℂ (ConstantSource.value coordinate)
   (-(coordinate.value-1/2) • acted-(2:ℂ) • material)=0
 have coordinateRead : coordinate.value=observation.coordinate := rfl
 rw [coordinateRead]
 linear_combination zero

/-- Original K is recovered from the same generated field with both actual constant-contact source stocks. -/
theorem actual_constant_contact_K_R_source (material : BurnolL2) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 let A:=star (OriginalRieszSource.Kernel.A coordinate)
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 (2*coordinate.value-1)*inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) acted=
 A*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeU-OriginalRieszSource.Response.wholeV) acted+
 b*inner ℂ (OriginalRieszSource.Response.wholeU-fourierL2 OriginalRieszSource.Response.wholeV) acted+
 coordinate.value*A*inner ℂ ConstantSource.seed acted+
 (1-coordinate.value)*b*inner ℂ (fourierL2 ConstantSource.seed) acted-
 (2:ℂ)*inner ℂ (ConstantSource.value coordinate) material := by
 dsimp only
 have source:=actual_constant_contact_R_ward observation nontrivial half material
 dsimp only at source
 unfold ConstantSource.value ConstantSource.velocity at source
 simp only [inner_add_left,inner_sub_left,inner_smul_left,starRingEnd_apply,
   inner_sub_right,inner_smul_right,star_neg,star_sub,star_div₀,star_mul,star_ofNat,star_one,star_star] at source
 unfold ConstantSource.value
 simp only [inner_add_left,inner_sub_left,inner_smul_left,starRingEnd_apply]
 linear_combination -source



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantContactSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
