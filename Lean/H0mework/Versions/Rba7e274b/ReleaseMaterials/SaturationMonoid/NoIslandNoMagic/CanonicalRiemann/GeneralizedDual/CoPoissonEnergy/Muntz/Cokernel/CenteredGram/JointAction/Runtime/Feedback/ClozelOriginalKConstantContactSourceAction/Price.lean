import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantContactSourceAction.Input
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


def actualConstantContactMeanKPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=(OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 let A:=star (OriginalRieszSource.Kernel.A coordinate)
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 (A*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeU) acted-
 b*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeV) acted-
 coordinate.value*A*((1/2:ℂ)*OriginalKGapMeanRSourceAction.actualMeanGram observation nontrivial half h/(coordinate.value/2))+
 (1-coordinate.value)*b*inner ℂ (fourierL2 ConstantSource.seed) acted-
 (2:ℂ)*actualConstantContactMeanInputPrice observation nontrivial half h)/(2*coordinate.value-1)

/-- The source right-half qualification prices the original K from its true constant-contact response, without any beta/A branch. -/
theorem actual_constant_contact_K_mean_price (h : ℝ) :
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt
       (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=
 actualConstantContactMeanKPrice observation nontrivial half h := by
 have source:=actual_constant_contact_mean_source observation nontrivial half h
 dsimp only at source
 rw [actual_constant_seed_R_price,actual_constant_contact_mean_input_price] at source
 have nonzero : 2*(OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value-1≠0 := by
  intro zero
  have real:=congrArg Complex.re zero
  norm_num [Complex.sub_re,Complex.mul_re] at real
  linarith [(OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf]
 unfold actualConstantContactMeanKPrice
 dsimp only
 apply (eq_div_iff nonzero).mpr
 linear_combination source



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantContactSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
