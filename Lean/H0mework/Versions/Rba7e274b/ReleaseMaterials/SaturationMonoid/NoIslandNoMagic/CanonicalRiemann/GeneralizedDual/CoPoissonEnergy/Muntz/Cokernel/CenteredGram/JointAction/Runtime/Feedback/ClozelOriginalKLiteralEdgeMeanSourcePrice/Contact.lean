import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKLiteralEdgeMeanSourcePrice.Input
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKLiteralEdgeMeanSourcePrice
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

def actualContactMeanRPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 star (OriginalRieszSource.Kernel.A coordinate)*actualPositionEdgeMeanRPrice observation nontrivial half h-
 star (OriginalRieszSource.Kernel.beta coordinate)*inner ℂ (OriginalRieszFiniteSource.fourierPrimitive coordinate) acted

/-- Complete contact response consumes its generated position-edge price, retaining the actual Fourier-edge cost. -/
theorem actual_contact_mean_R_price (h : ℝ) :
 inner ℂ (OriginalKSourceBalance.contactCorrection (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=
 actualContactMeanRPrice observation nontrivial half h := by
 unfold OriginalKSourceBalance.contactCorrection actualContactMeanRPrice
 simp only [inner_sub_left,inner_smul_left,starRingEnd_apply]
 rw [actual_position_edge_mean_R_price]

def actualPositionPricedKMeanRPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=(OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 show ℂ from
 (-actualKMeanInputPrice observation nontrivial half h-
   inner ℂ (OriginalKSourceBalance.contactCorrection coordinate) material-
   (coordinate.value-1/2)*actualContactMeanRPrice observation nontrivial half h+
   (1/2:ℂ)*inner ℂ (OriginalKSourceBalance.regularSource coordinate) acted)/(coordinate.value-1/2)

/-- The original K mean price now directly consumes the generated position contact source action. -/
theorem actual_position_priced_K_mean_R_price (h : ℝ) :
 OriginalKMeanReturnMixedSource.actualKMeanRPrice observation nontrivial half h=
 actualPositionPricedKMeanRPrice observation nontrivial half h := by
 unfold OriginalKMeanReturnMixedSource.actualKMeanRPrice actualPositionPricedKMeanRPrice
 dsimp only
 rw [inner_add_left]
 have input:=actual_K_mean_input_price observation nontrivial half h
 change inner ℂ
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)=
   actualKMeanInputPrice observation nontrivial half h at input
 rw [input,actual_contact_mean_R_price]
 ring



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKLiteralEdgeMeanSourcePrice
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
