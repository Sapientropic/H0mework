import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierRegularMeanAction.Quarter
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierRegularMeanAction
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

/-- The literal Fourier edge returns to the original position edge through its own source parity. -/
theorem actual_fourier_edge_returns (coordinate : BurnolCompletedMellinCoordinate) :
 fourierL2 (OriginalRieszFiniteSource.fourierPrimitive coordinate)=OriginalRieszFiniteSource.edgePrimitive coordinate := by
 change fourierL2 (fourierL2 (OriginalRieszFiniteSource.edgePrimitive coordinate))=_
 rw [fourierL2_fourierL2]
 unfold OriginalRieszFiniteSource.edgePrimitive
 rw [map_smul,burnolAmbientEvenPart_even]

def actualFourierCorrectedMeanInputPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 inner ℂ (fourierL2 (OriginalKSourceBalance.correctedField coordinate))
   (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)

/-- Real A/beta coupling consumes the generated position edge response; no determinant branch is assumed. -/
theorem actual_generated_source_matrix (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 star (OriginalRieszSource.Kernel.A coordinate)*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeV) acted-
 star (OriginalRieszSource.Kernel.beta coordinate)*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeU) acted+
 (2*(coordinate.value-1/2)*star (OriginalRieszSource.Kernel.beta coordinate))*
   OriginalKLiteralEdgeMeanSourcePrice.actualPositionEdgeMeanRPrice observation nontrivial half h=
 (2:ℂ)*actualFourierCorrectedMeanInputPrice observation nontrivial half h := by
 have source:=actual_Fourier_regular_mean_coupling observation nontrivial half h
 dsimp only at source ⊢
 rw [actual_fourier_edge_returns,OriginalKLiteralEdgeMeanSourcePrice.actual_position_edge_mean_R_price] at source
 simp only [star_mul,star_sub,star_ofNat,star_div₀,star_one,star_star] at source
 unfold actualFourierCorrectedMeanInputPrice
 linear_combination source

/-- One remaining response channel is eliminated without division by beta or A. -/
theorem actual_weighted_regular_mean_R_price (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 star (OriginalRieszSource.Kernel.beta coordinate)*
   inner ℂ (OriginalKSourceBalance.regularSource coordinate) acted=
 (star (OriginalRieszSource.Kernel.A coordinate)^2-star (OriginalRieszSource.Kernel.beta coordinate)^2)*
   inner ℂ (fourierL2 OriginalRieszSource.Response.wholeV) acted+
 (2*(coordinate.value-1/2)*star (OriginalRieszSource.Kernel.A coordinate)*
   star (OriginalRieszSource.Kernel.beta coordinate))*
   OriginalKLiteralEdgeMeanSourcePrice.actualPositionEdgeMeanRPrice observation nontrivial half h-
 (2*star (OriginalRieszSource.Kernel.A coordinate))*actualFourierCorrectedMeanInputPrice observation nontrivial half h-
 (2*(coordinate.value-1/2)*star (OriginalRieszSource.Kernel.beta coordinate)^2)*
   inner ℂ (OriginalRieszFiniteSource.fourierPrimitive coordinate) acted := by
 dsimp only
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 have coupled:=actual_generated_source_matrix observation nontrivial half h
 have prices:=actual_original_UV_R_prices observation nontrivial half h
 dsimp only at coupled
 have regular : inner ℂ (OriginalKSourceBalance.regularSource coordinate) acted=
   star (OriginalRieszSource.Kernel.A coordinate)*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeU) acted-
   star (OriginalRieszSource.Kernel.beta coordinate)*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeV) acted-
   (2*(coordinate.value-1/2)*star (OriginalRieszSource.Kernel.beta coordinate))*
     inner ℂ (OriginalRieszFiniteSource.fourierPrimitive coordinate) acted := by
  unfold OriginalKSourceBalance.regularSource
  simp only [inner_sub_left,inner_add_left,inner_smul_left,starRingEnd_apply]
  rw [prices.1,prices.2]
  simp only [star_mul,star_sub,star_ofNat,star_div₀,star_one,star_star]
  ring
 rw [regular]
 linear_combination -(star (OriginalRieszSource.Kernel.A coordinate))*coupled



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierRegularMeanAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
