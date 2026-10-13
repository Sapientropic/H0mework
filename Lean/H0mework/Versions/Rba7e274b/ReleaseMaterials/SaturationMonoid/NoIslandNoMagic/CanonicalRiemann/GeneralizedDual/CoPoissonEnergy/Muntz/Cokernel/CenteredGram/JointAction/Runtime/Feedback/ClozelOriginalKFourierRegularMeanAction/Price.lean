import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierRegularMeanAction.Matrix
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

def actualWeightedRegularMeanRPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 (star (OriginalRieszSource.Kernel.A coordinate)^2-star (OriginalRieszSource.Kernel.beta coordinate)^2)*
   inner ℂ (fourierL2 OriginalRieszSource.Response.wholeV) acted+
 (2*(coordinate.value-1/2)*star (OriginalRieszSource.Kernel.A coordinate)*
   star (OriginalRieszSource.Kernel.beta coordinate))*
   OriginalKLiteralEdgeMeanSourcePrice.actualPositionEdgeMeanRPrice observation nontrivial half h-
 (2*star (OriginalRieszSource.Kernel.A coordinate))*actualFourierCorrectedMeanInputPrice observation nontrivial half h-
 (2*(coordinate.value-1/2)*star (OriginalRieszSource.Kernel.beta coordinate)^2)*
   inner ℂ (OriginalRieszFiniteSource.fourierPrimitive coordinate) acted

def actualWeightedKMeanRPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=(OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 show ℂ from
 (-b*OriginalKLiteralEdgeMeanSourcePrice.actualKMeanInputPrice observation nontrivial half h-
   b*inner ℂ (OriginalKSourceBalance.contactCorrection coordinate) material-
   (coordinate.value-1/2)*b*OriginalKLiteralEdgeMeanSourcePrice.actualContactMeanRPrice observation nontrivial half h+
   (1/2:ℂ)*actualWeightedRegularMeanRPrice observation nontrivial half h)/(coordinate.value-1/2)

/-- The source-generated weighted regular price is consumed inside the original K action, including beta=0. -/
theorem actual_weighted_K_mean_R_price (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 star (OriginalRieszSource.Kernel.beta coordinate)*
 OriginalKLiteralEdgeMeanSourcePrice.actualPositionPricedKMeanRPrice observation nontrivial half h=
 actualWeightedKMeanRPrice observation nontrivial half h := by
 dsimp only
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 have regular:=actual_weighted_regular_mean_R_price observation nontrivial half h
 change b*inner ℂ (OriginalKSourceBalance.regularSource coordinate)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2))=
   actualWeightedRegularMeanRPrice observation nontrivial half h at regular
 unfold OriginalKLiteralEdgeMeanSourcePrice.actualPositionPricedKMeanRPrice actualWeightedKMeanRPrice
 dsimp only
 rw [←mul_div_assoc]
 congr 1
 linear_combination (1/2:ℂ)*regular

/-- Both character legs consume this actual weighted source action with their own star units. -/
theorem actual_weighted_mean_price_faces (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 let kp:=OriginalKLiteralEdgeMeanSourcePrice.actualPositionPricedKMeanRPrice observation nontrivial half h
 let fp:=inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2))
 (b*star b)*star (kp+fp)=b*star (actualWeightedKMeanRPrice observation nontrivial half h+b*fp) ∧
 (b*star b)*(kp-fp)=star b*(actualWeightedKMeanRPrice observation nontrivial half h-b*fp) := by
 dsimp only
 have source:=actual_weighted_K_mean_R_price observation nontrivial half h
 dsimp only at source
 constructor
 · rw [←source,←mul_add,star_mul]
   ring
 · rw [←source]
   ring



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierRegularMeanAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
