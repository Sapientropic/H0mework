import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.Foot
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
open Complex MeasureTheory Set Filter FourierTransform SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

local instance gapPricePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualFSeedRPrice (coordinate : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) : ℂ:=
 (-2/(coordinate.value-1):ℂ)*
 (star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
  inner ℂ (burnolCompletedMellinRieszVector coordinate)
   (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical)+
  (1/2:ℂ)*Paid.actualMean (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical:BurnolL2))

def actualGapRPrice (coordinate : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) : ℂ:=
 (star actualGapA*OriginalKCompactAdjointRSource.actualCompactFourierResponsePrice coordinate OriginalRieszSource.Response.wholeU physical-
 star actualGapBeta*OriginalKCompactAdjointRSource.actualCompactFourierResponsePrice coordinate OriginalRieszSource.Response.wholeV physical+
 coordinate.value*star actualGapA*(-Paid.actualMean (physical:BurnolL2)/coordinate.value)+
 (1-coordinate.value)*star actualGapBeta*actualFSeedRPrice coordinate physical-
 (2:ℂ)*actualGapCorrectedInputPrice physical)/coordinate.value

def actualFourierGapRPrice (coordinate : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) : ℂ:=
 (-star actualGapA*OriginalKCompactAdjointRSource.actualCompactFourierResponsePrice coordinate OriginalRieszSource.Response.wholeV physical+
 star actualGapBeta*OriginalKCompactAdjointRSource.actualCompactFourierResponsePrice coordinate OriginalRieszSource.Response.wholeU physical-
 (coordinate.value-1)*star actualGapA*actualFSeedRPrice coordinate physical+
 coordinate.value*star actualGapBeta*(-Paid.actualMean (physical:BurnolL2)/coordinate.value)+
 (2:ℂ)*actualFourierGapCorrectedInputPrice physical)/(1-coordinate.value)

theorem actual_gap_R_source_price (coordinate : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2)
  (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2))=actualGapRPrice coordinate physical :=by
 have source:=actual_gap_R_equation coordinate (physical:BurnolL2)
 dsimp only at source
 have U:=actual_source_quarter_R_zero coordinate OriginalRieszSource.Response.u physical
 have V:=actual_source_quarter_R_zero coordinate OriginalRieszSource.Response.v physical
 change inner ℂ OriginalRieszSource.Response.wholeU _=0 at U
 change inner ℂ OriginalRieszSource.Response.wholeV _=0 at V
 have qualified:=OriginalKCompactAdjointRSource.actual_original_UV_compact_even
 have FU:=OriginalKCompactAdjointRSource.actual_compact_F_R_source_price coordinate
  OriginalRieszSource.Response.wholeU qualified.1 qualified.2.1 physical
 have FV:=OriginalKCompactAdjointRSource.actual_compact_F_R_source_price coordinate
  OriginalRieszSource.Response.wholeV qualified.2.2.1 qualified.2.2.2 physical
 rw [inner_sub_left,inner_sub_left,U,V,FU,FV,actual_seed_R_physical_price,
  OriginalKConstantSeedWholeRAction.actual_Fconstant_seed_R_source_price,actual_gap_corrected_input] at source
 have rate:coordinate.value≠0:=by
  intro zero
  have real:=congrArg Complex.re zero
  simp only [Complex.zero_re] at real
  linarith [coordinate.rightHalf]
 unfold actualGapRPrice actualFSeedRPrice
 apply (eq_div_iff rate).mpr
 linear_combination source

theorem actual_fourier_gap_R_source_price (coordinate : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (fourierL2 (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2))
  (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2))=actualFourierGapRPrice coordinate physical :=by
 have source:=actual_fourier_gap_R_equation coordinate (physical:BurnolL2)
 dsimp only at source
 have U:=actual_source_quarter_R_zero coordinate OriginalRieszSource.Response.u physical
 have V:=actual_source_quarter_R_zero coordinate OriginalRieszSource.Response.v physical
 change inner ℂ OriginalRieszSource.Response.wholeU _=0 at U
 change inner ℂ OriginalRieszSource.Response.wholeV _=0 at V
 have qualified:=OriginalKCompactAdjointRSource.actual_original_UV_compact_even
 have FU:=OriginalKCompactAdjointRSource.actual_compact_F_R_source_price coordinate
  OriginalRieszSource.Response.wholeU qualified.1 qualified.2.1 physical
 have FV:=OriginalKCompactAdjointRSource.actual_compact_F_R_source_price coordinate
  OriginalRieszSource.Response.wholeV qualified.2.2.1 qualified.2.2.2 physical
 rw [inner_sub_left,inner_sub_left,U,V,FU,FV,actual_seed_R_physical_price,
  OriginalKConstantSeedWholeRAction.actual_Fconstant_seed_R_source_price,actual_fourier_gap_corrected_input] at source
 have rate:1-coordinate.value≠0:=by
  intro zero
  have real:=congrArg Complex.re zero
  norm_num at real
  linarith [coordinate.belowOne]
 unfold actualFourierGapRPrice actualFSeedRPrice
 apply (eq_div_iff rate).mpr
 linear_combination source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
