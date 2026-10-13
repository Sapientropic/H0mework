import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPositionQuarterFTCAction.Seed
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPositionQuarterFTCAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

private theorem actual_physical_quarter_source_price (physical : BurnolPaAmbientCarrier) (material : BurnolL2) :
 inner ℂ (physical : BurnolL2) (originalPhysicalCutoff q material)=
 (1/2:ℂ)*star (Paid.actualMean (physical : BurnolL2))*Paid.actualMean material := by
 have read:=(burnolRadiusRestriction q).adjoint_inner_right (physical : BurnolL2) (burnolRadiusRestriction q material)
 change inner ℂ (physical : BurnolL2) (originalPhysicalCutoff q material)=
   inner ℂ (burnolRadiusRestriction q (physical : BurnolL2)) (burnolRadiusRestriction q material) at read
 have source : burnolRadiusRestriction q (physical : BurnolL2)=
   Paid.actualMean (physical : BurnolL2) • intervalConstant q :=
   (burnolGenericPhysicalValue_gap physical).symm
 rw [source,inner_smul_left] at read
 have normRead : (‖intervalConstant q‖:ℂ)^2=(1/2:ℂ) := by
  have paid:=burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)
  norm_num at paid
  exact paid
 have meanRead : Paid.actualMean material=(2:ℂ)*inner ℂ (intervalConstant q) (burnolRadiusRestriction q material) := by
  change ((‖intervalConstant q‖:ℂ)^2)⁻¹*inner ℂ (intervalConstant q) (burnolRadiusRestriction q material)=_
  rw [normRead]
  norm_num
 rw [read]
 simp only [starRingEnd_apply]
 linear_combination -(1/2:ℂ)*star (Paid.actualMean (physical : BurnolL2))*meanRead

def actualPositionQuarterPairPrice (h : ℝ) : ℂ :=
 (1/2:ℂ)*
 (Paid.actualMean (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)+
  Paid.actualMean (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)))*
 star (actualPositionQuarterMean observation nontrivial half h)

def actualPositionQuarterSiblingPrice (h : ℝ) : ℂ :=
 (1/2:ℂ)*
 (star (Paid.actualMean (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))-
  star (Paid.actualMean (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))))*
 actualPositionQuarterMean observation nontrivial half h

/-- The generated position quarter response is read by the original K and Fourier K physical restrictions. -/
theorem actual_position_quarter_K_prices (h : ℝ) (nonnegative : 0≤h) :
 OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
   (originalPhysicalCutoff q (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKInsideDebtRSource.actualInsidePosition observation nontrivial half h)))=
 actualPositionQuarterPairPrice observation nontrivial half h ∧
 OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
   (originalPhysicalCutoff q (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKInsideDebtRSource.actualInsidePosition observation nontrivial half h)))=
 actualPositionQuarterSiblingPrice observation nontrivial half h := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k:=burnolCompletedMellinRieszVector coordinate
 let material:=OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (OriginalKInsideDebtRSource.actualInsidePosition observation nontrivial half h)
 have first:=actual_physical_quarter_source_price k material
 have second:=actual_physical_quarter_source_price (evenFaceFourierEquiv burnolUnscaledCommonGapRadius k) material
 change inner ℂ (fourierL2 (k : BurnolL2)) (originalPhysicalCutoff q material)=
   (1/2:ℂ)*star (Paid.actualMean (fourierL2 (k : BurnolL2)))*Paid.actualMean material at second
 constructor
 · rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification]
   rw [first,second,actual_position_R_quarter_mean observation nontrivial half h nonnegative]
   unfold actualPositionQuarterPairPrice
   simp only [star_add,star_mul,star_star]
   norm_num
   ring
 · rw [OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
   rw [first,second,actual_position_R_quarter_mean observation nontrivial half h nonnegative]
   unfold actualPositionQuarterSiblingPrice
   ring

def actualPositionResidualInsideREffect (h : ℝ) : BurnolL2 :=
 OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h •
   burnolRadiusNormalizedUnitTail (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) q (by norm_num)+
 fourierL2 (FiniteMobiusResolventFlux.Rplus
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)
   (OriginalKInsideDebtRSource.actualInsideFourier observation nontrivial half h))+
 OriginalKGapMeanRSourceAction.actualMeanExteriorRField observation nontrivial half h

/-- Complete original source inventory now has generated position quarter prices and its real tail/Fourier/exterior residual. -/
theorem actual_position_price_inventory (h : ℝ) (nonnegative : 0≤h) :
 OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
   (OriginalKGapMeanRSourceAction.actualMeanResidualInsideREffect observation nontrivial half h)=
 actualPositionQuarterPairPrice observation nontrivial half h+
 OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
   (actualPositionResidualInsideREffect observation nontrivial half h) ∧
 OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
   (OriginalKGapMeanRSourceAction.actualMeanResidualInsideREffect observation nontrivial half h)=
 actualPositionQuarterSiblingPrice observation nontrivial half h+
 OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
   (actualPositionResidualInsideREffect observation nontrivial half h) := by
 have source : OriginalKGapMeanRSourceAction.actualMeanResidualInsideREffect observation nontrivial half h=
   originalPhysicalCutoff q (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKInsideDebtRSource.actualInsidePosition observation nontrivial half h))+
   actualPositionResidualInsideREffect observation nontrivial half h := by
  unfold OriginalKGapMeanRSourceAction.actualMeanResidualInsideREffect actualPositionResidualInsideREffect
  module
 rw [source]
 have prices:=actual_position_quarter_K_prices observation nontrivial half h nonnegative
 constructor
 · rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
    OriginalKPairedResponseGramAction.original_kernel_paired_qualification]
   rw [←prices.1,OriginalKPairedResponseGramAction.original_kernel_paired_qualification]
   simp only [inner_add_right,star_add]
   ring
 · rw [OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,
    OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
   rw [←prices.2,OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
   simp only [inner_add_right]
   ring

/-- Original character consumes the actual quarter FTC, original seed inventory and both K/F K prices. -/
theorem actual_position_priced_character_source (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 A*OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h=
 characterPrice*star a*star
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h+
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 star characterPrice*a*
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h-
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 characterPrice*((2*star a)*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
   A*OriginalKInsideDebtRSource.actualWavePaPairPrice observation nontrivial half h nonnegative bounded-
   A*star a*((actualPositionQuarterPairPrice observation nontrivial half h+OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
     (actualPositionResidualInsideREffect observation nontrivial half h))+OriginalKGapMeanRSourceAction.actualMeanQuarterPairPrice observation nontrivial half h))+
 star characterPrice*((2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*((actualPositionQuarterSiblingPrice observation nontrivial half h+OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
     (actualPositionResidualInsideREffect observation nontrivial half h))+OriginalKGapMeanRSourceAction.actualMeanQuarterSiblingPrice observation nontrivial half h)) := by
 have source:=OriginalKGapMeanRSourceAction.actual_mean_priced_character_source observation nontrivial half h nonnegative bounded
 have prices:=actual_position_price_inventory observation nontrivial half h nonnegative
 dsimp only at source ⊢
 rw [prices.1,prices.2] at source
 exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPositionQuarterFTCAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
