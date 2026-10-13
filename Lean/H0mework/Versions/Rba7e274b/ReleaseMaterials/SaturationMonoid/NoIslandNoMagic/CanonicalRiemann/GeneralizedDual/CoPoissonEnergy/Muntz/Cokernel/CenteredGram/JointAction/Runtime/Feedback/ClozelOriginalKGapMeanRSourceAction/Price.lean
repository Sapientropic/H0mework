import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapMeanRSourceAction.Inventory
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapMeanRSourceAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFiniteSynthesis
local instance priceGapMeanRComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean source_negative_restriction actual_mean_source_negative actual_mean_physical)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (source_weight_mean_phase source_mean_R_read)
end Paid
local notation "q" => (1/4:ℝ)
local notation "G" => gapMeanVector
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualMeanGeneratedInsideREffect (h : ℝ) : BurnolL2 :=
 OriginalPaPhysicalGreen.originalPhysicalCutoff q
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (OriginalKInsideDebtRSource.actualInsidePosition observation nontrivial half h))+
 OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h •
   burnolRadiusNormalizedUnitTail (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) q (by norm_num)+
 fourierL2 (FiniteMobiusResolventFlux.Rplus
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)
   (OriginalKInsideDebtRSource.actualInsideFourier observation nontrivial half h))+
 (actualMeanQuarterRField observation nontrivial half h+actualMeanExteriorRField observation nontrivial half h)

/-- The original inside source consumer now reads the actual mean-generated field and its full retained outside cost. -/
theorem actual_mean_generated_inside_R_effect (h : ℝ) :
 OriginalKInsideDebtRSource.actualInsideNativeREffect observation nontrivial half h=
 actualMeanGeneratedInsideREffect observation nontrivial half h := by
 unfold OriginalKInsideDebtRSource.actualInsideNativeREffect actualMeanGeneratedInsideREffect
 rw [actual_complete_mean_R_source observation nontrivial half h]

/-- The actual character price directly consumes the new source mean field; no full-field price is erased. -/
theorem actual_mean_generated_character_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
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
   A*star a*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
     (actualMeanGeneratedInsideREffect observation nontrivial half h))+
 star characterPrice*((2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
     (actualMeanGeneratedInsideREffect observation nontrivial half h)) := by
 have source:=OriginalKInsideDebtRSource.actual_rank_generated_character_price observation nontrivial half h nonnegative bounded
 rw [actual_mean_generated_inside_R_effect observation nontrivial half h] at source
 exact source


private theorem quarter_unit_physical_read (material : BurnolL2) :
 inner ℂ material (burnolRadiusZeroExtension q (intervalConstant q))=
 (1/2:ℂ)*star (Paid.actualMean material) := by
 have read:=(burnolRadiusRestriction q).adjoint_inner_right material (intervalConstant q)
 change inner ℂ material (burnolRadiusZeroExtension q (intervalConstant q))=
   inner ℂ (burnolRadiusRestriction q material) (intervalConstant q) at read
 have normRead : (‖intervalConstant q‖:ℂ)^2=(1/2:ℂ) := by
  have paid:=burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)
  norm_num at paid
  exact paid
 have mean : Paid.actualMean material=(2:ℂ)*inner ℂ (intervalConstant q) (burnolRadiusRestriction q material) := by
  change ((‖intervalConstant q‖:ℂ)^2)⁻¹*inner ℂ (intervalConstant q) (burnolRadiusRestriction q material)=_
  rw [normRead]
  norm_num
 rw [read,mean]
 rw [←inner_conj_symm (𝕜:=ℂ) (intervalConstant q) (burnolRadiusRestriction q material)]
 simp only [star_mul,star_ofNat]
 norm_num
 ring

def actualMeanQuarterCoefficient (h : ℝ) : ℂ :=
 -actualMeanGram observation nontrivial half h/
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)

def actualMeanQuarterPairPrice (h : ℝ) : ℂ :=
 star (actualMeanQuarterCoefficient observation nontrivial half h)*(1/2:ℂ)*
 (Paid.actualMean (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)+
  Paid.actualMean (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)))

def actualMeanQuarterSiblingPrice (h : ℝ) : ℂ :=
 actualMeanQuarterCoefficient observation nontrivial half h*(1/2:ℂ)*
 (star (Paid.actualMean (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))-
  star (Paid.actualMean (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))))

/-- The same generated quarter field is priced by original K and Fourier K using their actual physical gap restriction. -/
theorem actual_mean_quarter_K_prices (h : ℝ) :
 OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
   (actualMeanQuarterRField observation nontrivial half h)=actualMeanQuarterPairPrice observation nontrivial half h ∧
 OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
   (actualMeanQuarterRField observation nontrivial half h)=actualMeanQuarterSiblingPrice observation nontrivial half h := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k:=burnolCompletedMellinRieszVector coordinate
 have first:=quarter_unit_physical_read (k : BurnolL2)
 have second:=quarter_unit_physical_read (Fphysical k : BurnolL2)
 change inner ℂ (fourierL2 (k : BurnolL2)) (burnolRadiusZeroExtension q (intervalConstant q))=
   (1/2:ℂ)*star (Paid.actualMean (fourierL2 (k : BurnolL2))) at second
 constructor
 · rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification]
   unfold actualMeanQuarterRField actualMeanQuarterPairPrice actualMeanQuarterCoefficient
   simp only [inner_smul_right]
   rw [first,second]
   simp only [star_add,star_mul,star_star]
   norm_num
   ring
 · rw [OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
   unfold actualMeanQuarterRField actualMeanQuarterSiblingPrice actualMeanQuarterCoefficient
   simp only [inner_smul_right]
   rw [first,second]
   ring

def actualMeanResidualInsideREffect (h : ℝ) : BurnolL2 :=
 OriginalPaPhysicalGreen.originalPhysicalCutoff q
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (OriginalKInsideDebtRSource.actualInsidePosition observation nontrivial half h))+
 OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h •
   burnolRadiusNormalizedUnitTail (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) q (by norm_num)+
 fourierL2 (FiniteMobiusResolventFlux.Rplus
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)
   (OriginalKInsideDebtRSource.actualInsideFourier observation nontrivial half h))+
 actualMeanExteriorRField observation nontrivial half h

/-- The source-generated scalar quarter price and the real residual together consume the full original inside response. -/
theorem actual_inside_mean_price_inventory (h : ℝ) :
 OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
   (actualMeanGeneratedInsideREffect observation nontrivial half h)=
 OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
   (actualMeanResidualInsideREffect observation nontrivial half h)+actualMeanQuarterPairPrice observation nontrivial half h ∧
 OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
   (actualMeanGeneratedInsideREffect observation nontrivial half h)=
 OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
   (actualMeanResidualInsideREffect observation nontrivial half h)+actualMeanQuarterSiblingPrice observation nontrivial half h := by
 have source : actualMeanGeneratedInsideREffect observation nontrivial half h=
   actualMeanResidualInsideREffect observation nontrivial half h+actualMeanQuarterRField observation nontrivial half h := by
  unfold actualMeanGeneratedInsideREffect actualMeanResidualInsideREffect
  module
 have pair (left right : BurnolL2) :
   OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half (left+right)=
   OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half left+
   OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half right := by
  rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
    OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
    OriginalKPairedResponseGramAction.original_kernel_paired_qualification]
  simp only [inner_add_right,star_add]
  ring
 have sibling (left right : BurnolL2) :
   OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half (left+right)=
   OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half left+
   OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half right := by
  rw [OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,
    OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,
    OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
  simp only [inner_add_right]
  ring
 rw [source,pair,sibling]
 have prices:=actual_mean_quarter_K_prices observation nontrivial half h
 rw [prices.1,prices.2]
 exact ⟨rfl,rfl⟩

/-- Original character directly consumes both actual K/F K mean prices and the retained residual source. -/
theorem actual_mean_priced_character_source (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
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
   A*star a*(OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
     (actualMeanResidualInsideREffect observation nontrivial half h)+actualMeanQuarterPairPrice observation nontrivial half h))+
 star characterPrice*((2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*(OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
     (actualMeanResidualInsideREffect observation nontrivial half h)+actualMeanQuarterSiblingPrice observation nontrivial half h)) := by
 have source:=actual_mean_generated_character_price observation nontrivial half h nonnegative bounded
 have prices:=actual_inside_mean_price_inventory observation nontrivial half h
 dsimp only at source ⊢
 rw [prices.1,prices.2] at source
 exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapMeanRSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
