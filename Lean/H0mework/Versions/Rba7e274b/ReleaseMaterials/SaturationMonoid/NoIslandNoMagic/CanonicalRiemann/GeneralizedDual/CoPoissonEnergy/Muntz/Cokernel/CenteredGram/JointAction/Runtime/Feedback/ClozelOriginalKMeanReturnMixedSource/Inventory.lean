import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMeanReturnMixedSource.Price
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMeanReturnMixedSource
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

/-- The generated full mean action consumes the actual quarter/exterior split; no exterior stock is erased. -/
theorem actual_full_mean_price_inventory (h : ℝ) :
 OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
   (OriginalKGapMeanRSourceAction.actualMeanExteriorRField observation nontrivial half h)+
   OriginalKGapMeanRSourceAction.actualMeanQuarterPairPrice observation nontrivial half h=
 actualFullMeanPairPrice observation nontrivial half h ∧
 OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
   (OriginalKGapMeanRSourceAction.actualMeanExteriorRField observation nontrivial half h)+
   OriginalKGapMeanRSourceAction.actualMeanQuarterSiblingPrice observation nontrivial half h=
 actualFullMeanSiblingPrice observation nontrivial half h := by
 have complete:=OriginalKGapMeanRSourceAction.actual_complete_mean_R_source observation nontrivial half h
 have quarter:=OriginalKGapMeanRSourceAction.actual_mean_quarter_K_prices observation nontrivial half h
 have prices:=actual_full_mean_R_source_prices observation nontrivial half h
 constructor
 · have source:=congrArg (OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half) complete
   rw [prices.1] at source
   have linear : OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
     (OriginalKGapMeanRSourceAction.actualMeanQuarterRField observation nontrivial half h+
       OriginalKGapMeanRSourceAction.actualMeanExteriorRField observation nontrivial half h)=
     OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
       (OriginalKGapMeanRSourceAction.actualMeanQuarterRField observation nontrivial half h)+
     OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
       (OriginalKGapMeanRSourceAction.actualMeanExteriorRField observation nontrivial half h) := by
    rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
      OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
      OriginalKPairedResponseGramAction.original_kernel_paired_qualification]
    simp only [inner_add_right,star_add]
    ring
   rw [linear,quarter.1] at source
   linear_combination -source
 · have source:=congrArg (OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half) complete
   rw [prices.2] at source
   have linear : OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
     (OriginalKGapMeanRSourceAction.actualMeanQuarterRField observation nontrivial half h+
       OriginalKGapMeanRSourceAction.actualMeanExteriorRField observation nontrivial half h)=
     OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
       (OriginalKGapMeanRSourceAction.actualMeanQuarterRField observation nontrivial half h)+
     OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
       (OriginalKGapMeanRSourceAction.actualMeanExteriorRField observation nontrivial half h) := by
    rw [OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,
      OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,
      OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
    simp only [inner_add_right]
    ring
   rw [linear,quarter.2] at source
   linear_combination -source



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMeanReturnMixedSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
