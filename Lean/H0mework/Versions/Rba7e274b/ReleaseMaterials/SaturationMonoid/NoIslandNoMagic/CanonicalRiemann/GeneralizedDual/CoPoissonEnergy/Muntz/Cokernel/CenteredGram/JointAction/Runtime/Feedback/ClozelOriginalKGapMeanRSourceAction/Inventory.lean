import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapMeanRSourceAction.Field
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
local instance inventoryGapMeanRComplete : CompleteSpace BurnolPaAmbientCarrier := by
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

namespace Full
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.SourceJoint.FullStock (meanDebt)
end Full

def actualMeanGram (h : ℝ) : ℂ :=
 (∫ x : ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h x)*inner ℂ G G+
 (∫ x : ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h x)*inner ℂ G (Fphysical G)

/-- The two actual source seed masses act on the real G/F G Gram inventory. -/
theorem actual_two_seed_mean_Gram (h : ℝ) :
 Paid.actualMean (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)=
 actualMeanGram observation nontrivial half h := by
 rw [Paid.actual_mean_physical,←gapMeanVector_readback]
 unfold Full.meanDebt gapMeanAdjoint actualMeanGram
 simp only [ContinuousLinearMap.toSpanSingleton_apply,map_smul,inner_add_right,inner_smul_right]

/-- The literal two-mean source generates its own entire quarter R field. -/
theorem actual_two_mean_debt_quarter_R_field (h : ℝ) :
 burnolRadiusRestriction q (OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=
 (-actualMeanGram observation nontrivial half h/
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)) • intervalConstant q := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have source:=original_R_quarter_source_action (coordinate.value/2) right (Full.meanDebt coordinate h)
 rw [actual_two_seed_mean_Gram observation nontrivial half h] at source
 exact source

def actualMeanQuarterRField (h : ℝ) : BurnolL2 :=
 (-actualMeanGram observation nontrivial half h/
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)) •
 burnolRadiusZeroExtension q (intervalConstant q)

def actualMeanExteriorRField (h : ℝ) : BurnolL2 :=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)-
 OriginalPaPhysicalGreen.originalPhysicalCutoff q
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))

/-- The actual generated quarter field is re-embedded with its original q unit. -/
theorem actual_mean_quarter_R_source (h : ℝ) :
 OriginalPaPhysicalGreen.originalPhysicalCutoff q
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=
 actualMeanQuarterRField observation nontrivial half h := by
 have source:=congrArg (burnolRadiusZeroExtension q)
   (actual_two_mean_debt_quarter_R_field observation nontrivial half h)
 rw [map_smul] at source
 exact source

/-- Both source-generated means are paid on the quarter field; the true exterior R stock is retained. -/
theorem actual_complete_mean_R_source (h : ℝ) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)=
 actualMeanQuarterRField observation nontrivial half h+actualMeanExteriorRField observation nontrivial half h := by
 unfold actualMeanExteriorRField
 rw [←actual_mean_quarter_R_source observation nontrivial half h]
 module


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapMeanRSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
