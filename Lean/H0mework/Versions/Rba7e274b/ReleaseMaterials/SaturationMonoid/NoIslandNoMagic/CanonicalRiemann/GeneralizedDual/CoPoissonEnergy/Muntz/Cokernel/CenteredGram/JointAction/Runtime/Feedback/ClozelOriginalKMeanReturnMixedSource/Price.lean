import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMeanReturnMixedSource.Action
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

theorem actual_return_rate_ne_zero (coordinate : BurnolCompletedMellinCoordinate) :
 coordinate.value-1/2≠0 := by
 intro zero
 have real:=congrArg Complex.re zero
 simp only [Complex.sub_re] at real
 norm_num at real
 linarith [coordinate.rightHalf]

def actualKMeanRPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k:=(burnolCompletedMellinRieszVector coordinate : BurnolL2)
 let material:=(OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half material
 let contact:=OriginalKSourceBalance.contactCorrection coordinate
 let regular:=OriginalKSourceBalance.regularSource coordinate
 show ℂ from
 (-inner ℂ (k+contact) material-(coordinate.value-1/2)*inner ℂ contact acted+
   (1/2:ℂ)*inner ℂ regular acted)/(coordinate.value-1/2)

/-- The actual complete G/F G source is priced by its original corrected/contact/regular stocks, not an independent K response input. -/
theorem actual_K_mean_R_source_price (h : ℝ) :
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=
 actualKMeanRPrice observation nontrivial half h := by
 have source:=actual_K_material_R_source_action observation nontrivial half
   (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)
 dsimp only at source
 unfold actualKMeanRPrice
 dsimp only
 apply (eq_div_iff (actual_return_rate_ne_zero
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))).mpr
 linear_combination source

def actualFullMeanPairPrice (h : ℝ) : ℂ :=
 star (actualKMeanRPrice observation nontrivial half h+
   inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
    (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)))

def actualFullMeanSiblingPrice (h : ℝ) : ℂ :=
 actualKMeanRPrice observation nontrivial half h-
   inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
    (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))

theorem actual_full_mean_R_source_prices (h : ℝ) :
 OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=
 actualFullMeanPairPrice observation nontrivial half h ∧
 OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=
 actualFullMeanSiblingPrice observation nontrivial half h := by
 constructor
 · rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,actual_K_mean_R_source_price]
   rfl
 · rw [OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,actual_K_mean_R_source_price]
   rfl



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMeanReturnMixedSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
