import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
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



/-- A new actual compact source is consumed by the previously certified generic rank and q/4 split. -/
theorem actual_compact_R_rank_source (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2)
 (supported : originalPhysicalCutoff q source=source) (even : reflectL2 source=source) :
 burnolDirectRightResolvent (coordinate.value/2) source=
 originalPhysicalCutoff q (burnolDirectRightResolvent (coordinate.value/2) source)+
 (2*burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf
   (burnolTateReciprocalL2 source)) • burnolRadiusNormalizedUnitTail coordinate q (by norm_num) := by
 have tateEven : reflectL2 (burnolTateReciprocalL2 source)=burnolTateReciprocalL2 source := by
  rw [←burnolTateReciprocal_reflect,even]
 have rank:=FiniteMobiusResolventFlux.cutoff_Rplus_rank coordinate (burnolTateReciprocalL2 source) tateEven
 have sourceSupport:=paid170TateSupport source supported
 rw [sourceSupport] at rank
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have empty : Paid.Rplus (coordinate.value/2) 0=0 := by
  unfold Paid.Rplus Paid.RplusIntegrand
  simp
 rw [empty,sub_zero,←FiniteMobiusResolventFlux.tate_R _ right] at rank
 have generated:=congrArg burnolTateReciprocalL2 rank
 rw [paid170QuarterSplit,map_smul,FiniteMobiusResolventFlux.interiorBase,
   burnolTateReciprocalL2_involutive] at generated
 linear_combination (norm:=module) generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
