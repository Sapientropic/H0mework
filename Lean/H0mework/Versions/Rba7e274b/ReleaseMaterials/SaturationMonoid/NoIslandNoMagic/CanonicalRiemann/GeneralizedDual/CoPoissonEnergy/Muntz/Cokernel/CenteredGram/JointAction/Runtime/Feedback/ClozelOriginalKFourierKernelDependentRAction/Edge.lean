import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierKernelDependentRAction.Strong
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
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





namespace Whole
export OriginalKConstantSeedWholeRAction (actualWholeSeedRField actual_original_R_seed_whole_field)
export OriginalKConstantSeedWholeRAction.ConstantSource (seed)
end Whole

/-- The original whole seed action and the new generated Jordan field produce the entire resonant edge response. -/
theorem actual_resonant_edge_whole_field (coordinate : BurnolCompletedMellinCoordinate) :
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 burnolDirectRightResolvent (dual.value/2) (OriginalRieszFiniteSource.edgePrimitive coordinate)=
 (-(dual.value-1)/2:ℂ) • actualResonantField (dual.value/2) Whole.seed-
 Whole.actualWholeSeedRField dual :=by
 dsimp only
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 have right : 1/4<(dual.value/2).re :=by
  rw [Complex.div_re];norm_num;linarith [dual.rightHalf]
 have source:=Whole.actual_original_R_seed_whole_field dual
 have generated:=congrArg (burnolDirectRightResolvent (dual.value/2)) source
 have dualtwice : OriginalKQuarterTailPhysicalSource.actualStarSource dual=coordinate :=by
  cases coordinate
  unfold dual OriginalKQuarterTailPhysicalSource.actualStarSource
  dsimp only
  congr 1
  exact star_star _
 unfold Whole.actualWholeSeedRField at generated
 rw [dualtwice,burnolDirectRightResolvent_smul] at generated
 have add : burnolDirectRightResolvent (dual.value/2)
   (OriginalRieszFiniteSource.edgePrimitive coordinate+Whole.seed)=
  burnolDirectRightResolvent (dual.value/2) (OriginalRieszFiniteSource.edgePrimitive coordinate)+
  burnolDirectRightResolvent (dual.value/2) Whole.seed :=by
  have read:=burnolDirectRightResolvent_sub (dual.value/2) right
    (OriginalRieszFiniteSource.edgePrimitive coordinate) (-Whole.seed)
  rw [←neg_one_smul ℂ Whole.seed,burnolDirectRightResolvent_smul,neg_one_smul] at read
  simpa only [neg_one_smul,sub_neg_eq_add] using read
 rw [add,actual_resonant_repeated_R _ right,source] at generated
 have qualified : dual.value-1≠0 :=by
  intro zero
  have real:=congrArg Complex.re zero
  norm_num at real
  linarith [dual.belowOne]
 have scalar : (-(dual.value-1)/2:ℂ)*(-2/(dual.value-1))=1 :=by field_simp [qualified]
 have paid:=congrArg (fun field:BurnolL2=>(-(dual.value-1)/2:ℂ) • field) generated
 rw [smul_smul,scalar,one_smul] at paid
 exact (eq_sub_of_add_eq paid.symm)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
