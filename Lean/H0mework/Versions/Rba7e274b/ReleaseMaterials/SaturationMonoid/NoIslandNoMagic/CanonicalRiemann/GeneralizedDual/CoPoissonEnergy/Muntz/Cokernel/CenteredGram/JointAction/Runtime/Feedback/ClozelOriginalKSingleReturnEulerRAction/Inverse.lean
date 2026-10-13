import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSingleReturnEulerRAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSingleReturnEulerRAction
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

def actualReturnForcing (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
 (1/2:ℂ) • (OriginalRieszSource.Kernel.A coordinate • OriginalRieszSource.Response.wholeV-
 OriginalRieszSource.Kernel.beta coordinate • OriginalRieszSource.Response.wholeU+
 ((star coordinate.value-1)*actualReturnEndpoint coordinate) • Native.seed)

/-- The same original return is realized by the original inverse source engine, including every original forcing stock. -/
theorem actual_original_R_return_forcing (coordinate : BurnolCompletedMellinCoordinate) :
 let z:=(OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2
 burnolDirectRightResolvent z (actualReturnForcing coordinate)=actualCorrectedReturn coordinate :=by
 dsimp only
 let z:=(OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2
 have source:=actual_return_corrected_strong coordinate
 have rescaledSource:HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (actualCorrectedReturn coordinate))
  (actualReturnVelocity coordinate) ((fun time:ℝ=>-time/2) 0):=by
  simpa only [neg_zero,zero_div] using source
 have scalar:HasDerivAt (fun time:ℝ=>-time/2) (-1/2:ℝ) 0:=by
  simpa only [Pi.neg_apply,neg_div,id_eq] using ((hasDerivAt_id (0:ℝ)).neg.div_const 2)
 have generated:=rescaledSource.scomp (0:ℝ) scalar
 have right:1/4<z.re:=by
  dsimp only [z]
  rw [Complex.div_re];norm_num;linarith [(OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).rightHalf]
 apply (burnolDirectRightResolvent_of_strongEquation z right
  (actualReturnForcing coordinate) (actualCorrectedReturn coordinate) ?_).symm
 convert! generated using 1
 rw [←algebraMap_smul ℂ (-1/2:ℝ)]
 push_cast
 unfold actualReturnForcing actualCorrectedReturn actualReturnVelocity
 dsimp only [z,OriginalKQuarterTailPhysicalSource.actualStarSource]
 module

/-- Real repeated action consumes the generated return forcing; no target resonant value is supplied. -/
theorem actual_return_R_response (coordinate : BurnolCompletedMellinCoordinate) :
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 burnolDirectRightResolvent z (Native.actualWholeSingleReturn coordinate)=
 OriginalKFourierKernelDependentRAction.actualResonantField z (actualReturnForcing coordinate)+
 actualReturnEndpoint coordinate • OriginalKConstantSeedWholeRAction.actualWholeSeedRField dual :=by
 dsimp only
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 have right:1/4<z.re:=by
  dsimp only [z]
  rw [Complex.div_re];norm_num;linarith [dual.rightHalf]
 have source:=actual_original_R_return_forcing coordinate
 dsimp only at source
 have written:Native.actualWholeSingleReturn coordinate=
  burnolDirectRightResolvent z (actualReturnForcing coordinate)+actualReturnEndpoint coordinate • Native.seed :=by
  rw [source]
  unfold actualCorrectedReturn
  module
 rw [written]
 have mapped:=burnolDirectRightResolvent_sub z right
  (burnolDirectRightResolvent z (actualReturnForcing coordinate)) (-(actualReturnEndpoint coordinate • Native.seed))
 rw [←neg_one_smul ℂ (actualReturnEndpoint coordinate • Native.seed),burnolDirectRightResolvent_smul,neg_one_smul] at mapped
 simp only [neg_one_smul] at mapped
 rw [←sub_neg_eq_add,mapped,sub_neg_eq_add,burnolDirectRightResolvent_smul,
  OriginalKFourierKernelDependentRAction.actual_resonant_repeated_R z right,
  OriginalKConstantSeedWholeRAction.actual_original_R_seed_whole_field dual]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSingleReturnEulerRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
