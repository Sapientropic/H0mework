import Lean
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantSeedWholeRAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantSeedWholeRAction
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



elab "originalEdgeEvenRead" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKLiteralEdgeMeanSourcePrice.Source".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKLiteralEdgeMeanSourcePrice.even_source_read".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full

local instance wholeSeedPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The literal original edge reads the actual input physical face through its own native kernel. -/
theorem actual_edge_physical_input_price (coordinate : BurnolCompletedMellinCoordinate)
 (physical : BurnolPaAmbientCarrier) :
 inner ℂ (OriginalRieszFiniteSource.edgePrimitive coordinate) (physical : BurnolL2)=
 star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
   inner ℂ (burnolCompletedMellinRieszVector coordinate) physical := by
 have read:=burnolAmbientCompletedMellinRieszVector_readback coordinate (physical : BurnolL2)
 rw [burnolAmbientCompletedMellinRieszVector_eq_kernelFormula] at read
 have restriction:=congrArg (fun reader : BurnolPaAmbientCarrier→L[ℂ]ℂ=>reader physical)
   (burnolAmbientCompletedMellinEvaluator_restrict coordinate)
 change burnolAmbientCompletedMellinEvaluator coordinate (physical : BurnolL2)=
   burnolCompletedMellinEvaluator coordinate physical at restriction
 rw [restriction,←burnolCompletedMellinRieszVector_readback] at read
 change inner ℂ (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate •
   burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)) (physical : BurnolL2)=_
 rw [inner_smul_left,originalEdgeEvenRead _ _ (mem_evenL2ClosedFace_iff.mp physical.property.2),read]
 rfl

/-- Whole R-star seed field meets only the receiver's genuine Fourier physical face. -/
theorem actual_Fconstant_seed_R_source_price (coordinate : BurnolCompletedMellinCoordinate)
 (physical : BurnolPaAmbientCarrier) :
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical
 inner ℂ (fourierL2 ConstantSource.seed) (burnolDirectRightResolvent (coordinate.value/2) (physical : BurnolL2))=
 (-2/(coordinate.value-1):ℂ)*
 (star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
    inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
  (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)) := by
 dsimp only
 have moved:=OriginalKCompactAdjointRSource.actual_compact_F_R_physical_action coordinate ConstantSource.seed physical
 rw [actual_original_R_seed_whole_field] at moved
 unfold actualWholeSeedRField at moved
 have dualtwice : OriginalKQuarterTailPhysicalSource.actualStarSource
   (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)=coordinate := by
  cases coordinate
  unfold OriginalKQuarterTailPhysicalSource.actualStarSource
  dsimp only
  congr 1
  exact star_star _
 rw [dualtwice] at moved
 rw [inner_smul_left,inner_add_left] at moved
 change inner ℂ (fourierL2 ConstantSource.seed) (burnolDirectRightResolvent (coordinate.value/2) (physical : BurnolL2))=
   (starRingEnd ℂ) (-2/((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value-1))*
   (inner ℂ (OriginalRieszFiniteSource.edgePrimitive coordinate)
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical : BurnolL2)+
    inner ℂ ConstantSource.seed (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical : BurnolL2)) at moved
 rw [actual_edge_physical_input_price,OriginalKConstantContactSourceAction.actual_constant_seed_input_price] at moved
 simp only [OriginalKQuarterTailPhysicalSource.actualStarSource] at moved
 simp only [starRingEnd_apply,star_div₀,star_neg,star_sub,star_ofNat,star_one,star_star] at moved
 exact moved

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantSeedWholeRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
