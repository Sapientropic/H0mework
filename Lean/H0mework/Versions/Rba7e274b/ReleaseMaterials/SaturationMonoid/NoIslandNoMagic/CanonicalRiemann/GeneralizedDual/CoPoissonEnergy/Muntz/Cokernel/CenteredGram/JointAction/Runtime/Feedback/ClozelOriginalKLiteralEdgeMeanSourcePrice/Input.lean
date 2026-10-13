import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKLiteralEdgeMeanSourcePrice.Source
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKLiteralEdgeMeanSourcePrice
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

private theorem actual_G_left_price (physical : BurnolPaAmbientCarrier) :
 inner ℂ physical OriginalRieszFiniteSynthesis.gapMeanVector=
 star (Paid.actualMean (physical : BurnolL2)) := by
 rw [←inner_conj_symm physical OriginalRieszFiniteSynthesis.gapMeanVector,
   OriginalRieszFiniteSynthesis.gapMeanVector_readback]
 rfl

def actualKMeanInputPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k:=(burnolCompletedMellinRieszVector coordinate : BurnolL2)
 (∫ x : ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h x)*star (Paid.actualMean k)+
 (∫ x : ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h x)*star (Paid.actualMean (fourierL2 k))

/-- Both literal seed masses act on the own actual G/F G mean vectors; no K input price is free. -/
theorem actual_K_mean_input_price (h : ℝ) :
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
   (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h)=
 actualKMeanInputPrice observation nontrivial half h := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k:=burnolCompletedMellinRieszVector coordinate
 let g:=OriginalRieszFiniteSynthesis.gapMeanVector
 have first:=actual_G_left_price k
 have second:=actual_G_left_price (evenFaceFourierEquiv burnolUnscaledCommonGapRadius k)
 have twice : fourierL2 (fourierL2 (k : BurnolL2))=(k : BurnolL2) := by
  rw [fourierL2_fourierL2]
  exact mem_evenL2ClosedFace_iff.mp k.property.2
 have moved:=fourierL2.inner_map_map (fourierL2 (k : BurnolL2)) (g : BurnolL2)
 rw [twice] at moved
 change inner ℂ k (evenFaceFourierEquiv burnolUnscaledCommonGapRadius g)=
   inner ℂ (evenFaceFourierEquiv burnolUnscaledCommonGapRadius k) g at moved
 change inner ℂ k g=star (Paid.actualMean (k : BurnolL2)) at first
 change inner ℂ (evenFaceFourierEquiv burnolUnscaledCommonGapRadius k) g=
   star (Paid.actualMean (fourierL2 (k : BurnolL2))) at second
 unfold OriginalKGapMeanRSourceAction.Full.meanDebt OriginalRieszFiniteSynthesis.gapMeanAdjoint actualKMeanInputPrice
 simp only [ContinuousLinearMap.toSpanSingleton_apply,map_smul,inner_add_right,inner_smul_right]
 rw [first,moved,second]

def actualPositionEdgeMeanRPrice (h : ℝ) : ℂ :=
 -star (actualEdgeSourceNormalization (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))*
   actualKMeanInputPrice observation nontrivial half h/
 ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value-1/2)

/-- The source kernel and true R action consume the literal two-mean material and generate its complete position-edge price. -/
theorem actual_position_edge_mean_R_price (h : ℝ) :
 inner ℂ (OriginalRieszFiniteSource.edgePrimitive (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=
 actualPositionEdgeMeanRPrice observation nontrivial half h := by
 have source:=actual_edge_R_material_price
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
   (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h)
 rw [actual_K_mean_input_price] at source
 exact source



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKLiteralEdgeMeanSourcePrice
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
