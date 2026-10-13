import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSingleReturnEulerRAction.Inventory
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

local instance singleReturnPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualReturnJointFKField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 ((1/2:ℂ)*OriginalRieszSource.Kernel.A coordinate) •
  OriginalKFourierKernelDependentRAction.actualResonantField z OriginalRieszSource.Response.wholeV-
 ((1/2:ℂ)*OriginalRieszSource.Kernel.beta coordinate) •
  OriginalKFourierKernelDependentRAction.actualResonantField z OriginalRieszSource.Response.wholeU+
 ((1/2:ℂ)*(star coordinate.value-1)*OriginalRieszSource.Kernel.A coordinate) •
  OriginalKFourierKernelDependentRAction.actualResonantField z Native.seed+
 OriginalRieszSource.Kernel.A coordinate • OriginalKConstantSeedWholeRAction.actualWholeSeedRField dual

/-- Original K stays fixed; only its true Fourier source restrictions are consumed on the same actual mean material. -/
theorem actual_return_joint_FK_field_read (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
  (OriginalKFullSourceRResponse.Op.R observation nontrivial half (material : BurnolL2))=
 inner ℂ (actualReturnJointFKField coordinate) (fourierL2 (material : BurnolL2)) :=by
 dsimp only
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 rw [OriginalKFourierKernelDependentRAction.actual_original_FK_single_source,
  inner_add_left,inner_sub_left,OriginalKFourierKernelDependentRAction.actual_single_source_R_mean_price,
  sub_zero]
 rw [OriginalKCombCofinalRAction.original_R_direct]
 change inner ℂ (fourierL2 (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)))
  (burnolDirectRightResolvent (coordinate.value/2) (material : BurnolL2))+
  inner ℂ (fourierL2 (Native.actualWholeSingleReturn coordinate))
  (burnolDirectRightResolvent (coordinate.value/2) (material : BurnolL2))=_
 rw [OriginalKCompactAdjointRSource.actual_compact_F_R_physical_action coordinate _ material,
  OriginalKCompactAdjointRSource.actual_compact_F_R_physical_action coordinate _ material,
  ←inner_add_left,actual_complete_FK_R_source_inventory]
 rfl

def actualReturnJointFKMeanPrice (h shift : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 let A:=star (OriginalRieszSource.Kernel.A coordinate)
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 (A/2)*inner ℂ (OriginalKFourierKernelDependentRAction.actualResonantField z OriginalRieszSource.Response.wholeV) (Fphysical : BurnolL2)-
 (b/2)*inner ℂ (OriginalKFourierKernelDependentRAction.actualResonantField z OriginalRieszSource.Response.wholeU) (Fphysical : BurnolL2)+
 ((coordinate.value-1)*A/2)*
  (star (1/z^2)*(1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)+
   OriginalKJordanExteriorSourceAction.actualExteriorSourcePrice observation nontrivial half h shift)-
 (2*A/(coordinate.value-1))*
  (star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
    inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
   (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2))

/-- Actual A/beta U/V/seed Jordan stocks pay the original FK read, with the full previous exterior finite action and tail retained. -/
theorem actual_return_joint_FK_mean_price (h shift : ℝ) (nonnegative : 0≤shift) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
  (OriginalKFullSourceRResponse.Op.R observation nontrivial half (material : BurnolL2))=
 actualReturnJointFKMeanPrice observation nontrivial half h shift :=by
 dsimp only
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 have right:1/4<z.re:=by
  dsimp only [z]
  rw [Complex.div_re];norm_num;linarith [dual.rightHalf]
 rw [actual_return_joint_FK_field_read]
 unfold actualReturnJointFKField actualReturnJointFKMeanPrice
 dsimp only
 rw [inner_add_left,inner_add_left,inner_sub_left,inner_smul_left,inner_smul_left,inner_smul_left,inner_smul_left]
 have jPrice:=OriginalKJordanSeedFieldSource.actual_jordan_seed_physical_price z right Fphysical
 have ePrice:=OriginalKJordanExteriorSourceAction.actual_native_exterior_source_price observation nontrivial half h shift nonnegative
 dsimp only at ePrice
 rw [ePrice] at jPrice
 change inner ℂ (OriginalKFourierKernelDependentRAction.actualResonantField z Native.seed)
  (fourierL2 (material : BurnolL2))=_ at jPrice
 rw [jPrice]
 unfold OriginalKConstantSeedWholeRAction.actualWholeSeedRField
 have dualTwice:∀ native:BurnolCompletedMellinCoordinate,
  OriginalKQuarterTailPhysicalSource.actualStarSource (OriginalKQuarterTailPhysicalSource.actualStarSource native)=native:=by
  intro native
  cases native
  unfold OriginalKQuarterTailPhysicalSource.actualStarSource
  dsimp only
  congr 1
  exact star_star _
 have twice:OriginalKQuarterTailPhysicalSource.actualStarSource dual=coordinate:=dualTwice coordinate
 rw [twice,inner_smul_left,inner_add_left]
 have edge:=OriginalKConstantSeedWholeRAction.actual_edge_physical_input_price coordinate Fphysical
 have seed:=OriginalKConstantContactSourceAction.actual_constant_seed_input_price Fphysical
 change inner ℂ (OriginalRieszFiniteSource.edgePrimitive coordinate) (fourierL2 (material : BurnolL2))=_ at edge
 change inner ℂ Native.seed (fourierL2 (material : BurnolL2))=_ at seed
 rw [edge,seed]
 have sameFace:(evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h) : BurnolL2)=
  fourierL2 (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2):=rfl
 dsimp only [z,dual,Fphysical,material,coordinate]
 rw [sameFace]
 simp only [OriginalKQuarterTailPhysicalSource.actualStarSource,starRingEnd_apply,star_mul,
  star_neg,star_sub,star_div₀,star_one,star_ofNat,star_star]
 ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSingleReturnEulerRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
