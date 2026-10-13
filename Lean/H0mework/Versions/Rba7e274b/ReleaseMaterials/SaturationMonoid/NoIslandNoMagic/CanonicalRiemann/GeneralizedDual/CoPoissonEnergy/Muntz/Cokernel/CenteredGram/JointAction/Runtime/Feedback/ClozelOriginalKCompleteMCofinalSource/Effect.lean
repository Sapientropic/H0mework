import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteMCofinalSource.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMCofinalSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance cofinalMEffectPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector

def actualFiniteMInventoryField (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):BurnolPaAmbientCarrier:=
 actualFiniteMSourceTateInventory c h n • OriginalKCompleteMResidualSource.actualMeanZeroCompactRField c-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization
  (OriginalKQuarterTailPhysicalSource.actualStarSource c)*OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h) •
 K (OriginalKQuarterTailPhysicalSource.actualStarSource c)-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass c h) • G-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass c h) • Fphysical G

/-- The complete original M coefficient pays its own actual source residual by the existing source contraction. -/
theorem actual_complete_M_source_error (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat) :
 ‖actualMSourceTateResidual c h n‖≤
 ‖actualMSourceRead c h‖*((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) :=by
 rw [←actual_complete_M_source_residual]
 rw [←actual_M_joint_source_read]
 unfold actualFiniteMSourceTateInventory
 rw [←map_sub]
 exact ((actualMSourceRead c h).le_opNorm _).trans
  (mul_le_mul_of_nonneg_left (Cofinal.actual_source_error_from_eta n) (norm_nonneg _))

/-- The actual original R M action consumes the finite producer on the complete physical field and writes back exactly the same source residual. -/
theorem actual_original_M_finite_source_action (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat) :
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c) •
  burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c) •
  (actualFiniteMInventoryField c h n+actualMSourceTateResidual c h n •
   OriginalKCompleteMResidualSource.actualMeanZeroCompactRField c) :=by
 have field:OriginalKCompleteMResidualSource.actualCompleteMSourceInventoryField c h=
  actualFiniteMInventoryField c h n+actualMSourceTateResidual c h n •
   OriginalKCompleteMResidualSource.actualMeanZeroCompactRField c :=by
  rw [actual_complete_M_inventory_source_split]
  unfold actualFiniteMInventoryField
  rw [add_smul]
  module
 exact (OriginalKCompleteMResidualSource.actual_original_complete_M_inventory_action c h).trans
  (congrArg (fun value:BurnolPaAmbientCarrier=>
   (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c) • value) field)

/-- Whole original inventory error is paid after the actual source map; this bound makes no projected norm or terminal-margin transfer. -/
theorem actual_complete_M_inventory_error (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat) :
 ‖OriginalKCompleteMResidualSource.actualCompleteMSourceInventoryField c h-actualFiniteMInventoryField c h n‖≤
 ‖OriginalKCompleteMResidualSource.actualMeanZeroCompactRField c‖*‖actualMSourceRead c h‖*
 ((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) :=by
 have source:=actual_complete_M_inventory_source_split c h n
 have residual:OriginalKCompleteMResidualSource.actualCompleteMSourceInventoryField c h-
  actualFiniteMInventoryField c h n=actualMSourceTateResidual c h n •
  OriginalKCompleteMResidualSource.actualMeanZeroCompactRField c :=by
  rw [source]
  unfold actualFiniteMInventoryField
  rw [add_smul]
  module
 rw [residual,norm_smul]
 exact (mul_le_mul_of_nonneg_right (actual_complete_M_source_error c h n) (norm_nonneg _)).trans_eq (by ring)

/-- The complete original M coefficient consumes the already-paid actual cofinal source closure. -/
theorem actual_complete_M_cofinal_source (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
 Tendsto (actualFiniteMSourceTateInventory c h) atTop
  (𝓝 (OriginalKCompleteMResidualSource.actualMSourceTateInventory c h)) :=by
 have source:=((actualMSourceRead c h).continuous.tendsto _).comp Cofinal.actual_source_tendsto
 rw [actual_M_joint_source_read] at source
 exact source

/-- The actual same source residual converges to zero through the source producer, not a target cancellation premise. -/
theorem actual_complete_M_cofinal_residual (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
 Tendsto (actualMSourceTateResidual c h) atTop (𝓝 0) :=by
 have constant:Tendsto (fun _:Nat=>OriginalKCompleteMResidualSource.actualMSourceTateInventory c h) atTop
  (𝓝 (OriginalKCompleteMResidualSource.actualMSourceTateInventory c h)):=tendsto_const_nhds
 have source:=constant.sub (actual_complete_M_cofinal_source c h)
 simp only [sub_self] at source
 exact source.congr (fun n=>actual_complete_M_source_residual c h n)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMCofinalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
