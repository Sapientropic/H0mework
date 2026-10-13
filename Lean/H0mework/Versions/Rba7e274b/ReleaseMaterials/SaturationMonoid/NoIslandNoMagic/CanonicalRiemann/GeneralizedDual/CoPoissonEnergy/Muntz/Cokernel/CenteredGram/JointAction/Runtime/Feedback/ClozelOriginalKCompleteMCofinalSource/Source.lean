import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapKernelGreenSource.Consumer
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
local instance cofinalMSourcePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


namespace Cofinal
export OriginalKResponseCofinalSourceAction
 (actualU actualV actualWholeRead actualFirstRead actual_first_read_source actual_source_step
  actual_source_increment actual_source_residual actual_source_tendsto actual_V_source_tendsto
  actual_source_error_from_eta actual_V_source_error_bound actual_first_coefficient_error_from_eta)
end Cofinal
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "S" => burnolMeanZeroTruncatedFourierSquare
local notation "a" => OriginalKCompleteMResidualSource.actualMSourceUCoefficient
local notation "b" => OriginalKCompleteMResidualSource.actualMSourceVCoefficient

def actualMSourceRead (c:BurnolCompletedMellinCoordinate) (h:ℝ) :BurnolQuarterMeanZeroCarrier→L[ℂ]ℂ:=
 a c h • Cofinal.actualFirstRead (OriginalKQuarterTailPhysicalSource.actualStarSource c)+
 b c h • (Cofinal.actualFirstRead (OriginalKQuarterTailPhysicalSource.actualStarSource c)).comp T

def actualFiniteMSourceTateInventory (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 actualMSourceRead c h (Cofinal.actualU n)

def actualMSourceTateResidual (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 actualMSourceRead c h ((S^n) OriginalRieszSource.Response.u)

/-- The read acts on the actual original source and genuine Fourier return; it does not recognize a receiver value as a source occurrence. -/
theorem actual_M_joint_source_read (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
 actualMSourceRead c h OriginalRieszSource.Response.u=
 OriginalKCompleteMResidualSource.actualMSourceTateInventory c h :=by
 have starSource:OriginalKQuarterTailPhysicalSource.actualStarSource
  (OriginalKQuarterTailPhysicalSource.actualStarSource c)=c :=by
  cases c
  simp only [OriginalKQuarterTailPhysicalSource.actualStarSource,star_star]
 unfold actualMSourceRead OriginalKCompleteMResidualSource.actualMSourceTateInventory
 simp only [add_apply,smul_apply,
  ContinuousLinearMap.comp_apply,smul_eq_mul]
 rw [Cofinal.actual_first_read_source,Cofinal.actual_first_read_source,starSource]
 rfl

/-- The actual eta/T-square source action generates each complete M coefficient increment. -/
theorem actual_complete_M_source_increment (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat) :
 actualFiniteMSourceTateInventory c h (n+1)-actualFiniteMSourceTateInventory c h n=
 actualMSourceRead c h ((S^n) OriginalRieszSource.Response.eta) :=by
 unfold actualFiniteMSourceTateInventory
 rw [←map_sub,Cofinal.actual_source_increment]

/-- The same original source residual is carried into current complete M inventory without a zero premise. -/
theorem actual_complete_M_source_residual (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat) :
 OriginalKCompleteMResidualSource.actualMSourceTateInventory c h-
 actualFiniteMSourceTateInventory c h n=actualMSourceTateResidual c h n :=by
 rw [←actual_M_joint_source_read]
 unfold actualFiniteMSourceTateInventory actualMSourceTateResidual
 rw [←map_sub,Cofinal.actual_source_residual]

/-- The complete original M inventory consumes its actual finite source and exact same residual on the whole physical field. -/
theorem actual_complete_M_inventory_source_split (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat) :
 OriginalKCompleteMResidualSource.actualCompleteMSourceInventoryField c h=
 (actualFiniteMSourceTateInventory c h n+actualMSourceTateResidual c h n) •
  OriginalKCompleteMResidualSource.actualMeanZeroCompactRField c-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization
  (OriginalKQuarterTailPhysicalSource.actualStarSource c)*b c h) •
 burnolCompletedMellinRieszVector (OriginalKQuarterTailPhysicalSource.actualStarSource c)-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass c h) • G-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass c h) • Fphysical G :=by
 have source:=actual_complete_M_source_residual c h n
 have generated:OriginalKCompleteMResidualSource.actualMSourceTateInventory c h=
  actualFiniteMSourceTateInventory c h n+actualMSourceTateResidual c h n :=by
  linear_combination source
 unfold OriginalKCompleteMResidualSource.actualCompleteMSourceInventoryField
 rw [generated]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMCofinalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
