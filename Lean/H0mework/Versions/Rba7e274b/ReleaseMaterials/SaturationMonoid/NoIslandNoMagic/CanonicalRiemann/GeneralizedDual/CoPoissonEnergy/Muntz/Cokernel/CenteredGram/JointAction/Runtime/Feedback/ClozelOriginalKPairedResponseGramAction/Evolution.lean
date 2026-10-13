import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedResponseGramAction.Boundary
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedResponseGramAction
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
local instance evolutionAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
def actualBoundaryPaStock (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolPaAmbientCarrier :=
 burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
 (BoundarySource.generatedBoundary (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded)
def actualMovedOutsideStock (h : ℝ) : BurnolL2 :=
 originalOutside (pairedBurnolMultiplicativeDilation h
 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
def actualBoundaryPaRStock (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolL2 :=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualBoundaryPaStock observation nontrivial half h nonnegative bounded : BurnolL2)
def actualMovedOutsideRStock (h : ℝ) : BurnolL2 :=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualMovedOutsideStock observation nontrivial half h)

private theorem actual_paired_compression_read (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
 burnolPairedAmbientCompression h (burnolCompletedMellinRieszVector coordinate)=
 P (pairedBurnolMultiplicativeDilation h (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := by
 unfold burnolPairedAmbientCompression evenBurnolMultiplicativeCompression SourceGeneratedCompressedUnitaryDefectPort.compression pairedBurnolMultiplicativeDilation
 simp only [ContinuousLinearMap.comp_apply,smul_apply,add_apply,Submodule.subtypeL_apply,map_smul,map_add]
 rfl

private theorem actual_paired_R_action (h : ℝ) (material : BurnolL2) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (pairedBurnolMultiplicativeDilation h material)=
 pairedBurnolMultiplicativeDilation h (OriginalKFullSourceRResponse.Op.R observation nontrivial half material) := by
 unfold pairedBurnolMultiplicativeDilation
 simp only [smul_apply,add_apply,map_smul,map_add]
 simp only [OriginalKCombCofinalRAction.original_R_direct]
 exact congrArg (fun value : BurnolL2=>(1/2:ℂ) • value)
   (congrArg₂ (fun left right : BurnolL2=>left+right)
     (burnolDirectRightResolvent_dilation (observation.coordinate/2) h material)
     (burnolDirectRightResolvent_dilation (observation.coordinate/2) (-h) material))

/-- The same source B response is generated from the original K response and its actual projection inventories. -/
theorem actual_original_B_R_action (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 originalBoundaryRResponse observation nontrivial half h nonnegative bounded=
 pairedMellinTranslationCharacter observation.coordinate h • originalKernelRResponse observation nontrivial half-
 pairedBurnolMultiplicativeDilation h (originalKernelRResponse observation nontrivial half)+
 actualMovedOutsideRStock observation nontrivial half h-
 actualBoundaryPaRStock observation nontrivial half h nonnegative bounded := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let whole:=BoundarySource.generatedBoundary coordinate h nonnegative bounded
 have split:=congrArg (fun material : BurnolPaAmbientCarrier=>(material : BurnolL2))
   (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal whole)
 change (actualBoundaryPaStock observation nontrivial half h nonnegative bounded : BurnolL2)+
   (originalGeneratedPaBoundary observation nontrivial half h nonnegative bounded : BurnolL2)=(whole : BurnolL2) at split
 have outside:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal
   (pairedBurnolMultiplicativeDilation h (burnolCompletedMellinRieszVector coordinate : BurnolL2))
 change (P (pairedBurnolMultiplicativeDilation h (burnolCompletedMellinRieszVector coordinate : BurnolL2)) : BurnolL2)+
   actualMovedOutsideStock observation nontrivial half h=
   pairedBurnolMultiplicativeDilation h (burnolCompletedMellinRieszVector coordinate : BurnolL2) at outside
 have original:whole=pairedMellinTranslationCharacter observation.coordinate h • burnolCompletedMellinRieszVector coordinate-
   P (pairedBurnolMultiplicativeDilation h (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := by
  dsimp only [whole]
  rw [BoundarySource.generated_boundary_realizes_original coordinate observation.mathlibZero h nonnegative bounded]
  unfold burnolZeroPairedFixedAnnulusBoundary
  change pairedMellinTranslationCharacter coordinate.value h • burnolCompletedMellinRieszVector coordinate-
    burnolPairedAmbientCompression h (burnolCompletedMellinRieszVector coordinate)=_
  rw [OriginalKCombCofinalTwoDirection.coordinate_value,actual_paired_compression_read]
 have rawOriginal:=congrArg (fun material : BurnolPaAmbientCarrier=>(material : BurnolL2)) original
 simp only [Submodule.coe_sub,Submodule.coe_smul] at rawOriginal
 have input : (originalGeneratedPaBoundary observation nontrivial half h nonnegative bounded : BurnolL2)=
   pairedMellinTranslationCharacter observation.coordinate h • (burnolCompletedMellinRieszVector coordinate : BurnolL2)-
   pairedBurnolMultiplicativeDilation h (burnolCompletedMellinRieszVector coordinate : BurnolL2)+
   actualMovedOutsideStock observation nontrivial half h-(actualBoundaryPaStock observation nontrivial half h nonnegative bounded : BurnolL2) := by
  have generated:=eq_sub_of_add_eq' split
  have contact:=eq_sub_of_add_eq outside
  calc
   _ = (whole : BurnolL2)-(actualBoundaryPaStock observation nontrivial half h nonnegative bounded : BurnolL2) := generated
   _ = _ := by rw [rawOriginal,contact]; abel
 have generated:=congrArg (fun material : BurnolL2=>OriginalKFullSourceRResponse.Op.R observation nontrivial half material) input
 simp only [map_sub,map_add,map_smul] at generated
 rw [actual_paired_R_action] at generated
 exact generated

def actualOriginalWaveStock (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolPaAmbientCarrier :=
 OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded

theorem actual_original_Pa_stock_conservation (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 actualPaSourceStock observation nontrivial half h-
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • actualBoundaryPaStock observation nontrivial half h nonnegative bounded=
 actualOriginalWaveStock observation nontrivial half h nonnegative bounded := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let stock:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
 have whole:=OriginalCommonInverseForcing.SourceJoint.FullStock.actual_whole_boundary_source coordinate observation.mathlibZero h nonnegative bounded
 rw [←BoundarySource.generated_boundary_realizes_original coordinate observation.mathlibZero h nonnegative bounded] at whole
 have generated:=congrArg stock whole
 have kernelZero:stock (burnolCompletedMellinRieszVector coordinate)=0 := by
  exact (Submodule.starProjection_apply_eq_zero_iff _).mpr
   (riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate observation.mathlibZero)
 have waveRead:stock (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient coordinate h nonnegative bounded)=
   OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient coordinate h nonnegative bounded :=
   Submodule.starProjection_eq_self_iff.mpr
     (OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa coordinate h nonnegative bounded)
 simp only [map_smul,map_add,map_sub,kernelZero,waveRead,smul_zero,zero_sub] at generated
 have actual : actualPaSourceStock observation nontrivial half h=
   stock (P (OriginalCommonInverseForcing.SourceJoint.upperSourceCorrection coordinate h))+
   OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h • stock (OriginalCommonInverseForcing.SourceJoint.FullStock.meanDebt coordinate h) := by
  unfold actualPaSourceStock OriginalKCombCofinalPaAction.E
  change stock (P (ActionSource.completeSource observation nontrivial half h))=_
  rw [OriginalKFullSourceRResponse.actual_source_physical_restriction,map_add,map_smul]
 change (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • actualBoundaryPaStock observation nontrivial half h nonnegative bounded=
   -actualOriginalWaveStock observation nontrivial half h nonnegative bounded+
   stock (P (OriginalCommonInverseForcing.SourceJoint.upperSourceCorrection coordinate h))+
   OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h • stock (OriginalCommonInverseForcing.SourceJoint.FullStock.meanDebt coordinate h) at generated
 rw [actual]
 rw [generated]
 module

def actualOriginalWaveRStock (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolL2 :=
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualOriginalWaveStock observation nontrivial half h nonnegative bounded : BurnolL2)

theorem actual_original_Pa_R_stock_conservation (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 actualPaRResponseStock observation nontrivial half h-
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • actualBoundaryPaRStock observation nontrivial half h nonnegative bounded=
 actualOriginalWaveRStock observation nontrivial half h nonnegative bounded := by
 have raw:=congrArg (fun material : BurnolPaAmbientCarrier=>(material : BurnolL2))
   (actual_original_Pa_stock_conservation observation nontrivial half h nonnegative bounded)
 simp only [Submodule.coe_sub,Submodule.coe_smul] at raw
 have generated:=congrArg (fun material : BurnolL2=>OriginalKFullSourceRResponse.Op.R observation nontrivial half material) raw
 simp only [map_sub,map_smul] at generated
 exact generated

/-- Both independent B and Pa-boundary responses are removed by their same-source action equations. -/
theorem actual_original_complete_response_evolution (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (ActionSource.completeSource observation nontrivial half h)=
 ((2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*pairedMellinTranslationCharacter (star observation.coordinate) h) • originalKernelRResponse observation nontrivial half-
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • pairedBurnolMultiplicativeDilation h (originalKernelRResponse observation nontrivial half)+
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • actualMovedOutsideRStock observation nontrivial half h+
 actualOriginalWaveRStock observation nontrivial half h nonnegative bounded+
 actualOutsideRResponseStock observation nontrivial half h := by
 have generated:=actual_original_R_source_coupling observation nontrivial half h nonnegative bounded
 rw [actual_original_B_R_action observation nontrivial half h nonnegative bounded] at generated
 have stock:=actual_original_Pa_R_stock_conservation observation nontrivial half h nonnegative bounded
 rw [←stock]
 rw [generated]
 module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedResponseGramAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
