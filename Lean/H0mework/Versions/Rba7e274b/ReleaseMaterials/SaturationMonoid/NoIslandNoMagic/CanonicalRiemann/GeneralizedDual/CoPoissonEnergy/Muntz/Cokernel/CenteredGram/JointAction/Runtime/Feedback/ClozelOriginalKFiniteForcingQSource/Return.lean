import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteForcingQSource.Inventory
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteForcingQSource
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
local instance returnAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

private theorem actual_original_R_paired_action (h : ℝ) (material : BurnolL2) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (pairedBurnolMultiplicativeDilation h material)=
 pairedBurnolMultiplicativeDilation h (OriginalKFullSourceRResponse.Op.R observation nontrivial half material) := by
 unfold pairedBurnolMultiplicativeDilation
 simp only [smul_apply,add_apply,map_smul,map_add]
 simp only [OriginalKCombCofinalRAction.original_R_direct]
 exact congrArg (fun value : BurnolL2=>(1/2:ℂ) • value)
   (congrArg₂ (fun left right : BurnolL2=>left+right)
     (burnolDirectRightResolvent_dilation (observation.coordinate/2) h material)
     (burnolDirectRightResolvent_dilation (observation.coordinate/2) (-h) material))

/-- R acts on the actual K forcing programme and consumes its genuine returned primitive. -/
theorem actual_original_finite_forcing_return (h : ℝ) :
 OriginalKSourceScaledMaximalResponse.Return.sourceA observation •
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (Paid.originalForcingPair observation nontrivial half h)=
 Paid.originalForcingPair observation nontrivial half h-
 (2:ℂ) • OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h := by
 have native:=congrArg (fun material : BurnolL2=>OriginalKFullSourceRResponse.Op.R observation nontrivial half material)
   (Paid.actual_original_K_finite_pair observation nontrivial half h)
 rw [actual_original_R_paired_action,map_add,map_smul,map_smul] at native
 change pairedBurnolMultiplicativeDilation h
   (OriginalKPairedResponseGramAction.originalKernelRResponse observation nontrivial half)=
   pairedMellinTranslationCharacter (star observation.coordinate) h •
   OriginalKPairedResponseGramAction.originalKernelRResponse observation nontrivial half+
   (1/2:ℂ) • OriginalKFullSourceRResponse.Op.R observation nontrivial half
    (Paid.originalForcingPair observation nontrivial half h) at native
 have weighted:=congrArg (fun material : BurnolL2=>OriginalKSourceScaledMaximalResponse.Return.sourceA observation • material) native
 have source : pairedBurnolMultiplicativeDilation h
   (OriginalKSourceScaledMaximalResponse.closedKernelSource observation nontrivial half)=
   pairedMellinTranslationCharacter (star observation.coordinate) h •
   OriginalKSourceScaledMaximalResponse.closedKernelSource observation nontrivial half+
   (1/2:ℂ) • (OriginalKSourceScaledMaximalResponse.Return.sourceA observation •
     OriginalKFullSourceRResponse.Op.R observation nontrivial half (Paid.originalForcingPair observation nontrivial half h)) := by
  rw [←OriginalKSourceScaledMaximalResponse.actual_original_K_return]
  rw [map_smul]
  linear_combination (norm:=module) weighted
 unfold OriginalKSourceScaledMaximalResponse.closedKernelSource at source
 rw [map_add,Paid.actual_original_K_finite_pair] at source
 unfold OriginalKSourceScaledMaximalResponse.primitiveFiniteAction
 linear_combination (norm:=module) (-2:ℂ) • source

/-- The complete source effect is generated from actual finite forcing and both omitted R inventories. -/
theorem actual_scaled_R_finite_source (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 OriginalKSourceScaledMaximalResponse.Return.sourceA observation •
 OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)=
 -OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h •
   (Paid.originalForcingPair observation nontrivial half h-
    (2:ℂ) • OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
 OriginalKSourceScaledMaximalResponse.Return.sourceA observation •
   OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualFinitePaStock observation nontrivial half h : BurnolL2)+
 OriginalKSourceScaledMaximalResponse.Return.sourceA observation •
   OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualFiniteOutsideStock observation nontrivial half h) := by
 have source:=congrArg (fun material : BurnolL2=>OriginalKSourceScaledMaximalResponse.Return.sourceA observation • material)
   (actual_R_finite_source observation nontrivial half h nonnegative bounded)
 calc
  _ = _ := source
  _ = -OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h •
      (OriginalKSourceScaledMaximalResponse.Return.sourceA observation •
       OriginalKFullSourceRResponse.Op.R observation nontrivial half (Paid.originalForcingPair observation nontrivial half h))+
      OriginalKSourceScaledMaximalResponse.Return.sourceA observation •
       OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualFinitePaStock observation nontrivial half h : BurnolL2)+
      OriginalKSourceScaledMaximalResponse.Return.sourceA observation •
       OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualFiniteOutsideStock observation nontrivial half h) := by module
  _ = _ := by rw [actual_original_finite_forcing_return]


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteForcingQSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
