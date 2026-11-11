import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
local instance relationConsumerGroups (grade : Nat) : ∀ target,
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- The actual root's source generator is evaluated before its R model is read. -/
theorem factor_source_class :
 factor observation nontrivial half depth ordinal (sourceClass observation nontrivial half depth ordinal)=
 H.projection (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
  (D.input observation nontrivial half depth ordinal) := by
 have square := factor_source_word observation nontrivial half depth ordinal
  (sourceGenerator observation nontrivial half depth ordinal)
 let payload := Own.raw (sourceRoot observation nontrivial half depth ordinal)
  (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)
 have singleRead : evaluation (R:=ℤ) payload.environment
  (sourceGenerator observation nontrivial half depth ordinal).val=payload.expression.eval payload.environment := by
  change evaluation (R:=ℤ) payload.environment (Finsupp.single payload.expression 1)=_
  simp only [evaluation,Finsupp.linearCombination_single,one_smul]
 have sourceValue : Calc.calculatedValue observation nontrivial half depth ordinal=
  payload.expression.eval payload.environment := RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.completed_value
  (sourceRoot observation nontrivial half depth ordinal) (sourceCurrent observation nontrivial half depth ordinal)
  (sourceReader observation nontrivial half depth ordinal)
 have generated := (congrArg (CF.collapseValue (D.packet observation nontrivial half depth ordinal).1)
  (singleRead.trans sourceValue.symm)).trans
  (Calc.calculated_full_R_branches observation nontrivial half depth ordinal)
 have recovered := (congrArg (branchReadback observation nontrivial half) generated).trans
  (source_branches_readback observation nontrivial half (D.input observation nontrivial half depth ordinal))
 exact square.trans (congrArg
  (H.projection (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)) recovered)

def receivedModel : SourceModel observation nontrivial half :=
 factor observation nontrivial half depth ordinal (sourceClass observation nontrivial half depth ordinal)

theorem received_model_next :
 H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
  (receivedModel observation nontrivial half depth ordinal)=
 receivedModel observation nontrivial half depth (ordinal+1) := by
 exact (congrArg (H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half))
  (factor_source_class observation nontrivial half depth ordinal)).trans
  ((H.modelAction_source (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
    (D.input observation nontrivial half depth ordinal)).trans
   ((congrArg (H.projection (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half))
     (actual_source_step observation nontrivial half depth ordinal)).trans
    (factor_source_class observation nontrivial half depth (ordinal+1)).symm))

theorem received_source_future (steps : Nat) :
 modelReadback observation nontrivial half
  (((H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half))^steps)
   (receivedModel observation nontrivial half depth ordinal))=
 D.input observation nontrivial half depth (ordinal+steps) := by
 have modelSource := (congrArg
  ((H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half))^steps)
  (factor_source_class observation nontrivial half depth ordinal)).trans
  (model_iterate_source observation nontrivial half (D.input observation nontrivial half depth ordinal) steps)
 exact (congrArg (modelReadback observation nontrivial half) modelSource).trans
  ((model_readback_source observation nontrivial half _).trans
   (actual_source_iterate observation nontrivial half depth ordinal steps))

def sourceDisposition : ResidualDispositionOutcome (sourceEvaluation observation nontrivial half depth ordinal) :=
 Own.Rel.disposition (sourceRoot observation nontrivial half depth ordinal)
 (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)
 (sourceRuntime observation nontrivial half depth ordinal)

/-- A full relation kernel may remain nonzero although this R restriction kills it. -/
theorem factor_kills_relation_kernel
 (sound : GeneratedRelationSoundnessAt (sourceEvaluation observation nontrivial half depth ordinal))
 (coordinate : GeneratedKernelResidualCoordinateAt (sourceEvaluation observation nontrivial half depth ordinal) sound) :
 factor observation nontrivial half depth ordinal coordinate.coordinate=0 := by
 unfold factor
 change H.projection _ _ (branchReadback _ _ _ (CF.collapseValue _
  ((sourceEvaluation observation nontrivial half depth ordinal).completionEvaluation
   (sourceSound observation nontrivial half depth ordinal) coordinate.coordinate)))=0
 have zero := coordinate.maps_to_zero
 have same : sound=sourceSound observation nontrivial half depth ordinal := Subsingleton.elim _ _
 rw [same] at zero
 rw [zero]
 change H.projection _ _ (branchReadback _ _ _ ((collapseLinear _) 0))=0
 rw [map_zero,map_zero,map_zero]

section ExistingDispositionElimination
variable {Root Generator Carrier Target : Type} [AddCommGroup Carrier] [AddCommGroup Target]
 {rootOccurrence : RootedAccountedUnfolding Root}
 {seed : RootedAccountedUnfolding (PresentedRelationEventAt Generator)}
 {continuation : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator→RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
 {history : CofinalHistorySettlement.RootGeneratedCofinalHistoryAt rootOccurrence seed continuation}
 {evaluator : RootedAccountedUnfolding (Generator→Carrier)}
 (face : CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt history evaluator)
 (restriction : history.CompletionCarrier→ₗ[ℤ] Target)

private def restrictionRead (selected : ResidualDispositionOutcome face) : Prop :=
 match selected with
 | .faithful _ _ _ => True
 | .unsound _ _ => False
 | .kernelResidual _ _ coordinate => coordinate.coordinate≠0 ∧ restriction coordinate.coordinate=0
 | .coverageResidual sound _ coordinate =>
   ∀ preimage : history.CompletionCarrier,
    face.completionEvaluation sound preimage≠coordinate.representative

private theorem consumeRestriction
 (sound : GeneratedRelationSoundnessAt face)
 (kills : ∀ receipt,∀ coordinate : GeneratedKernelResidualCoordinateAt face receipt,
  restriction coordinate.coordinate=0)
 (selected : ResidualDispositionOutcome face) : restrictionRead face restriction selected := by
 cases selected with
 | faithful _ _ _ => exact True.intro
 | unsound obstruction _ => exact False.elim (obstruction.notSound sound.sound)
 | kernelResidual receipt _ coordinate =>
  refine ⟨?_,kills receipt coordinate⟩
  intro zero
  exact coordinate.coordinate_ne_zero (congrArg Subtype.val zero)
 | coverageResidual receipt _ coordinate =>
  intro preimage same
  exact coordinate.representative_not_mem_range ⟨preimage,same⟩
end ExistingDispositionElimination

def DispositionReadAt
 (selected : ResidualDispositionOutcome (sourceEvaluation observation nontrivial half depth ordinal)) : Prop :=
 restrictionRead (sourceEvaluation observation nontrivial half depth ordinal)
  (factor observation nontrivial half depth ordinal) selected

theorem disposition_read
 (selected : ResidualDispositionOutcome (sourceEvaluation observation nontrivial half depth ordinal)) :
 DispositionReadAt observation nontrivial half depth ordinal selected :=
 consumeRestriction (sourceEvaluation observation nontrivial half depth ordinal)
  (factor observation nontrivial half depth ordinal) (sourceSound observation nontrivial half depth ordinal)
  (factor_kills_relation_kernel observation nontrivial half depth ordinal) selected

/-- The independent consumer uses the original installed relation face and
the existing runtime's own disposition and generated whole-next. -/
theorem actual_root_relation_consumer :
 (∀ steps:Nat,modelReadback observation nontrivial half
  (((H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half))^steps)
   (receivedModel observation nontrivial half depth ordinal))=
  D.input observation nontrivial half depth (ordinal+steps)) ∧
 DispositionReadAt observation nontrivial half depth ordinal
  (sourceDisposition observation nontrivial half depth ordinal) ∧
 type_of% (Own.Rel.coversAt_factorizes (sourceRoot observation nontrivial half depth ordinal)
  (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)
  (sourceRuntime observation nontrivial half depth ordinal)) :=
 ⟨received_source_future observation nontrivial half depth ordinal,
  disposition_read observation nontrivial half depth ordinal
   (sourceDisposition observation nontrivial half depth ordinal),
  Own.Rel.coversAt_factorizes (sourceRoot observation nontrivial half depth ordinal)
   (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)
   (sourceRuntime observation nontrivial half depth ordinal)⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
