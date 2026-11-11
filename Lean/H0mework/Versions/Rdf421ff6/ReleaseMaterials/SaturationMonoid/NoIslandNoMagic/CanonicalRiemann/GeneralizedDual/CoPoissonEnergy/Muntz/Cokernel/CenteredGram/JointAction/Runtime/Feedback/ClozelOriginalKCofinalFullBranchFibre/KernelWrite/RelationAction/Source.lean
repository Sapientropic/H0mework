import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Consumer
import H0mework.Realization.Operations.Execution.Cochain.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.RelationAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open SourceGeneratedScalarDifferentialResidual
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace PairAction
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Action
 (updatedPairEnvironment)
end PairAction
namespace PR
export KernelWrite.PR (raw pairInventory)
end PR
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (face disposition queryRaw queryReader queryResult query_word_read)
end J
namespace JC
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Generated
 (query_environment)
end JC
namespace RawSource
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
 (raw raw_environment)
end RawSource
namespace P
export SourceOperationPaidRelations (words paid_boundary events_trace)
end P
namespace CC
export SourceOperationExecution.Cochain (boundary expression trace relations written generated_boundary source_zero)
end CC
local instance relationGroups (grade:Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
section NativeSource
variable {W X:Unit→Type} [∀ target,AddCommGroup (W target)]
local instance nativeGroups (grade:Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
private abbrev nativeBornRaw (native:AS.AdmissionPacket (W:=W) (X:=X) (s:=())) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue (L.Value W native.1)) (Var:=X) (sort:=()) :=
 PR.raw native.2.1.2 (A.epoch (AS.bornAfterNative native).2.1.1)
  (S.actualOccurrence (AS.bornAfterNative native).2.1.1)
private abbrev nativeBornAction (native:AS.AdmissionPacket (W:=W) (X:=X) (s:=())) :
 Env (PairValue (L.Value W native.1)) X :=
 PairAction.updatedPairEnvironment (A.epoch (AS.bornAfterNative native).2.1.1)
  (S.actualOccurrence (AS.bornAfterNative native).2.1.1)
private theorem nativeBornRaw_environment (native:AS.AdmissionPacket (W:=W) (X:=X) (s:=())) :
 (nativeBornRaw native).environment=nativeBornAction native := RawSource.raw_environment _ _ _
end NativeSource

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)

abbrev bornRaw := nativeBornRaw (originalNative observation nontrivial half depth ordinal)
abbrev bornActionEnvironment := nativeBornAction (originalNative observation nontrivial half depth ordinal)
abbrev bornFace := J.face (writerSeed observation nontrivial half depth ordinal)
 (A.epoch (writerBorn observation nontrivial half depth ordinal))
 (S.actualOccurrence (writerBorn observation nontrivial half depth ordinal))
abbrev bornPhase := J.disposition (writerSeed observation nontrivial half depth ordinal)
 (A.epoch (writerBorn observation nontrivial half depth ordinal))
 (S.actualOccurrence (writerBorn observation nontrivial half depth ordinal))
abbrev bornResult := J.queryResult (writerSeed observation nontrivial half depth ordinal)
 (A.epoch (writerBorn observation nontrivial half depth ordinal))
 (S.actualOccurrence (writerBorn observation nontrivial half depth ordinal))

theorem original_current_environment :
 (writerRaw observation nontrivial half depth ordinal).environment=
 PairAction.updatedPairEnvironment (A.epoch (writerSelected observation nontrivial half depth ordinal))
  (S.actualOccurrence (writerSelected observation nontrivial half depth ordinal)) :=
 RawSource.raw_environment _ _ _

theorem original_born_environment :
 (bornRaw observation nontrivial half depth ordinal).environment=
 bornActionEnvironment observation nontrivial half depth ordinal :=
 nativeBornRaw_environment (originalNative observation nontrivial half depth ordinal)

abbrev currentEnvironment := (writerQuery observation nontrivial half depth ordinal).environment
def sourceIncrement : type_of% (currentEnvironment observation nontrivial half depth ordinal) :=
 (show type_of% (currentEnvironment observation nontrivial half depth ordinal) from
  (bornRaw observation nontrivial half depth ordinal).environment)-
 currentEnvironment observation nontrivial half depth ordinal
abbrev queryTrace := (writerResult observation nontrivial half depth ordinal).2.1.2
abbrev sourceBoundary := relationMap (R:=ℤ) (currentEnvironment observation nontrivial half depth ordinal)
 (queryTrace observation nontrivial half depth ordinal).relationWords

/-- Both endpoints of this increment are literal source physical actions, not arbitrary receiver environments. -/
theorem original_increment_actions :
 sourceIncrement observation nontrivial half depth ordinal=
 bornActionEnvironment observation nontrivial half depth ordinal-
 PairAction.updatedPairEnvironment (A.epoch (writerSelected observation nontrivial half depth ordinal))
  (S.actualOccurrence (writerSelected observation nontrivial half depth ordinal)) := by
 have current:(writerQuery observation nontrivial half depth ordinal).environment=
  (writerRaw observation nontrivial half depth ordinal).environment := JC.query_environment _ _ _ _ _
 exact congrArg₂ (fun a b : type_of% (currentEnvironment observation nontrivial half depth ordinal)=>a-b)
  (original_born_environment observation nontrivial half depth ordinal)
  (current.trans (original_current_environment observation nontrivial half depth ordinal))

/-- Full mixed terms execute the actual update effect of the complete original query trace boundary. -/
def effectCode := Coefficients.terms
 ((Coefficients.expression (sourceBoundary observation nontrivial half depth ordinal)).mixedTerms.map
  (fun term=>(term,(1:ℤ))))
abbrev effectEnvironment := mixedEnvironment (currentEnvironment observation nontrivial half depth ordinal)
 (sourceIncrement observation nontrivial half depth ordinal)
abbrev effectValue := (effectCode observation nontrivial half depth ordinal).eval
 (effectEnvironment observation nontrivial half depth ordinal)
abbrev effectTrace := execution (effectEnvironment observation nontrivial half depth ordinal)
 (effectCode observation nontrivial half depth ordinal)

theorem actual_effect_value :
 effectValue observation nontrivial half depth ordinal=
 effectEvaluator (R:=ℤ) (currentEnvironment observation nontrivial half depth ordinal)
  (sourceIncrement observation nontrivial half depth ordinal) (sourceBoundary observation nontrivial half depth ordinal) := by
 unfold effectValue effectCode
 rw [Coefficients.terms_eval]
 simp only [List.map_map,Function.comp_def,one_zsmul]
 exact ((Coefficients.expression (sourceBoundary observation nontrivial half depth ordinal)).mixedTerms_sum _ _).trans
  (Coefficients.expression_effect _ _ _)

theorem born_boundary_evaluator :
 evaluation (R:=ℤ) (bornRaw observation nontrivial half depth ordinal).environment
  (sourceBoundary observation nontrivial half depth ordinal)=effectValue observation nontrivial half depth ordinal := by
 rw [actual_effect_value]
 have source:=(queryTrace observation nontrivial half depth ordinal).relation_old (R:=ℤ)
 change evaluation (R:=ℤ) (currentEnvironment observation nontrivial half depth ordinal)
  (sourceBoundary observation nontrivial half depth ordinal)=0 at source
 have generated:=LinearMap.congr_fun (evaluation_update (R:=ℤ)
  (currentEnvironment observation nontrivial half depth ordinal) (sourceIncrement observation nontrivial half depth ordinal))
  (sourceBoundary observation nontrivial half depth ordinal)
 have endpoint:currentEnvironment observation nontrivial half depth ordinal+
  sourceIncrement observation nontrivial half depth ordinal=(bornRaw observation nontrivial half depth ordinal).environment := by
  unfold sourceIncrement
  abel
 rw [endpoint,LinearMap.add_apply,source,zero_add] at generated
 exact generated

/-- The existing cochain compiler executes this actual update boundary; zero is generated by its AST. -/
abbrev cochainTrace := CC.trace (currentEnvironment observation nontrivial half depth ordinal)
 (sourceIncrement observation nontrivial half depth ordinal) (sourceBoundary observation nontrivial half depth ordinal)
theorem actual_cochain_boundary : type_of% (CC.generated_boundary
 (currentEnvironment observation nontrivial half depth ordinal) (sourceIncrement observation nontrivial half depth ordinal)
 (sourceBoundary observation nontrivial half depth ordinal)) := CC.generated_boundary _ _ _

/-- The actual written query trace enters the original born relation closure by the paid transport. -/
theorem actual_boundary_in_born : sourceBoundary observation nontrivial half depth ordinal∈
 (J.Past.I.bornHistory (writerSeed observation nontrivial half depth ordinal)
  (writerBorn observation nontrivial half depth ordinal)).relationClosure :=
 SourceOperationPaidRelations.relations_next
  (RootedAccountedUnfolding.zero (S.actualOccurrence (writerSelected observation nontrivial half depth ordinal)))
  (SourceOperationPaidRelations.exposure (queryTrace observation nontrivial half depth ordinal))
  (RootedAccountedUnfolding.zero (S.actualOccurrence (writerBorn observation nontrivial half depth ordinal)))
  (PR.pairInventory (writerSeed observation nontrivial half depth ordinal)
   (A.epoch (writerBorn observation nontrivial half depth ordinal))
   (S.actualOccurrence (writerBorn observation nontrivial half depth ordinal)))
  (original_query_trace_written observation nontrivial half depth ordinal)
  (SourceOperationPaidRelations.boundary_in_inventory
   (RootedAccountedUnfolding.zero (S.actualOccurrence (writerSelected observation nontrivial half depth ordinal)))
   (queryTrace observation nontrivial half depth ordinal))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.RelationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
