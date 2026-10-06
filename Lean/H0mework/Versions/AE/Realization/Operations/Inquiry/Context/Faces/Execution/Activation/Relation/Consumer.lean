import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Relation.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.RelationProgramme
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (Shared.base frame).root.source.base (component (epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (Shared.baseRoot frame programme).source.base (Shared.queryLaw (epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (Shared.queryRoot frame programme).source.base (Shared.resultLaw (epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (Shared.resultRoot frame programme).source.base (Shared.consumerLaw (epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (Shared.consumerRoot frame programme).source.base (Shared.compilationLaw (epoch frame) programme))

def face : SourceNativeRootSemanticFaceAt (Shared.root frame programme) (Shared.visit frame programme) where
  projection := (installation frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem query_raw : (Shared.query frame programme).raw = (face frame).rootRead.2.2.2.1 := rfl

theorem original_material : (face frame).rootRead.1 =
    Context.Installation.materialAt (epoch frame) (Shared.actualOccurrence frame) := rfl

theorem relation_word : (face frame).rootRead.2.1 =
    word (epoch frame) (Shared.actualOccurrence frame) := rfl

theorem whole_material : (face frame).rootRead.2.2.2.2 =
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      (Mother.baseState (epoch frame)).root.toAuthoritativeRoot (Shared.actualOccurrence frame) := rfl

theorem relation_value : (raw frame occurrence).expression.eval (raw frame occurrence).environment = (0,0) := by
  rw [raw,eval_liftExpr,SourceOperationExecution.Coefficients.expression_eval]
  change (SourceOperationScalarRelations.evaluation (R:=ℤ) (mixedEnvironment (original frame occurrence).environment
      (delta frame occurrence)) (word frame occurrence),
    (SourceOperationExecution.Coefficients.expression (word frame occurrence)).effect
      (mixedEnvironment (original frame occurrence).environment (delta frame occurrence)) 0) = (0,0)
  rw [SourceOperationScalarCochain.evaluation_updateWord,SourceOperationEffects.Expr.effect_zero]

theorem query_value : (Shared.resultFace frame programme).rootRead.2.2.1 = (0,0) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
    (relation_value (epoch frame) (Shared.actualOccurrence frame))

theorem query_cost : (Shared.resultFace frame programme).rootRead.2.1.2.length =
    SourceOperationExecution.Coefficients.cost (word (epoch frame) (Shared.actualOccurrence frame)) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
    (SourceOperationExecution.Coefficients.lifted_remaining _)
abbrev event := (Shared.root frame programme).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (Shared.visit frame programme)

theorem birth_old_inventory (projection : (Shared.root frame programme).source.base.projectionLaw.Projection) :
    type_of% ((Shared.targetAt frame programme (event frame)).oldOutcome_heq projection) :=
  (Shared.targetAt frame programme (event frame)).oldOutcome_heq projection

theorem birth_whole_first_write : type_of% ((Shared.targetAt frame programme (event frame)).firstDestination_heq) :=
  (Shared.targetAt frame programme (event frame)).firstDestination_heq

theorem birth_literal_next : type_of% ((Shared.targetAt frame programme (event frame)).targetAnswerAndNext_next_eq) :=
  (Shared.targetAt frame programme (event frame)).targetAnswerAndNext_next_eq
end SourceOperationInquiry.Context.Faces.Execution.Activation.RelationProgramme
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
