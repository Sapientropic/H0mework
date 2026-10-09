import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
theorem raw_environment : (raw seed frame occurrence).environment = Action.updatedPairEnvironment frame occurrence :=
  add_sub_cancel _ _

theorem value : (raw seed frame occurrence).expression.eval (raw seed frame occurrence).environment =
    effectEvaluator (R:=ℤ) (originalRaw seed frame occurrence).environment
      ((raw seed frame occurrence).environment-(originalRaw seed frame occurrence).environment)
      (SourceOperationScalarPresentation.relationMap (R:=ℤ) (originalRaw seed frame occurrence).environment
        ((sourceResult seed frame occurrence).2.1.2.relationWords (R:=ℤ))) := by
  have generated := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.updated_value (R:=ℤ)
    (actualRequest seed frame occurrence)
  have increment : (actualRequest seed frame occurrence).increment =
      (raw seed frame occurrence).environment-(originalRaw seed frame occurrence).environment := by
    rw [raw_environment]
    rfl
  exact generated.trans (congrArg (fun change => effectEvaluator (R:=ℤ) (originalRaw seed frame occurrence).environment change
    (SourceOperationScalarPresentation.relationMap (R:=ℤ) (originalRaw seed frame occurrence).environment
      ((sourceResult seed frame occurrence).2.1.2.relationWords (R:=ℤ)))) increment)

theorem inverse : (SourceGeneratedScalarDifferentialResidual.residualEquivRange
    (evaluation (R:=ℤ) ((originalRaw seed frame occurrence).environment +
      ((raw seed frame occurrence).environment-(originalRaw seed frame occurrence).environment)))
    (SourceGeneratedScalarDifferentialResidual.canonicalResidual
      (evaluation (R:=ℤ) ((originalRaw seed frame occurrence).environment +
        ((raw seed frame occurrence).environment-(originalRaw seed frame occurrence).environment)))
      (SourceOperationScalarPresentation.relationMap (R:=ℤ) (originalRaw seed frame occurrence).environment
        ((sourceResult seed frame occurrence).2.1.2.relationWords (R:=ℤ))))).val =
    (raw seed frame occurrence).expression.eval (raw seed frame occurrence).environment :=
  ((sourceResult seed frame occurrence).2.1.2.updated_residual (R:=ℤ)
    ((raw seed frame occurrence).environment-(originalRaw seed frame occurrence).environment)).trans (value seed frame occurrence).symm

def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (Shared.base frame).root.source.base (sourceComponent seed (epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.baseRoot frame (configuration seed)).source.base
    (Shared.queryLaw (epoch frame) (configuration seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.queryRoot frame (configuration seed)).source.base
    (Shared.resultLaw (epoch frame) (configuration seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.resultRoot frame (configuration seed)).source.base
    (Shared.consumerLaw (epoch frame) (configuration seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.consumerRoot frame (configuration seed)).source.base
    (Shared.compilationLaw (epoch frame) (configuration seed)))
def face : SourceNativeRootSemanticFaceAt (Shared.root frame (configuration seed)) (Shared.visit frame (configuration seed)) where
  projection := (installation seed frame).embed (.inl PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

theorem original_material : (face seed frame).rootRead.1 = Pair.material seed (epoch frame) (Shared.actualOccurrence frame) := rfl

theorem actual_query : (Shared.query frame (configuration seed)).raw = (face seed frame).rootRead.2.2 := rfl

theorem actual_effect : (Shared.resultFace frame (configuration seed)).rootRead.2.2.1 =
    effectEvaluator (R:=ℤ) (originalRaw seed (epoch frame) (Shared.actualOccurrence frame)).environment
      ((raw seed (epoch frame) (Shared.actualOccurrence frame)).environment-
        (originalRaw seed (epoch frame) (Shared.actualOccurrence frame)).environment)
      (SourceOperationScalarPresentation.relationMap (R:=ℤ)
        (originalRaw seed (epoch frame) (Shared.actualOccurrence frame)).environment
        ((sourceResult seed (epoch frame) (Shared.actualOccurrence frame)).2.1.2.relationWords (R:=ℤ))) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
    (value seed (epoch frame) (Shared.actualOccurrence frame))

theorem actual_cost : (Shared.resultFace frame (configuration seed)).rootRead.2.1.2.length =
    remaining (raw seed (epoch frame) (Shared.actualOccurrence frame)).expression :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _

theorem complete_cost : (face seed frame).rootRead.2.1.2.1.2.length +
    (Shared.resultFace frame (configuration seed)).rootRead.2.1.2.length =
    remaining (originalRaw seed (epoch frame) (Shared.actualOccurrence frame)).expression +
      remaining (raw seed (epoch frame) (Shared.actualOccurrence frame)).expression :=
  congrArg₂ (· + ·) (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _) (actual_cost seed frame)

abbrev event := (Shared.root frame (configuration seed)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (Shared.visit frame (configuration seed))
theorem whole_first_write : type_of% ((Shared.targetAt frame (configuration seed) (event seed frame)).firstDestination_heq) :=
  (Shared.targetAt frame (configuration seed) (event seed frame)).firstDestination_heq

theorem literal_next : type_of% ((Shared.targetAt frame (configuration seed) (event seed frame)).targetAnswerAndNext_next_eq) :=
  (Shared.targetAt frame (configuration seed) (event seed frame)).targetAnswerAndNext_next_eq

theorem initial_seed_preserved : ∀ atom ∈ seed.trace, atom ∈ (face seed frame).rootRead.1.2.1.trace :=
  InventoryProgramme.supplied_seed_preserved seed frame

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
