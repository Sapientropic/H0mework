import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Execution.Residual.Family
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Execution.Residual.Source

/-! The mother emitter installs each residual's complete source material and
reads its native syntax as the actual query. The original shared engine
retains its own whole ledger and successor. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Residual.Family
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
def component : SourceNativeProjectionLaw (A.base frame).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => PacketAt (A.epoch frame) occurrence
  project := fun _ {_current} occurrence _ => packetAt (A.epoch frame) occurrence

def programme : A.Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) where
  LowVar := SourceOperationInquiry.Context.Native.Orbit.Var PhysicalVar
  datum frame := {
    component := some (component frame)
    reader := fun {_current} occurrence => ((component frame).project PUnit.unit occurrence PUnit.unit).2.2.2.1.1 }

def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (A.base frame).root.source.base (component (A.epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryLaw (A.epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryRoot frame programme).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultLaw (A.epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultRoot frame programme).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerLaw (A.epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerRoot frame programme).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.compilationLaw (A.epoch frame) programme))

def face : SourceNativeRootSemanticFaceAt (A.root frame programme)
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame programme) where
  projection := (installation frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem query_residual : (A.query frame programme).raw = (face frame).rootRead.2.2.2.1.1 := rfl

theorem endpoint_actual : HEq (sourceEndpoint frame (A.actualOccurrence frame))
    (SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.actualResult frame).2.1 :=
  (SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.result_state_receipt frame).symm

theorem canonical_expression : (residualRaw frame (A.actualOccurrence frame)).expression =
    (Residual.registered frame).input.expression := by
  change Expr.add (Residual.raw frame).expression
    (.linear (-AddMonoidHom.id _) (sourceEndpoint frame (A.actualOccurrence frame)).1) =
      Expr.add (Residual.raw frame).expression
        (.linear (-AddMonoidHom.id _) (Execution.actualResult frame).2.1.1)
  exact congrArg (fun state => Expr.add (Residual.raw frame).expression
    (.linear (-AddMonoidHom.id _) state.1)) (eq_of_heq (endpoint_actual frame))

theorem canonical_environment : (residualRaw frame (A.actualOccurrence frame)).environment =
    (Residual.registered frame).input.environment := rfl

theorem first_material_read : (face frame).rootRead.2.2.2.2.1 =
    O.I.sourceMaterialAt (firstRoot (A.epoch frame) (A.actualOccurrence frame))
      (firstOccurrence (A.epoch frame) (A.actualOccurrence frame)) := rfl

theorem next_material_read : (face frame).rootRead.2.2.2.2.2 =
    O.I.sourceMaterialAt (nextRoot (A.epoch frame) (A.actualOccurrence frame))
      (nextOccurrence (A.epoch frame) (A.actualOccurrence frame)) := rfl

theorem normal_effect : (A.resultFace frame programme).rootRead.2.2.1 =
    effectEvaluator (R := ℤ)
      (sourceRaw (A.epoch frame) (A.actualOccurrence frame)).environment
      (SourceSubstitution.sourceEnvironment SourceOperationInquiry.Context.Native.Orbit.binding
        (sourceRaw (A.epoch frame) (A.actualOccurrence frame)).environment -
          (sourceRaw (A.epoch frame) (A.actualOccurrence frame)).environment)
      (relationMap (R := ℤ) (sourceRaw (A.epoch frame) (A.actualOccurrence frame)).environment
        (R.relations (R := ℤ) (residualMaterial (A.epoch frame) (A.actualOccurrence frame)))) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).toAuthoritativeRoot
    ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame programme).reader)
    (A.actualOccurrence frame)).trans
      (residual_effect (A.epoch frame) (A.actualOccurrence frame))

theorem normal_inverse :
    (SourceGeneratedScalarDifferentialResidual.residualEquivRange
      (evaluation (R := ℤ) (residualRaw (A.epoch frame) (A.actualOccurrence frame)).environment)
      (SourceGeneratedScalarDifferentialResidual.canonicalResidual
        (evaluation (R := ℤ) (residualRaw (A.epoch frame) (A.actualOccurrence frame)).environment)
        (relationMap (R := ℤ) (sourceRaw (A.epoch frame) (A.actualOccurrence frame)).environment
          (R.relations (R := ℤ) (residualMaterial (A.epoch frame) (A.actualOccurrence frame)))))).val =
      (A.resultFace frame programme).rootRead.2.2.1 :=
  (R.residual_value (R := ℤ) (residualMaterial (A.epoch frame) (A.actualOccurrence frame))).trans
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).toAuthoritativeRoot
      ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame programme).reader)
      (A.actualOccurrence frame)).symm

variable (initial : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
abbrev frames := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames initial programme
abbrev runtime := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.runtime initial programme

theorem actual_query (count : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query initial programme count) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query initial programme count

theorem actual_answer (count : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer initial programme count) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer initial programme count

theorem actual_next (count : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next initial programme count) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next initial programme count

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Residual.Family
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
