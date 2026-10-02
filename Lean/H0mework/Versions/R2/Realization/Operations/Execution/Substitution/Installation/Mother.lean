import H0mework.Versions.R2.Realization.Operations.Execution.Substitution.Installation.Family
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Runtime
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Consumer

/-! The original shared engine reads the occurrence's forward substitution
packet. Its actual normal and cost consume the source syntax; the original
root action determines every whole write and heterogeneous successor. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.ForwardSubstitution
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift RootInquiryCompletion
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (root base baseRoot query resultFace actualOccurrence actualVisit frames runtime actual_answer actual_next datum)
end S
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)] {sort : Sorts}
variable (binding : ∀ target, PhysicalVar target → Expr PhysicalValue PhysicalVar target)
variable (frame : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (S.base frame).root.source.base (component binding (A.epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (S.baseRoot frame (programme binding)).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryLaw (A.epoch frame) (programme binding))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryRoot frame (programme binding)).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultLaw (A.epoch frame) (programme binding))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultRoot frame (programme binding)).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerLaw (A.epoch frame) (programme binding))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerRoot frame (programme binding)).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.compilationLaw (A.epoch frame) (programme binding)))

def face : SourceNativeRootSemanticFaceAt (S.root frame (programme binding))
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame (programme binding)) where
  projection := (installation binding frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem query_source : (S.query frame (programme binding)).raw = (face binding frame).rootRead.2.2.1 := rfl

theorem normal_source : (S.resultFace frame (programme binding)).rootRead.2.2.1 =
    (raw binding (A.epoch frame) (S.actualOccurrence frame)).expression.eval
      (raw binding (A.epoch frame) (S.actualOccurrence frame)).environment :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (S.baseRoot frame (programme binding)).toAuthoritativeRoot
    ((S.datum frame (programme binding)).reader) (S.actualOccurrence frame)

private theorem raw_pair
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (o : C.Occurrence frame (current := current)) :
    (raw binding frame o).expression.eval (raw binding frame o).environment =
      (((original frame o).raw.expression.subst binding).eval (oldEnv frame o),
       ((original frame o).raw.expression.subst binding).effect (oldEnv frame o) (delta frame o)) := by
  have sourceEnvironment :
      (fun target name => (pairBinding binding target name).eval (pairEnv frame o)) =
        pairEnvironment
          (fun target name => (binding target name).eval (oldEnv frame o))
          (fun target name => (binding target name).effect (oldEnv frame o) (delta frame o)) := by
    funext target name
    exact eval_liftExpr (binding target name) (oldEnv frame o) (delta frame o)
  change ((sourceExpr frame o).subst (pairBinding binding)).eval (pairEnv frame o) = _
  rw [Expr.eval_subst, sourceEnvironment, eval_liftExpr, Expr.eval_subst, Expr.effect_subst]

theorem normal_pair : (S.resultFace frame (programme binding)).rootRead.2.2.1 =
    (((original (A.epoch frame) (S.actualOccurrence frame)).raw.expression.subst binding).eval
      (oldEnv (A.epoch frame) (S.actualOccurrence frame)),
     ((original (A.epoch frame) (S.actualOccurrence frame)).raw.expression.subst binding).effect
      (oldEnv (A.epoch frame) (S.actualOccurrence frame))
      (delta (A.epoch frame) (S.actualOccurrence frame))) :=
  (normal_source binding frame).trans (raw_pair binding (A.epoch frame) (S.actualOccurrence frame))

theorem actual_replay_cost : (S.resultFace frame (programme binding)).rootRead.2.1.2.length =
    (replayTrace binding (A.epoch frame) (S.actualOccurrence frame)).length :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    (S.baseRoot frame (programme binding)).toAuthoritativeRoot
    ((S.datum frame (programme binding)).reader) (S.actualOccurrence frame)).trans
      (source_cost binding (A.epoch frame) (S.actualOccurrence frame)).symm

abbrev commonReader := fun (_ : (originRoot frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (S.actualVisit frame).current) =>
  (S.datum frame (programme binding)).reader (S.actualOccurrence frame)

abbrev chargedState (count : Nat) := O.K.state (S.baseRoot frame (programme binding)).toAuthoritativeRoot
  (S.actualVisit frame).current (commonReader binding frame) count

theorem charged_source_state (count : Nat) : chargedState binding frame count =
    state binding (A.epoch frame) (S.actualOccurrence frame) count :=
  SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.CofaceTransport.state_preserved
    (originRoot frame) (S.actualVisit frame).current (commonReader binding frame)
    (component binding (A.epoch frame)) count

theorem charged_source_whole (count : Nat) :
    HEq (O.whole (S.baseRoot frame (programme binding)).toAuthoritativeRoot
      (S.actualVisit frame).current (commonReader binding frame) (chargedState binding frame count))
      (O.whole (originRoot frame) (S.actualVisit frame).current (commonReader binding frame)
        (state binding (A.epoch frame) (S.actualOccurrence frame) count)) :=
  SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.CofaceTransport.whole_preserved
    (originRoot frame) (S.actualVisit frame).current (commonReader binding frame)
    (component binding (A.epoch frame)) _ _ (heq_of_eq (charged_source_state binding frame count))

def chargedPayment (count : Fin (remaining (raw binding (A.epoch frame) (S.actualOccurrence frame)).expression)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activePayment
    (S.baseRoot frame (programme binding)).toAuthoritativeRoot
    (S.actualVisit frame).current (commonReader binding frame) count

variable (initial : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
abbrev actualRuntime := S.runtime initial (programme binding)
abbrev actualFrame (count : Nat) := S.frames initial (programme binding) count
abbrev actualSource := SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.rawSource initial (programme binding)

theorem actual_answer_next (count : Nat) : type_of% (S.actual_answer initial (programme binding) count) ∧
    type_of% (S.actual_next initial (programme binding) count) :=
  ⟨S.actual_answer initial (programme binding) count, S.actual_next initial (programme binding) count⟩

theorem actual_debt_current (count : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current
      (programme binding) initial count) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current
    (programme binding) initial count

end SourceOperationInquiry.Context.ForwardSubstitution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
