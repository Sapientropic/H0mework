import H0mework.Realization.Operations.Execution.Coefficients.Words
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Reverse.Mother
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Payment

/-! Original coefficient integers generate source syntax. Each supplied
occurrence retains its complete reverse packet and each actual calculation
stage's original material, action and whole write. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Reverse.Coefficients
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift
namespace F
export SourceOperationInquiry.Context.Faces.Reverse.Family (LowPacket lowPacket material oldEnv nextEnv delta nextWord)
end F
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base root next)
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
end A
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw Current World law action whole mathEntry authoritativeRoot)
namespace Completion
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion (state)
end Completion
namespace Installation
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (SourceMaterialAt sourceMaterialAt)
end Installation
end O
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)] {sort : Sorts}
variable (frame : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current))

namespace W
export SaturationMonoid.SourceOperationExecution.Coefficients (expression expression_eval expression_effect expression_remaining)
end W

abbrev pairRaw : O.Raw (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort) :=
  ⟨pairEnvironment (F.oldEnv frame occurrence) (F.delta frame occurrence),
    liftExpr (W.expression (F.nextWord frame occurrence))⟩
abbrev originRoot := (A.base frame).root.toAuthoritativeRoot
abbrev reader := fun (_ : (originRoot frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) =>
  pairRaw frame occurrence
abbrev state (count : Nat) := O.Completion.state (originRoot frame) current (reader frame occurrence) count
abbrev calculationRoot := O.authoritativeRoot (originRoot frame) current (reader frame occurrence)
abbrev StageMaterial (count : Nat) := O.Installation.SourceMaterialAt (calculationRoot frame occurrence)
  ((calculationRoot frame occurrence).emitted (state frame occurrence count))

structure ReceiptAt : Type u where
  private mk ::
  raw : O.Raw (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort)
  material : (count : Fin (remaining raw.expression + 1)) → StageMaterial frame occurrence count.1
  action : (count : Fin (remaining raw.expression + 1)) →
    SourceOperationExecutionDebt.Settlement (state frame occurrence count.1) ⊕
      DebtActivationWorld.GeneratedStepAt (O.law (originRoot frame) current (reader frame occurrence))
        (state frame occurrence count.1)
  whole : (count : Fin (remaining raw.expression + 1)) → LedgerWriteEvolutionAt
    (O.World (originRoot frame) current (reader frame occurrence))
    ⟨RootGeneratedDebtActivationJointSource.OwnerFree.supportAt (originRoot frame) current
      (reader frame occurrence) (state frame occurrence count.1)⟩
    ⟨RootGeneratedDebtActivationJointSource.OwnerFree.supportAt (originRoot frame) current
      (reader frame occurrence) (RootGeneratedDebtActivationJointSource.OwnerFree.nextState
        (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1))⟩

def receiptAt : ReceiptAt frame occurrence :=
  ⟨pairRaw frame occurrence,
    fun count => O.Installation.sourceMaterialAt (calculationRoot frame occurrence)
      ((calculationRoot frame occurrence).emitted (state frame occurrence count.1)),
    fun count => O.action (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1),
    fun count => O.whole (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1)⟩

abbrev PacketAt : Type u := F.LowPacket frame occurrence × ReceiptAt frame occurrence

def packetAt : PacketAt frame occurrence := ⟨F.lowPacket frame occurrence, receiptAt frame occurrence⟩

theorem packet_word : (packetAt frame occurrence).1.2.1 = F.nextWord frame occurrence := rfl

theorem packet_raw : (packetAt frame occurrence).2.raw = pairRaw frame occurrence := rfl

def activePayment (count : Fin (remaining (pairRaw frame occurrence).expression)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activePayment
    (originRoot frame) current (reader frame occurrence) count

def activeContinuation (count : Fin (remaining (pairRaw frame occurrence).expression)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activeContinuation
    (originRoot frame) current (reader frame occurrence) count

theorem stage_budget (count : Nat) :
    (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.debtCurrent
      (originRoot frame) current (reader frame occurrence) count).budget =
      SaturationMonoid.SourceOperationExecution.Coefficients.cost (F.nextWord frame occurrence) - count :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.budget
    (originRoot frame) current (reader frame occurrence) count).trans
      (congrArg (fun budget => budget - count)
        (SaturationMonoid.SourceOperationExecution.Coefficients.lifted_remaining (F.nextWord frame occurrence)))

theorem stage_material (count : Fin (remaining (pairRaw frame occurrence).expression + 1)) :
    HEq ((receiptAt frame occurrence).material count).1.1
      ((calculationRoot frame occurrence).toLedgerRoot.generatedLedgerAt (state frame occurrence count.1)) := HEq.rfl

end SourceOperationInquiry.Context.Faces.Reverse.Coefficients
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
