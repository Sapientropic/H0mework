import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Factory
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Words
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Update
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query datum actualOccurrence)
end Q
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end E
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
local instance stageGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (binding : ∀ t, X t → Expr W X t) (n : Nat)
variable (seed : Lower.SourceFamily.Seed W X s n)
variable (frame : M.Frame (Value := Lower.Value W n) (Var := X) (sort := s))
variable (scalar : Lower.SourceFamily.Seed W X s (n + 1))
variable (pair : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W (n + 1))) X s)))
def cfg := Lower.SourceFamily.cfg (Lower.SourceFamily.Foresight.factory (s := s) binding) n seed
def receiver : M.Frame (Value := Lower.Value W (n + 1)) (Var := X) (sort := s) :=
  B.initial frame (cfg binding n seed) scalar pair
def after : Env (Lower.Value W (n + 1)) X :=
  SourceGeneratedInquiryReceiptAction.afterEnvironment frame (cfg binding n seed)
def nextSeed := SourceHistoryCommon.seed scalar
  (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
    (receiver binding n seed frame scalar pair).registered.input.expression))
def nextCfg := Lower.SourceFamily.cfg (Lower.SourceFamily.Foresight.factory (s := s) binding) (n + 1)
  (nextSeed binding n seed frame scalar pair)
def nextEnv : Env (PairValue (Lower.Value W (n + 1))) X :=
  (Q.query (receiver binding n seed frame scalar pair)
    (nextCfg binding n seed frame scalar pair)).raw.environment
def sourceOccurrence := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
  (receiver binding n seed frame scalar pair).registered (receiver binding n seed frame scalar pair).packetAt
  (Q.actualOccurrence (receiver binding n seed frame scalar pair))
def decoder : Env (Lower.Value W (n + 1)) X :=
  (receiver binding n seed frame scalar pair).environment (sourceOccurrence binding n seed frame scalar pair)
def acted : Env (Lower.Value W (n + 1)) X :=
  SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n + 1))
    (decoder binding n seed frame scalar pair)
def increment : Env (Lower.Value W (n + 1)) X :=
  acted binding n seed frame scalar pair - decoder binding n seed frame scalar pair

theorem same_source_decoder : decoder binding n seed frame scalar pair =
    ((Q.datum frame (cfg binding n seed)).reader
      (sourceOccurrence binding n seed frame scalar pair)).environment := rfl

theorem receiver_source : Future.Replay.physicalEnvironment
    (E.epoch (receiver binding n seed frame scalar pair))
    (Q.actualOccurrence (receiver binding n seed frame scalar pair)) =
      decoder binding n seed frame scalar pair := rfl

theorem actual_environment : nextEnv binding n seed frame scalar pair =
    pairEnvironment (decoder binding n seed frame scalar pair) (increment binding n seed frame scalar pair) := by
  have generated := congrArg (fun raw => raw.environment)
    (Lower.SourceFamily.Foresight.factory_raw binding (n + 1)
      (nextSeed binding n seed frame scalar pair) (receiver binding n seed frame scalar pair))
  apply generated.trans
  change Future.Replay.actionPairEnvironment (Future.Replay.Binding.at binding (n + 1))
    (E.epoch (receiver binding n seed frame scalar pair))
    (Q.actualOccurrence (receiver binding n seed frame scalar pair)) = _
  exact congrArg (fun base : Env (Lower.Value W (n + 1)) X =>
    pairEnvironment base (SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n + 1)) base - base))
    (receiver_source binding n seed frame scalar pair)

theorem actual_word (t : S) (word : Formal ℤ (Lower.Value W (n + 1)) X t) :
    evaluation (R := ℤ) (nextEnv binding n seed frame scalar pair) (liftMap word) =
      updateInventory (R := ℤ) (decoder binding n seed frame scalar pair)
        (increment binding n seed frame scalar pair) word := by
  rw [actual_environment]
  exact LinearMap.congr_fun (evaluation_liftMap (R := ℤ) (s := t)
    (decoder binding n seed frame scalar pair) (increment binding n seed frame scalar pair)) word

def wholeMorphism (t : S) :
    Morphism (updateInventory (R := ℤ) (s := t) (decoder binding n seed frame scalar pair)
      (increment binding n seed frame scalar pair))
      (evaluation (R := ℤ) (s := t) (nextEnv binding n seed frame scalar pair)) where
  sourceMap := liftMap
  targetMap := LinearMap.id
  commutes := by
    rw [LinearMap.id_comp, actual_environment]
    exact (evaluation_liftMap _ _).symm

theorem decoder_after_when_paid
    (paid : DebtActivationWorld.GeneratedStepAt
      (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression)
      frame.event.state) (actual : frame.action = .inr paid) :
    decoder binding n seed frame scalar pair = after binding n seed frame := by
  unfold after SourceGeneratedInquiryReceiptAction.afterEnvironment
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
  rw [actual]
  rfl

theorem paid_environment
    (paid : DebtActivationWorld.GeneratedStepAt
      (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression)
      frame.event.state) (actual : frame.action = .inr paid) :
    nextEnv binding n seed frame scalar pair = pairEnvironment (after binding n seed frame)
      (SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n + 1))
        (after binding n seed frame) - after binding n seed frame) := by
  have generated := actual_environment binding n seed frame scalar pair
  unfold increment acted at generated
  rw [decoder_after_when_paid binding n seed frame scalar pair paid actual] at generated
  exact generated

end Lower.SourceFamily.Foresight.Update
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

end
