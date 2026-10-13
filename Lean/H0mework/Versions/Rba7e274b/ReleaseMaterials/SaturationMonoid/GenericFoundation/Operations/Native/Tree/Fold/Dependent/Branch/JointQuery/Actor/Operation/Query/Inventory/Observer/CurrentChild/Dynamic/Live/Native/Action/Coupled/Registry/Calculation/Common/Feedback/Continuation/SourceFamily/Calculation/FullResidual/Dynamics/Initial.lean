import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.FullResidual.Dynamics.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics.Initial
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export Lower.SourceFamily (Factory Seed cfg)
end SF
namespace D
export Lower.SourceFamily.Admissions (packetAt packetAt_successor_grade)
end D
namespace AS
export Lower.SourceFamily.ActivationSource (stock_action_reader AdmissionPacket)
end AS
namespace AI
export Lower.SourceFamily.ActualInputCalculation (withActualInput HasActualInput action_reader)
end AI
namespace Dyn
export Lower.SourceFamily.FullSourceDynamics (cofinal_native_value programme_updated_value collapse_generated_successor)
end Dyn
namespace CF
export Lower.SourceFamily.CalculationFactory (collapseValue)
end CF
namespace L
export Lower (Value groups)
end L
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next)
end S
variable {W X : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (W target)]
local instance levelGroups (grade : Nat) (target : PUnit.{u+1}) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X PUnit.unit)
variable (initial : A.M.Frame (Value := W) (Var := X) (sort := PUnit.unit))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := PUnit.unit))
variable (language : cfg.LowVar = X)

theorem packet_zero : D.packetAt factory initial cfg language 0 =
    (⟨0, ⟨initial, RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator initial.registered.input.expression)⟩,
      cfg, ⟨language⟩⟩ : AS.AdmissionPacket (W := W) (X := X) (s := PUnit.unit)) := rfl

variable (sourceCode : Expr (PairValue W) X PUnit.unit) (baseFactory : SF.Factory W X PUnit.unit)
variable (seed : SF.Seed W X PUnit.unit 0)
abbrev programme : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := PUnit.unit) :=
  SF.cfg (AI.withActualInput sourceCode baseFactory) 0 seed

theorem generated : AI.HasActualInput sourceCode 0 (programme sourceCode baseFactory seed) rfl := by
  intro sourceFrame current supplied
  exact (AS.stock_action_reader sourceFrame (programme sourceCode baseFactory seed) supplied).trans
    (AI.action_reader 0 sourceFrame sourceCode baseFactory seed supplied)

theorem first_collapsed_value
    (keepNext : (S.next initial (programme sourceCode baseFactory seed)).activeEnvironment = initial.activeEnvironment)
    (name : X PUnit.unit) :
    let successor := D.packetAt (AI.withActualInput sourceCode baseFactory) initial (programme sourceCode baseFactory seed) rfl 1
    CF.collapseValue successor.1 (successor.2.1.1.activeEnvironment PUnit.unit name, 0) =
      sourceCode.eval (pairEnvironment initial.activeEnvironment 0) := by
  dsimp only
  have value := Dyn.cofinal_native_value (AI.withActualInput sourceCode baseFactory) initial
    (programme sourceCode baseFactory seed) rfl 0 name
  rw [packet_zero] at value
  have computed := value.trans
    (Dyn.programme_updated_value sourceCode 0 (programme sourceCode baseFactory seed) rfl initial
      (generated sourceCode baseFactory seed))
  have preserved := computed.trans (heq_of_eq (congrArg (fun env => sourceCode.eval (pairEnvironment env 0)) keepNext))
  have grade := D.packetAt_successor_grade (AI.withActualInput sourceCode baseFactory) initial
    (programme sourceCode baseFactory seed) rfl 0
  rw [packet_zero] at grade
  exact Dyn.collapse_generated_successor 0 _ grade _ _ preserved

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics.Initial
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
