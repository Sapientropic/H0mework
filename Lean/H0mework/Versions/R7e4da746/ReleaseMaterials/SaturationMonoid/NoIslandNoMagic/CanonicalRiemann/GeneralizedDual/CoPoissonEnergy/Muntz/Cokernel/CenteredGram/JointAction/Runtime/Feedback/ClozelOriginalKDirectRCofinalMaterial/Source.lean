import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalRAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMaterial
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement

namespace D
export OriginalKCombFirstFullSourceDynamics (factory initial firstCfg packet input raw raw_successor)
end D
namespace P
export OriginalKCombPhysicalAction (code R)
end P
namespace C
export OriginalKCombReceiptFeedback (Value Var)
end C
namespace AI
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
 (HasActualInput cofinal_actual_input actual_environment)
end AI
namespace FR
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation
 (jointCode)
end FR
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket stock_action_reader)
end AS
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
 (defaultFactory)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
 (Value groups)
end L
namespace Dyn
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
 (cofinal_next_active)
end Dyn
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next actualOccurrence)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actualMaterial afterEnvironment)
end R

section Source
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance materialGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade

private theorem packet_increment
 (code : Expr (PairValue W) X ())
 (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))
 (generated : AI.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down)
 (nextActive : (S.next packet.2.1.1 packet.2.2.1).activeEnvironment=packet.2.1.1.activeEnvironment) :
 (R.actualMaterial packet.2.1.1 packet.2.2.1).increment=0 := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=X at sameVar
  cases sameVar
  let cfg : A.Programme (PhysicalValue:=L.Value W grade) (PhysicalVar:=X) (sort:=()) :=
   ⟨X,datum,inventory,pairInventory⟩
  have before := congrArg (fun sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
   (Value:=PairValue (L.Value W grade)) (Var:=X) (sort:=()) => sourceRaw.environment)
   ((AS.stock_action_reader data.1 cfg (S.actualOccurrence data.1)).symm.trans
    (generated data.1 (S.actualOccurrence data.1)))
  have after := congrArg (fun sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
   (Value:=PairValue (L.Value W grade)) (Var:=X) (sort:=()) => sourceRaw.environment)
   ((AS.stock_action_reader (S.next data.1 cfg) cfg (S.actualOccurrence (S.next data.1 cfg))).symm.trans
    (generated (S.next data.1 cfg) (S.actualOccurrence (S.next data.1 cfg))))
  have beforeActual := before.trans
   (congrArg (fun environment => pairEnvironment environment (0 : Env (L.Value W grade) X))
    (AI.actual_environment grade data.1))
  have afterActual := after.trans
   (congrArg (fun environment => pairEnvironment environment (0 : Env (L.Value W grade) X))
    (AI.actual_environment grade (S.next data.1 cfg)))
  change (R.afterEnvironment data.1 cfg)-
   (R.actionReader data.1 cfg (S.actualOccurrence data.1)).environment=0
  change (R.actionReader (S.next data.1 cfg) cfg (S.actualOccurrence (S.next data.1 cfg))).environment-
   (R.actionReader data.1 cfg (S.actualOccurrence data.1)).environment=0
  rw [beforeActual,afterActual,nextActive,sub_self]
end Source

local instance originalGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

theorem actual_material_increment :
 let packet:=D.packet observation nontrivial half depth ordinal
 (R.actualMaterial packet.2.1.1 packet.2.2.1).increment=0 :=
 packet_increment (FR.jointCode (P.code observation nontrivial half))
  (D.packet observation nontrivial half depth ordinal)
  (AI.cofinal_actual_input (FR.jointCode (P.code observation nontrivial half))
   (SF.defaultFactory (PairValue C.Value) C.Var ())
   (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal)
  (Dyn.cofinal_next_active (D.factory observation nontrivial half)
   (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMaterial
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
