import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Runtime
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceSuccessor

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyActualSourceActivation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
 (Factory runtime processWithSourceFamily actual_node actual_next actual_query actual_receipt actual_whole
  actual_first_activation_full actual_first_native actual_first_born)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (firstProgramme firstReceiver firstReceipt firstReceiptRaw firstPaidAt firstSelected firstBorn secondPresentation first_born_full)
end AS
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
 (state presentation compiles_paid compiles_settled face consumer target_current target_root)
end ST
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames)
end S
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace W
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (material)
end W
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_distance_exact)
end Prefix

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)] {sort : Sorts}
local instance stageGroups (n : Nat) (target : Sorts) : AddCommGroup
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Value Value n target) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.groups Value n target
variable (factory : SF.Factory Value Var sort)
variable (initial : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (language : cfg.LowVar = Var)

theorem actual_first_paid_budget : 0 < (AS.firstReceipt factory initial cfg language).1 := by
 have budget := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget (W.material initial cfg)
 have clock := SourceRegisteredClaimClock.remainder_generated (AS.firstReceiver factory initial cfg language)
 change remaining (AS.firstReceiver factory initial cfg language).event.state.1 =
  remaining (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression (W.material initial cfg)) - 1 at clock
 have distance := Prefix.receipt_distance_exact (AS.firstProgramme factory initial cfg language)
  (AS.firstReceiver factory initial cfg language) 0
 change (AS.firstReceipt factory initial cfg language).1 =
  remaining (AS.firstReceiver factory initial cfg language).event.state.1 at distance
 omega

def actual_first_paid := AS.firstPaidAt factory initial cfg language
 ⟨0,actual_first_paid_budget factory initial cfg language⟩

theorem paid_compilation : type_of% (ST.compiles_paid (AS.firstReceiver factory initial cfg language)
 (AS.firstProgramme factory initial cfg language) (actual_first_paid factory initial cfg language).1
 (actual_first_paid factory initial cfg language).2.down) :=
 ST.compiles_paid _ _ _ (actual_first_paid factory initial cfg language).2.down

theorem settled_compilation : type_of% (ST.compiles_settled (AS.firstSelected factory initial cfg language)
 (AS.firstProgramme factory initial cfg language) (AS.firstReceipt factory initial cfg language).2.1
 (AS.firstReceipt factory initial cfg language).2.2.2) :=
 ST.compiles_settled _ _ _ (AS.firstReceipt factory initial cfg language).2.2.2

theorem settled_not_old_answered :
 (ST.state (AS.firstSelected factory initial cfg language) (AS.firstProgramme factory initial cfg language)).compileInquiry
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.query
   (AS.firstSelected factory initial cfg language) (AS.firstProgramme factory initial cfg language)) ≠
 .answered (ST.face (AS.firstSelected factory initial cfg language) (AS.firstProgramme factory initial cfg language))
  (ST.consumer (AS.firstSelected factory initial cfg language) (AS.firstProgramme factory initial cfg language)) := by
 rw [settled_compilation]
 intro impossible
 cases impossible

theorem actual_paid_activation : ((SF.runtime factory initial cfg language).stateAt 1).engine.node =
 .active (ST.presentation (AS.firstReceiver factory initial cfg language) (AS.firstProgramme factory initial cfg language)) := by
 exact SF.actual_first_native factory initial cfg language 0 (Nat.zero_le _)

theorem actual_settled_activation :
 ((SF.runtime factory initial cfg language).stateAt (1+(AS.firstReceipt factory initial cfg language).1)).engine.node =
 .active (ST.presentation (AS.firstSelected factory initial cfg language) (AS.firstProgramme factory initial cfg language)) :=
 SF.actual_first_native factory initial cfg language _ (Nat.le_refl _)

example : type_of% (SF.actual_first_activation_full factory initial cfg language) := SF.actual_first_activation_full _ _ _ _
example : type_of% (SF.actual_first_born factory initial cfg language) := SF.actual_first_born _ _ _ _
example : type_of% (SF.actual_query factory initial cfg language 1) := SF.actual_query _ _ _ _ _
example : type_of% (SF.actual_receipt factory initial cfg language 1) := SF.actual_receipt _ _ _ _ _
example : type_of% (SF.actual_whole factory initial cfg language 1) := SF.actual_whole _ _ _ _ _
example : type_of% (SF.actual_receipt factory initial cfg language (1+(AS.firstReceipt factory initial cfg language).1)) :=
 SF.actual_receipt _ _ _ _ _
example : type_of% (SF.actual_whole factory initial cfg language (1+(AS.firstReceipt factory initial cfg language).1)) :=
 SF.actual_whole _ _ _ _ _

namespace NamedOriginalK
namespace D
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombSourceSuccessor
 (factory data configuration source_whole source_next)
end D
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate = -2*(n+1))
variable (depth : Nat)
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
attribute [local irreducible] NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction.code

def actualSourceRuntime := SF.runtime D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl)

example : (actualSourceRuntime observation nontrivial depth half).initialState.engine.node =
 .active (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Actual.presentationAt
  D.factory (D.data observation nontrivial depth half).1 (D.configuration observation nontrivial half) (by rfl) 0) := rfl
example : type_of% (SF.actual_first_activation_full D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl)) := SF.actual_first_activation_full _ _ _ _
example : type_of% (actual_paid_activation D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl)) := actual_paid_activation _ _ _ _
example : type_of% (paid_compilation D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl)) := paid_compilation _ _ _ _
example : type_of% (actual_settled_activation D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl)) := actual_settled_activation _ _ _ _
example : type_of% (settled_compilation D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl)) := settled_compilation _ _ _ _
example : type_of% (SF.actual_first_born D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl)) := SF.actual_first_born _ _ _ _
example : type_of% (D.source_whole observation nontrivial depth half) := D.source_whole _ _ _ _
example : type_of% (D.source_next observation nontrivial depth half) := D.source_next _ _ _ _
example (value : SourceOperationInquiry.Field (actualSourceRuntime observation nontrivial depth half)) :
 type_of% (SourceOperationInquiry.word_action (actualSourceRuntime observation nontrivial depth half) value) :=
 SourceOperationInquiry.word_action _ value
end NamedOriginalK

#print axioms SF.actual_first_activation_full
#print axioms SF.actual_first_native
#print axioms SF.actual_first_born
#print axioms actual_first_paid_budget
#print axioms actual_paid_activation
#print axioms paid_compilation
#print axioms settled_compilation
#print axioms settled_not_old_answered
end SourcePolicyActualSourceActivation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
