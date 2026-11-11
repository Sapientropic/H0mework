import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRInverseKernel
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalInverseAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace C
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback (Value Var)
end C
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace AI
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation (raw actual_environment withActualInput source_callbacks HasActualInput native_after_admission_input born_after_native_input)
end AI
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory (codeAt collapseValue code_base_value)
end CF
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory Packet cfg)
end SF
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (baseRoot actualOccurrence next frames)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actionResultAt actualMaterial)
end R
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
namespace SS
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
  (oldPair nativeValue updated_total actual_whole actual_next actual_compiles born born_environment actual_writeback write successorPacket nextCfg)
end SS

local instance levelGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (AdmissionPacket nativeAfterAdmission bornAfterNative stockCfg write)
end AS
namespace Native
export ActualCofinalSourceAction
  (nativePacket sourceBorn selected receipt nativeValue actual_next_packet packetTransport born_transport born_environment receiver_ast receiver_input decoder_source born_inventory born_pair_inventory whole_paid_in_born)
end Native
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid nativeValue native_value updated_total)
end WB

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def actionCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .linear (s := ()) (t := ()) (actionPair observation nontrivial half).toAddMonoidHom (.var (s := ()) ())

def factory := AI.withActualInput (actionCode observation nontrivial half) (D.factory observation nontrivial half)

abbrev parentPacket (ordinal : Nat) := D.packet observation nontrivial half depth ordinal

-- The parent emitter generates the native programme, and its paid prefix generates this born packet.
abbrev incomingPacket (ordinal : Nat) := AS.nativeAfterAdmission (factory observation nontrivial half)
  (parentPacket observation nontrivial half depth ordinal)
def actionPacket (ordinal : Nat) : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) :=
  AS.bornAfterNative (incomingPacket observation nontrivial half depth ordinal)
abbrev configuration (ordinal : Nat) := (actionPacket observation nontrivial half depth ordinal).2.2.1
abbrev material (ordinal : Nat) := R.actualMaterial (actionPacket observation nontrivial half depth ordinal).2.1.1
  (configuration observation nontrivial half depth ordinal)
abbrev receipt (ordinal : Nat) := R.actionResultAt (actionPacket observation nontrivial half depth ordinal).2.1.1
  (configuration observation nontrivial half depth ordinal)
  (S.actualOccurrence (actionPacket observation nontrivial half depth ordinal).2.1.1)

theorem actual_admitted_input (ordinal : Nat) :
    AI.HasActualInput (actionCode observation nontrivial half)
      (actionPacket observation nontrivial half depth ordinal).1
      (actionPacket observation nontrivial half depth ordinal).2.2.1
      (actionPacket observation nontrivial half depth ordinal).2.2.2.down :=
  AI.born_after_native_input (actionCode observation nontrivial half) _
    (AI.native_after_admission_input (actionCode observation nontrivial half)
      (D.factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal))

private theorem value_of_actual_input
    (code : Expr (PairValue (PairValue C.Value)) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
    (generated : AI.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down) :
    CF.collapseValue packet.1 (R.actionResultAt packet.2.1.1 packet.2.2.1
      (S.actualOccurrence packet.2.1.1)).2.2.1 =
    code.eval (fun target name => CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment target name, 0)) := by
  rcases packet with ⟨grade, packetData, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = C.Var at sameVar
    cases sameVar
    let cfg : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()) :=
      ⟨C.Var, datum, inventory, pairInventory⟩
    let frame := packetData.1
    let supplied := S.actualOccurrence frame
    have raw := (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.stock_action_reader
      frame cfg supplied).symm.trans (generated frame supplied)
    have paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
      (S.baseRoot frame cfg).toAuthoritativeRoot (R.actionReader frame cfg) supplied
    have read := paid.trans (congrArg
      (fun sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
        (Value := PairValue (L.Value (PairValue C.Value) grade)) (Var := C.Var) (sort := ()) =>
        sourceRaw.expression.eval sourceRaw.environment) raw)
    have actual := (congrArg (CF.collapseValue grade) read).trans
      (CF.code_base_value code grade _)
    exact actual.trans (congrArg (fun environment => code.eval
      (fun target name => CF.collapseValue grade (environment target name, 0)))
      (AI.actual_environment grade frame))

theorem actual_admitted_value (ordinal : Nat) : type_of%
    (value_of_actual_input (actionCode observation nontrivial half)
      (actionPacket observation nontrivial half depth ordinal)
      (actual_admitted_input observation nontrivial half depth ordinal)) :=
  value_of_actual_input (actionCode observation nontrivial half) _
    (actual_admitted_input observation nontrivial half depth ordinal)

def totalBranches (value : (BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)) : BurnolL2 :=
  (value.1.1 + value.1.2) + (value.2.1 + value.2.2)

theorem action_code_total (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    totalBranches ((actionCode observation nontrivial half).eval environment) =
      inverse observation nontrivial half (totalBranches (environment () ())) := by
  change (inversePair observation nontrivial half (environment () ()).1).1 +
    (inversePair observation nontrivial half (environment () ()).1).2 +
    ((inversePair observation nontrivial half (environment () ()).2).1 +
      (inversePair observation nontrivial half (environment () ()).2).2) = _
  rw [inverse_pair_total, inverse_pair_total, ← map_add]
  rfl

private theorem total_of_actual_input
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
    (generated : AI.HasActualInput (actionCode observation nontrivial half) packet.1 packet.2.2.1 packet.2.2.2.down) :
    totalBranches (CF.collapseValue packet.1 (R.actionResultAt packet.2.1.1 packet.2.2.1
      (S.actualOccurrence packet.2.1.1)).2.2.1) =
    inverse observation nontrivial half (totalBranches (CF.collapseValue packet.1
      (packet.2.1.1.activeEnvironment () (), 0))) :=
  (congrArg totalBranches (value_of_actual_input (actionCode observation nontrivial half) packet generated)).trans
    (action_code_total observation nontrivial half _)

theorem actual_admitted_total (ordinal : Nat) : type_of%
    (total_of_actual_input observation nontrivial half (actionPacket observation nontrivial half depth ordinal)
      (actual_admitted_input observation nontrivial half depth ordinal)) :=
  total_of_actual_input observation nontrivial half _
    (actual_admitted_input observation nontrivial half depth ordinal)

attribute [irreducible] factory actionPacket

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalInverseAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
