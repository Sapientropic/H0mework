import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Installation.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Source
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFamilyActualCurrentMaterialEnvironmentUpdate
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace I
export SourceOperationInquiry.Context.Installation (materialAt component Occurrence)
end I
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory Seed cfg)
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Packet)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme SourceDatum epoch)
end A
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader)
end R
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
namespace Q
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery (programme action_original_raw result_value common_classifier stock_retained common_generated)
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery (commonLaw component commonEmbedding commonMaterial)
end Q
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence resultFace)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (datum)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot baseInstallation queryRoot queryLaw resultRoot resultLaw consumerRoot consumerLaw root compilationLaw)
end S
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (nextCfg next_action_reader template)
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (nextSeed AdmissionPacket stockCfg)
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (stockCfg)
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (nextBase write)
end AS
namespace Native
export ActualCofinalSourceAction (nativePacket native_packet_actual actual_next_packet receiver_input receiver_ast decoder_source)
end Native
namespace Inv
export SourceGeneratedInquiryReceiptAction.Inventory (stockLaw component)
end Inv
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (programme)
end WB

section Source
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))

def reader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : I.Occurrence frame (current := current)) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := PairValue Value) (Var := Var) (sort := s) :=
 let material := (I.component frame).project PUnit.unit supplied PUnit.unit
 ⟨pairEnvironment material.raw.environment (material.nextRaw.environment - material.raw.environment),
  liftExpr material.raw.expression⟩

variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current := current))
theorem reader_pair : (reader frame supplied).expression.eval (reader frame supplied).environment =
 (I.materialAt frame supplied).pair := rfl

def reader_trace : Trace (reader frame supplied).environment (reader frame supplied).expression
 (.const (I.materialAt frame supplied).pair) := (I.materialAt frame supplied).pairTrace

variable {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)]
local instance familyGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X s)

def datum (n : Nat) (seed : SF.Seed W X s n)
 (currentFrame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :
 A.SourceDatum (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) X currentFrame :=
 { factory.datum n seed currentFrame with calculationReader := some (reader currentFrame) }

def update : SF.Factory W X s := { factory with datum := datum factory }

variable (n : Nat) (seed : SF.Seed W X s n)
variable (currentFrame : M.Frame (Value := L.Value W n) (Var := X) (sort := s))
variable {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
variable (occurrence : I.Occurrence currentFrame (current := sourceCurrent))

theorem actual_action_raw :
 R.actionReader currentFrame (SF.cfg (update factory) n seed) occurrence =
 reader (A.epoch currentFrame) occurrence := rfl

theorem actual_action_pair :
 (R.actionReader currentFrame (SF.cfg (update factory) n seed) occurrence).expression.eval
 (R.actionReader currentFrame (SF.cfg (update factory) n seed) occurrence).environment =
 (I.materialAt (A.epoch currentFrame) occurrence).pair := reader_pair _ _
end Source

section Query
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance queryGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X s)

def queryDatum (n : Nat) (seed : SF.Seed W X s n)
 (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :=
 (Q.programme (SF.cfg (update factory) n seed)).datum frame

def queryFactory : SF.Factory W X s := { factory with datum := queryDatum factory }

theorem query_cfg (n : Nat) (seed : SF.Seed W X s n) :
 SF.cfg (queryFactory factory) n seed = Q.programme (SF.cfg (update factory) n seed) := rfl

variable (n : Nat) (seed : SF.Seed W X s n)
variable (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current := current))

theorem query_action_raw :
 R.actionReader frame (SF.cfg (queryFactory factory) n seed) supplied = reader (A.epoch frame) supplied :=
 (Q.action_original_raw frame (SF.cfg (update factory) n seed) supplied).trans
  (actual_action_raw factory n seed frame supplied)

theorem query_value :
 (S.resultFace frame (SF.cfg (queryFactory factory) n seed)).rootRead.2.2.1 =
 (I.materialAt (A.epoch frame) (S.actualOccurrence frame)).pair :=
 (Q.result_value frame (SF.cfg (update factory) n seed)).trans
  (actual_action_pair factory n seed frame (S.actualOccurrence frame))
end Query

section Next
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance nextGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X s)

theorem query_factory_transport {Y Z : Sorts → Type u} (same : Y = Z)
 (original : SF.Factory W Z s) :
 (same.symm ▸ queryFactory original : SF.Factory W Y s) =
 queryFactory (same.symm ▸ original) := by
 cases same
 rfl

variable (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X)
variable (nextFrame : M.Frame (Value := PairValue (L.Value W n)) (Var := sourceCfg.LowVar) (sort := s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current nextFrame.registered}
variable (supplied : I.Occurrence nextFrame (current := current))

theorem next_action_raw :
 R.actionReader nextFrame (AS.nextCfg (queryFactory factory) n data sourceCfg language) supplied =
 reader (A.epoch nextFrame) supplied := by
 refine (AS.next_action_reader (queryFactory factory) n data sourceCfg language nextFrame supplied).trans ?_
 unfold AS.template
 rw [query_factory_transport language factory]
 unfold R.actionReader S.datum SF.cfg queryFactory queryDatum
 simp only [Q.programme]
 rfl

variable (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
variable (currentFrame : M.Frame (Value := L.Value W (packet.1+1)) (Var := packet.2.2.1.LowVar) (sort := s))
variable {currentFrameCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
variable (atCurrent : I.Occurrence currentFrame (current := currentFrameCurrent))

theorem native_action_raw :
 R.actionReader currentFrame
  (AS.stockCfg (Native.nativePacket (queryFactory factory) packet).2.2.1) atCurrent =
 reader (A.epoch currentFrame) atCurrent :=
 next_action_raw factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down currentFrame atCurrent

def native_action_trace : Trace
 (R.actionReader currentFrame (AS.stockCfg (Native.nativePacket (queryFactory factory) packet).2.2.1) atCurrent).environment
 (R.actionReader currentFrame (AS.stockCfg (Native.nativePacket (queryFactory factory) packet).2.2.1) atCurrent).expression
 (.const (I.materialAt (A.epoch currentFrame) atCurrent).pair) := by
 rw [native_action_raw]
 exact reader_trace _ _
end Next

section Common
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable (configuration : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))

def commonInStock : SourceNativeProjectionLaw.InstallationAt
 (Q.commonLaw (A.epoch frame) configuration)
 (S.root frame (AS.stockCfg (Q.programme configuration))).source.base.projectionLaw :=
 (Q.commonEmbedding (A.epoch frame) configuration).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  { (S.base frame).root.source.base with projectionLaw := Q.component (A.epoch frame) configuration }
  (Inv.stockLaw (A.epoch frame) (Q.programme configuration))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (S.base frame).root.source.base (Inv.component (A.epoch frame) (Q.programme configuration))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (S.baseRoot frame (AS.stockCfg (Q.programme configuration))).source.base
  (S.queryLaw (A.epoch frame) (AS.stockCfg (Q.programme configuration)))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (S.queryRoot frame (AS.stockCfg (Q.programme configuration))).source.base
  (S.resultLaw (A.epoch frame) (AS.stockCfg (Q.programme configuration)))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (S.resultRoot frame (AS.stockCfg (Q.programme configuration))).source.base
  (S.consumerLaw (A.epoch frame) (AS.stockCfg (Q.programme configuration)))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (S.consumerRoot frame (AS.stockCfg (Q.programme configuration))).source.base
  (S.compilationLaw (A.epoch frame) (AS.stockCfg (Q.programme configuration))))

def commonStockOutcome := (S.root frame (AS.stockCfg (Q.programme configuration))).source.base.projectionLaw.outcomeAt
 ((commonInStock frame configuration).embed PUnit.unit) (S.actualOccurrence frame)

theorem common_stock_generated : HEq (commonStockOutcome frame configuration)
 ((Q.commonLaw (A.epoch frame) configuration).outcomeAt PUnit.unit (S.actualOccurrence frame)) :=
 (commonInStock frame configuration).outcome_heq (S.actualOccurrence frame) PUnit.unit
end Common

section NativeCommon
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance commonGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X s) (n : Nat)
variable (data : SF.Packet (W := W) (X := X) (s := s) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X)

def nativeLowProgramme :=
 { SF.cfg (update (language.symm ▸ factory)) (n+1)
   (AS.nextSeed (queryFactory factory) n data sourceCfg language) with
  datum := fun frame =>
   { (SF.cfg (update (language.symm ▸ factory)) (n+1)
      (AS.nextSeed (queryFactory factory) n data sourceCfg language)).datum frame with
    nextEnvironmentReadAt := ((WB.programme data.1 sourceCfg
     (AS.write (queryFactory factory) n data sourceCfg language)).datum frame).nextEnvironmentReadAt } }

theorem native_base_query :
 AS.nextBase (queryFactory factory) n data sourceCfg language =
 Q.programme (nativeLowProgramme factory n data sourceCfg language) := by
 unfold AS.nextBase AS.template
 rw [query_factory_transport language factory]
 rfl

variable (frame : M.Frame (Value := PairValue (L.Value W n)) (Var := sourceCfg.LowVar) (sort := s))

def commonAtNative : SourceNativeProjectionLaw.InstallationAt
 (Q.commonLaw (A.epoch frame) (nativeLowProgramme factory n data sourceCfg language))
 (S.root frame (AS.nextCfg (queryFactory factory) n data sourceCfg language)).source.base.projectionLaw := by
 change SourceNativeProjectionLaw.InstallationAt
  (Q.commonLaw (A.epoch frame) (nativeLowProgramme factory n data sourceCfg language))
  (S.root frame (AS.stockCfg (AS.nextBase (queryFactory factory) n data sourceCfg language))).source.base.projectionLaw
 rw [native_base_query]
 exact commonInStock frame (nativeLowProgramme factory n data sourceCfg language)

def nativeCommonOutcome :=
 (S.root frame (AS.nextCfg (queryFactory factory) n data sourceCfg language)).source.base.projectionLaw.outcomeAt
 ((commonAtNative factory n data sourceCfg language frame).embed PUnit.unit) (S.actualOccurrence frame)

theorem native_common_generated : HEq (nativeCommonOutcome factory n data sourceCfg language frame)
 ((Q.commonLaw (A.epoch frame) (nativeLowProgramme factory n data sourceCfg language)).outcomeAt
  PUnit.unit (S.actualOccurrence frame)) :=
 (commonAtNative factory n data sourceCfg language frame).outcome_heq (S.actualOccurrence frame) PUnit.unit
end NativeCommon

section PaidSource
namespace AN
export ActualNativeRelationTransport (paid paid_raw paid_environment)
end AN
namespace I
export SourceOperationInquiry.Context.Installation (nextRawAt rawAt)
end I
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current := current))

theorem reader_paid_raw :
 (reader (A.epoch frame) supplied).expression = liftExpr (AN.paid frame).raw := rfl

theorem actual_action_isLeft :
 (RootGeneratedDebtActivationJointSource.mathAction
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current.2).isLeft =
 frame.action.isLeft := by
 unfold RootGeneratedDebtActivationJointSource.mathAction
 unfold RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.action
 unfold RootGeneratedDebtActivationJointSource.mathAction
 rfl

theorem reader_paid_environment
 (settled : (RootGeneratedDebtActivationJointSource.mathAction
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current.2).isLeft = true) :
 (reader (A.epoch frame) (S.actualOccurrence frame)).environment =
 pairEnvironment (AN.paid frame).environment (AN.paid frame).increment := by
 have next : (I.nextRawAt (A.epoch frame) (S.actualOccurrence frame)).environment =
   (N.input (AN.paid frame)).environment := by
  dsimp only [I.nextRawAt, A.epoch]
  cases chosen : RootGeneratedDebtActivationJointSource.mathAction
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current.2 with
  | inr value => simp only [chosen, Sum.isLeft] at settled; cases settled
  | inl value => rfl
 change pairEnvironment (AN.paid frame).environment
   ((I.nextRawAt (A.epoch frame) (S.actualOccurrence frame)).environment - (AN.paid frame).environment) = _
 rw [next]
 change pairEnvironment (AN.paid frame).environment
   (((AN.paid frame).environment + (AN.paid frame).increment) - (AN.paid frame).environment) = _
 rw [add_sub_cancel_left]
end PaidSource

end SourceFamilyActualCurrentMaterialEnvironmentUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
