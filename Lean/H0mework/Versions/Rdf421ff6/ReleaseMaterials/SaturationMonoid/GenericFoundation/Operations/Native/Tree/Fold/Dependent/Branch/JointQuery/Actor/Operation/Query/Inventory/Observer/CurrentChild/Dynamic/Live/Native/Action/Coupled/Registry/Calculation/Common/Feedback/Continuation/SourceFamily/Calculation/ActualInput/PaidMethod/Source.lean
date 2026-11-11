import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.Consumer
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Laws
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Installation

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory Seed Packet cfg runtime actual_receipt actual_whole actual_next)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (stockCfg nextCfg nextBase next_action_reader nextSeed receiver AdmissionPacket nativeAfterAdmission bornAfterNative localNativeReceipt)
end AS
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme SourceDatum epoch optionalSourceRoot)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot queryRoot resultRoot consumerRoot root queryLaw resultLaw consumerLaw compilationLaw visit actualOccurrence frames)
end S
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actionResultAt actualMaterial)
end R
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (component stockLaw seed)
end I
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (completeWrittenInventory)
end J
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end Stock
namespace Faces
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower (component combined configuration installation face material)
namespace E
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.Elimination (fourFaces dual_readback)
end E
end Faces

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance levelGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t

-- This is syntax: the source chooses the action once, before any emitted value is read.
def pairAction {T : Type u} [AddCommGroup T] (f : T →+ T) : T × T →+ T × T where
 toFun := fun value => (f value.1, f value.2)
 map_zero' := Prod.ext f.map_zero f.map_zero
 map_add' := fun left right => Prod.ext (f.map_add left.1 right.1) (f.map_add left.2 right.2)

def actionAt (f : W s →+ W s) : (n : Nat) → L.Value W n s →+ L.Value W n s
 | 0 => f
 | n+1 => @pairAction (L.Value W n s) (levelGroups n s) (actionAt f n)

def retainedCode (n : Nat) (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :
 Expr (L.Value W n) X s :=
 match frame.registered.input.expression with
 | .add (.add _ paid) _ => .linear (-AddMonoidHom.id (L.Value W n s)) paid
 | .add _ paid => .linear (-AddMonoidHom.id (L.Value W n s)) paid
 | source => source

def raw (f : W s →+ W s) (n : Nat)
 (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := PairValue (L.Value W n)) (Var := X) (sort := s) :=
 ⟨pairEnvironment frame.registered.input.environment 0,
  .linear (@pairAction (L.Value W n s) (levelGroups n s) (actionAt f n)) (liftExpr (retainedCode n frame))⟩

def methodBase (baseFactory : SF.Factory W X s) (f : W s →+ W s) (n : Nat) (seed : SF.Seed W X s n) :
 A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
 { SF.cfg baseFactory n seed with
   datum := fun frame => { (baseFactory.datum n seed frame) with
    reader := fun {_current} _supplied => raw f n frame
    calculationReader := some (fun {_current} _supplied => raw f n frame) } }

def completeQueryWritten (n : Nat)
 (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :=
 J.completeWrittenInventory (I.seed frame) (A.epoch frame) (S.actualOccurrence frame)

def completePairOutput (baseFactory : SF.Factory W X s) (n : Nat) (seed : SF.Seed W X s n)
 (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :=
 Stock.preserve (baseFactory.nextPairInventory n seed frame) (completeQueryWritten n frame)

def factory (baseFactory : SF.Factory W X s) (f : W s →+ W s) : SF.Factory W X s :=
 { baseFactory with
   datum := fun n seed frame => (Faces.configuration (methodBase baseFactory f n seed)).datum frame
   nextPairInventory := fun n seed frame => some (completePairOutput baseFactory n seed frame) }

theorem completePairOutput_query (baseFactory : SF.Factory W X s) (n : Nat) (seed : SF.Seed W X s n)
 (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :
 ∀ event ∈ (completeQueryWritten n frame).trace, event ∈ (completePairOutput baseFactory n seed frame).trace := by
 unfold completePairOutput Stock.preserve
 cases baseFactory.nextPairInventory n seed frame with
 | none => exact fun _ present => present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1

theorem factory_reader (baseFactory : SF.Factory W X s) (f : W s →+ W s) (n : Nat)
 (seed : SF.Seed W X s n) (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :
 R.actionReader frame (SF.cfg (factory baseFactory f) n seed) (S.actualOccurrence frame) = raw f n frame := rfl

namespace Generic
variable {U Y : Sorts → Type u} [∀ t, AddCommGroup (U t)]
theorem effect_zero (expr : Expr U Y s) (env : Env U Y) : expr.effect env 0 = 0 := by
 have generated := Expr.eval_update expr env 0
 rw [add_zero] at generated
 exact add_left_cancel (generated.symm.trans (add_zero _).symm)
theorem pair_zero (expr : Expr U Y s) (env : Env U Y) :
 (liftExpr expr).eval (pairEnvironment env 0) = (expr.eval env, 0) :=
 (eval_liftExpr expr env 0).trans (congrArg (fun effect => (expr.eval env, effect)) (effect_zero expr env))
end Generic

theorem raw_value (f : W s →+ W s) (n : Nat)
 (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :
 (raw f n frame).expression.eval (raw f n frame).environment =
 (actionAt f n ((retainedCode n frame).eval frame.registered.input.environment), 0) := by
 change (@pairAction (L.Value W n s) (levelGroups n s) (actionAt f n))
  ((liftExpr (retainedCode n frame)).eval (pairEnvironment frame.registered.input.environment 0)) = _
 rw [Generic.pair_zero]
 change (actionAt f n ((retainedCode n frame).eval frame.registered.input.environment), actionAt f n 0) = _
 rw [map_zero]

-- The exact existing Faces installer is used before the inventory reader is emitted.
def datumInstalled (baseFactory : SF.Factory W X s) (f : W s →+ W s) (n : Nat)
 (seed : SF.Seed W X s n) (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) :=
 Faces.installation frame (methodBase baseFactory f n seed)

-- Only the inherited coordinate is followed through the actual stock compiler.
-- This is the first uncompiled source commuting seam; no target equation is supplied.
def templateFace (baseFactory : SF.Factory W X s) (f : W s →+ W s)
 (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
 (language : sourceCfg.LowVar = X)
 (frame : M.Frame (Value := L.Value W (n+1)) (Var := sourceCfg.LowVar) (sort := s)) :
 SourceNativeRootSemanticFaceAt
  (S.root frame (AS.nextCfg (factory baseFactory f) n data sourceCfg language))
  (S.visit frame (AS.nextCfg (factory baseFactory f) n data sourceCfg language)) := by
 cases sourceCfg with
 | mk Y datum inventory pairInventory =>
  change Y = X at language
  cases language
  let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
   ⟨X, datum, inventory, pairInventory⟩
  let method := methodBase baseFactory f (n+1) (AS.nextSeed (factory baseFactory f) n data cfg rfl)
  let base := AS.nextBase (factory baseFactory f) n data cfg rfl
  let actual := AS.stockCfg base
  let installed := ((SourceNativeProjectionLaw.InstallationAt.componentCoface
   (A.optionalSourceRoot (S.base (A.epoch frame)).root (method.datum (A.epoch frame)).component).source.base
   (Faces.component (A.epoch frame) method)).trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    { (S.base (A.epoch frame)).root.source.base with projectionLaw := Faces.combined (A.epoch frame) method }
    (I.stockLaw (A.epoch frame) base))) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base frame).root.source.base
    (I.component (A.epoch frame) base)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.baseRoot frame actual).source.base
    (S.queryLaw (A.epoch frame) actual)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.queryRoot frame actual).source.base
    (S.resultLaw (A.epoch frame) actual)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.resultRoot frame actual).source.base
    (S.consumerLaw (A.epoch frame) actual)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.consumerRoot frame actual).source.base
    (S.compilationLaw (A.epoch frame) actual))

  exact { projection := installed.embed PUnit.unit, active := PUnit.unit, classifier_eq := rfl }

def templateMethod (baseFactory : SF.Factory W X s) (f : W s →+ W s)
 (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
 (language : sourceCfg.LowVar = X) :
 A.Programme (PhysicalValue := L.Value W (n+1)) (PhysicalVar := sourceCfg.LowVar) (sort := s) :=
 methodBase (language.symm ▸ baseFactory : SF.Factory W sourceCfg.LowVar s) f (n+1)
  (AS.nextSeed (factory baseFactory f) n data sourceCfg language)

-- A generated output receipt fixes the dependent codomain before language elimination.
-- No face, packet, equation, or completed family enters the source constructor.
structure InstalledFaces {U Y : Sorts → Type u} [∀ t, AddCommGroup (U t)]
 (frame : M.Frame (Value := U) (Var := Y) (sort := s))
 (method actual : A.Programme (PhysicalValue := U) (PhysicalVar := Y) (sort := s)) where
 face : SourceNativeRootSemanticFaceAt (S.root frame actual) (S.visit frame actual)
 packet : type_of% (Faces.material (A.epoch frame) method (S.actualOccurrence frame))
 source_readback : HEq face.rootRead packet
 original_face : packet = (Faces.face frame method).rootRead
 reader_source : packet.2.2.1 = (method.datum (A.epoch frame)).reader (S.actualOccurrence frame)
 fourFaces : type_of% (Faces.E.fourFaces (A.epoch frame) method (S.actualOccurrence frame) packet)
 dual_readback : type_of% (Faces.E.dual_readback (A.epoch frame) method (S.actualOccurrence frame) packet)

def templateFourFaces (baseFactory : SF.Factory W X s) (f : W s →+ W s)
 (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
 (language : sourceCfg.LowVar = X)
 (frame : M.Frame (Value := L.Value W (n+1)) (Var := sourceCfg.LowVar) (sort := s)) :
 InstalledFaces frame (templateMethod baseFactory f n data sourceCfg language)
  (AS.nextCfg (factory baseFactory f) n data sourceCfg language) := by
 cases sourceCfg with
 | mk Y datum inventory pairInventory =>
  change Y = X at language
  cases language
  let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
   ⟨X, datum, inventory, pairInventory⟩
  let method := methodBase baseFactory f (n+1) (AS.nextSeed (factory baseFactory f) n data cfg rfl)
  let actualFace := templateFace baseFactory f n data cfg rfl frame
  exact { face := actualFace
          packet := actualFace.rootRead
          source_readback := HEq.rfl
          original_face := rfl
          reader_source := rfl
          fourFaces := Faces.E.fourFaces (A.epoch frame) method (S.actualOccurrence frame) actualFace.rootRead
          dual_readback := Faces.E.dual_readback (A.epoch frame) method (S.actualOccurrence frame) actualFace.rootRead }

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
