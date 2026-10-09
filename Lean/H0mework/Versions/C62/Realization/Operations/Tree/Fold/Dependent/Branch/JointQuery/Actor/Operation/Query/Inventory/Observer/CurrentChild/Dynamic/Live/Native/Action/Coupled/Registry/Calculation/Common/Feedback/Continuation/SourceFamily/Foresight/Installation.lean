import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Model
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Decoder
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Next
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Facets
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Packet
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Installed
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base actualOccurrence actualVisit root visit baseRoot queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw)
end Q
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch optionalSourceRoot)
end E
namespace F
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower
  (configuration)
end F
namespace H
export Lower.SourceFamily.Foresight
  (Model sourceMap readPrefix next sourceCoordinates recoveredCurrent recoveredNext recovered_current)
end H
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
local instance stageGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (originalBinding : ∀ t, X t → Expr W X t) (n : Nat)
variable (seed : Lower.SourceFamily.Seed W X s n)
local notation "FrameAt" => M.Frame (Value := Lower.Value W n) (Var := X) (sort := s)
abbrev binding := Future.Replay.Binding.at originalBinding n
abbrev baseCfg := F.configuration (Future.Replay.Installed.programme (binding originalBinding n) seed)
abbrev OccurrenceIndex (frame : FrameAt) := Sigma fun current => SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)
def epochIndex (frame : FrameAt) : OccurrenceIndex n frame :=
  ⟨(Q.actualVisit (E.epoch frame)).current, Q.actualOccurrence (E.epoch frame)⟩
def SameEpochOccurrence (frame : FrameAt) (index : OccurrenceIndex n frame) : Prop :=
  index = epochIndex n frame

def nativeState (frame : FrameAt) : Lower.SourceFamily.Foresight.Tail.State (W := W) (X := X) (s := s) :=
  ⟨n, ⟨E.epoch frame, seed⟩⟩
def modelValues (frame : FrameAt) :=
  (H.sourceCoordinates originalBinding (nativeState n seed frame) 0,
   H.recoveredCurrent originalBinding (nativeState n seed frame) 0,
   H.recoveredNext originalBinding (nativeState n seed frame) 0,
   (fun t => H.sourceMap originalBinding (nativeState n seed frame) t 0),
   (fun t bound => H.readPrefix originalBinding (nativeState n seed frame) t 0 bound),
   (fun t => H.next originalBinding (nativeState n seed frame) t 0),
   (fun t => Lower.SourceFamily.Foresight.Successor.nextCharacter originalBinding (nativeState n seed frame) t),
   (fun t => Lower.SourceFamily.Foresight.logical originalBinding (nativeState n seed frame) t 0),
   (fun t => Lower.SourceFamily.Foresight.fullPrime originalBinding (nativeState n seed frame) t 0),
   (fun t => Lower.SourceFamily.Foresight.wordDual originalBinding (nativeState n seed frame) t 0))
abbrev High (frame : FrameAt) := type_of% (modelValues originalBinding n seed frame)
abbrev Low (frame : FrameAt) (index : OccurrenceIndex n frame) :=
  type_of% (Future.Replay.Source.material (binding originalBinding n) seed frame index.2)
def preciseHighAt (frame : FrameAt) (index : OccurrenceIndex n frame)
    (_same : SameEpochOccurrence n frame index) : High originalBinding n seed frame :=
  modelValues originalBinding n seed frame

def component (frame : FrameAt) : SourceNativeProjectionLaw (Q.base frame).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {current} supplied _ =>
    Low originalBinding n seed frame ⟨current, supplied⟩ ×
      (SameEpochOccurrence n frame ⟨current, supplied⟩ → High originalBinding n seed frame)
  project := fun _ {current} supplied _ =>
    ⟨Future.Replay.Source.material (binding originalBinding n) seed frame supplied,
      preciseHighAt originalBinding n seed frame ⟨current, supplied⟩⟩

def combined (frame : FrameAt) :=
  (E.optionalSourceRoot (Q.base frame).root ((baseCfg originalBinding n seed).datum frame).component).source.base.withProjectionCoface
    (component originalBinding n seed frame) |>.projectionLaw

def sourceHigh (frame : FrameAt) : High originalBinding n seed frame :=
  ((component originalBinding n seed (E.epoch frame)).project PUnit.unit
    (Q.actualOccurrence (E.epoch frame)) PUnit.unit).2 rfl

def sourceDecoder (frame : FrameAt) : Env (Lower.Value W n) X := fun t name =>
  ((sourceHigh originalBinding n seed frame).2.1 t name).1 +
    ((sourceHigh originalBinding n seed frame).2.1 t name).2

theorem source_decoder_generated (frame : FrameAt) :
    sourceDecoder originalBinding n seed frame =
      Lower.SourceFamily.Foresight.physicalDecoder originalBinding (nativeState n seed frame) 0 := rfl

def configuration := {baseCfg originalBinding n seed with datum := fun sourceFrame =>
  {((baseCfg originalBinding n seed).datum sourceFrame) with
    component := some (combined originalBinding n seed sourceFrame)
    calculationReader := none
    nextEnvironmentReadAt := none
    nextEnvironmentRead := some (fun _ => sourceDecoder originalBinding n seed sourceFrame)}}

def componentEmbedding (frame : FrameAt) := SourceNativeProjectionLaw.InstallationAt.componentCoface
  (E.optionalSourceRoot (Q.base frame).root ((baseCfg originalBinding n seed).datum frame).component).source.base
  (component originalBinding n seed frame)
def installation (frame : FrameAt) := (componentEmbedding originalBinding n seed (E.epoch frame)).trans
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (Q.base frame).root.source.base
    (combined originalBinding n seed (E.epoch frame))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.baseRoot frame (configuration originalBinding n seed)).source.base
    (Q.queryLaw (E.epoch frame) (configuration originalBinding n seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.queryRoot frame (configuration originalBinding n seed)).source.base
    (Q.resultLaw (E.epoch frame) (configuration originalBinding n seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.resultRoot frame (configuration originalBinding n seed)).source.base
    (Q.consumerLaw (E.epoch frame) (configuration originalBinding n seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Q.consumerRoot frame (configuration originalBinding n seed)).source.base
    (Q.compilationLaw (E.epoch frame) (configuration originalBinding n seed)))
def face (frame : FrameAt) : SourceNativeRootSemanticFaceAt
    (Q.root frame (configuration originalBinding n seed)) (Q.visit frame (configuration originalBinding n seed)) where
  projection := (installation originalBinding n seed frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem reader_preserved (frame : FrameAt) (index : OccurrenceIndex n frame) :
  ((configuration originalBinding n seed).datum frame).reader index.2 =
    ((baseCfg originalBinding n seed).datum frame).reader index.2 := rfl
theorem decoder_installed (frame : FrameAt) :
  ((configuration originalBinding n seed).datum frame).nextEnvironmentRead =
    some (fun _ => sourceDecoder originalBinding n seed frame) := rfl

theorem source_decoder_original (frame : FrameAt) :
    sourceDecoder originalBinding n seed frame =
      Future.Replay.Source.physicalNext (binding originalBinding n)
        (E.epoch frame) (Q.actualOccurrence (E.epoch frame)) :=
  Lower.SourceFamily.Foresight.decoder_source originalBinding (nativeState n seed frame) 0
theorem inventories_preserved :
  (configuration originalBinding n seed).nextInventory = (baseCfg originalBinding n seed).nextInventory ∧
  (configuration originalBinding n seed).nextPairInventory = (baseCfg originalBinding n seed).nextPairInventory := ⟨rfl, rfl⟩

theorem native_actual_index (frame : FrameAt) (depth : frame.depth = 0) :
  (⟨(Q.actualVisit frame).current, Q.actualOccurrence frame⟩ : OccurrenceIndex n frame) = epochIndex n frame := by
  cases frame with
  | mk N V old registered packetAt environment frameDepth inventory pairInventory =>
      change frameDepth = 0 at depth
      cases depth
      rfl

def actualHighRead (frame : FrameAt) (depth : frame.depth = 0) : High originalBinding n seed frame :=
  (face originalBinding n seed frame).rootRead.2 (native_actual_index n frame depth)
theorem actualHigh_read_rfl (frame : FrameAt) (depth : frame.depth = 0) :
  actualHighRead originalBinding n seed frame depth = modelValues originalBinding n seed frame := rfl

theorem supplied_material (frame : FrameAt) (index : OccurrenceIndex n frame) :
  ((component originalBinding n seed frame).project PUnit.unit index.2 PUnit.unit).1 =
    Future.Replay.Source.material (binding originalBinding n) seed frame index.2 := rfl

end Lower.SourceFamily.Foresight.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
