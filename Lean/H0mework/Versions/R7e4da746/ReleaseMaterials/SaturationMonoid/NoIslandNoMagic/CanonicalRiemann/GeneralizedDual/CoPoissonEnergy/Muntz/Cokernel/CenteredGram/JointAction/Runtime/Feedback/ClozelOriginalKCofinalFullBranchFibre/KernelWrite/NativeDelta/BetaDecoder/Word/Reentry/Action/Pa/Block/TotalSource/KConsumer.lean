import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.Born
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.OriginalKInheritance

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.KConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace H
export ActualNativeCofaceInheritance (OldProjection LawFibre Carrier sharedCarrier selectedCarrier sharedProjection shared_outcome receipt_epoch installationFibre)
end H
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative
  (originalState reader betaState request bareTargetRoot originLaw generatedAction)
end SN
namespace SP
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.Splice
  (born answeredState oldInstallation)
end SP
namespace OI
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry (oldInstallation)
end OI
namespace J
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly (oldInstallation)
end J
namespace R
export RootGeneratedDebtActivationJointSource.Successor.Restructuring (projection_original)
end R
namespace C
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current originalOccurrence)
end C
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base answeredState actualOccurrence)
end S
namespace I
export SourceOperationInquiry.Context.Installation (Occurrence)
end I
namespace Receipt
export SourceGeneratedInquiryReceiptAction (packetAt)
end Receipt
namespace AS
export ActualNativeRelationTransport.AS (stockCfg stockScalar)
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (bornAfterNative localNativeReceipt)
end AS
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A

section Word
variable {V X : Unit → Type} [∀ t, AddCommGroup (V t)]
variable (frame : A.M.Frame (Value := PairValue V) (Var := X) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue V) (PhysicalVar := X) (sort := ()))
variable (before : Inventory (V := V) (X := X) (s := ()))
variable (oldEnvironment : Env V X)
variable (admissions : List (AdmissionReceipt.Admission before (AS.stockScalar frame base)))
variable {α : Type} (expected : α)
variable (carried : H.Carrier expected frame)

private def betaInstallation := OI.oldInstallation (SN.originalState frame base)
  (SN.reader frame base before oldEnvironment admissions)

private def targetInstallation :=
  (J.oldInstallation (SN.betaState frame base before oldEnvironment admissions)
    (SN.request frame base before oldEnvironment admissions) (Receipt.packetAt frame (AS.stockCfg base))).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (SN.bareTargetRoot frame base before oldEnvironment admissions).source.base
      (SN.originLaw frame base before oldEnvironment admissions))

def spliceCarrier : H.Carrier expected (SP.born frame base before oldEnvironment admissions) := by
  let original := H.sharedCarrier expected frame (AS.stockCfg base) carried
  let beta := H.installationFibre expected
    (betaInstallation frame base before oldEnvironment admissions) original
  exact H.installationFibre expected (SP.oldInstallation frame base before oldEnvironment admissions)
    (H.installationFibre expected (targetInstallation frame base before oldEnvironment admissions)
      ⟨.inl beta.1, fun occurrence =>
        (R.projection_original (SN.betaState frame base before oldEnvironment admissions).root.toAuthoritativeRoot
          (SN.request frame base before oldEnvironment admissions) (Receipt.packetAt frame (AS.stockCfg base))
          occurrence beta.1).trans (beta.2 _)⟩)
end Word

namespace P
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa
  (programme lowBase nativeBorn)
end P
namespace B
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block
  (programme lowBase nativeBorn)
end B
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRSource
  (born continuation programme lowBase nativeBorn oldInstallation sourceLaw codeReader carryAt)
namespace Core
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRSource.Assembly
  (oldInstalled programme)
end Core
end F
namespace T
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born
  (programme oldConfiguration lowBase actualCurrent actualBorn sourceFace oldInstallation
    actual_whole_first actual_target_next sourceAt sourceLaw codeReader carryAt)
end T

namespace Point
universe u
abbrev At {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (old : RootInquiryStateAt N V) :=
  Σ current : V.Current,
    old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current

abbrev outcome {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (old : RootInquiryStateAt N V) (projection : old.root.source.base.projectionLaw.Projection)
    (point : At old) := old.root.source.base.projectionLaw.outcomeAt projection point.2

def left {α β : Type u} {actual : α} {expected : β} (_same : HEq actual expected) : α := actual

def read {α β : Type u} {actual : α} {expected : β} (same : HEq actual expected) : β :=
  cast (type_eq_of_heq same) actual

theorem read_eq {α β : Type u} {actual : α} {expected : β} (same : HEq actual expected) :
    read same = expected :=
  eq_of_heq ((cast_heq _ _).trans same)

structure Receipt {α β : Type u} (actual : α) (expected : β) where
  value : β
  transported : HEq actual value
  agrees : value = expected

def receipt {α β : Type u} {actual : α} {expected : β} (same : HEq actual expected) :
    Receipt actual expected where
  value := read same
  transported := (cast_heq (type_eq_of_heq same) actual).symm
  agrees := read_eq same

theorem Receipt.source {α β : Type u} {actual : α} {expected : β}
    (receipt : Receipt actual expected) : HEq actual expected :=
  receipt.transported.trans (heq_of_eq receipt.agrees)

theorem through4 {α β γ δ ε : Type u} {a : α} {b : β} {c : γ} {d : δ} {e : ε}
    (ab : HEq a b) (bc : HEq b c) (cd : HEq c d) (de : HEq d e) : HEq a e :=
  ab.trans (bc.trans (cd.trans de))

variable {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
variable (frame : A.M.Frame (Value := Value) (Var := Var) (sort := ()))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()))
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (atReceipt)
end Q
namespace Mat
export SourceGeneratedInquiryReceiptAction.Configured.Material (initial programme selected born)
end Mat
namespace Epoch
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end Epoch

private theorem transported_outcome
    (left right : A.M.Frame (Value := Value) (Var := Var) (sort := ())) (same : left = right)
    (projection : H.OldProjection right) (point : At left.old) :
    HEq (outcome left.old (Eq.mp (congrArg H.OldProjection same.symm) projection) point)
      (outcome right.old projection
        (Eq.mp (congrArg (fun f : A.M.Frame (Value := Value) (Var := Var) (sort := ()) => At f.old) same) point)) := by
  cases same
  rfl

def selectedProjection (projection : H.OldProjection frame) :
    H.OldProjection (Q.atReceipt cfg frame 0) := by
  have same := congrArg
    (fun f : A.M.Frame (Value := Value) (Var := Var) (sort := ()) => H.OldProjection f)
    (H.receipt_epoch frame cfg).symm
  exact Eq.mp same projection

def selectedPoint (point : At (Q.atReceipt cfg frame 0).old) : At frame.old := by
  have same := congrArg
    (fun f : A.M.Frame (Value := Value) (Var := Var) (sort := ()) => At f.old)
    (H.receipt_epoch frame cfg)
  exact Eq.mp same point

theorem selected_outcome (projection : H.OldProjection frame)
    (point : At (Q.atReceipt cfg frame 0).old) :
    HEq (outcome (Q.atReceipt cfg frame 0).old (selectedProjection frame cfg projection) point)
      (outcome frame.old projection (selectedPoint frame cfg point)) :=
  transported_outcome (Epoch.epoch (Q.atReceipt cfg frame 0)) (Epoch.epoch frame)
    (H.receipt_epoch frame cfg) projection point

variable (low : A.Programme (PhysicalValue := PairValue Value) (PhysicalVar := cfg.LowVar) (sort := ()))

def materialProjection
    (projection : (S.answeredState frame cfg).root.source.base.projectionLaw.Projection) :
    H.OldProjection (Mat.born frame cfg low) :=
  H.sharedProjection (Mat.selected frame cfg low) (Mat.programme frame cfg low)
    (selectedProjection (Mat.initial frame cfg) (Mat.programme frame cfg low) projection)

def materialPoint (point : At (Mat.born frame cfg low).old) : At (S.answeredState frame cfg) :=
  selectedPoint (Mat.initial frame cfg) (Mat.programme frame cfg low)
    ⟨_, C.originalOccurrence (Mat.selected frame cfg low).registered
      (Mat.selected frame cfg low).packetAt point.2⟩

theorem material_outcome
    (projection : (S.answeredState frame cfg).root.source.base.projectionLaw.Projection)
    (point : At (Mat.born frame cfg low).old) :
    HEq (outcome (Mat.born frame cfg low).old (materialProjection frame cfg low projection) point)
      (outcome (S.answeredState frame cfg) projection (materialPoint frame cfg low point)) :=
  (H.shared_outcome (Mat.selected frame cfg low) (Mat.programme frame cfg low)
    (selectedProjection (Mat.initial frame cfg) (Mat.programme frame cfg low) projection) point.2).trans
    (selected_outcome (Mat.initial frame cfg) (Mat.programme frame cfg low) projection
      ⟨_, C.originalOccurrence (Mat.selected frame cfg low).registered
        (Mat.selected frame cfg low).packetAt point.2⟩)
end Point

namespace Assembly
variable {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
variable (baseProgramme : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()))
variable (law : (receiver : A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
  SourceNativeProjectionLaw (S.base receiver).root.source.base.restructuringSource.toLedgerSource)
variable (reader : (receiver : A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
  {current : C.Current receiver.registered} → I.Occurrence receiver (current := current) →
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue Value) (Var := baseProgramme.LowVar) (sort := ()))
variable (carry : (receiver : A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
  {current : C.Current receiver.registered} → I.Occurrence receiver (current := current) →
  Option (Inventory (V := PairValue (PairValue Value)) (X := baseProgramme.LowVar) (s := ())))
variable (receiver : A.M.Frame (Value := Value) (Var := Var) (sort := ()))
local notation "cfg" => F.Core.programme baseProgramme law reader carry

def projection (oldProjection : H.OldProjection receiver) :
    (S.answeredState receiver cfg).root.source.base.projectionLaw.Projection :=
  (F.Core.oldInstalled baseProgramme law reader carry receiver).embed
    (H.sharedProjection receiver baseProgramme oldProjection)

theorem outcome (oldProjection : H.OldProjection receiver)
    {current : C.Current receiver.registered} (supplied : I.Occurrence receiver (current := current)) :
    type_of% (((F.Core.oldInstalled baseProgramme law reader carry receiver).outcome_heq supplied
    (H.sharedProjection receiver baseProgramme oldProjection)).trans
      (H.shared_outcome receiver baseProgramme oldProjection supplied)) :=
  ((F.Core.oldInstalled baseProgramme law reader carry receiver).outcome_heq supplied
    (H.sharedProjection receiver baseProgramme oldProjection)).trans
      (H.shared_outcome receiver baseProgramme oldProjection supplied)
end Assembly

namespace SourcePath
variable {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
variable (baseProgramme : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()))
variable (law : (receiver : A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
  SourceNativeProjectionLaw (S.base receiver).root.source.base.restructuringSource.toLedgerSource)
variable (reader : (receiver : A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
  {current : C.Current receiver.registered} → I.Occurrence receiver (current := current) →
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue Value) (Var := baseProgramme.LowVar) (sort := ()))
variable (carry : (receiver : A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
  {current : C.Current receiver.registered} → I.Occurrence receiver (current := current) →
  Option (Inventory (V := PairValue (PairValue Value)) (X := baseProgramme.LowVar) (s := ())))
variable (receiver : A.M.Frame (Value := Value) (Var := Var) (sort := ()))
variable (low : A.Programme (PhysicalValue := PairValue Value) (PhysicalVar := ((F.Core.programme baseProgramme law reader carry)).LowVar) (sort := ()))
variable (nextLaw : (child : A.M.Frame (Value := PairValue Value) (Var := ((F.Core.programme baseProgramme law reader carry)).LowVar) (sort := ())) →
  SourceNativeProjectionLaw (S.base child).root.source.base.restructuringSource.toLedgerSource)
variable (nextReader : (child : A.M.Frame (Value := PairValue Value) (Var := ((F.Core.programme baseProgramme law reader carry)).LowVar) (sort := ())) →
  {current : C.Current child.registered} → I.Occurrence child (current := current) →
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue (PairValue Value)) (Var := ((Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low)).LowVar) (sort := ()))
variable (nextCarry : (child : A.M.Frame (Value := PairValue Value) (Var := ((F.Core.programme baseProgramme law reader carry)).LowVar) (sort := ())) →
  {current : C.Current child.registered} → I.Occurrence child (current := current) →
  Option (Inventory (V := PairValue (PairValue (PairValue Value))) (X := ((Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low)).LowVar) (s := ())))
variable {α : Type} (expected : α) (carried : H.Carrier expected receiver)

include baseProgramme law reader carry receiver low nextLaw nextReader nextCarry expected carried in
def projection : (S.answeredState (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) (F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry)).root.source.base.projectionLaw.Projection :=
  Assembly.projection (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low)
    (Point.materialProjection receiver (F.Core.programme baseProgramme law reader carry) low
      (Assembly.projection baseProgramme law reader carry receiver carried.1))

include baseProgramme law reader carry receiver low nextLaw nextReader nextCarry in
def oldPoint (actual : Point.At (S.answeredState (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) (F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry))) :=
  Point.materialPoint receiver (F.Core.programme baseProgramme law reader carry) low
    ⟨_, C.originalOccurrence ((Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low)).registered ((Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low)).packetAt actual.2⟩

include baseProgramme law reader carry receiver low nextLaw nextReader nextCarry expected carried in
def readAt (actual : Point.At (S.answeredState (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) (F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry))) :
    Point.Receipt (Point.outcome (S.answeredState (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) (F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry))
      (projection baseProgramme law reader carry receiver low nextLaw nextReader nextCarry expected carried) actual) expected := by
  let prior := oldPoint baseProgramme law reader carry receiver low nextLaw nextReader nextCarry actual
  let first := Assembly.projection baseProgramme law reader carry receiver carried.1
  let inherited := Point.materialProjection receiver (F.Core.programme baseProgramme law reader carry) low first
  exact Point.receipt <| Point.through4
    (Assembly.outcome (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) inherited actual.2)
    (Point.material_outcome receiver (F.Core.programme baseProgramme law reader carry) low first
      ⟨_, C.originalOccurrence ((Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low)).registered ((Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low)).packetAt actual.2⟩)
    (Assembly.outcome baseProgramme law reader carry receiver carried.1 prior.2)
    (carried.2 (C.originalOccurrence receiver.registered receiver.packetAt prior.2))

variable (nextLow : A.Programme (PhysicalValue := PairValue (PairValue Value))
  (PhysicalVar := ((F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry)).LowVar) (sort := ()))

include baseProgramme law reader carry receiver low nextLaw nextReader nextCarry expected carried nextLow in
def nextProjection : H.OldProjection (Point.Mat.born (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) (F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry) nextLow) :=
  Point.materialProjection (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) (F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry) nextLow
    (projection baseProgramme law reader carry receiver low nextLaw nextReader nextCarry expected carried)

include baseProgramme law reader carry receiver low nextLaw nextReader nextCarry expected carried nextLow in
def nextReadAt (actual : Point.At ((Point.Mat.born (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) (F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry) nextLow)).old) :
    Point.Receipt (Point.outcome ((Point.Mat.born (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) (F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry) nextLow)).old
      (nextProjection baseProgramme law reader carry receiver low nextLaw nextReader nextCarry expected carried nextLow) actual) expected :=
  Point.receipt <| (Point.material_outcome (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) (F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry) nextLow
    (projection baseProgramme law reader carry receiver low nextLaw nextReader nextCarry expected carried) actual).trans
    (readAt baseProgramme law reader carry receiver low nextLaw nextReader nextCarry expected carried
      (Point.materialPoint (Point.Mat.born receiver (F.Core.programme baseProgramme law reader carry) low) (F.Core.programme (Point.Mat.programme receiver (F.Core.programme baseProgramme law reader carry) low) nextLaw nextReader nextCarry) nextLow actual)).source
end SourcePath

namespace N
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction (BaseValue)
end N
namespace FC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRCode (Value)
end FC
namespace L
export ActualNativeCofaceInheritance.L (Value groups)
end L
namespace K
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.OriginalKInheritance
  (sourceCarrier originalMaterial originalOutcome sourceNative)
end K
namespace D
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFirstFullSourceDynamics
  (factory)
end D
namespace NS
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma
  (NativeFactory NativePacket)
end NS
namespace WordNative
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (beforeStock beforeEnvironment admissions)
end WordNative

local instance baseGroups (initial : Nat) : ∀ t, AddCommGroup (N.BaseValue initial t) :=
  L.groups (PairValue NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback.Value) initial
local instance originGroups (initial : Nat) : ∀ t, AddCommGroup (L.Value (N.BaseValue initial) 2 t) :=
  L.groups (N.BaseValue initial) 2
local instance runtimeGroups (initial : Nat) : ∀ t, AddCommGroup (L.Value (L.Value (N.BaseValue initial) 2) 0 t) :=
  L.groups (L.Value (N.BaseValue initial) 2) 0
local instance valueGroups (initial : Nat) : ∀ t, AddCommGroup (FC.Value initial t) :=
  L.groups (N.BaseValue initial) 5

open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace CV
export OriginalKCombReceiptFeedback (Var)
end CV
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
section Pipeline
variable (initial : Nat)
variable (frame : A.M.Frame (Value := PairValue (N.BaseValue initial)) (Var := CV.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (N.BaseValue initial)) (PhysicalVar := CV.Var) (sort := ()))
variable (before : Inventory (V := N.BaseValue initial) (X := CV.Var) (s := ()))
variable (oldEnvironment : Env (N.BaseValue initial) CV.Var)
variable (admissions : List (AdmissionReceipt.Admission before (AS.stockScalar frame base)))
variable {α : Type} (expected : α) (carried : H.Carrier expected frame)
local notation "sf" => SP.born frame base before oldEnvironment admissions
local notation "current" => T.actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sf
local notation "cfg" => T.programme initial frame base before oldEnvironment admissions observation nontrivial half sf


local notation "fullLaw" => (fun receiver => F.sourceLaw observation nontrivial half initial frame base before oldEnvironment admissions sf receiver)
local notation "fullReader" => (fun receiver {_current} supplied => F.codeReader observation nontrivial half initial frame base before oldEnvironment admissions sf receiver supplied)
local notation "fullCarry" => (fun receiver {_current} supplied => F.carryAt observation nontrivial half initial frame base before oldEnvironment admissions sf receiver supplied)
local notation "totalLaw" => (fun receiver => T.sourceLaw initial frame base before oldEnvironment admissions receiver)
local notation "totalReader" => (fun receiver {_current} supplied => T.codeReader initial frame base before oldEnvironment admissions observation nontrivial half receiver supplied)
local notation "totalCarry" => (fun receiver {_current} supplied => T.carryAt initial frame base before oldEnvironment admissions observation nontrivial half sf receiver supplied)

def paCarrier : H.Carrier expected
    (P.nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions sf) :=
  ActualNativeCofaceInheritance.materialCarrier expected sf
    (P.programme observation nontrivial half initial frame base before oldEnvironment admissions)
    (P.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sf)
    (spliceCarrier frame base before oldEnvironment admissions expected carried)

def blockCarrier : H.Carrier expected
    (F.born observation nontrivial half initial frame base before oldEnvironment admissions sf) :=
  ActualNativeCofaceInheritance.materialCarrier expected
    (P.nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions sf)
    (B.programme observation nontrivial half initial frame base before oldEnvironment admissions sf)
    (B.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sf)
    (paCarrier observation nontrivial half initial frame base before oldEnvironment admissions expected carried)

def fullProjection :=
  Assembly.projection
    (F.continuation observation nontrivial half initial frame base before oldEnvironment admissions sf)
    fullLaw fullReader fullCarry
    (F.born observation nontrivial half initial frame base before oldEnvironment admissions sf)
    (blockCarrier observation nontrivial half initial frame base before oldEnvironment admissions expected carried).1

def currentProjection := Point.materialProjection
  (F.born observation nontrivial half initial frame base before oldEnvironment admissions sf)
  (F.programme observation nontrivial half initial frame base before oldEnvironment admissions sf)
  (F.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sf)
  (fullProjection observation nontrivial half initial frame base before oldEnvironment admissions expected carried)

def totalProjection :=
  Assembly.projection
    (T.oldConfiguration initial frame base before oldEnvironment admissions observation nontrivial half sf)
    totalLaw totalReader totalCarry current
    (currentProjection observation nontrivial half initial frame base before oldEnvironment admissions expected carried)

def sourcePoint (actual : Point.At (S.answeredState current cfg)) :=
  Point.materialPoint
    (F.born observation nontrivial half initial frame base before oldEnvironment admissions sf)
    (F.programme observation nontrivial half initial frame base before oldEnvironment admissions sf)
    (F.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sf)
    ⟨_, C.originalOccurrence (current).registered (current).packetAt actual.2⟩

def sourceReadAt (actual : Point.At (S.answeredState current cfg)) :=
  SourcePath.readAt
    (F.continuation observation nontrivial half initial frame base before oldEnvironment admissions sf)
    fullLaw fullReader fullCarry
    (F.born observation nontrivial half initial frame base before oldEnvironment admissions sf)
    (F.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sf)
    totalLaw totalReader totalCarry expected
    (blockCarrier observation nontrivial half initial frame base before oldEnvironment admissions expected carried) actual

def nextProjection := Point.materialProjection current cfg
  (T.lowBase initial frame base before oldEnvironment admissions observation nontrivial half sf current)
  (totalProjection observation nontrivial half initial frame base before oldEnvironment admissions expected carried)

def nextPoint : Point.At (T.actualBorn initial frame base before oldEnvironment admissions observation nontrivial half sf).old :=
  let born := T.actualBorn initial frame base before oldEnvironment admissions observation nontrivial half sf
  ⟨_, C.originalOccurrence born.registered born.packetAt (S.actualOccurrence born)⟩

def nextReadAt :=
  SourcePath.nextReadAt
    (F.continuation observation nontrivial half initial frame base before oldEnvironment admissions sf)
    fullLaw fullReader fullCarry
    (F.born observation nontrivial half initial frame base before oldEnvironment admissions sf)
    (F.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sf)
    totalLaw totalReader totalCarry expected
    (blockCarrier observation nontrivial half initial frame base before oldEnvironment admissions expected carried)
    (T.lowBase initial frame base before oldEnvironment admissions observation nontrivial half sf current)
    (nextPoint observation nontrivial half initial frame base before oldEnvironment admissions)
def inputPoint : Point.At (S.answeredState current cfg) := ⟨_, S.actualOccurrence current⟩

def inputRead :=
  (sourceReadAt (α := α) observation nontrivial half initial frame base before oldEnvironment admissions expected carried
    (inputPoint observation nontrivial half initial frame base before oldEnvironment admissions)).value

theorem input_read_source :
    inputRead observation nontrivial half initial frame base before oldEnvironment admissions expected carried = expected := by
  exact (sourceReadAt (α := α) observation nontrivial half initial frame base before oldEnvironment admissions expected carried
    (inputPoint observation nontrivial half initial frame base before oldEnvironment admissions)).agrees

end Pipeline

attribute [local irreducible] ActualNativeCofaceInheritance.ProjectionFibre

section ReadAt
variable (depth initial : Nat)
variable (frame : A.M.Frame (Value := PairValue (N.BaseValue initial)) (Var := CV.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (N.BaseValue initial)) (PhysicalVar := CV.Var) (sort := ()))
variable (before : Inventory (V := N.BaseValue initial) (X := CV.Var) (s := ()))
variable (oldEnvironment : Env (N.BaseValue initial) CV.Var)
variable (admissions : List (AdmissionReceipt.Admission before (AS.stockScalar frame base)))
variable (carried : H.Carrier (α := type_of% (K.originalOutcome observation nontrivial half depth)) (K.originalOutcome observation nontrivial half depth) frame)
local notation "sf" => SP.born frame base before oldEnvironment admissions
local notation "current" => T.actualCurrent initial frame base before oldEnvironment admissions observation nontrivial half sf
local notation "cfg" => T.programme initial frame base before oldEnvironment admissions observation nontrivial half sf

def inputMaterial : type_of% (K.originalMaterial observation nontrivial half depth) :=
  match inputRead observation nontrivial half initial frame base before oldEnvironment admissions (K.originalOutcome observation nontrivial half depth) carried with
  | .inl actual => actual.2
  | .inr impossible => nomatch impossible

theorem input_material_source :
    inputMaterial observation nontrivial half depth initial frame base before oldEnvironment admissions carried =
      K.originalMaterial observation nontrivial half depth := by
  unfold inputMaterial
  rw [input_read_source]
  rfl

def inputReceipt :=
  (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit
    (inputMaterial observation nontrivial half depth initial frame base before oldEnvironment admissions carried).1).effect.originalK.receiptAt
      (by change 1 / 2 < observation.coordinate.re; exact half.down))

theorem input_receipt_source :
    (inputReceipt observation nontrivial half depth initial frame base before oldEnvironment admissions carried).1 =
        installedOriginalKReceiptAt observation nontrivial half.down ∧
      (inputMaterial observation nontrivial half depth initial frame base before oldEnvironment admissions carried).1 =
        (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence ∧
      (type_of% (runtimeEffectFacadeReadoutAt_factorizes observation nontrivial depth)) := by
  have material := input_material_source observation nontrivial half depth initial frame base before oldEnvironment admissions carried
  refine ⟨?_, ?_, runtimeEffectFacadeReadoutAt_factorizes observation nontrivial depth⟩
  · dsimp only [inputReceipt]
    rw [material]
    rfl
  · rw [material]
    rfl

private def bundleAt :=
  let source := (T.sourceFace initial frame base before oldEnvironment admissions observation nontrivial half sf current).rootRead
  let reader := SourceGeneratedInquiryReceiptAction.actionReader current cfg (S.actualOccurrence current)
  let currentRead := sourceReadAt (α := type_of% (K.originalOutcome observation nontrivial half depth)) observation nontrivial half initial frame base before oldEnvironment admissions (K.originalOutcome observation nontrivial half depth) carried
    (inputPoint observation nontrivial half initial frame base before oldEnvironment admissions)
  let material := inputMaterial observation nontrivial half depth initial frame base before oldEnvironment admissions carried
  let receipt := inputReceipt observation nontrivial half depth initial frame base before oldEnvironment admissions carried
  let born := T.actualBorn initial frame base before oldEnvironment admissions observation nontrivial half sf
  let nextRead := nextReadAt (α := type_of% (K.originalOutcome observation nontrivial half depth)) observation nontrivial half initial frame base before oldEnvironment admissions (K.originalOutcome observation nontrivial half depth) carried
  let actualData := (source,reader,currentRead,material,receipt,born,nextRead)
  PProd.mk actualData <|
    And.intro (input_receipt_source observation nontrivial half depth initial frame base before oldEnvironment admissions carried) <|
      And.intro (T.actual_whole_first initial frame base before oldEnvironment admissions observation nontrivial half sf)
        (T.actual_target_next initial frame base before oldEnvironment admissions observation nontrivial half sf)

def ResultAt := type_of% (bundleAt observation nontrivial half depth initial frame base before oldEnvironment admissions carried)

def readAt : ResultAt observation nontrivial half depth initial frame base before oldEnvironment admissions carried :=
  bundleAt observation nontrivial half depth initial frame base before oldEnvironment admissions carried
end ReadAt

attribute [local irreducible] ResultAt
variable (depth : Nat)
variable (factory : NS.NativeFactory) (packet : NS.NativePacket)

private def InputAt {α : Type} (expected : α) (initial : Nat) (varFamily : Unit → Type) :=
  Σ frame : A.M.Frame (Value := PairValue (N.BaseValue initial)) (Var := varFamily) (sort := ()),
  Σ base : A.Programme (PhysicalValue := PairValue (N.BaseValue initial)) (PhysicalVar := varFamily) (sort := ()),
  Σ before : Inventory (V := N.BaseValue initial) (X := varFamily) (s := ()),
  Env (N.BaseValue initial) varFamily ×
    List (AdmissionReceipt.Admission before (AS.stockScalar frame base)) × H.Carrier expected frame

def packetRead
    (stock : Inventory (V := N.BaseValue packet.1) (X := packet.2.2.1.LowVar) (s := ()))
    (environment : Env (N.BaseValue packet.1) packet.2.2.1.LowVar)
    (admissions : List (AdmissionReceipt.Admission stock
      (AS.stockScalar (ActualCofinalSourceAction.selected factory packet)
        (ActualCofinalSourceAction.nativePacket factory packet).2.2.1)))
    (carried : H.Carrier (K.originalOutcome observation nontrivial half depth)
      (ActualCofinalSourceAction.selected factory packet)) :=
  let source : InputAt (K.originalOutcome observation nontrivial half depth) packet.1 packet.2.2.1.LowVar :=
    ⟨ActualCofinalSourceAction.selected factory packet,
      (ActualCofinalSourceAction.nativePacket factory packet).2.2.1,stock,environment,admissions,carried⟩
  let target : InputAt (K.originalOutcome observation nontrivial half depth) packet.1 CV.Var :=
    Eq.mp (congrArg (InputAt (K.originalOutcome observation nontrivial half depth) packet.1) packet.2.2.2.down) source
  let output := readAt observation nontrivial half depth packet.1 target.1 target.2.1 target.2.2.1
    target.2.2.2.1 target.2.2.2.2.1 target.2.2.2.2.2
  let maternal := inputMaterial observation nontrivial half depth packet.1 target.1 target.2.1 target.2.2.1
    target.2.2.2.1 target.2.2.2.2.1 target.2.2.2.2.2
  let receipt := inputReceipt observation nontrivial half depth packet.1 target.1 target.2.1 target.2.2.1
    target.2.2.2.1 target.2.2.2.2.1 target.2.2.2.2.2
  let sourceProof := input_material_source observation nontrivial half depth packet.1 target.1 target.2.1 target.2.2.1
    target.2.2.2.1 target.2.2.2.2.1 target.2.2.2.2.2
  PProd.mk
    (⟨maternal,receipt,sourceProof⟩ :
      Σ material : type_of% (K.originalMaterial observation nontrivial half depth),
        PProd (type_of% (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit material.1).effect.originalK.receiptAt half.down))
          (material = K.originalMaterial observation nontrivial half depth))
    output

attribute [local irreducible] AS.localNativeReceipt
variable (ordinal : Nat)
local notation "native" => K.sourceNative observation nontrivial half depth (ordinal+1)
local notation "factory₀" => D.factory observation nontrivial half

def originalRead := packetRead observation nontrivial half depth factory₀ (AS.bornAfterNative native)
  (WordNative.beforeStock native) (WordNative.beforeEnvironment native) (WordNative.admissions factory₀ native)
  (K.sourceCarrier observation nontrivial half depth (ordinal+1))

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.KConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
