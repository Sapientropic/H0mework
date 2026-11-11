import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Admissions
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Material.Consumer

/-! The same source-owned whole fibre follows original admissions, paid prefixes
and native births. This transports an existing law; it creates no coface. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativeCofaceInheritance
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift

namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch epoch_math)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (answeredState baseInstallation frames next nextBorn baseRoot queryRoot resultRoot consumerRoot
    queryLaw resultLaw consumerLaw compilationLaw)
end S
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
  (receipt atReceipt)
end Q
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix
  (receipt_read)
end Prefix
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
  (Factory Packet)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
  (Value groups)
end L
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (AdmissionPacket nativeAfterAdmission bornAfterNative stockCfg receiver nextSeed nextBase)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
  (packetAt packetAt_successor)
end D
namespace SS
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
  (receiver nextCfg born)
end SS

variable {Sorts : Type u} {Value Var : Sorts → Type u}
variable [∀ target, AddCommGroup (Value target)] {sort : Sorts}

abbrev OldProjection (frame : M.Frame (Value := Value) (Var := Var) (sort := sort)) :=
  frame.old.root.source.base.projectionLaw.Projection

def sharedInstallation
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort)) :=
  (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly.oldInstallation
    frame.old frame.registered frame.packetAt).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      frame.currentState.root.source.base
      (SourceOperationInquiry.Context.Installation.component (A.epoch frame))) |>.trans
    (S.baseInstallation frame cfg) |>.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (S.baseRoot frame cfg).source.base (S.queryLaw (A.epoch frame) cfg)) |>.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (S.queryRoot frame cfg).source.base (S.resultLaw (A.epoch frame) cfg)) |>.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (S.resultRoot frame cfg).source.base (S.consumerLaw (A.epoch frame) cfg)) |>.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (S.consumerRoot frame cfg).source.base (S.compilationLaw (A.epoch frame) cfg))

def sharedProjection
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (projection : OldProjection frame) :
    (S.answeredState frame cfg).root.source.base.projectionLaw.Projection :=
  (sharedInstallation frame cfg).embed (.inl projection)

theorem shared_outcome
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (projection : OldProjection frame)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : (S.answeredState frame cfg).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    HEq ((S.answeredState frame cfg).root.source.base.projectionLaw.outcomeAt
      (sharedProjection frame cfg projection) occurrence)
      (frame.old.root.source.base.projectionLaw.outcomeAt projection
        (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
          frame.registered frame.packetAt occurrence)) :=
  ((sharedInstallation frame cfg).outcome_heq occurrence (.inl projection)).trans
    (RootGeneratedDebtActivationJointSource.Successor.Restructuring.projection_original
      frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt occurrence projection)

abbrev WholeInvariant {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (projection : OldProjection frame) : Prop :=
  ∀ {current : frame.V.Current}
    (occurrence : frame.old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current),
    HEq (frame.old.root.source.base.projectionLaw.outcomeAt projection occurrence) expected

def ProjectionFibre {α : Type u} (expected : α)
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}} {source : SourceNativeLedgerSource N V}
    (law : SourceNativeProjectionLaw source) :=
  { projection : law.Projection //
    ∀ {current : V.Current}
      (occurrence : source.source.toRootSource.actual.OccurrenceAt current),
      HEq (law.outcomeAt projection occurrence) expected }

abbrev LawFibre {α : Type u} (expected : α)
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}} (old : RootInquiryStateAt N V) :=
  ProjectionFibre expected old.root.source.base.projectionLaw

def installationFibre {α : Type u} (expected : α)
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}} {source : SourceNativeLedgerSource N V}
    {base target : SourceNativeProjectionLaw source}
    (installation : SourceNativeProjectionLaw.InstallationAt base target)
    (carried : ProjectionFibre expected base) : ProjectionFibre expected target :=
  ⟨installation.embed carried.1,
    fun occurrence => (installation.outcome_heq occurrence carried.1).trans (carried.2 _)⟩

abbrev Carrier {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort)) :=
  LawFibre expected frame.old

def makeCarrier {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (projection : OldProjection frame) (whole : WholeInvariant expected frame projection) :
    Carrier expected frame := ⟨projection, whole⟩

def carrierProjection {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (carried : Carrier expected frame) : OldProjection frame := carried.1

theorem carrier_whole {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (carried : Carrier expected frame) :
    WholeInvariant expected frame (carrierProjection expected frame carried) := carried.2

theorem shared_invariant {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (projection : OldProjection frame) (whole : WholeInvariant expected frame projection) :
    WholeInvariant expected (SourceGeneratedInquiryReceiptAction.bornFrame frame cfg)
      (sharedProjection frame cfg projection) := by
  intro current occurrence
  exact (shared_outcome frame cfg projection occurrence).trans (whole _)

def sharedCarrier {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (carried : Carrier expected frame) :
    Carrier expected (SourceGeneratedInquiryReceiptAction.bornFrame frame cfg) :=
  ⟨sharedProjection frame cfg carried.1,
    shared_invariant expected frame cfg carried.1 carried.2⟩

theorem receipt_epoch
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort)) :
    A.epoch (Q.atReceipt cfg frame 0) = A.epoch frame := by
  apply Prefix.receipt_read cfg frame (fun stage => A.epoch (S.frames frame cfg stage))
  intro stage paid actual
  have same : S.frames frame cfg (stage + 1) = (S.frames frame cfg stage).mathNext := by
    change S.next _ cfg = _
    unfold S.next
    rw [actual]
  exact (congrArg A.epoch same).trans (A.epoch_math _)

def selectedCarrier {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (carried : Carrier expected frame) : Carrier expected (Q.atReceipt cfg frame 0) := by
  have same := congrArg
    (fun current : M.Frame (Value := Value) (Var := Var) (sort := sort) => Carrier expected current)
    (receipt_epoch frame cfg).symm
  exact Eq.mp same carried

def bornCarrier {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (carried : Carrier expected frame) :
    Carrier expected (S.nextBorn (Q.atReceipt cfg frame 0) cfg) :=
  let selected := selectedCarrier expected frame cfg carried
  ⟨sharedProjection (Q.atReceipt cfg frame 0) cfg selected.1,
    shared_invariant expected (Q.atReceipt cfg frame 0) cfg selected.1 selected.2⟩

local instance familyGroups (grade : Nat) (target : Sorts) :
    AddCommGroup (L.Value Value grade target) := L.groups Value grade target

private def packetTransport {Y Z : Sorts → Type u} (same : Y = Z) :
    AS.AdmissionPacket (W := Value) (X := Y) (s := sort) →
    AS.AdmissionPacket (W := Value) (X := Z) (s := sort) := by
  cases same
  exact id

private def packetCarrierTransport {α : Type u} (expected : α)
    {Y Z : Sorts → Type u} (same : Y = Z)
    (packet : AS.AdmissionPacket (W := Value) (X := Y) (s := sort))
    (carried : Carrier expected packet.2.1.1) :
    Carrier expected (packetTransport same packet).2.1.1 := by
  cases same
  exact carried

def nativeCarrier {α : Type u} (expected : α)
    (factory : SF.Factory Value Var sort)
    (packet : AS.AdmissionPacket (W := Value) (X := Var) (s := sort))
    (carried : Carrier expected packet.2.1.1) :
    Carrier expected (AS.nativeAfterAdmission factory packet).2.1.1 :=
  packetCarrierTransport expected packet.2.2.2.down
    ⟨packet.1 + 1,
      ⟨AS.receiver factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
        AS.nextSeed factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
      AS.nextBase factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down, ⟨rfl⟩⟩
    ⟨sharedProjection packet.2.1.1 packet.2.2.1 carried.1,
      shared_invariant expected packet.2.1.1 packet.2.2.1 carried.1 carried.2⟩

def stoppedCarrier {α : Type u} (expected : α)
    (packet : AS.AdmissionPacket (W := Value) (X := Var) (s := sort))
    (carried : Carrier expected packet.2.1.1) :
    Carrier expected (AS.bornAfterNative packet).2.1.1 :=
  bornCarrier expected packet.2.1.1 (AS.stockCfg packet.2.2.1) carried

/-- The raw receiver keeps its own LowVar family at the actual Word source stop. -/
def sourceSelectedCarrier {α : Type u} (expected : α)
    (factory : SF.Factory Value Var sort)
    (packet : AS.AdmissionPacket (W := Value) (X := Var) (s := sort))
    (carried : Carrier expected packet.2.1.1) :
    Carrier expected (ActualCofinalSourceAction.selected factory packet) :=
  selectedCarrier expected (ActualCofinalSourceAction.nativePacket factory packet).2.1.1
    (AS.stockCfg (ActualCofinalSourceAction.nativePacket factory packet).2.2.1)
    (sharedCarrier expected packet.2.1.1 packet.2.2.1 carried)

def ordinalCarrier {α : Type u} (expected : α)
    (factory : SF.Factory Value Var sort)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (language : cfg.LowVar = Var)
    (carried : Carrier expected frame) :
    (ordinal : Nat) → Carrier expected (D.packetAt factory frame cfg language ordinal).2.1.1
  | 0 => carried
  | ordinal + 1 => by
    rw [D.packetAt_successor]
    exact stoppedCarrier expected _ (nativeCarrier expected factory _
      (ordinalCarrier expected factory frame cfg language carried ordinal))

def configuredCarrier {W X : PUnit.{u + 1} → Type u} [∀ target, AddCommGroup (W target)]
    {α : Type u} (expected : α)
    (factory : SF.Factory W X PUnit.unit) (grade : Nat)
    (data : SF.Packet (W := W) (X := X) (s := PUnit.unit) grade)
    (cfg : A.Programme (PhysicalValue := L.Value W grade) (PhysicalVar := X) (sort := PUnit.unit))
    (language : cfg.LowVar = X) (carried : Carrier expected data.1) :
    Carrier expected (SS.born factory grade data cfg language) :=
  bornCarrier expected (SS.receiver factory grade data cfg language)
    (SS.nextCfg factory grade data cfg language)
    (sharedCarrier expected data.1 cfg carried)

def materialSourceCarrier {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (low : A.Programme (PhysicalValue := PairValue Value) (PhysicalVar := cfg.LowVar) (sort := sort))
    (carried : LawFibre expected (S.answeredState frame cfg)) :
    Carrier expected (SourceGeneratedInquiryReceiptAction.Configured.Material.born frame cfg low) :=
  bornCarrier expected (SourceGeneratedInquiryReceiptAction.Configured.Material.initial frame cfg)
    (SourceGeneratedInquiryReceiptAction.Configured.Material.programme frame cfg low) carried

def materialCarrier {α : Type u} (expected : α)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (low : A.Programme (PhysicalValue := PairValue Value) (PhysicalVar := cfg.LowVar) (sort := sort))
    (carried : Carrier expected frame) :
    Carrier expected (SourceGeneratedInquiryReceiptAction.Configured.Material.born frame cfg low) :=
  materialSourceCarrier expected frame cfg low (sharedCarrier expected frame cfg carried)

def readFibre {α : Type u} (expected : α)
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}} (old : RootInquiryStateAt N V)
    (carried : LawFibre expected old) {current : V.Current}
    (occurrence : old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) : α :=
  cast (type_eq_of_heq (carried.2 occurrence))
    (old.root.source.base.projectionLaw.outcomeAt carried.1 occurrence)

theorem read_fibre_eq {α : Type u} (expected : α)
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}} (old : RootInquiryStateAt N V)
    (carried : LawFibre expected old) {current : V.Current}
    (occurrence : old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    readFibre expected old carried occurrence = expected := by
  dsimp only [readFibre]
  exact eq_of_heq ((cast_heq _ _).trans (carried.2 occurrence))

end ActualNativeCofaceInheritance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
