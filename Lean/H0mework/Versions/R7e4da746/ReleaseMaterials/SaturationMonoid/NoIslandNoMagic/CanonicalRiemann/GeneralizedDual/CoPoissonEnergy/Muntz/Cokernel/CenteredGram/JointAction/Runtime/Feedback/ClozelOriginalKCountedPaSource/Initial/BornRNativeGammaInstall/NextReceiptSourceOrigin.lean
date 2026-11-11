import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block.SourceOrigin.Segment
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptPositionFibre

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u uParent uIndex uWhole uNext uHistoryEnd uHistory

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptPosition
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
open ActualNativeRelationTransport (OccurrenceBlock)

namespace Cfa
export ActualCofinalSourceAction (sourceWordAction source_word_action_inventory receiverOld receiverIncrement)
end Cfa
namespace B
export ActualCofinalSourceAction.SourceReceiptOccurrence.Batch
  (SourceRequestAt sourceRequestAt sourceRequestAt_segment_position)
end B
namespace R
export ActualCofinalSourceAction.SourceReceiptOccurrence (atBirth)
end R
open private following_literal from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt
open private block_reindex from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptBlock
open private readLiteral from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptPosition

section Generic
variable {S : Type u} {W X Y : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
local instance sourceOriginGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value W grade t) := Cfa.groups W grade

private theorem readLiteral_native_address (native : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (target : Cfa.AdmissionPacket (W := W) (X := Y) (s := s))
    (language : X = Y) (same : Cfa.packetTransport language native = target)
    (stock : R.InventoryAt native) (installed : native.2.1.1.inventory = some stock)
    (decoder : Env (Cfa.Value W native.1) X) (decoderRead : native.2.1.1.activeEnvironment = decoder)
    (requests : List (F.Request (V := Cfa.Value W native.1) (X := X) (s := s)))
    (whole : OccurrenceBlock (F.executedTrace decoder requests) stock.trace) :
    let literal := block_reindex native target language same stock installed (F.executedTrace decoder requests) whole
    ∀ (position : Nat) (word : Formal ℤ (Cfa.Value W target.1) Y s)
      (lower : literal.2.2.1.before.length ≤ position)
      (upper : position < literal.2.2.1.before.length + literal.2.1.length)
      (actual : literal.1.trace[position]? = some (.relation word)),
    let found := readLiteral native target language same stock installed decoder decoderRead
      requests whole position word lower upper actual
    found.nativeExecution.segment.before.length =
      (F.executionSegmentAt decoder requests (stock := stock) whole found.requestIndex).before.length := by
  cases language
  cases same
  intros
  rfl

variable (factory : Cfa.Factory W X s) (packet : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
variable (birth : R.ExecutionAt packet)
local notation "native" => Cfa.sourceBorn factory packet
local notation "allRequests" => B.requests factory packet birth
local notation "frame" => Cfa.selected factory packet
set_option quotPrecheck false in
local notation "base" => (Cfa.nativePacket factory packet).2.2.1
local notation "decoder" => Cfa.stockDecodedEnvironment frame base

/-- A backward-selected request and the original forward occurrence share the actual write address. -/
structure SourceStepMatch (ordinal : Fin (allRequests).length)
    (raw : F.Request (V := Cfa.Value W (native).1) (X := packet.2.2.1.LowVar) (s := s))
    (address : Nat) where
  origin : B.SourceRequestAt factory packet birth ordinal
  request_eq : raw =
    (R.atBirth factory packet birth.stock birth.installed (birth.step origin.sourceIndex) origin.supportIndex).request
  address_eq : address =
    (R.atBirth factory packet birth.stock birth.installed (birth.step origin.sourceIndex) origin.supportIndex).segment.before.length
  action_eq :
    evaluation (R := ℤ) (Cfa.nativePacket factory packet).2.1.1.registered.input.environment
        (Cfa.sourceWordAction packet (birth.step origin.sourceIndex).word) =
      updateInventory (R := ℤ) (Cfa.receiverOld factory packet) (Cfa.receiverIncrement factory packet)
        (birth.step origin.sourceIndex).word

private def matchLiteral
    (target : Cfa.AdmissionPacket (W := W) (X := Y) (s := s))
    (language : packet.2.2.1.LowVar = Y) (same : Cfa.packetTransport language native = target) :=
  fun (position : Nat) word lower upper actual =>
    let stock := Cfa.bornStock factory packet
    let installed := Cfa.born_inventory factory packet
    let whole := B.nextBlock factory packet birth
    let decoderRead := Cfa.decoded_environment frame base
    let found := readLiteral native target language same stock installed decoder decoderRead
      allRequests whole position word lower upper actual
    let origin := B.sourceRequestAt factory packet birth found.requestIndex
    show SourceStepMatch factory packet birth found.requestIndex found.nativeExecution.request
        found.nativeExecution.segment.before.length from
      ⟨origin, found.request_source.trans origin.request_eq,
        (readLiteral_native_address native target language same stock installed decoder decoderRead
          allRequests whole position word lower upper actual).trans
            (B.sourceRequestAt_segment_position factory packet birth found.requestIndex).symm,
        LinearMap.congr_fun (Cfa.source_word_action_inventory factory packet) (birth.step origin.sourceIndex).word⟩
end Generic

local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance sourceActualGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value A.W grade t) := Cfa.groups A.W grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : BornRSourcePrice.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
  (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff)
local notation "factory" => A.fixedRFactory observation nontrivial half
local notation "initial" => H.receiver observation nontrivial half depth ordinal
local notation "programme" => H.methodProgramme observation nontrivial half depth ordinal
local notation "site" => Cfa.packetAt factory initial programme rfl
local notation "current" => site (update+2)
local notation "nextSite" => site ((update+2)+1)
local notation "birth" => N.actualBirth observation nontrivial half depth ordinal method
set_option quotPrecheck false in
local notation "language" => (current).2.2.2.down

set_option backward.isDefEq.respectTransparency false in
/-- Read the source action that generated the original literal successor's addressed Step. -/
def actualSourceRequest :=
  matchLiteral factory current birth nextSite language
    (following_literal observation nontrivial half depth ordinal (update := update))

end CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptPosition
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
