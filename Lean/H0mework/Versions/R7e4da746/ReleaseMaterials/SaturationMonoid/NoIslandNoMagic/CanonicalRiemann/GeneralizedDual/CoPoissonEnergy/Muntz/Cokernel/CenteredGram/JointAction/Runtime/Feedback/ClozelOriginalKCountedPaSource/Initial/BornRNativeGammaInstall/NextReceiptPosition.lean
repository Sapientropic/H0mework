import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block.Position
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptBlock

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u uParent uIndex uWhole uNext uHistoryEnd uHistory

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptPosition
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
open ActualNativeRelationTransport (OccurrenceBlock)

namespace Cfa
export ActualCofinalSourceAction (sourceBorn bornStock born_inventory nativePacket selected packetTransport)
export ActualCofinalSourceAction.AS (AdmissionPacket)
export ActualCofinalSourceAction.D (packetAt)
export ActualCofinalSourceAction.L (Value groups)
export ActualNativeRelationTransport (decoded_environment)
export ActualNativeRelationTransport.AS (stockDecodedEnvironment)
end Cfa
namespace R
export ActualCofinalSourceAction.SourceReceiptOccurrence (ExecutionAt InventoryAt)
export ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt (reindex)
end R
namespace F
export SourceInventoryExecutionFeed (Event Request receipt relationSpace)
export SourceInventoryExecutionFeed.ReceiptOccurrence
  (executedTrace readExecutedStep executionSegmentAt executionSegmentAt_before)
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end F
namespace P
export SourceOperationPaidRelations (words stepOccurrence AtStep paidCut)
end P
namespace B
export ActualCofinalSourceAction.SourceReceiptOccurrence.Batch (requests nextBlock)
export PhysicalGammaNextReceiptBlock (actualBlock)
end B
namespace N
export PhysicalGammaNextReceipt (actualBirth)
end N
namespace A
export BornRCanonicalMethodRuntime (W X fixedRFactory)
end A
namespace H
export BornRSourceMethodHistory (receiver methodProgramme)
end H
namespace RF
export BornRWordPaWriteback.RelationFeedback (RelationAt)
end RF

open private following_literal from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt
open private block_reindex from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptBlock

section Generic
variable {S : Type u} {W X Y : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
local instance levelGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value W grade t) := Cfa.groups W grade

/-- The absolute relation address retains its original request, paid execution and typed cut. -/
structure LocatedAt (native : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (target : Cfa.AdmissionPacket (W := W) (X := Y) (s := s))
    (language : X = Y) (same : Cfa.packetTransport language native = target)
    (decoder : Env (Cfa.Value W native.1) X)
    (requests : List (F.Request (V := Cfa.Value W native.1) (X := X) (s := s)))
    (stock : R.InventoryAt target) (position : Nat) (word : Formal ℤ (Cfa.Value W target.1) Y s) where
  requestIndex : Fin requests.length
  nativeExecution : R.ExecutionAt native
  request_source : nativeExecution.request = requests.get requestIndex
  decoder_source : nativeExecution.decoder = decoder
  paid_source : HEq nativeExecution.paid (F.receipt decoder (requests.get requestIndex))
  index : Fin (P.words (R.reindex native target language same nativeExecution).paid).length
  cut : P.AtStep (R.reindex native target language same nativeExecution).paid index.val
  stock_eq : (R.reindex native target language same nativeExecution).stock = stock
  position_eq : ((R.reindex native target language same nativeExecution).step index).before.length = position
  word_eq : ((R.reindex native target language same nativeExecution).step index).word = word

namespace LocatedAt
variable {native : Cfa.AdmissionPacket (W := W) (X := X) (s := s)}
variable {target : Cfa.AdmissionPacket (W := W) (X := Y) (s := s)}
variable {language : X = Y} {same : Cfa.packetTransport language native = target}
variable {decoder : Env (Cfa.Value W native.1) X}
variable {requests : List (F.Request (V := Cfa.Value W native.1) (X := X) (s := s))}
variable {stock : R.InventoryAt target} {position : Nat} {word : Formal ℤ (Cfa.Value W target.1) Y s}

abbrev execution (found : LocatedAt native target language same decoder requests stock position word) :
    R.ExecutionAt target := R.reindex native target language same found.nativeExecution
end LocatedAt

set_option cleanup.letToHave false in
private def readNative (packet : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (stock : R.InventoryAt packet) (installed : packet.2.1.1.inventory = some stock)
    (decoder : Env (Cfa.Value W packet.1) X) (decoderRead : packet.2.1.1.activeEnvironment = decoder)
    (requests : List (F.Request (V := Cfa.Value W packet.1) (X := X) (s := s)))
    (whole : OccurrenceBlock (F.executedTrace decoder requests) stock.trace)
    (position : Nat) (word : Formal ℤ (Cfa.Value W packet.1) X s)
    (lower : whole.before.length ≤ position)
    (upper : position < whole.before.length + (F.executedTrace decoder requests).length)
    (actual : stock.trace[position]? = some (.relation word)) :
    LocatedAt packet packet rfl rfl decoder requests stock position word := by
  let localAddress := position - whole.before.length
  have inside : localAddress < (F.executedTrace decoder requests).length := by
    dsimp only [localAddress]
    omega
  have inBatch : (F.executedTrace decoder requests)[localAddress]? = some (.relation word) := by
    rw [whole.trace_eq, List.append_assoc, List.getElem?_append_right lower, List.getElem?_append_left inside] at actual
    exact actual
  let located := F.readExecutedStep decoder requests localAddress word inBatch
  let request := requests.get located.requestIndex
  let execution : R.ExecutionAt packet :=
    ⟨stock, installed, decoder, decoderRead, request, F.receipt decoder request,
      F.executionSegmentAt decoder requests (stock := stock) whole located.requestIndex⟩
  let index : Fin (P.words execution.paid).length := located.selected.index
  have segmentPosition : execution.segment.before.length = whole.before.length +
      (F.executedTrace decoder (requests.take located.requestIndex.val)).length :=
    F.executionSegmentAt_before decoder requests (stock := stock) whole located.requestIndex
  have stepPosition := execution.step_position index
  have batchPosition : position - whole.before.length =
      (F.executedTrace decoder (requests.take located.requestIndex.val)).length + located.localIndex :=
    located.offset_eq
  have localPosition : located.localIndex = 1 + index.val := located.selected.position_eq
  refine ⟨located.requestIndex, execution, rfl, rfl, HEq.rfl, index,
    P.paidCut execution.paid index, rfl, ?_, ?_⟩
  · change (execution.step index).before.length = position
    omega
  · exact ((P.stepOccurrence execution.paid index).transport_word execution.segment).trans located.selected.word_eq

set_option cleanup.letToHave false in
private def readLiteral (native : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (target : Cfa.AdmissionPacket (W := W) (X := Y) (s := s))
    (language : X = Y) (same : Cfa.packetTransport language native = target)
    (stock : R.InventoryAt native) (installed : native.2.1.1.inventory = some stock)
    (decoder : Env (Cfa.Value W native.1) X) (decoderRead : native.2.1.1.activeEnvironment = decoder)
    (requests : List (F.Request (V := Cfa.Value W native.1) (X := X) (s := s)))
    (whole : OccurrenceBlock (F.executedTrace decoder requests) stock.trace) :
    let literal := block_reindex native target language same stock installed (F.executedTrace decoder requests) whole
    (position : Nat) → (word : Formal ℤ (Cfa.Value W target.1) Y s) →
    literal.2.2.1.before.length ≤ position →
    position < literal.2.2.1.before.length + literal.2.1.length →
    literal.1.trace[position]? = some (.relation word) →
    LocatedAt native target language same decoder requests literal.1 position word := by
  cases language
  cases same
  exact readNative native stock installed decoder decoderRead requests whole

private theorem relation_word_in_stock {V Var : S → Type u} [∀ t, AddCommGroup (V t)]
    {stock : SourceInventoryExecutionFeed.Inventory (V := V) (X := Var) (s := s)}
    (actual : F.RelationOccurrence stock) : actual.word ∈ F.relationSpace stock := by
  apply Submodule.subset_span
  rw [actual.trace_eq]
  exact List.mem_append_right _ List.mem_cons_self
end Generic

local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance actualGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value A.W grade t) := Cfa.groups A.W grade

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
local notation "native" => Cfa.sourceBorn factory current
set_option quotPrecheck false in
local notation "language" => (current).2.2.2.down
local notation "recognition" => following_literal observation nontrivial half depth ordinal (update := update)
local notation "born" => N.actualBirth observation nontrivial half depth ordinal method
local notation "requests" => B.requests factory current born
local notation "selected" => Cfa.selected factory current
set_option quotPrecheck false in
local notation "base" => (Cfa.nativePacket factory current).2.2.1
local notation "decoder" => Cfa.stockDecodedEnvironment selected base
local notation "literal" => B.actualBlock observation nontrivial half depth ordinal method

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
/-- Read an absolute relation slot of the original Gamma execution block at the literal successor. -/
def actualPosition :=
  readLiteral native nextSite language recognition (Cfa.bornStock factory current)
    (Cfa.born_inventory factory current) decoder (Cfa.decoded_environment selected base)
    requests (B.nextBlock factory current born)

end CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptPosition
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
