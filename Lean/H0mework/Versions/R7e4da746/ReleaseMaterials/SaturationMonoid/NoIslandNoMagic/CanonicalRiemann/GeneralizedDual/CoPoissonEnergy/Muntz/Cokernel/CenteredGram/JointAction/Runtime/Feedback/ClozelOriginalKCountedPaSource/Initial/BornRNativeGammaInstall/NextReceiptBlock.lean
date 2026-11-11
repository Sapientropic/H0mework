import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u uParent uIndex uWhole uNext uHistoryEnd uHistory

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptBlock

open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
open ActualNativeRelationTransport (OccurrenceBlock)

namespace Cfa
export ActualCofinalSourceAction (nativePacket selected sourceBorn bornStock born_inventory packetTransport sourceWordAction)
export ActualCofinalSourceAction.AS (AdmissionPacket)
export ActualCofinalSourceAction.D (packetAt)
export ActualCofinalSourceAction.L (Value groups)
export ActualNativeRelationTransport (decoded_environment)
export ActualNativeRelationTransport.AS (stockDecodedEnvironment stockCfg)
end Cfa
namespace R
export ActualCofinalSourceAction.SourceReceiptOccurrence (ExecutionAt InventoryAt)
export ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt (reindex)
end R
namespace F
export SourceInventoryExecutionFeed (Event affine)
export SourceInventoryExecutionFeed.ReceiptOccurrence (executedTrace requestWord)
end F
namespace Batch
export ActualCofinalSourceAction.SourceReceiptOccurrence.Batch (requests nextBlock nextBlock_boundary)
end Batch
namespace A
export BornRCanonicalMethodRuntime (W X fixedRFactory)
end A
namespace H
export BornRSourceMethodHistory (receiver methodProgramme)
end H
namespace BF
export PhysicalGammaBoundaryFeedback (actualBoundary actualBoundary_source nextBoundary nextBoundary_source actedBoundaryWord)
end BF
namespace N
export PhysicalGammaNextReceipt (actualBirth)
end N

open private born_packet_literal from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.BoundaryFeedback
open private originalBirth following_literal from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt

section Generic
variable {Sorts : Type u} {W X Y : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance gradeGroups (n : Nat) : ∀ t, AddCommGroup (Cfa.Value W n t) := Cfa.groups W n

private def boundary {p : Cfa.AdmissionPacket (W := W) (X := X) (s := s)} (e : R.ExecutionAt p) :
    Formal ℤ (Cfa.Value W p.1) X s :=
  Finsupp.single e.request.expression 1 - Finsupp.single (.const (e.request.expression.eval e.decoder)) 1

private theorem boundary_reindex (p : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (q : Cfa.AdmissionPacket (W := W) (X := Y) (s := s)) (language : X = Y)
    (same : Cfa.packetTransport language p = q) (e : R.ExecutionAt p) :
    HEq (boundary (R.reindex p q language same e)) (boundary e) := by
  cases language
  cases same
  exact HEq.rfl

private def block_reindex (p : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (q : Cfa.AdmissionPacket (W := W) (X := Y) (s := s)) (language : X = Y)
    (same : Cfa.packetTransport language p = q) (stock : R.InventoryAt p)
    (installed : p.2.1.1.inventory = some stock)
    (trace : List (F.Event (V := Cfa.Value W p.1) (X := X) (s := s)))
    (block : OccurrenceBlock trace stock.trace) :
    Σ targetStock : R.InventoryAt q,
      Σ targetTrace : List (F.Event (V := Cfa.Value W q.1) (X := Y) (s := s)),
        {targetBlock : OccurrenceBlock targetTrace targetStock.trace //
          q.2.1.1.inventory = some targetStock ∧ HEq targetTrace trace ∧
            targetBlock.before.length = block.before.length} := by
  cases language
  cases same
  exact ⟨stock,trace,block,installed,HEq.rfl,rfl⟩
end Generic

local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance levelGroups (grade : Nat) : ∀ target, AddCommGroup (Cfa.Value A.W grade target) :=
  Cfa.groups A.W grade

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
local notation "site" => Cfa.packetAt factory
  (H.receiver observation nontrivial half depth ordinal)
  (H.methodProgramme observation nontrivial half depth ordinal) rfl
local notation "sourceSite" => site (update+2)
local notation "receiptSite" => site ((update+2)+1)
local notation "born" => N.actualBirth observation nontrivial half depth ordinal method
local notation "requests" => Batch.requests factory sourceSite born
local notation "nativeStock" => Cfa.bornStock factory sourceSite
local notation "nativeFrame" => Cfa.selected factory sourceSite
set_option quotPrecheck false in
local notation "nativeBase" => (Cfa.nativePacket factory sourceSite).2.2.1
local notation "decoder" => Cfa.stockDecodedEnvironment nativeFrame nativeBase

set_option cleanup.letToHave false in
/-- Every receipt paid by the original Gamma Step interval is in the literal next packet. -/
def actualBlock :=
  block_reindex (Cfa.sourceBorn factory sourceSite) receiptSite (sourceSite).2.2.2.down
    (following_literal observation nontrivial half depth ordinal (update := update))
    nativeStock (Cfa.born_inventory factory sourceSite) (F.executedTrace decoder requests)
    (Batch.nextBlock factory sourceSite born)

private theorem actual_boundary_eq :
    (BF.actualBoundary observation nontrivial half depth ordinal method).val = boundary born := by
  have reindexed := boundary_reindex (Cfa.sourceBorn factory method.source) sourceSite method.source.2.2.2.down
    (born_packet_literal observation nontrivial half depth ordinal method)
    (originalBirth observation nontrivial half depth ordinal method)
  exact eq_of_heq ((BF.actualBoundary_source observation nontrivial half depth ordinal method).trans reindexed.symm)

set_option cleanup.letToHave false in
/-- The signed sum of the actual ordered batch is the old next relation boundary. -/
theorem actual_batch_boundary :
    HEq (BF.nextBoundary observation nontrivial half depth ordinal method).val
      (((requests).map (F.requestWord decoder)).sum) := by
  have original := BF.nextBoundary_source observation nontrivial half depth ordinal method
  have sameWord := congrArg (Cfa.sourceWordAction sourceSite)
    (actual_boundary_eq observation nontrivial half depth ordinal method)
  have sameDecoder := Cfa.decoded_environment nativeFrame nativeBase
  have read := congrArg₂ (fun environment word => F.affine environment word) sameDecoder sameWord
  exact original.trans (heq_of_eq (read.trans (Batch.nextBlock_boundary factory sourceSite born).symm))

end CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptBlock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
