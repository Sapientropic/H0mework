import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block.SourceOrigin

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction.SourceReceiptOccurrence.Batch

open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement
open private executedTrace_append from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance segmentOriginGroups (grade : Nat) : ∀ t, AddCommGroup (S.Value W grade t) := S.groups W grade
variable (factory : S.Factory W X s) (packet : S.AdmissionPacket (W := W) (X := X) (s := s))
variable (execution : ExecutionAt packet)
set_option quotPrecheck false in
local notation "frame" => S.selected factory packet
set_option quotPrecheck false in
local notation "base" => (S.nativePacket factory packet).2.2.1
local notation "sourceStock" => S.stockScalar frame base
local notation "decoder" => S.stockDecodedEnvironment frame base
local notation "batch" => requests factory packet execution
local notation "block" => nextBlock factory packet execution
set_option quotPrecheck false in
local notation "prefixRequests" => F.requestsFrom 0 (sourceBlock factory packet execution).before

/-- The forward request and the ordinal-selected execution have the same actual write address. -/
theorem sourceRequestAt_segment_position (ordinal : Fin (batch).length) :
    let origin := sourceRequestAt factory packet execution ordinal
    (atBirth factory packet execution.stock execution.installed
      (execution.step origin.sourceIndex) origin.supportIndex).segment.before.length =
    (F.executionSegmentAt decoder batch (stock := S.bornStock factory packet) block ordinal).before.length := by
  let origin := sourceRequestAt factory packet execution ordinal
  have blockStart : (block).before.length =
      (sourceStock).trace.length + (F.executedTrace decoder prefixRequests).length :=
    List.length_append
  have forward := atBirth_segment_position factory packet execution.stock execution.installed
    (execution.step origin.sourceIndex) origin.supportIndex
  have inverse := F.executionSegmentAt_before decoder batch (stock := S.bornStock factory packet) block ordinal
  refine forward.trans (Eq.trans ?_ inverse.symm)
  change (sourceStock).trace.length + (F.executedTrace decoder (F.relationPrefix
    (acted factory packet execution.stock execution.installed (execution.step origin.sourceIndex)) origin.supportIndex)).length =
    (block).before.length + (F.executedTrace decoder ((batch).take ordinal.val)).length
  let front := (F.executedTrace decoder prefixRequests).length
  let rest := (F.executedTrace decoder ((batch).take ordinal.val)).length
  have lengths :
      (F.executedTrace decoder (F.relationPrefix
        (acted factory packet execution.stock execution.installed (execution.step origin.sourceIndex))
        origin.supportIndex)).length = front + rest :=
    (congrArg (fun items => (F.executedTrace decoder items).length) origin.prefix_eq).trans
      ((congrArg List.length (executedTrace_append decoder prefixRequests ((batch).take ordinal.val))).trans
        List.length_append)
  calc
    _ = (sourceStock).trace.length + (front + rest) :=
      congrArg ((sourceStock).trace.length + ·) lengths
    _ = ((sourceStock).trace.length + front) + rest := (Nat.add_assoc _ _ _).symm
    _ = _ := congrArg (· + rest) blockStart.symm

end ActualCofinalSourceAction.SourceReceiptOccurrence.Batch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
