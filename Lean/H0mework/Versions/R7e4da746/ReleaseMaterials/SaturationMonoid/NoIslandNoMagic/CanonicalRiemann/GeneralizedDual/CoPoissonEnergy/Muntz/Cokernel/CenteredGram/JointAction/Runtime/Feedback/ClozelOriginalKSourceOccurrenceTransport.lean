import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPowerWaveSourceOccurrences
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Step

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceOccurrenceTransport
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace C
export OriginalKCombReceiptFeedback (Value Var sourcePaidInventory)
end C
namespace A
export ActualCofinalSourceAction (L.Value L.groups sourceBorn actual_next_packet)
end A
namespace B
export OriginalKBFiniteCalculation.BornInventory (initialStock packetAt)
end B
namespace D
export OriginalKCombFirstFullSourceDynamics (factory initial firstCfg)
end D
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative (oldStock native)
end WN
namespace NW
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback (admissionWord)
end NW
namespace SR
export ActualNativeRelationTransport.SourceRelationOccurrence (born born_word born_before_length)
end SR
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (wordMapAt)
end R
open private initialBlock from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPowerWaveInitialSourceOccurrences
open private stockAt stock_inventory languagePoint languagePoint_word languagePoint_length
  reindexPoint reindexPoint_word reindexPoint_length nativePoint nativePoint_word nativePoint_length from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPowerWaveSourceOccurrences

local instance levelGroups (grade : Nat) : ∀ target,
    AddCommGroup (A.L.Value (PairValue C.Value) grade target) := A.L.groups (PairValue C.Value) grade
local instance lowGroups : ∀ target, AddCommGroup (A.L.Value C.Value 0 target) := A.L.groups C.Value 0
local instance firstPairGroups : ∀ target,
    AddCommGroup (PairValue (A.L.Value C.Value 0) target) := A.L.groups C.Value 1

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "factory" => D.factory observation nontrivial half
local notation "packet" => B.packetAt observation nontrivial half depth

/-- The already generated first-birth block is independent of which source Code made the point. -/
private def initialSegment : SourceInventoryTraceSegment
    ((C.sourcePaidInventory observation nontrivial depth half).map
      ActualCofinalSourceAction.T.liftEvent)
    (B.initialStock observation nontrivial half depth) := by
  let block := initialBlock observation nontrivial depth half
  refine ⟨block.before, block.after, ?_⟩
  simpa only [ActualCofinalSourceAction.T.mapped_trace] using block.trace_eq

variable (point : WR.RelationOccurrence (C.sourcePaidInventory observation nontrivial depth half))

private def initialPoint : WR.RelationOccurrence (B.initialStock observation nontrivial half depth) :=
  point.lift.transport (initialSegment observation nontrivial half depth)

private def pointAt : (tick : Nat) →
    WR.RelationOccurrence (stockAt observation nontrivial half depth tick)
  | 0 => initialPoint observation nontrivial half depth point
  | tick + 1 => reindexPoint
      (A.actual_next_packet factory (D.initial observation nontrivial half depth)
        (D.firstCfg observation nontrivial half depth) rfl tick).symm _
      (languagePoint (packet tick).2.2.2.down (A.sourceBorn factory (packet tick)) _
        (SR.born factory (packet tick) (stockAt observation nontrivial half depth tick)
          (stock_inventory observation nontrivial half depth tick) (pointAt tick)))

private theorem pointAt_word (tick : Nat) :
    (pointAt observation nontrivial half depth point tick).word =
      R.wordMapAt observation nontrivial half depth tick point.word := by
  induction tick with
  | zero => rfl
  | succ tick previous =>
    dsimp only [pointAt]
    rw [reindexPoint_word, languagePoint_word, SR.born_word, previous]
    rfl

private def packetOffset : Nat → Nat
  | 0 => (initialSegment observation nontrivial half depth).before.length
  | tick + 1 =>
      (ActualNativeRelationTransport.SourceInventoryBlock.source factory (packet tick)
        (stockAt observation nontrivial half depth tick)
        (stock_inventory observation nontrivial half depth tick)).before.length + packetOffset tick

private theorem pointAt_before_length (tick : Nat) :
    (pointAt observation nontrivial half depth point tick).before.length =
      packetOffset observation nontrivial half depth tick + point.before.length := by
  induction tick with
  | zero =>
    change (point.lift.transport (initialSegment observation nontrivial half depth)).before.length = _
    rw [SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence.transport_position,
      SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence.lift_position]
    rfl
  | succ tick previous =>
    dsimp only [pointAt]
    rw [reindexPoint_length, languagePoint_length, SR.born_before_length, previous]
    change _ = (_ + packetOffset observation nontrivial half depth tick) + point.before.length
    exact (Nat.add_assoc _ _ _).symm

def actualSourceOffset (ordinal : Nat) : Nat :=
  (ActualNativeRelationTransport.SourceInventoryBlock.source factory (packet (ordinal + 1))
    (stockAt observation nontrivial half depth (ordinal + 1))
    (stock_inventory observation nontrivial half depth (ordinal + 1))).before.length +
      packetOffset observation nontrivial half depth (ordinal + 1)

/-- The original point enters the actual cofinal source action without replacing its occurrence. -/
def actualSourceOccurrence (ordinal : Nat) :
    WR.RelationOccurrence (WN.oldStock (WN.native observation nontrivial half depth ordinal)) :=
  nativePoint factory (packet (ordinal + 1))
    (stockAt observation nontrivial half depth (ordinal + 1))
    (stock_inventory observation nontrivial half depth (ordinal + 1))
    (pointAt observation nontrivial half depth point (ordinal + 1))

theorem actualSourceOccurrence_word (ordinal : Nat) :
    (actualSourceOccurrence observation nontrivial half depth point ordinal).word =
      NW.admissionWord factory (packet (ordinal + 1))
        (liftMap (R := ℤ)
          (R.wordMapAt observation nontrivial half depth (ordinal + 1) point.word)) := by
  rw [actualSourceOccurrence, nativePoint_word, pointAt_word]

theorem actualSourceOccurrence_before_length (ordinal : Nat) :
    (actualSourceOccurrence observation nontrivial half depth point ordinal).before.length =
      actualSourceOffset observation nontrivial half depth ordinal + point.before.length := by
  rw [actualSourceOccurrence, nativePoint_length, pointAt_before_length]
  exact (Nat.add_assoc _ _ _).symm

end OriginalKSourceOccurrenceTransport
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
