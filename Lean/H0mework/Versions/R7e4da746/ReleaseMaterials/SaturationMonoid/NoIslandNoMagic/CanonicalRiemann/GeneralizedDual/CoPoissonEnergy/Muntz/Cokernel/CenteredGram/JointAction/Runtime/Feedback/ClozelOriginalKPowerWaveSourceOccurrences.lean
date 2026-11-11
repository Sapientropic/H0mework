import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPowerWaveInitialSourceOccurrences
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Native
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRSourceReceiptConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Relation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPowerWaveSourceOccurrences
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace C
export OriginalKCombReceiptFeedback (Value Var wholeDebtRWaveSourceTrace)
end C
namespace A
export ActualCofinalSourceAction
  (AS.nativeAfterAdmission L.Value L.groups sourceBorn bornStock born_inventory packetTransport
   actual_next_packet sourceWordAction)
end A
namespace Born
export OriginalKBFiniteCalculation.BornInventory
  (Packet StockAt initialStock initial_inventory stockTransport packetAt)
end Born
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
export ActualNativeRelationTransport.SourceRelationOccurrence
  (source born source_word born_word source_before_length born_before_length)
end SR
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (wordMapAt)
end R
open private reindexStock transport_inventory from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteBornInventory
open private reindexWord languageWord stepWord from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRSourceReceiptConsumer

local instance levelGroups (grade : Nat) : ∀ target,
    AddCommGroup (A.L.Value (PairValue C.Value) grade target) := A.L.groups (PairValue C.Value) grade

private def languagePoint {Y Z : Unit → Type} (same : Y = Z)
    (packet : Born.Packet Y) (stock : Born.StockAt packet) (point : WR.RelationOccurrence stock) :
    WR.RelationOccurrence (Born.stockTransport same packet stock) := by
  cases same
  exact point

private theorem languagePoint_word {Y Z : Unit → Type} (same : Y = Z)
    (packet : Born.Packet Y) (stock : Born.StockAt packet) (point : WR.RelationOccurrence stock) :
    (languagePoint same packet stock point).word = languageWord same packet point.word := by
  cases same
  rfl

private theorem languagePoint_length {Y Z : Unit → Type} (same : Y = Z)
    (packet : Born.Packet Y) (stock : Born.StockAt packet) (point : WR.RelationOccurrence stock) :
    (languagePoint same packet stock point).before.length = point.before.length := by
  cases same
  rfl

private def reindexPoint {left right : Born.Packet C.Var} (same : left = right)
    (stock : Born.StockAt left) (point : WR.RelationOccurrence stock) :
    WR.RelationOccurrence (reindexStock same stock) := by
  cases same
  exact point

private theorem reindexPoint_word {left right : Born.Packet C.Var} (same : left = right)
    (stock : Born.StockAt left) (point : WR.RelationOccurrence stock) :
    (reindexPoint same stock point).word = reindexWord same point.word := by
  cases same
  rfl

private theorem reindexPoint_length {left right : Born.Packet C.Var} (same : left = right)
    (stock : Born.StockAt left) (point : WR.RelationOccurrence stock) :
    (reindexPoint same stock point).before.length = point.before.length := by
  cases same
  rfl

private theorem reindex_inventory {left right : Born.Packet C.Var} (same : left = right)
    (stock : Born.StockAt left) (present : left.2.1.1.inventory = some stock) :
    right.2.1.1.inventory = some (reindexStock same stock) := by
  cases same
  exact present

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "factory" => D.factory observation nontrivial half
local notation "packet" => Born.packetAt observation nontrivial half depth
abbrev Index := Fin (SourceOperationPaidRelations.words
  (C.wholeDebtRWaveSourceTrace observation nontrivial depth half)).length

-- Each stock is the literal inventory of the original packet, including its full Feed.
private def stockAt : (tick : Nat) → Born.StockAt (packet tick)
  | 0 => Born.initialStock observation nontrivial half depth
  | tick + 1 => reindexStock
      (A.actual_next_packet factory (D.initial observation nontrivial half depth)
        (D.firstCfg observation nontrivial half depth) rfl tick).symm
      (Born.stockTransport (packet tick).2.2.2.down (A.sourceBorn factory (packet tick))
        (A.bornStock factory (packet tick)))

private theorem stock_inventory (tick : Nat) :
    (packet tick).2.1.1.inventory = some (stockAt observation nontrivial half depth tick) := by
  cases tick with
  | zero => exact Born.initial_inventory observation nontrivial half depth
  | succ tick =>
    exact reindex_inventory _ _
      (transport_inventory (packet tick).2.2.2.down (A.sourceBorn factory (packet tick))
        (A.bornStock factory (packet tick)) (A.born_inventory factory (packet tick)))

private def pointAt : (tick : Nat) → Index observation nontrivial half depth →
    WR.RelationOccurrence (stockAt observation nontrivial half depth tick)
  | 0, index =>
      OriginalKPowerWaveInitialSourceOccurrences.initialWaveOccurrence observation nontrivial depth half index
  | tick + 1, index => reindexPoint
      (A.actual_next_packet factory (D.initial observation nontrivial half depth)
        (D.firstCfg observation nontrivial half depth) rfl tick).symm _
      (languagePoint (packet tick).2.2.2.down (A.sourceBorn factory (packet tick)) _
        (SR.born factory (packet tick) (stockAt observation nontrivial half depth tick)
          (stock_inventory observation nontrivial half depth tick)
          (pointAt tick index)))

private theorem point_word (tick : Nat) (index : Index observation nontrivial half depth) :
    (pointAt observation nontrivial half depth tick index).word =
      R.wordMapAt observation nontrivial half depth tick
        ((SourceOperationPaidRelations.words
          (C.wholeDebtRWaveSourceTrace observation nontrivial depth half)).get index) := by
  induction tick with
  | zero =>
    exact OriginalKPowerWaveInitialSourceOccurrences.initial_wave_word observation nontrivial depth half index
  | succ tick previous =>
    dsimp only [pointAt]
    rw [reindexPoint_word, languagePoint_word, SR.born_word, previous]
    rfl

private theorem point_positions (tick : Nat) :
    StrictMono (fun index : Index observation nontrivial half depth =>
      (pointAt observation nontrivial half depth tick index).before.length) := by
  induction tick with
  | zero =>
    exact OriginalKPowerWaveInitialSourceOccurrences.initial_wave_positions observation nontrivial depth half
  | succ tick previous =>
    intro left right less
    change (pointAt observation nontrivial half depth (tick + 1) left).before.length <
      (pointAt observation nontrivial half depth (tick + 1) right).before.length
    dsimp only [pointAt]
    rw [reindexPoint_length, reindexPoint_length, languagePoint_length, languagePoint_length,
      SR.born_before_length, SR.born_before_length]
    exact Nat.add_lt_add_left (previous less) _

private def nativePoint (sourceFactory : OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.NativeFactory)
    (sourcePacket : Born.Packet C.Var) (prior : Born.StockAt sourcePacket)
    (present : sourcePacket.2.1.1.inventory = some prior) (point : WR.RelationOccurrence prior) :
    WR.RelationOccurrence (WN.oldStock (A.AS.nativeAfterAdmission sourceFactory sourcePacket)) := by
  rcases sourcePacket with ⟨grade, data, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = C.Var at sameVar
    cases sameVar
    exact SR.source sourceFactory ⟨grade, data, ⟨C.Var, datum, inventory, pairInventory⟩, ⟨rfl⟩⟩
      prior present point

private theorem nativePoint_word
    (sourceFactory : OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.NativeFactory)
    (sourcePacket : Born.Packet C.Var) (prior : Born.StockAt sourcePacket)
    (present : sourcePacket.2.1.1.inventory = some prior) (point : WR.RelationOccurrence prior) :
    (nativePoint sourceFactory sourcePacket prior present point).word =
      NW.admissionWord sourceFactory sourcePacket (liftMap (R := ℤ) point.word) := by
  rcases sourcePacket with ⟨grade, data, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = C.Var at sameVar
    cases sameVar
    rfl

private theorem nativePoint_length
    (sourceFactory : OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.NativeFactory)
    (sourcePacket : Born.Packet C.Var) (prior : Born.StockAt sourcePacket)
    (present : sourcePacket.2.1.1.inventory = some prior) (point : WR.RelationOccurrence prior) :
    (nativePoint sourceFactory sourcePacket prior present point).before.length =
      (ActualNativeRelationTransport.SourceInventoryBlock.source sourceFactory sourcePacket prior present).before.length +
        point.before.length := by
  rcases sourcePacket with ⟨grade, data, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = C.Var at sameVar
    cases sameVar
    exact SR.source_before_length sourceFactory
      ⟨grade, data, ⟨C.Var, datum, inventory, pairInventory⟩, ⟨rfl⟩⟩ prior present point

/-- The same original Step is located in the actual native Feed input at every cofinal ordinal. -/
def actualOccurrence (ordinal : Nat) (index : Index observation nontrivial half depth) :
    WR.RelationOccurrence (WN.oldStock (WN.native observation nontrivial half depth ordinal)) :=
  nativePoint factory (packet (ordinal + 1)) (stockAt observation nontrivial half depth (ordinal + 1))
    (stock_inventory observation nontrivial half depth (ordinal + 1))
    (pointAt observation nontrivial half depth (ordinal + 1) index)

theorem actual_word (ordinal : Nat) (index : Index observation nontrivial half depth) :
    (actualOccurrence observation nontrivial half depth ordinal index).word =
      NW.admissionWord factory (packet (ordinal + 1))
        (liftMap (R := ℤ) (R.wordMapAt observation nontrivial half depth (ordinal + 1)
          ((SourceOperationPaidRelations.words
            (C.wholeDebtRWaveSourceTrace observation nontrivial depth half)).get index))) := by
  rw [actualOccurrence, nativePoint_word, point_word]

theorem actual_positions (ordinal : Nat) :
    StrictMono (fun index : Index observation nontrivial half depth =>
      (actualOccurrence observation nontrivial half depth ordinal index).before.length) := by
  intro left right less
  change (actualOccurrence observation nontrivial half depth ordinal left).before.length <
    (actualOccurrence observation nontrivial half depth ordinal right).before.length
  dsimp only [actualOccurrence]
  rw [nativePoint_length, nativePoint_length]
  exact Nat.add_lt_add_left (point_positions observation nontrivial half depth (ordinal + 1) less) _

end OriginalKPowerWaveSourceOccurrences
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
