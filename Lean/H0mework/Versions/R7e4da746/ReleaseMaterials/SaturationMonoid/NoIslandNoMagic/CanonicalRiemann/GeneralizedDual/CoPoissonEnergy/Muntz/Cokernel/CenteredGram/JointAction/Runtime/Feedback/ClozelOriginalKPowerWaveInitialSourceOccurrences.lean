import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteBornInventory
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPowerWaveInitialSourceOccurrences
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
open CofinalHistorySettlement ActualNativeRelationTransport OriginalKCombReceiptFeedback
namespace C
export OriginalKCombReceiptFeedback
  (sourcePaidInventory wholeDebtRWaveSourceTrace wholeDebtRWaveStepOccurrence
   wholeDebtRWaveStepOffset whole_debt_R_wave_step_word whole_debt_R_wave_step_before_length)
end C
namespace B
export OriginalKBFiniteCalculation.BornInventory (initialStock)
end B
namespace Q
export OriginalKCombFirstFullSource (factory data configuration initial)
end Q
namespace SS
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor (scalar seed)
end SS
namespace IP
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
  (priorSeed updatedSeed)
end IP
namespace Pair
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair
  (relationWrite disposition)
end Pair
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end A
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end Shared
namespace L
export ActualCofinalSourceAction.L (Value groups)
end L
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
namespace PT
export SourceOperationPaidRelations (words)
end PT
open private lowCarried seedLeft preserveRight from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory
open private firstSeed firstSelected from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteBornInventory

local instance levelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue Value) grade target) := L.groups (PairValue Value) grade target
local instance lowGroups : ∀ target, AddCommGroup (L.Value Value 0 target) := L.groups Value 0
local instance firstPairGroups : ∀ target, AddCommGroup (PairValue (L.Value Value 0) target) :=
  L.groups Value 1

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (depth : Nat) (half : OriginalKCombCalculation.Half observation)

private abbrev liftedInventory :=
  (C.sourcePaidInventory observation nontrivial depth half).trace.map
    (ActualCofinalSourceAction.T.liftEvent (W := Value) (X := Var) (s := ()))

private def scalarBlock : OccurrenceBlock
    (liftedInventory observation nontrivial depth half)
    (SS.scalar Q.factory 0 (Q.data observation nontrivial half depth)
      (Q.configuration observation nontrivial half) rfl).trace :=
  preserveRight _ _ _ (lowCarried (Q.initial observation nontrivial half depth)
    (Q.configuration observation nontrivial half) rfl
    (C.sourcePaidInventory observation nontrivial depth half) rfl)

private def seedBlock : OccurrenceBlock
    (liftedInventory observation nontrivial depth half)
    (firstSeed observation nontrivial half depth).trace :=
  seedLeft _ _ _ (scalarBlock observation nontrivial depth half)

private def priorBlock : OccurrenceBlock
    (liftedInventory observation nontrivial depth half)
    (IP.priorSeed (firstSeed observation nontrivial half depth)
      (A.epoch (firstSelected observation nontrivial half depth))).trace := by
  unfold IP.priorSeed
  cases (A.epoch (firstSelected observation nontrivial half depth)).inventory with
  | none => exact seedBlock observation nontrivial depth half
  | some _ => exact seedLeft _ _ _ (seedBlock observation nontrivial depth half)

private def updatedBlock : OccurrenceBlock
    (liftedInventory observation nontrivial depth half)
    (IP.updatedSeed (firstSeed observation nontrivial half depth)
      (A.epoch (firstSelected observation nontrivial half depth))
      (Shared.actualOccurrence (firstSelected observation nontrivial half depth))).trace :=
  seedLeft _ _ _ (priorBlock observation nontrivial depth half)

/-- The constructor-selected whole block survives the first actual source birth. -/
private def initialBlock : OccurrenceBlock
    (liftedInventory observation nontrivial depth half)
    (B.initialStock observation nontrivial half depth).trace := by
  unfold B.initialStock Pair.relationWrite
  cases Pair.disposition (firstSeed observation nontrivial half depth)
      (A.epoch (firstSelected observation nontrivial half depth))
      (Shared.actualOccurrence (firstSelected observation nontrivial half depth)) with
  | faithful _ _ _ => exact updatedBlock observation nontrivial depth half
  | unsound _ _ => exact updatedBlock observation nontrivial depth half
  | kernelResidual _ _ _ => exact seedLeft _ _ _ (updatedBlock observation nontrivial depth half)
  | coverageResidual _ _ _ => exact updatedBlock observation nontrivial depth half

/-- The original Fin slot, rather than membership, selects this born occurrence. -/
def initialWaveOccurrence
    (index : Fin (PT.words (C.wholeDebtRWaveSourceTrace observation nontrivial depth half)).length) :
    WR.RelationOccurrence (B.initialStock observation nontrivial half depth) := by
  let original := C.wholeDebtRWaveStepOccurrence observation nontrivial depth half index
  let block := initialBlock observation nontrivial depth half
  let lift := ActualCofinalSourceAction.T.liftEvent (W := Value) (X := Var) (s := ())
  refine ⟨block.before ++ original.before.map lift, liftMap original.word,
    original.after.map lift ++ block.after, ?_⟩
  have mapped := congrArg (List.map lift) original.trace_eq
  simp only [List.map_append,List.map_cons] at mapped
  change (C.sourcePaidInventory observation nontrivial depth half).trace.map lift =
    original.before.map lift ++ PresentedRelationEventAt.relation (liftMap original.word) ::
      original.after.map lift at mapped
  exact block.trace_eq.trans
    ((congrArg (fun middle => block.before ++ middle ++ block.after) mapped).trans
      (by
        simp only [List.cons_append,List.append_assoc]
        rfl))

def initialWaveOffset : Nat :=
  (initialBlock observation nontrivial depth half).before.length +
    C.wholeDebtRWaveStepOffset observation nontrivial depth half

theorem initial_wave_word
    (index : Fin (PT.words (C.wholeDebtRWaveSourceTrace observation nontrivial depth half)).length) :
    (initialWaveOccurrence observation nontrivial depth half index).word =
      liftMap ((PT.words (C.wholeDebtRWaveSourceTrace observation nontrivial depth half)).get index) := by
  change liftMap (C.wholeDebtRWaveStepOccurrence observation nontrivial depth half index).word = _
  rw [C.whole_debt_R_wave_step_word]

theorem initial_wave_before_length
    (index : Fin (PT.words (C.wholeDebtRWaveSourceTrace observation nontrivial depth half)).length) :
    (initialWaveOccurrence observation nontrivial depth half index).before.length =
      initialWaveOffset observation nontrivial depth half + index.val := by
  change ((initialBlock observation nontrivial depth half).before ++
    (C.wholeDebtRWaveStepOccurrence observation nontrivial depth half index).before.map _).length = _
  rw [List.length_append,List.length_map,C.whole_debt_R_wave_step_before_length]
  unfold initialWaveOffset
  omega

/-- Equal word syntax at different paid Steps keeps strictly different born addresses. -/
theorem initial_wave_positions : StrictMono (fun index :
    Fin (PT.words (C.wholeDebtRWaveSourceTrace observation nontrivial depth half)).length =>
      (initialWaveOccurrence observation nontrivial depth half index).before.length) := by
  intro first second ordered
  change (initialWaveOccurrence observation nontrivial depth half first).before.length <
    (initialWaveOccurrence observation nontrivial depth half second).before.length
  rw [initial_wave_before_length,initial_wave_before_length]
  exact Nat.add_lt_add_left (show first.val < second.val from ordered) _

end OriginalKPowerWaveInitialSourceOccurrences
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
