import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKReceiptSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceOccurrenceTransport
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Step

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKReciprocalCotestSourceOccurrences
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace C
export OriginalKCombReceiptFeedback (sourcePaidInventory wholeDebtRReciprocalSourceTrace reciprocalSourceSegment)
end C
namespace PT
export SourceOperationPaidRelations
  (words stepOccurrence stepOccurrence_word stepOccurrence_before_length stepOccurrence_positions)
end PT
namespace T
export OriginalKSourceOccurrenceTransport
  (actualSourceOccurrence actualSourceOccurrence_word actualSourceOccurrence_before_length actualSourceOffset)
end T
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative (oldStock native)
end WN
namespace NW
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback (admissionWord)
end NW
namespace B
export OriginalKBFiniteCalculation.BornInventory (packetAt)
end B
namespace D
export OriginalKCombFirstFullSourceDynamics (factory)
end D
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (wordMapAt)
end R
local instance levelGroups (grade : Nat) : ∀ target,
    AddCommGroup (ActualCofinalSourceAction.L.Value
      (PairValue OriginalKCombReceiptFeedback.Value) grade target) :=
  ActualCofinalSourceAction.L.groups (PairValue OriginalKCombReceiptFeedback.Value) grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
abbrev Index := Fin (PT.words (C.wholeDebtRReciprocalSourceTrace observation nontrivial depth half)).length

def sourceOccurrence (index : Index observation nontrivial half depth) :=
  (PT.stepOccurrence (C.wholeDebtRReciprocalSourceTrace observation nontrivial depth half) index).transport
    (C.reciprocalSourceSegment observation nontrivial depth half)

def actualOccurrence (ordinal : Nat) (index : Index observation nontrivial half depth) :
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence
      (WN.oldStock (WN.native observation nontrivial half depth ordinal)) :=
  T.actualSourceOccurrence observation nontrivial half depth
    (sourceOccurrence observation nontrivial half depth index) ordinal

theorem actual_word (ordinal : Nat) (index : Index observation nontrivial half depth) :
    (actualOccurrence observation nontrivial half depth ordinal index).word =
      NW.admissionWord (D.factory observation nontrivial half)
        (B.packetAt observation nontrivial half depth (ordinal+1))
        (liftMap (R := ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
          ((PT.words (C.wholeDebtRReciprocalSourceTrace observation nontrivial depth half)).get index))) := by
  rw [actualOccurrence, T.actualSourceOccurrence_word]
  simp only [sourceOccurrence,
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence.transport_word, PT.stepOccurrence_word]

theorem actual_before_length (ordinal : Nat) (index : Index observation nontrivial half depth) :
    (actualOccurrence observation nontrivial half depth ordinal index).before.length =
      T.actualSourceOffset observation nontrivial half depth ordinal +
        (C.reciprocalSourceSegment observation nontrivial depth half).before.length + 1 + index.val := by
  simp only [actualOccurrence, T.actualSourceOccurrence_before_length, sourceOccurrence,
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence.transport_position,
    PT.stepOccurrence_before_length, Nat.add_assoc]

theorem actual_positions (ordinal : Nat) :
    StrictMono (fun index : Index observation nontrivial half depth =>
      (actualOccurrence observation nontrivial half depth ordinal index).before.length) := by
  intro first second ordered
  change (actualOccurrence observation nontrivial half depth ordinal first).before.length <
    (actualOccurrence observation nontrivial half depth ordinal second).before.length
  simp only [actualOccurrence, T.actualSourceOccurrence_before_length, sourceOccurrence,
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence.transport_position]
  exact Nat.add_lt_add_left
    (Nat.add_lt_add_left
      (PT.stepOccurrence_positions
        (C.wholeDebtRReciprocalSourceTrace observation nontrivial depth half) ordered) _) _

end OriginalKReciprocalCotestSourceOccurrences
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
