import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceOccurrenceTransport

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativeCayleySourceOccurrences
open BurnolPhysicalState SourceOperationScalarInventoryLift
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
namespace C
export OriginalKCombReceiptFeedback (paNativeCayleySourceTrace paNativeCayleySourceSegment)
end C
namespace T
export OriginalKSourceOccurrenceTransport
  (actualSourceOccurrence actualSourceOccurrence_word actualSourceOccurrence_before_length actualSourceOffset)
end T
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative (native oldStock)
end WN
namespace PT
export SourceOperationPaidRelations (words stepOccurrence stepOccurrence_word stepOccurrence_before_length stepOccurrence_positions)
end PT
namespace NW
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback (admissionWord)
end NW
namespace Born
export OriginalKBFiniteCalculation.BornInventory (packetAt)
end Born
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
abbrev Index (field : Fin 3) :=
  Fin (PT.words (C.paNativeCayleySourceTrace observation nontrivial depth half field)).length

def sourceOccurrence (field : Fin 3) (index : Index observation nontrivial half depth field) :=
  (PT.stepOccurrence (C.paNativeCayleySourceTrace observation nontrivial depth half field) index).transport
    (C.paNativeCayleySourceSegment observation nontrivial depth half field)

def actualOccurrence (ordinal : Nat) (field : Fin 3) (index : Index observation nontrivial half depth field) :
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence
      (WN.oldStock (WN.native observation nontrivial half depth ordinal)) :=
  T.actualSourceOccurrence observation nontrivial half depth
    (sourceOccurrence observation nontrivial half depth field index) ordinal

theorem actual_word (ordinal : Nat) (field : Fin 3) (index : Index observation nontrivial half depth field) :
    (actualOccurrence observation nontrivial half depth ordinal field index).word =
      NW.admissionWord (D.factory observation nontrivial half)
        (Born.packetAt observation nontrivial half depth (ordinal+1))
        (liftMap (R := ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
          ((PT.words (C.paNativeCayleySourceTrace observation nontrivial depth half field)).get index))) := by
  rw [actualOccurrence, T.actualSourceOccurrence_word]
  simp only [sourceOccurrence,
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence.transport_word, PT.stepOccurrence_word]

theorem actual_before_length (ordinal : Nat) (field : Fin 3) (index : Index observation nontrivial half depth field) :
    (actualOccurrence observation nontrivial half depth ordinal field index).before.length =
      T.actualSourceOffset observation nontrivial half depth ordinal+
        (C.paNativeCayleySourceSegment observation nontrivial depth half field).before.length+1+index.val := by
  simp only [actualOccurrence, T.actualSourceOccurrence_before_length, sourceOccurrence,
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence.transport_position,
    PT.stepOccurrence_before_length, Nat.add_assoc]

theorem actual_positions (ordinal : Nat) (field : Fin 3) :
    StrictMono (fun index : Index observation nontrivial half depth field =>
      (actualOccurrence observation nontrivial half depth ordinal field index).before.length) := by
  intro first second ordered
  change (actualOccurrence observation nontrivial half depth ordinal field first).before.length <
    (actualOccurrence observation nontrivial half depth ordinal field second).before.length
  simp only [actualOccurrence, T.actualSourceOccurrence_before_length, sourceOccurrence,
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence.transport_position]
  exact Nat.add_lt_add_left
    (Nat.add_lt_add_left
      (PT.stepOccurrence_positions
        (C.paNativeCayleySourceTrace observation nontrivial depth half field) ordered) _) _

end OriginalKPaNativeCayleySourceOccurrences
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKPaNativeCayleySourceOccurrences"
