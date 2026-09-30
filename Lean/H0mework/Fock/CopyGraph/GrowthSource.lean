import H0mework.Fock.CopyGraph.RefinementObservation
import H0mework.Fock.HistoryModel.Installed
import H0mework.Probability.HistoryWord.Coherence

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
noncomputable section

theorem old_material (depth : Nat) (index : Index depth) :
    NativeCopy.Fock.material (depth + 1) (FamilyModel.Fock.oldIndex depth index) = NativeCopy.Fock.material depth index :=
  ((FamilyModel.Fock.runtime_family_next_factorizes depth).2.2.2.1 index).2

theorem old_index (depth : Nat) (index : Index depth) (state : Nat) :
    SourceCopyProgram.indexAfter (depth + 1) (FamilyModel.Fock.oldIndex depth index) state =
      SourceCopyProgram.indexAfter depth index state :=
  congrArg (fun material => NativeWindow.bound (NativeCopy.copy material
    (NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.finiteVisit state).current)) (old_material depth index)

theorem old_complex_action (depth : Nat) (index : Index depth) (word : Nat →₀ ℂ) :
    SourceCopyGraph.complexAction (depth + 1) (FamilyModel.Fock.oldIndex depth index) word =
      SourceCopyGraph.complexAction depth index word := by
  unfold SourceCopyGraph.complexAction
  rw [funext (old_index depth index)]

theorem normalized_graph {old fresh : Nat} (retained : old ≤ fresh) (value : Space (historyPMF old)) :
    SourceJointClockGraph.read (SourceHistoryWord.word fresh (SourceHistoryGrowth.normalizedInclusion retained value)) =
      SourceJointClockGraph.read (SourceHistoryWord.word old value) :=
  congrArg SourceJointClockGraph.read (SourceHistoryWord.normalized_word retained value)

theorem tick_copy_read (depth : Nat) (index : Index depth) (value : Space (historyPMF depth)) :
    SourceConditionalGraph.copyRead (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (SourceHistoryGrowth.normalizedInclusion (Nat.le_succ depth) value) =
        SourceConditionalGraph.copyRead depth depth index value := by
  change SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (SourceJointClockGraph.read (SourceHistoryWord.word (depth + 1) (SourceHistoryGrowth.normalizedInclusion (Nat.le_succ depth) value))) =
      SourceCopyGraph.action depth index (SourceJointClockGraph.read (SourceHistoryWord.word depth value))
  rw [normalized_graph, SourceCopyGraph.action_source, SourceCopyGraph.action_source, old_complex_action]

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
