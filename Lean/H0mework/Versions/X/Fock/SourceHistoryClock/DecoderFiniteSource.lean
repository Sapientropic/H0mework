import H0mework.Versions.X.Fock.SourceHistoryClock.DecoderError
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointFiniteDecoder

open SourceGeneratedAtomicObservation SourceGeneratedRuntimeHistoryProbability SourceSuccessorBoundary
noncomputable section

abbrev Space (bound : Nat) := SourceWeightedRecovery.Space (historyPMF bound)

def read (bound : Nat) : Space bound →L[ℂ] SourceJointClockGraph.Carrier :=
  ∑ index : Fin (bound + 1),
    (((Real.sqrt (historyPMF bound index).toReal : ℂ) •
      evalAtContinuous (historyPMF bound) index (SourceUniformFibreVariance.source_positive bound index)).smulRight
        (SourceJointClockGraph.read (Finsupp.single index.val (1 : ℂ))))

theorem read_source (bound : Nat) (value : Space bound) :
    read bound value = SourceJointClockGraph.read (SourceHistoryWord.word bound value) := by
  rw [read, sum_apply, SourceHistoryWord.word_sum, map_sum]
  apply Finset.sum_congr rfl
  intro index _
  change (SourceHistoryWord.coefficient bound index value) •
    SourceJointClockGraph.read (Finsupp.single index.val 1) =
      SourceJointClockGraph.read (Finsupp.single index.val (SourceHistoryWord.coefficient bound index value))
  rw [← map_smul]
  congr 1
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

def action (bound : Nat) : Space bound →L[ℂ] SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.action.comp (read bound)

theorem action_source (bound : Nat) (value : Space bound) :
    action bound value = SourceJointClockGraph.read (push ℂ (SourceHistoryWord.word bound value)) := by
  change SourceJointClockGraph.action (read bound value) = _
  rw [read_source, SourceJointClockGraph.action_source]

theorem source_energy (bound : Nat) (value : Space bound) :
    ‖action bound value‖ ^ 2 = ‖value‖ ^ 2 + ‖mass ℂ (SourceHistoryWord.word bound value)‖ ^ 2 +
      ‖SourceClockComplex.clock (push ℂ (SourceHistoryWord.word bound value))‖ ^ 2 := by
  rw [action_source, SourceJointClockGraph.norm_sq, SourceJointClockGraph.joint_source,
    SourceJointClockGraph.clock_source, ← SourceMassCompletion.action_source, SourceMassCompletion.action.norm_map,
    SourceMassCompletion.jointRead_apply, WithLp.prod_norm_sq_eq_of_L2]
  change (‖readWord (SourceHistoryWord.word bound value)‖ ^ 2 +
    ‖mass ℂ (SourceHistoryWord.word bound value)‖ ^ 2) + _ = _
  rw [SourceHistoryWord.hilbert_norm_sq]

theorem source_norm_le (bound : Nat) (value : Space bound) : ‖value‖ ≤ ‖action bound value‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [source_energy]
  nlinarith only [sq_nonneg ‖mass ℂ (SourceHistoryWord.word bound value)‖,
    sq_nonneg ‖SourceClockComplex.clock (push ℂ (SourceHistoryWord.word bound value))‖]

theorem source_antilipschitz (bound : Nat) : AntilipschitzWith 1 (action bound) :=
  (action bound).antilipschitz_of_bound (by intro value; simpa only [NNReal.coe_one, one_mul] using source_norm_le bound value)

theorem source_injective (bound : Nat) : Function.Injective (action bound) := (source_antilipschitz bound).injective

theorem source_closed_range (bound : Nat) : IsClosed (Set.range (action bound)) :=
  (source_antilipschitz bound).isClosed_range (action bound).uniformContinuous

end
end SourceJointFiniteDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
