import H0mework.Versions.X.Fock.HistoryConditional.WordStreamSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalWordStream

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (observation bornObservation count)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem word_read_injective : Function.Injective SourceJointClockGraph.read := by
  intro left right same
  apply SourceMassCompletion.jointRead_injective
  simpa only [SourceJointClockGraph.joint_source] using congrArg SourceJointClockGraph.joint same

theorem table_read_injective : Function.Injective read := by
  intro left right same
  apply Finsupp.ext
  intro value
  have entry := congrArg (fun table : SourceConditionalFiniteStream.Table => table value) same
  change ((left value).1, SourceJointClockGraph.read (left value).2) =
    ((right value).1, SourceJointClockGraph.read (right value).2) at entry
  apply Prod.ext
  · exact congrArg (fun item : ℝ × SourceJointClockGraph.Carrier => item.1) entry
  · apply word_read_injective
    exact congrArg (fun item : ℝ × SourceJointClockGraph.Carrier => item.2) entry

theorem support_read (table : Table) : (read table).support = table.support := by
  ext value
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  change ((table value).1, SourceJointClockGraph.read (table value).2) ≠ 0 ↔ table value ≠ 0
  constructor
  · intro nonzero zero
    apply nonzero
    rw [zero]
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
    rfl
  · intro nonzero zero
    apply nonzero
    apply Prod.ext
    · exact congrArg (fun item : ℝ × SourceJointClockGraph.Carrier => item.1) zero
    · apply word_read_injective
      exact (congrArg (fun item : ℝ × SourceJointClockGraph.Carrier => item.2) zero).trans (map_zero SourceJointClockGraph.read).symm

theorem support_exact (bound depth : Nat) :
    (generate depth bound).support = SourceUniformFibreVariance.outputs bound (observation bound depth) := by
  rw [← support_read, generated_read, SourceConditionalFiniteStream.support_exact]

theorem source_single (bound : Nat) (index : Fin (bound + 1)) : sourceWord bound index = Finsupp.single (index.val + 1) (1 : ℂ) := by
  change SourceClockComplex.ofNative (Finsupp.single (runtimeAt (index.val + 1)).state (1 : ℤ)) = _
  rw [SourceClockComplex.ofNative_single, runtimeAt_state]
  norm_num

theorem generated_entry (bound depth : Nat) (value : Field parity) :
    ((generate depth bound value).1, SourceJointClockGraph.read (generate depth bound value).2) =
      (count bound depth value, SourceConditionalInnovation.decoder bound depth value) := by
  have entry := congrArg (fun table : SourceConditionalFiniteStream.Table => table value) (generated_read bound depth)
  change ((generate depth bound value).1, SourceJointClockGraph.read (generate depth bound value).2) =
    SourceConditionalFiniteStream.generate depth bound value at entry
  exact entry.trans (SourceConditionalFiniteStream.generated_entry bound depth value)

theorem word_conditional (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support) :
    (generate depth bound value).2 =
      ∑ index : Fin (bound + 1),
        ((SourceConditionalInventory.conditional bound depth value supported index).toReal : ℂ) • sourceWord bound index := by
  apply word_read_injective
  have entry := congrArg Prod.snd (generated_entry bound depth value)
  change SourceJointClockGraph.read (generate depth bound value).2 = SourceConditionalInnovation.decoder bound depth value at entry
  rw [SourceConditionalInnovation.decoder_mean bound depth value supported] at entry
  rw [map_sum]
  simp only [map_smul, source_read]
  exact entry

theorem coordinate_word (word : Nat →₀ ℂ) (index : Nat) :
    SourceGInformationCost.coordinateRead index (SourceJointClockGraph.read word) = word index := by
  change SourceSuccessorBoundary.readWord word index = word index
  exact SourceSuccessorBoundary.readWord_coordinate word index

theorem word_coefficient (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support) (actor : Fin (bound + 1)) :
    (generate depth bound value).2 (actor.val + 1) =
      ((SourceConditionalInventory.conditional bound depth value supported actor).toReal : ℂ) := by
  rw [← coordinate_word]
  have entry := congrArg Prod.snd (generated_entry bound depth value)
  change SourceJointClockGraph.read (generate depth bound value).2 = SourceConditionalInnovation.decoder bound depth value at entry
  rw [entry, SourceConditionalInnovation.decoder_mean bound depth value supported]
  exact SourcePosteriorReadback.mean_coordinate bound _ actor

end
end SourceConditionalWordStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
