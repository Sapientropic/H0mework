import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Source.SourceGeneratedActualRelationCycleMemoryWitnessPublication

/-!
# Proof-carrying actual-cycle memory kernel escape

The canonical reflexive-memory witness separates exactly one period-three
authority-kernel pair.  The coarse seed observer remains non-faithful; the
refined observer gains a faithful reconstruction only on the generated
two-point restriction, never on all cross depths.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingActualRelationCycleMemoryKernelEscape

noncomputable section

open Observer
open M14SourceGeneratedActualRelationThreeCycle
open M14SourceGeneratedActualRelationCycleMemoryWitnessPublication
open M14ProofCarryingActualRelationCycleReflexiveMemory

theorem cycleMemory_coarseObserver_noOccurrenceLeftInverse (base : Nat) :
    type_of% ((cycleMemoryKernelPairAt base).noOccurrenceLeftInverse) :=
  (cycleMemoryKernelPairAt base).noOccurrenceLeftInverse

theorem cycleMemory_coarseObserver_noAuthorityFactorization (base : Nat) :
    type_of% ((cycleMemoryKernelPairAt base).noAuthorityFactorization) :=
  (cycleMemoryKernelPairAt base).noAuthorityFactorization

/-- The exact two generated endpoints become faithfully reconstructible only
after honest witness publication. -/
theorem cycleMemory_twoPointPosteriorReconstruction (base : Nat) :
    Nonempty
        (FaithfulAuthorityReconstruction
          (cycleMemoryKernelRefinementAt base).twoPointObserver) ∧
      Nonempty
        (AuthorityFactorization
          (cycleMemoryKernelRefinementAt base).twoPointObserver) :=
  ⟨⟨(cycleMemoryKernelRefinementAt base
      ).twoPointFaithfulAuthorityReconstruction⟩,
    ⟨(cycleMemoryKernelRefinementAt base).twoPointAuthorityFactorization⟩⟩

/-- Full direct consumer.  Its only public input is the actual cycle base. -/
theorem actualRelationCycleMemoryKernelEscape_directConsumer (base : Nat) :
    type_of% (actualRelationCycleReflexiveMemoryCore_directConsumer base) ∧
      type_of% (actualRelationThreeCycle_directConsumer base) ∧
      Nonempty (AuthorityKernelPair cycleMemoryAuthorityObserver) ∧
      Nonempty
        (SourceGeneratedActualRelationCycleMemoryWitnessAt base (base + 3)) ∧
      IsEmpty (SourceGeneratedActualRelationCycleMemoryWitnessAt base base) ∧
      (∀ depth : Nat,
        cycleMemoryPublicationTag base depth = true ↔
          Nonempty
            (SourceGeneratedActualRelationCycleMemoryWitnessAt base depth)) ∧
      cycleMemoryAuthorityObserver.forget (base + 3) =
        cycleMemoryAuthorityObserver.forget base ∧
      cycleMemoryAuthorityObserver.authorityK (base + 3) ≠
        cycleMemoryAuthorityObserver.authorityK base ∧
      type_of% (cycleMemory_coarseObserver_noOccurrenceLeftInverse base) ∧
      ¬ Nonempty
        (AuthorityFactorization cycleMemoryAuthorityObserver) ∧
      (cycleMemoryRefinedObserverAt base).forget (base + 3) ≠
        (cycleMemoryRefinedObserverAt base).forget base ∧
      type_of% (cycleMemory_twoPointPosteriorReconstruction base) :=
  ⟨actualRelationCycleReflexiveMemoryCore_directConsumer base,
    (sourceGeneratedActualRelationCycleMemoryWitnessAt base).actualCycle,
    ⟨cycleMemoryKernelPairAt base⟩,
    ⟨sourceGeneratedActualRelationCycleMemoryWitnessAt base⟩,
    cycleMemoryWitnessAt_base_isEmpty base,
    cycleMemoryPublicationTag_true_iff base,
    cycleMemory_coarseVisible_eq base,
    (cycleMemoryKernelPairAt base).authority_ne,
    cycleMemory_coarseObserver_noOccurrenceLeftInverse base,
    cycleMemory_coarseObserver_noAuthorityFactorization base,
    cycleMemory_refinedVisible_ne base,
    cycleMemory_twoPointPosteriorReconstruction base⟩

end
end M14ProofCarryingActualRelationCycleMemoryKernelEscape
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationCycleMemoryKernelEscape.cycleMemory_twoPointPosteriorReconstruction
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRelationCycleMemoryKernelEscape.actualRelationCycleMemoryKernelEscape_directConsumer
