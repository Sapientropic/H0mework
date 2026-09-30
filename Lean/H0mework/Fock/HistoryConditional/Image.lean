import H0mework.Fock.HistoryConditional.Polynomial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledWordOperator

open SourceGeneratedActionWords SourceCyclicModule
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem source_image (depth : Nat) (word : List (Fock.Letter depth)) (target : SourceOperationNative.Carrier process) :
    target ∈ (action depth word).range ↔ ∀ state,
      ¬ ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 < state + 1 ∧
        (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 ∣
          state + 1 - (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2) →
        target state = 0 := by
  constructor
  · rintro ⟨source, rfl⟩ state outside
    exact action_outside depth word source state (fun inside => outside ((index_range _ _).mp inside))
  · intro support
    refine ⟨recover depth word target, ?_⟩
    apply Finsupp.ext
    intro state
    by_cases inside : state ∈ Set.range (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)))
    · obtain ⟨prior, rfl⟩ := inside
      rw [action_coefficient, recovery_reads]
    · rw [action_outside depth word _ state inside]
      exact (support state (fun image => inside ((index_range _ _).mpr image))).symm

theorem shift_root_residual (depth : Nat) :
    residual depth [.inl ()] (program 1) = program 1 := by
  have recovered : recover depth [.inl ()] (program 1) = 0 := by
    apply Finsupp.ext
    intro state
    rw [recovery_reads, program_one, original_root]
    rw [SourceCopyWordAffine.execute_original]
    change Finsupp.single 0 (1 : ℤ) (state + 1) = 0
    simp
  change program 1 - action depth [.inl ()] (recover depth [.inl ()] (program 1)) = program 1
  rw [recovered, map_zero, sub_zero]

theorem no_shift_root_preimage (depth : Nat) :
    ¬ ∃ proposal : SourceOperationNative.Carrier process, action depth [.inl ()] proposal = program 1 := by
  rintro ⟨proposal, same⟩
  have vanished := ((original_fibre depth [.inl ()] (program 1) proposal).mp same).2
  rw [shift_root_residual, program_one, original_root] at vanished
  exact one_ne_zero (Finsupp.single_eq_zero.mp vanished)

end
end SourceCompiledWordOperator
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
