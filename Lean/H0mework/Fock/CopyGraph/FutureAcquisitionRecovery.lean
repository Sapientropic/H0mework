import H0mework.Fock.CopyGraph.FutureAcquisitionSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureAcquisition

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical InnerProductSpace
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem acquired_column_mem (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1) ∈
      SourceCopyCofinal.historyImages (inventoryBound runtime) index (steps + 1) := by
  refine ⟨SourceHistoryWord.lift (inventoryBound runtime + (steps + 1))
    (Finsupp.single (inventoryBound runtime + steps + 1) (1 : ℂ)), ?_⟩
  change SourceCopyGraph.action (inventoryBound runtime) index
    (SourceJointFiniteDecoder.read (inventoryBound runtime + (steps + 1)) _) = _
  rw [SourceJointFiniteDecoder.read_source, SourceHistoryWord.word_lift _ _ (by
    intro coordinate present
    simp only [Finsupp.support_single _ (one_ne_zero : (1 : ℂ) ≠ 0), Finset.mem_singleton] at present
    omega)]
  rfl

theorem acquired_read_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    observer runtime index (steps + 1) (arrival runtime index steps) ≠ 0 := by
  intro vanished
  have projected : (SourceCopyCofinal.historyImages (inventoryBound runtime) index (steps + 1)).starProjection
      (arrival runtime index steps) = 0 := by
    rw [SourceCopyCofinal.actual_projection, SourceCopyCofinal.advanced_action]
    change SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index (steps + 1) _) = 0
    rw [vanished, map_zero]
  have invisible : arrival runtime index steps ∈
      (SourceCopyCofinal.historyImages (inventoryBound runtime) index (steps + 1))ᗮ := by
    rwa [← Submodule.starProjection_apply_eq_zero_iff]
  have orthogonal := (Submodule.mem_orthogonal _ _).mp invisible
    (SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1))
    (acquired_column_mem runtime index steps)
  rw [acquired_pairing] at orthogonal
  exact one_ne_zero orthogonal

theorem old_read_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    observer runtime index steps (arrival runtime index steps) = 0 :=
  SourceCopyRecordedRecurrence.hidden_future_zero runtime index steps _

theorem recovered_birth (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceCopyGraph.recover (inventoryBound runtime) index
      (SourceRecordedEvolution.birth runtime index steps (arrival runtime index steps)) =
        observer runtime index (steps + 1) (arrival runtime index steps) := by
  have source := SourceCopyTemporalAcquisition.observer_step runtime index steps (arrival runtime index steps)
  rw [old_read_zero, zero_add] at source
  exact source.symm

theorem birth_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceRecordedEvolution.birth runtime index steps (arrival runtime index steps) ≠ 0 := by
  intro vanished
  have source := recovered_birth runtime index steps
  rw [vanished, map_zero] at source
  exact acquired_read_nonzero runtime index steps source.symm

end
end SourceCopyFutureAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
