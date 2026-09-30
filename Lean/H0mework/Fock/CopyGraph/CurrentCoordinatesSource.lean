import H0mework.Fock.CopyGraph.FutureAcquisitionObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem current_column_mem (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps) ∈
      SourceCopyCofinal.historyImages (inventoryBound runtime) index steps := by
  refine ⟨SourceHistoryWord.lift (inventoryBound runtime + steps)
    (Finsupp.single (inventoryBound runtime + steps) (1 : ℂ)), ?_⟩
  change SourceCopyGraph.action (inventoryBound runtime) index
    (SourceJointFiniteDecoder.read (inventoryBound runtime + steps) _) = _
  rw [SourceJointFiniteDecoder.read_source, SourceHistoryWord.word_lift _ _ (by
    intro coordinate present
    simp only [Finsupp.support_single _ (one_ne_zero : (1 : ℂ) ≠ 0), Finset.mem_singleton] at present
    omega)]
  rfl

theorem observed_column (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps),
      SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index steps target)⟫_ℂ =
        ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps), target⟫_ℂ := by
  have realized := SourceCopyCofinal.actual_projection runtime index steps target
  rw [SourceCopyCofinal.advanced_action] at realized
  change (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).starProjection target =
    SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index steps target) at realized
  rw [← realized]
  have source := Submodule.inner_starProjection_left_eq_right
    (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps)
    (SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps)) target
  rw [Submodule.starProjection_eq_self_iff.mpr (current_column_mem runtime index steps)] at source
  exact source.symm

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
