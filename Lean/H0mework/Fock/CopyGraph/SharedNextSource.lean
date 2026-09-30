import H0mework.Fock.CopyGraph.CurrentCoordinatesColumn

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedNext

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceCopyTimeModel (Packet finitePhases time)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem column_mem (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) :
    SourceColumnForcing.column (inventoryBound runtime) index actor.val ∈
      SourceCopyCofinal.historyImages (inventoryBound runtime) index steps := by
  refine ⟨SourceHistoryWord.lift (inventoryBound runtime + steps) (Finsupp.single actor.val (1 : ℂ)), ?_⟩
  change SourceCopyGraph.action (inventoryBound runtime) index (SourceJointFiniteDecoder.read (inventoryBound runtime + steps) _) = _
  rw [SourceJointFiniteDecoder.read_source, SourceHistoryWord.word_lift _ _ (by
    intro coordinate present
    simp only [Finsupp.support_single _ (one_ne_zero : (1 : ℂ) ≠ 0), Finset.mem_singleton] at present
    omega)]
  rfl

theorem observed_columns (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) (target : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
      SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index steps target)⟫_ℂ =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, target⟫_ℂ := by
  have projected := SourceCopyCofinal.actual_projection runtime index steps target
  rw [SourceCopyCofinal.advanced_action] at projected
  change (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).starProjection target =
    SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index steps target) at projected
  rw [← projected]
  have paired := Submodule.inner_starProjection_left_eq_right
    (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps)
    (SourceColumnForcing.column (inventoryBound runtime) index actor.val) target
  rw [Submodule.starProjection_eq_self_iff.mpr (column_mem runtime index steps actor)] at paired
  exact paired.symm

def columnRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (packet : Packet (inventoryBound runtime) index) (actor : Fin (inventoryBound runtime + steps + 1))
    (phase : Fin (index.val + 1)) : ℂ :=
  ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
    SourceCopyGraph.action (inventoryBound runtime) index (packet phase)⟫_ℂ

theorem column_read_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (actor : Fin (inventoryBound runtime + steps + 1)) (phase : Fin (index.val + 1)) :
    columnRead runtime index steps (finitePhases runtime index steps target) actor phase =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, time phase.val target⟫_ℂ :=
  observed_columns runtime index steps actor (time phase.val target)

theorem packet_samples (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (phase : Fin (index.val + 1)) :
    SourceColumnForcing.samples (inventoryBound runtime) (inventoryBound runtime + steps) index
      (SourceCopyGraph.action (inventoryBound runtime) index (finitePhases runtime index steps target phase)) =
      SourceColumnForcing.samples (inventoryBound runtime) (inventoryBound runtime + steps) index (time phase.val target) := by
  funext actor
  unfold SourceColumnForcing.samples
  rw [show ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
      SourceCopyGraph.action (inventoryBound runtime) index (finitePhases runtime index steps target phase)⟫_ℂ =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, time phase.val target⟫_ℂ from
    column_read_source runtime index steps target actor phase]

universe u
variable {Observed : Type u} [MeasurableSpace Observed]

theorem packet_forcing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (query : Fin (inventoryBound runtime + steps + 1) → Observed) (target : SourceJointClockGraph.Carrier)
    (phase : Fin (index.val + 1)) :
    SourceColumnForcing.forcing (inventoryBound runtime) (inventoryBound runtime + steps) index query
      (SourceCopyGraph.action (inventoryBound runtime) index (finitePhases runtime index steps target phase)) =
      SourceColumnForcing.forcing (inventoryBound runtime) (inventoryBound runtime + steps) index query (time phase.val target) := by
  unfold SourceColumnForcing.forcing
  rw [packet_samples]

end
end SourceCopySharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
