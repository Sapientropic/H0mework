import H0mework.Fock.HistoryConditional.MinimumWindowErrorMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPrecision

open SourceCopyProgram (Index)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def columnReader (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) (phase : Fin (index.val + 2)) :
    Window runtime index →L[ℂ] ℂ :=
  ((innerSL ℂ (SourceColumnForcing.column (inventoryBound runtime) index actor.val)).comp
    (SourceCopyGraph.action (inventoryBound runtime) index)).comp (ContinuousLinearMap.proj phase)

theorem column_original (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) (phase : Fin (index.val + 2)) :
    (columnReader runtime index steps actor phase).toLinearMap =
      SourceOperatorObservationAcquisition.columns runtime index steps actor phase := rfl

def cotest (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (actor : Nat) :
    SourceJointClockGraph.Carrier :=
  (SourceCopyGraph.action (inventoryBound runtime) index).adjoint
    (SourceColumnForcing.column (inventoryBound runtime) index actor)

theorem column_pairing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) (phase : Fin (index.val + 2)) (samples : Window runtime index) :
    columnReader runtime index steps actor phase samples = ⟪cotest runtime index actor.val, samples phase⟫_ℂ := by
  exact ((SourceCopyGraph.action (inventoryBound runtime) index).adjoint_inner_left _ _).symm

theorem column_bound (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) (phase : Fin (index.val + 2)) (samples : Window runtime index) :
    ‖columnReader runtime index steps actor phase samples‖ ≤ ‖cotest runtime index actor.val‖ * ‖samples phase‖ := by
  rw [column_pairing]
  exact norm_inner_le_norm _ _

end
end SourceWindowPrecision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
