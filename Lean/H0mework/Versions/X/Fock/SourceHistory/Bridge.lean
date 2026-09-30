import H0mework.Versions.X.Fock.SourceHistory.Projection
import H0mework.Versions.X.Fock.Cofinal.OperationNative

/-! The original whole native materialization factors through the same full source field and action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullProjection.Fock

open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFockRuntime

noncomputable section

def bridge : SourceOperationNative.Carrier process →ₗ[ℤ] Field nativeStep fullRead :=
  Finsupp.linearCombination ℤ fun state => fieldPoint nativeStep fullRead (finiteVisit state).current

theorem bridge_statePoint (state : process.State) :
    bridge (SourceOperationNative.statePoint process state) =
      fieldPoint nativeStep fullRead (finiteVisit state).current := by
  simp only [bridge, SourceOperationNative.statePoint, Finsupp.linearCombination_single]
  exact (Field nativeStep fullRead).isModule.one_smul _

theorem bridge_point (runtime : LivingRuntimeState process) :
    bridge (SourceOperationNative.point runtime) = fieldPoint nativeStep fullRead runtime.current.visit.current :=
  bridge_statePoint runtime.state

theorem original_materialization :
    stateProjection.comp bridge = ParticleWaveFockNativeConsumer.materialization := by
  apply SourceOperationNative.observer_unique
  intro state
  change stateProjection (bridge (SourceOperationNative.statePoint process state)) = _
  rw [bridge_statePoint]
  exact readNow_point nativeStep sourceStateAt (finiteVisit state).current

theorem bridge_action :
    (fieldAction nativeStep fullRead).comp bridge = bridge.comp (SourceOperationNative.sourceAction process) := by
  apply Finsupp.lhom_ext'
  intro state
  apply LinearMap.ext_ring
  change fieldAction nativeStep fullRead (bridge (SourceOperationNative.statePoint process state)) =
    bridge (SourceOperationNative.sourceAction process (SourceOperationNative.statePoint process state))
  rw [SourceOperationNative.sourceAction_statePoint, bridge_statePoint, bridge_statePoint]
  exact fieldPoint_action nativeStep fullRead ((finiteVisit state).current : Current)

end
end SourceOwnedObservationHistory.FullProjection.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
