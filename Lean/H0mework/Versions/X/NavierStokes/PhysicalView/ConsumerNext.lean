import H0mework.Versions.X.NavierStokes.WindowPhysics.RootRuntime
import H0mework.Versions.X.NavierStokes.WindowPhysics.RootPrediction
import H0mework.Versions.X.NavierStokes.PhysicalView.ConsumerObservation

set_option autoImplicit false
open scoped Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeViewConsumerNext

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowRootCarrier NativeViewRuntime NativeViewObservation

noncomputable section

abbrev Runtime := LivingRuntimeState process

def index (runtime : Runtime) : ℕ := runtime.state

theorem index_next (runtime : Runtime) : index runtime.tick.next = index runtime + 1 := rfl

/-- An explicit dependent index exposes the payload returned by the actual runtime projection. -/
def payload (runtime : Runtime) : CarrierAt initial (nativeTemporalEmitted initial (visit (index runtime)).current) :=
  carrier runtime

def advance (runtime : Runtime) : ℝ := (run initial (index runtime)).contact.time.1

theorem advance_nonnegative (runtime : Runtime) : 0 ≤ advance runtime :=
  (run initial (index runtime)).contact.time.2.1

theorem visit_current (index : ℕ) : (visit index).current = .finite index :=
  (nativeTemporalProductiveHistory initial).visitAt_current index

theorem measured_generated (runtime : Runtime) (time : ℝ) :
    measure (payload runtime) resolution time =
      NativeWindowHeatEvolution.source initial resolution.1 (elapsedTime initial (index runtime) + time) := by
  erw [measure_view, CarrierAt.view_generated]
  rw [visit_current]
  rfl

/-- The complete measured pair advances with the original root tick, including its zero mode and every stress entry. -/
theorem measured_next (runtime : Runtime) (time : ℝ) :
    measure (payload runtime.tick.next) resolution time =
      measure (payload runtime) resolution (advance runtime + time) := by
  rw [measured_generated, measured_generated, index_next]
  rw [elapsedTime_succ, add_assoc]
  rfl

def clock (runtime : Runtime) (time : ℝ) : ℝ :=
  NativeViewPreparation.rootClock initial (visit (index runtime)).current time

theorem clock_next (runtime : Runtime) (time : ℝ) :
    clock runtime.tick.next time = clock runtime (advance runtime + time) := by
  simp only [clock, index_next, visit_current]
  exact NativeViewPreparation.rootClock_finite_next initial (index runtime) time

def initialState (runtime : Runtime) : NativeCompleteStressAction.FullSpace :=
  NativeViewPreparation.preparedInitial (payload runtime) resolution

theorem initial_next (runtime : Runtime) :
    initialState runtime.tick.next = measure (payload runtime) resolution (advance runtime) := by
  change measure (payload runtime.tick.next) resolution 0 = _
  simpa only [add_zero] using measured_next runtime 0

/-- Duhamel's prediction from this preparation and its generated stress is written into the next preparation. -/
theorem forecast_next (runtime : Runtime) :
    NativeViewRootPrediction.predict (payload runtime) resolution (advance runtime) =
      NativeNegativeFourMomentum.embed (initialState runtime.tick.next).fst := by
  erw [NativeViewRootPrediction.prediction_recovers_velocity _ _ _ (advance_nonnegative runtime), initial_next, measure_view]

theorem pairing_next (runtime : Runtime) (time : ℝ) :
    NativeWindowRootPairing.data (payload runtime.tick.next) resolution time =
      NativeWindowRootPairing.data (payload runtime) resolution (advance runtime + time) :=
  NativeWindowRootPairing.data_eq_of_view_eq _ _ _ _ _ (measured_next runtime time)

end
end SaturationMonoid.NavierStokes.NativeViewConsumerNext
