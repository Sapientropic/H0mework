import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineCancellationForces
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineStationarity

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEnginePaidDepth
open PreparationVacuumEngineSource PreparationVacuumEngineIdentities PreparationVacuumEngineCancellation
open PreparationVacuumCanonicalMoyal PreparationActualFactor
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open PreparationPhaseSource PreparationVacuumWeyl
open scoped BigOperators

private abbrev originalClockAt := engine_const% "clockAt"

theorem sourceEngine_preserves_paid (small big : ℕ) (paid : small≤big)
    (a : Fin 4) (i : ℕ) (bound : i ≤ small) :
    originalClockAt (sourceEngine big) a i=originalClockAt (sourceEngine small) a i := by
  induction big,paid using Nat.le_induction with
  | base => rfl
  | succ big paid ih =>
    exact (sourceEngine_clockAgreement big a i (by omega)).trans ih

theorem sourceEngine_paidDepth (small big : ℕ) (paid : small≤big) (equation : Option (Fin 4)) :
    forceOrEnergy small (sourceEngine big) equation=forceOrEnergy small (sourceEngine small) equation :=
  forceOrEnergy_clockAgreement small _ _ (fun a i hi => sourceEngine_preserves_paid small big paid a i hi) equation

theorem sourceEngine_allForces_zero (k : ℕ) (a : Fin 4)
    (z : FlatConfiguration) (p : PhysicalMomentum)
    (position : z∈thetaPositionClosed) (direction : normalizedMomentum p∈thetaDirectionClosed) (nonzero : p≠0) :
    sourceEngineForces k a (z,p)=0 := by
  cases k with
  | zero => exact congrFun (sourceEngineForces_zero a) (z,p)
  | succ k => exact sourceEngineForces_successor_zero k a z p position direction nonzero

theorem sourceEngine_paidForces_zero (small big : ℕ) (paid : small≤big) (a : Fin 4)
    (z : FlatConfiguration) (p : PhysicalMomentum)
    (position : z∈thetaPositionClosed) (direction : normalizedMomentum p∈thetaDirectionClosed) (nonzero : p≠0) :
    forceOrEnergy small (sourceEngine big) (some a) (Fin.last small) (z,p)=0 := by
  rw [sourceEngine_paidDepth small big paid]
  exact sourceEngine_allForces_zero small a z p position direction nonzero

theorem sourceEngine_energy_paidDepth (small big : ℕ) (paid : small≤big) :
    forceOrEnergy small (sourceEngine big) none (Fin.last small)=sourceEngineEnergy small := by
  rw [sourceEngine_paidDepth small big paid]
  rfl

end LowEnergy.PreparationVacuumEnginePaidDepth
