import H0mework.Chemistry.LAlanineInertia.SourceSourceBoundLAlanine40KInertialStep
import H0mework.Chemistry.LAlanineInertia.DynamicsVelocityVerletResidual

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Producer

open Mechanics Force.Interface
open LAlanine40K2025.Inertia.Source

noncomputable section

theorem currentLedger_eq_parent :
    stepReadout.currentLedger = Force.Source.updateReadout.targetEnergyLedger := rfl

theorem currentPositionPicobohr_eq_parent :
    stepReadout.currentPositionPicobohr = Force.Source.updateReadout.recordedTargetPositions := by
  funext atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem currentNuclei_eq_parent : stepReadout.currentNuclei = Force.Source.updateReadout.targetNuclei := by decide
theorem nuclei_preserved : stepReadout.targetNuclei = stepReadout.currentNuclei := by decide

theorem masses_positive : ∀ atom, 0 < stepReadout.masses atom := by
  change ∀ atom, 0 < SourceParsing.massRead _ atom
  intro atom
  fin_cases atom <;> norm_num [SourceParsing.massRead, SourceParsing.rationalRead]

theorem masses_nonzero : ∀ atom, stepReadout.masses atom ≠ 0 :=
  fun atom => ne_of_gt (masses_positive atom)

theorem duration_eq_nativeClock : stepReadout.duration = Propagation.Producer.nativeClockStep := by
  rw [Propagation.Producer.nativeClockStep_exact]
  rfl

theorem duration_positive : 0 < stepReadout.duration :=
  duration_eq_nativeClock.symm ▸ Propagation.Producer.nativeClockStep_positive

theorem initial_momentum_zero : stepReadout.current.momentum = 0 := by
  change SourceParsing.coordinateRead _ = 0
  funext atom axis
  fin_cases atom <;> fin_cases axis <;>
    norm_num [SourceParsing.coordinateRead, SourceParsing.rationalRead]

def referenceNext : PhasePoint :=
  verletStep stepReadout.masses stepReadout.duration stepReadout.current.force stepReadout.target.force stepReadout.current.phase

def explicitResidual : PhasePoint := ⟨stepReadout.positionResidual, stepReadout.momentumResidual⟩

theorem targetPosition_reconstruction : ∀ atom axis,
    stepReadout.target.position atom axis = referenceNext.position atom axis + stepReadout.positionResidual atom axis := by
  change ∀ atom axis, SourceParsing.coordinateRead _ atom axis =
    SourceParsing.coordinateRead _ atom axis +
      SourceParsing.rationalRead _ * SourceParsing.coordinateRead _ atom axis / SourceParsing.massRead _ atom +
      SourceParsing.rationalRead _ ^ 2 * (-SourceParsing.coordinateRead _ atom axis) /
        (2 * SourceParsing.massRead _ atom) + SourceParsing.coordinateRead _ atom axis
  intro atom axis
  fin_cases atom <;> fin_cases axis <;>
    norm_num [SourceParsing.massRead, SourceParsing.coordinateRead, SourceParsing.rationalRead]

theorem targetMomentum_reconstruction : ∀ atom axis,
    stepReadout.target.momentum atom axis = referenceNext.momentum atom axis + stepReadout.momentumResidual atom axis := by
  change ∀ atom axis, SourceParsing.coordinateRead _ atom axis =
    SourceParsing.coordinateRead _ atom axis + SourceParsing.rationalRead _ *
      (-SourceParsing.coordinateRead _ atom axis + -SourceParsing.coordinateRead _ atom axis) / 2 +
      SourceParsing.coordinateRead _ atom axis
  intro atom axis
  fin_cases atom <;> fin_cases axis <;>
    norm_num [SourceParsing.coordinateRead, SourceParsing.rationalRead]

theorem targetPhase_reconstruction : stepReadout.target.phase = addResidual referenceNext explicitResidual := by
  apply PhasePoint.ext <;> funext atom axis
  · exact targetPosition_reconstruction atom axis
  · exact targetMomentum_reconstruction atom axis

theorem positionResidual_bound : ∀ atom axis,
    |stepReadout.positionResidual atom axis| < (2 : ℚ) / 10 ^ 15 := by
  change ∀ atom axis, |SourceParsing.coordinateRead _ atom axis| < (2 : ℚ) / 10 ^ 15
  intro atom axis
  fin_cases atom <;> fin_cases axis <;>
    norm_num [SourceParsing.coordinateRead, SourceParsing.rationalRead]

theorem momentumResidual_bound : ∀ atom axis,
    |stepReadout.momentumResidual atom axis| < (2 : ℚ) / 10 ^ 20 := by
  change ∀ atom axis, |SourceParsing.coordinateRead _ atom axis| < (2 : ℚ) / 10 ^ 20
  intro atom axis
  fin_cases atom <;> fin_cases axis <;>
    norm_num [SourceParsing.coordinateRead, SourceParsing.rationalRead]

theorem actual_position_changed : stepReadout.target.position ≠ stepReadout.current.position := by
  intro same
  have entry := congrFun (congrFun same (0 : Atom)) (0 : Axis)
  have different : stepReadout.target.position 0 0 ≠ stepReadout.current.position 0 0 := by
    change SourceParsing.rationalRead _ ≠ SourceParsing.rationalRead _
    norm_num [SourceParsing.rationalRead]
  exact different entry

theorem actual_momentum_changed : stepReadout.target.momentum ≠ stepReadout.current.momentum := by
  intro same
  have entry := congrFun (congrFun same (0 : Atom)) (0 : Axis)
  have different : stepReadout.target.momentum 0 0 ≠ stepReadout.current.momentum 0 0 := by
    change SourceParsing.rationalRead _ ≠ SourceParsing.rationalRead _
    norm_num [SourceParsing.rationalRead]
  exact different entry

theorem native_reverse_reference :
    verletStep stepReadout.masses (-stepReadout.duration) stepReadout.target.force stepReadout.current.force referenceNext =
      stepReadout.current.phase :=
  verletStep_reverse _ _ _ _ _ masses_nonzero

theorem actual_reverse_residual :
    verletStep stepReadout.masses (-stepReadout.duration) stepReadout.target.force stepReadout.current.force stepReadout.target.phase =
      addResidual stepReadout.current.phase (reverseResidual stepReadout.masses stepReadout.duration explicitResidual) := by
  rw [targetPhase_reconstruction]
  exact verletStep_reverse_residual _ _ _ _ _ _ masses_nonzero

end
end LAlanine40K2025.Inertia.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
