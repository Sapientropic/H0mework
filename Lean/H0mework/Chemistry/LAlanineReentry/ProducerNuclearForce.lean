import H0mework.Chemistry.LAlanineReentry.SourceSourceBoundReentry

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open Inertia.SourceParsing Force.Interface
open LAlanine40K2025.Reentry.Source
noncomputable section

theorem nuclearCurrent_gradient_six : stepReadout.nuclear.currentGradientComponents.size = 6 :=
  JointNext.Producer.nuclearTarget_gradient_six

theorem nuclearTarget_gradient_six : stepReadout.nuclear.targetGradientComponents.size = 6 := by decide

theorem nuclearCurrentGradientWholeLedger : ∀ atom axis,
    Inertia.Producer.forceComponentSum stepReadout.nuclear.currentGradientComponents atom axis +
      stepReadout.nuclear.currentGradientRoundingResidual atom axis =
        stepReadout.nuclear.currentGradientPicohartree atom axis := JointNext.Producer.nuclearTargetGradientWholeLedger

theorem nuclearTargetGradientWholeLedger : ∀ atom axis,
    Inertia.Producer.forceComponentSum stepReadout.nuclear.targetGradientComponents atom axis +
      stepReadout.nuclear.targetGradientRoundingResidual atom axis =
        stepReadout.nuclear.targetGradientPicohartree atom axis := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem nuclearCurrentForce_resolution : ∀ atom axis,
    |stepReadout.nuclear.current.force atom axis + (stepReadout.nuclear.currentGradientPicohartree atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := JointNext.Producer.nuclearTargetForce_resolution

theorem nuclearTargetForce_resolution : ∀ atom axis,
    |stepReadout.nuclear.target.force atom axis + (stepReadout.nuclear.targetGradientPicohartree atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := by
  change ∀ atom axis, |-coordinateRead _ atom axis + (Force.Source.coordinateRead _ atom axis : ℚ) / 10 ^ 12| <
    (1 : ℚ) / (2 * 10 ^ 12)
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> norm_num [coordinateRead, rationalRead, Force.Source.coordinateRead]

theorem nuclearCurrentPosition_resolution : ∀ atom axis,
    |stepReadout.nuclear.current.position atom axis - (stepReadout.nuclear.currentPositionPicobohr atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := JointNext.Producer.nuclearTargetPosition_resolution

theorem nuclearTargetPosition_resolution : ∀ atom axis,
    |stepReadout.nuclear.target.position atom axis - (stepReadout.nuclear.targetPositionPicobohr atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := by
  change ∀ atom axis, |coordinateRead _ atom axis - (Force.Source.coordinateRead _ atom axis : ℚ) / 10 ^ 12| <
    (1 : ℚ) / (2 * 10 ^ 12)
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> norm_num [coordinateRead, rationalRead, Force.Source.coordinateRead]

theorem nuclearCurrentGradientResidual_bound : ∀ atom axis,
    |stepReadout.nuclear.currentGradientRoundingResidual atom axis| ≤ 3 := JointNext.Producer.nuclearTargetGradientResidual_bound

theorem nuclearTargetGradientResidual_bound : ∀ atom axis,
    |stepReadout.nuclear.targetGradientRoundingResidual atom axis| ≤ 2 := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem nuclearCurrentNuclei_eq_parent :
    stepReadout.nuclear.currentNuclei = JointNext.Source.stepReadout.nuclear.targetNuclei := rfl

theorem nuclearCurrentPositionPicobohr_eq_parent :
    stepReadout.nuclear.currentPositionPicobohr = JointNext.Source.stepReadout.nuclear.targetPositionPicobohr := rfl

theorem nuclearTargetForce_changed : stepReadout.nuclear.target.force ≠ stepReadout.nuclear.current.force := by
  intro same
  have entry := congrFun (congrFun same (0 : Atom)) (0 : Axis)
  change -rationalRead _ = -rationalRead _ at entry
  norm_num [rationalRead] at entry

theorem nuclearNuclei_preserved : stepReadout.nuclear.targetNuclei = stepReadout.nuclear.currentNuclei := by decide
theorem nuclearNuclei_count : stepReadout.nuclear.targetNuclei.size = 13 := by decide

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
