import H0mework.Versions.AB.Chemistry.LAlanineJointNext.SourceSourceBoundJointStep

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Inertia.SourceParsing Force.Interface
open LAlanine40K2025.JointNext.Source
noncomputable section

theorem nuclearCurrent_gradient_six : stepReadout.nuclear.currentGradientComponents.size = 6 :=
  HeldForce.Producer.six_force_components

theorem nuclearTarget_gradient_six : stepReadout.nuclear.targetGradientComponents.size = 6 := by decide

theorem nuclearCurrentGradientWholeLedger : ∀ atom axis,
    Inertia.Producer.forceComponentSum stepReadout.nuclear.currentGradientComponents atom axis +
      stepReadout.nuclear.currentGradientRoundingResidual atom axis =
        stepReadout.nuclear.currentGradientPicohartree atom axis := HeldForce.Producer.forceWholeLedger

theorem nuclearTargetGradientWholeLedger : ∀ atom axis,
    Inertia.Producer.forceComponentSum stepReadout.nuclear.targetGradientComponents atom axis +
      stepReadout.nuclear.targetGradientRoundingResidual atom axis =
        stepReadout.nuclear.targetGradientPicohartree atom axis := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem nuclearCurrentForce_resolution : ∀ atom axis,
    |stepReadout.nuclear.current.force atom axis + (stepReadout.nuclear.currentGradientPicohartree atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := by
  intro atom axis
  change |-HeldForce.Source.rawGradient atom axis + (HeldForce.Source.gradientPicohartree atom axis : ℚ) / 10 ^ 12| < _
  simpa only [neg_add_eq_sub, abs_sub_comm] using HeldForce.Producer.rawGradient_resolution atom axis

theorem nuclearTargetForce_resolution : ∀ atom axis,
    |stepReadout.nuclear.target.force atom axis + (stepReadout.nuclear.targetGradientPicohartree atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := by
  change ∀ atom axis, |-coordinateRead _ atom axis + (Force.Source.coordinateRead _ atom axis : ℚ) / 10 ^ 12| <
    (1 : ℚ) / (2 * 10 ^ 12)
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> norm_num [coordinateRead, rationalRead, Force.Source.coordinateRead]

theorem nuclearCurrentPosition_resolution : ∀ atom axis,
    |stepReadout.nuclear.current.position atom axis - (stepReadout.nuclear.currentPositionPicobohr atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := Inertia.Producer.targetPosition_resolution

theorem nuclearTargetPosition_resolution : ∀ atom axis,
    |stepReadout.nuclear.target.position atom axis - (stepReadout.nuclear.targetPositionPicobohr atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := by
  change ∀ atom axis, |coordinateRead _ atom axis - (Force.Source.coordinateRead _ atom axis : ℚ) / 10 ^ 12| <
    (1 : ℚ) / (2 * 10 ^ 12)
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> norm_num [coordinateRead, rationalRead, Force.Source.coordinateRead]

theorem nuclearCurrentGradientResidual_bound : ∀ atom axis,
    |stepReadout.nuclear.currentGradientRoundingResidual atom axis| ≤ 3 := HeldForce.Producer.no_dropped_gradient_residual

theorem nuclearTargetGradientResidual_bound : ∀ atom axis,
    |stepReadout.nuclear.targetGradientRoundingResidual atom axis| ≤ 3 := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem nuclearCurrentNuclei_eq_parent :
    stepReadout.nuclear.currentNuclei = Inertia.Source.stepReadout.targetNuclei := by decide

theorem nuclearNuclei_preserved : stepReadout.nuclear.targetNuclei = stepReadout.nuclear.currentNuclei := by decide
theorem nuclearNuclei_count : stepReadout.nuclear.targetNuclei.size = 13 := by decide

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
