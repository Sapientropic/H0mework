import H0mework.Chemistry.LAlanineJointNext.SourceSourceBoundJointStep

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Inertia.SourceParsing
open LAlanine40K2025.JointNext.Source
noncomputable section

theorem nuclearCurrentTotal_is_sum :
    stepReadout.nuclear.current.total = stepReadout.nuclear.current.kinetic + stepReadout.nuclear.current.potential := rfl

theorem nuclearTargetTotal_is_sum :
    stepReadout.nuclear.target.total = stepReadout.nuclear.target.kinetic + stepReadout.nuclear.target.potential := by
  change rationalRead _ = rationalRead _ + rationalRead _
  norm_num [rationalRead]

theorem nuclearRecordedEnergyChange :
    stepReadout.nuclear.target.total - stepReadout.nuclear.current.total = recordedEnergyChange := by
  change rationalRead _ - (rationalRead _ + rationalRead _) = rationalRead _
  norm_num [rationalRead]

theorem nuclearWholeEnergyAccount :
    stepReadout.nuclear.target.total - stepReadout.nuclear.current.total =
      (stepReadout.nuclear.target.kinetic - stepReadout.nuclear.current.kinetic) +
      (stepReadout.nuclear.target.potential - stepReadout.nuclear.current.potential) := by
  rw [nuclearCurrentTotal_is_sum, nuclearTargetTotal_is_sum]
  ring

theorem nuclearRecordedEnergyChange_exact :
    recordedEnergyChange = (-389272014846841 : ℚ) / 154742504910672534362390528 := rfl

theorem nuclearEngineEnergyChange_exact : engineEnergyChange = (-11 : ℚ) / 4398046511104 := rfl

theorem nuclearEngineAccountingResidual_exact :
    engineAccountingResidual = (2243921869689 : ℚ) / 154742504910672534362390528 := rfl

theorem nuclearEngineEnergyAccount : engineEnergyChange = recordedEnergyChange + engineAccountingResidual := by
  rw [nuclearEngineEnergyChange_exact, nuclearRecordedEnergyChange_exact, nuclearEngineAccountingResidual_exact]
  norm_num

theorem nuclearEngineVsPhysicalAccount :
    engineEnergyChange = stepReadout.nuclear.target.total - stepReadout.nuclear.current.total +
      engineAccountingResidual := by
  rw [nuclearRecordedEnergyChange]
  exact nuclearEngineEnergyAccount

theorem nuclearEngineResidual_positive_small :
    0 < engineAccountingResidual ∧ engineAccountingResidual < (2 : ℚ) / 10 ^ 14 := by
  rw [nuclearEngineAccountingResidual_exact]
  norm_num

theorem nuclearRecordedResidual_negative_small :
    -(3 : ℚ) / 10 ^ 12 < recordedEnergyChange ∧ recordedEnergyChange < 0 := by
  rw [nuclearRecordedEnergyChange_exact]
  norm_num

theorem nuclearKinetic_increases : stepReadout.nuclear.current.kinetic < stepReadout.nuclear.target.kinetic := by
  change rationalRead _ < rationalRead _
  norm_num [rationalRead]

theorem nuclearPotential_decreases : stepReadout.nuclear.target.potential < stepReadout.nuclear.current.potential := by
  change rationalRead _ < rationalRead _
  norm_num [rationalRead]

theorem nuclearTotal_decreases : stepReadout.nuclear.target.total < stepReadout.nuclear.current.total := by
  have negative := nuclearRecordedResidual_negative_small.2
  rw [← nuclearRecordedEnergyChange] at negative
  exact sub_neg.mp negative

theorem nuclearEngine_not_recorded_change : engineEnergyChange ≠ recordedEnergyChange := by
  rw [nuclearEngineEnergyAccount]
  exact ne_of_gt (lt_add_of_pos_right _ nuclearEngineResidual_positive_small.1)

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
