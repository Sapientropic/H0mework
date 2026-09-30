import H0mework.Chemistry.LAlanineReentry.ProducerNuclear

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.NuclearRegression

open Inertia.Mechanics Inertia.SourceParsing Force.Interface
open LAlanine40K2025.Reentry.Source LAlanine40K2025.Reentry.Producer

example : nuclearClosure := sourceGeneratedNuclearReentry

theorem current_not_previous_ingress :
    stepReadout.nuclear.current ≠ JointNext.Source.stepReadout.nuclear.current := by
  intro same
  exact JointNext.Producer.nuclearMomentum_changed (congrArg Inertia.Interface.NuclearFrame.momentum same)

theorem target_force_not_parent_copy : stepReadout.nuclear.target.force ≠ Runtime.reentryParentFrame.force :=
  nuclearTargetForce_changed

theorem discrete_position_residual_not_erased : stepReadout.nuclear.positionResidual (0 : Atom) (0 : Axis) ≠ 0 := by
  change rationalRead _ ≠ 0
  norm_num [rationalRead]

theorem whole_energy_row_residual_not_erased : stepReadout.nuclear.targetLedger.rowResidualSum ≠ 0 := by
  rw [nuclearTargetEnergyResiduals.1]
  decide

example : engineEnergyChange ≠ stepReadout.nuclear.target.total - stepReadout.nuclear.current.total := by
  rw [nuclearRecordedEnergyChange]
  exact nuclearEngine_not_recorded_change

#print axioms sourceGeneratedNuclearReentry
#print axioms current_not_previous_ingress
#print axioms target_force_not_parent_copy
#print axioms discrete_position_residual_not_erased
#print axioms whole_energy_row_residual_not_erased

end LAlanine40K2025.Reentry.NuclearRegression
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
