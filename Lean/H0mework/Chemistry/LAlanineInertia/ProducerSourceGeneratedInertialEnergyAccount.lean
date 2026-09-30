import H0mework.Chemistry.LAlanineInertia.SourceSourceBoundLAlanine40KInertialStep

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Producer

open LAlanine40K2025.Inertia.Source

noncomputable section

theorem current_kinetic_exact : stepReadout.current.kinetic = 0 := by
  change (0 : ℚ) / 1 = 0
  norm_num

theorem current_potential_exact :
    stepReadout.current.potential = (-2845161862138847 : ℚ) / 8796093022208 := rfl
theorem current_total_exact :
    stepReadout.current.total = (-2845161862138847 : ℚ) / 8796093022208 := rfl
theorem target_kinetic_exact :
    stepReadout.target.kinetic = (309875285891609 : ℚ) / 38685626227668133590597632 := rfl
theorem target_potential_exact :
    stepReadout.target.potential = (-5690323724277861 : ℚ) / 17592186044416 := rfl
theorem target_total_exact :
    stepReadout.target.total = (-711290465534715 : ℚ) / 2199023255552 := rfl

theorem actual_kinetic_positive : 0 < stepReadout.target.kinetic := by
  rw [target_kinetic_exact]
  norm_num

theorem potential_change_exact :
    stepReadout.target.potential - stepReadout.current.potential = (-167 : ℚ) / 17592186044416 := by
  rw [target_potential_exact, current_potential_exact]
  norm_num

theorem actual_potential_changed : stepReadout.target.potential ≠ stepReadout.current.potential := by
  intro same
  have change := potential_change_exact
  rw [same, sub_self] at change
  norm_num at change

theorem total_change_exact :
    stepReadout.target.total - stepReadout.current.total = (-13 : ℚ) / 8796093022208 := by
  rw [target_total_exact, current_total_exact]
  norm_num

/-- Native floating addition is retained separately from the exact rational sum. -/
def fineEnergyArithmeticResidual : ℚ :=
  stepReadout.target.total - (stepReadout.target.kinetic + stepReadout.target.potential)

theorem fineEnergyArithmeticResidual_exact :
    fineEnergyArithmeticResidual = (186993141223 : ℚ) / 38685626227668133590597632 := by
  unfold fineEnergyArithmeticResidual
  rw [target_total_exact, target_kinetic_exact, target_potential_exact]
  norm_num

def schemeAndSCFResidual : ℚ :=
  (stepReadout.target.kinetic + stepReadout.target.potential) -
    (stepReadout.current.kinetic + stepReadout.current.potential)

theorem schemeAndSCFResidual_exact :
    schemeAndSCFResidual = (-57361597785575 : ℚ) / 38685626227668133590597632 := by
  unfold schemeAndSCFResidual
  rw [target_kinetic_exact, target_potential_exact, current_kinetic_exact, current_potential_exact]
  norm_num

theorem rawEnergyWholeAccount :
    stepReadout.target.total - stepReadout.current.total =
      schemeAndSCFResidual + fineEnergyArithmeticResidual := by
  rw [total_change_exact, schemeAndSCFResidual_exact, fineEnergyArithmeticResidual_exact]
  norm_num

end
end LAlanine40K2025.Inertia.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
