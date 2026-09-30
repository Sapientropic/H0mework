import H0mework.Chemistry.LAlanineThermalDynamics.GeneratedPoweredHamiltonian
import H0mework.Chemistry.LAlanineThermalDynamics.FiniteControllerEnergy

/-! # Source-fixed finite controller flow; no supplied target or energy balance -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Producer

open Propagation.Interface Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source (energyHamiltonian)
open scoped Matrix ComplexOrder

noncomputable section

theorem sourceBare_eq :
    Dynamics.bareHamiltonian Work.Drive.fieldBaseline 2 = Source.bare energyHamiltonian := by
  rw [← Source.pairHamiltonian_eq_source]
  unfold Dynamics.bareHamiltonian Source.bare Dynamics.controllerHamiltonian Source.controllerHamiltonian
  norm_num

theorem sourceResonance : Commute (Dynamics.bareHamiltonian Work.Drive.fieldBaseline 2) Source.sourceInteraction := by
  rw [sourceBare_eq]
  exact Source.source_energy_resonance

def sourceAdvance (elapsed : ℝ) (current : Dynamics.ControllerJoint (Basis × Basis)) :
    Dynamics.ControllerJoint (Basis × Basis) :=
  Dynamics.coupledNext Work.Drive.fieldBaseline 2 Source.sourceInteraction
    Work.Drive.fieldBaseline_hermitian Source.sourceInteraction_hermitian elapsed current

theorem sourceAdvance_positive (elapsed : ℝ) (current : Dynamics.ControllerJoint (Basis × Basis))
    (positive : current.PosSemidef) : (sourceAdvance elapsed current).PosSemidef :=
  Dynamics.coupledNext_positive _ _ _ _ _ elapsed current positive

theorem sourceAdvance_trace (elapsed : ℝ) (current : Dynamics.ControllerJoint (Basis × Basis)) :
    (sourceAdvance elapsed current).trace = current.trace :=
  Dynamics.coupledNext_trace _ _ _ _ _ elapsed current

theorem sourceAdvance_zero (current : Dynamics.ControllerJoint (Basis × Basis)) :
    sourceAdvance 0 current = current :=
  Dynamics.coupledNext_zero _ _ _ _ _ current

theorem sourceAdvance_add (elapsed next : ℝ) (current : Dynamics.ControllerJoint (Basis × Basis)) :
    sourceAdvance (elapsed + next) current = sourceAdvance elapsed (sourceAdvance next current) :=
  Dynamics.coupledNext_add _ _ _ _ _ elapsed next current

theorem sourceAdvance_energyBalance (elapsed : ℝ) (current : Dynamics.ControllerJoint (Basis × Basis)) :
    (Dynamics.systemEnergy Work.Drive.fieldBaseline (sourceAdvance elapsed current) -
      Dynamics.systemEnergy Work.Drive.fieldBaseline current) +
    (Dynamics.controllerEnergy 2 (sourceAdvance elapsed current) - Dynamics.controllerEnergy 2 current) = 0 :=
  Dynamics.controller_pays_system_change _ _ _ _ _ sourceResonance elapsed current

theorem sourceAdvance_energyBound (elapsed : ℝ) (current : Dynamics.ControllerJoint (Basis × Basis))
    (positive : current.PosSemidef) (normalized : current.trace = 1) :
    Dynamics.controllerEnergy 2 current - 2 ≤
      Dynamics.systemEnergy Work.Drive.fieldBaseline (sourceAdvance elapsed current) -
        Dynamics.systemEnergy Work.Drive.fieldBaseline current ∧
    Dynamics.systemEnergy Work.Drive.fieldBaseline (sourceAdvance elapsed current) -
      Dynamics.systemEnergy Work.Drive.fieldBaseline current ≤ Dynamics.controllerEnergy 2 current :=
  Dynamics.current_controller_energy_bound _ _ _ _ _ sourceResonance elapsed current positive normalized (by norm_num)

end

end LAlanine40K2025.Thermal.Powered.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
