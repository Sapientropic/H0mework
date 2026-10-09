import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Hamiltonian
set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak

open Collision Resource Propagation.Producer Load.Source Load.Producer.StrictThermal Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def controlEnergy (current : Live.State) : ℝ := energy controlPointerHamiltonian current.joint
def switchInWork (current : Live.State) : ℝ := controlEnergy current-Live.baselineEnergy current
def switchOutWork (current : Live.State) : ℝ := Live.baselineEnergy current-controlEnergy current
def pulseWork (current : Live.State) : ℝ := switchInWork current+switchOutWork (next current)

theorem next_control_energy (current : Live.State) : controlEnergy (next current)=controlEnergy current := by
  rw [controlEnergy,next_joint]
  exact control_energy_conserved (nativeClockStep : ℝ) current.joint

theorem pulse_work_actual (current : Live.State) :
    pulseWork current=Live.baselineEnergy (next current)-Live.baselineEnergy current := by
  unfold pulseWork switchInWork switchOutWork
  rw [next_control_energy]
  ring

theorem next_net_account (current : Live.State) :
    (Live.freeEnergy (next current)-Live.freeEnergy current)+
      (Live.entropyProduction (next current)-Live.entropyProduction current)=pulseWork current := by
  rw [pulse_work_actual]
  linarith [Live.complete_account current,Live.complete_account (next current)]

theorem execution_net_account :
    (Live.freeEnergy execution-Live.freeEnergy origin)+
      (Live.entropyProduction execution-Live.entropyProduction origin)=pulseWork origin := by
  have supply := next_net_account origin
  have load := Live.loadNext_net_account target
  change (Live.freeEnergy target-Live.freeEnergy origin)+
    (Live.entropyProduction target-Live.entropyProduction origin)=pulseWork origin at supply
  change (Live.freeEnergy execution-Live.freeEnergy target)+
    (Live.entropyProduction execution-Live.entropyProduction target)=0 at load
  linarith only [supply,load]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
