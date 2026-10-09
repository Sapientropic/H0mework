import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Extract.Runtime.Consumers
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
open Collision Resource Load.Producer.StrictThermal
open Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] Weak.execution

def measurementScale : ℝ := Measurement.measurementScale
  (Measurement.sourceOutputObservable Load.Source.loadTotalHamiltonian)

def measuredEnergy : ℝ := energy Load.Source.loadTotalHamiltonian Reservoir.Source.received.joint

theorem measured_scale_positive : 0 < measurementScale := Measurement.measurementScale_pos _

theorem source_pointer_contrast :
    2*measurementScale*((1/2 : ℝ)-oneRead sourceTarget)=measuredEnergy := by
  have decoded := sourceEffect_actual_read
  change 2*measurementScale*(energy sourceEffect Pointer.received.joint-1/2)=measuredEnergy at decoded
  rw [← sourceTarget_zero] at decoded
  have total := sourceTarget_binary.2.2
  have zero : zeroRead sourceTarget=1-oneRead sourceTarget := by linarith only [total]
  rw [zero] at decoded
  convert decoded using 1
  ring

theorem current_pointer_memory :
    oneRead (Extract.Runtime.readCurrent Extract.Runtime.afterFirst).joint=oneRead sourceTarget := by
  rw [Extract.Runtime.actual_retained_memory,Extract.Runtime.actual_sequence.1,
    Weak.execution_pointer_memory,Weak.origin,executed_pointer_memory,received,firstState,
    respondNext_one,receivedState_joint]

theorem current_positive_pointer_contrast_iff :
    (1/2 : ℝ) < oneRead (Extract.Runtime.readCurrent Extract.Runtime.afterFirst).joint ↔ measuredEnergy < 0 := by
  rw [current_pointer_memory]
  have exactRead := source_pointer_contrast
  have scale := measured_scale_positive
  constructor <;> intro h <;> nlinarith only [exactRead,scale,h]

theorem measured_energy_negative : measuredEnergy < 0 := by
  have pc : Load.Source.pcEnergy Reservoir.Source.received.joint < -(31/5 : ℝ) := by
    exact Charging.HeldEnergy.held_pc_energy_lt
  have environment : Load.Source.environmentEnergy Reservoir.Source.received.joint ≤ 2 :=
    (Powered.Dynamics.controllerEnergy_range 2 (by norm_num) _
      Reservoir.Source.received.positive Reservoir.Source.received.normalized).2
  have boundary : Load.Source.boundaryEnergy Reservoir.Source.received.joint ≤ 1 :=
    (abs_le.mp (Charging.HeldEnergy.boundary_energy_abs_le_one Reservoir.Source.received)).2
  rw [measuredEnergy,Load.Source.totalEnergy_split]
  linarith only [pc,environment,boundary]

theorem current_pointer_population :
    (1/2 : ℝ) < oneRead (Extract.Runtime.readCurrent Extract.Runtime.afterFirst).joint :=
  current_positive_pointer_contrast_iff.mpr measured_energy_negative

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
