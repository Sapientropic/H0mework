import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Producer.SourceGeneratedPointerCapacity
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Source.SourceGeneratedPointerLoadPulse
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerEnvironmentIncidence
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedFiniteReservoir

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Live

open Propagation.Producer
open scoped Matrix ComplexOrder
noncomputable section

structure State where
  localClock : ℚ
  action : Matrix.unitaryGroup PointerIndex ℂ

def State.joint (current : State) : PointerJoint := Quantum.conjugation current.action sourceInitial

theorem State.positive (current : State) : current.joint.PosSemidef :=
  Quantum.conjugation_posSemidef _ _ sourceInitial_positive

theorem State.normalized (current : State) : current.joint.trace = 1 :=
  (Quantum.conjugation_trace _ _).trans sourceInitial_trace

def initial : State := ⟨received.localClock, 1⟩
def measureNext (current : State) : State :=
  ⟨current.localClock + nativeClockStep, sourceUnitary * current.action⟩
def loadNext (current : State) : State :=
  ⟨current.localClock + nativeClockStep, Pointer.loadPulse (nativeClockStep : ℝ) * current.action⟩
def first : State := measureNext initial

theorem initial_joint : initial.joint = sourceInitial := by
  simp [State.joint, initial, Quantum.conjugation_apply]

theorem measureNext_joint (current : State) :
    (measureNext current).joint = Quantum.conjugation sourceUnitary current.joint :=
  (Environment.conjugation_comp sourceUnitary current.action sourceInitial).symm

theorem loadNext_joint (current : State) :
    (loadNext current).joint = Quantum.conjugation (Pointer.loadPulse (nativeClockStep : ℝ)) current.joint :=
  (Environment.conjugation_comp (Pointer.loadPulse (nativeClockStep : ℝ)) current.action sourceInitial).symm

theorem first_joint : first.joint = sourceTarget := by
  rw [first, measureNext_joint, initial_joint, sourceTarget_generated]

theorem initial_clock : initial.localClock = 5 * nativeClockStep := Producer.first_clock

theorem first_clock : first.localClock = 6 * nativeClockStep := by
  change initial.localClock + nativeClockStep = _
  rw [initial_clock]
  ring

theorem loadNext_clock (current : State) :
    (loadNext current).localClock = current.localClock + nativeClockStep := rfl

theorem loadNext_body (current : State) :
    bodyRead (loadNext current).joint =
      Quantum.conjugation (Current.loadPulse (nativeClockStep : ℝ)) (bodyRead current.joint) := by
  rw [loadNext_joint]
  simpa only [Quantum.conjugation_apply] using Pointer.loadPulse_bodyRead (nativeClockStep : ℝ) current.joint

theorem loadNext_pointer_zero (current : State) : zeroRead (loadNext current).joint = zeroRead current.joint := by
  rw [loadNext_joint]
  exact Pointer.loadPulse_zeroRead (nativeClockStep : ℝ) current.joint

theorem loadNext_pointer_one (current : State) : oneRead (loadNext current).joint = oneRead current.joint := by
  rw [loadNext_joint]
  exact Pointer.loadPulse_oneRead (nativeClockStep : ℝ) current.joint

theorem next_not_reset : (loadNext first).joint ≠ sourceInitial := by
  intro same
  have kept := loadNext_pointer_one first
  rw [same, first_joint, sourceInitial, prepared_one_read] at kept
  have positive := sourceTarget_one_positive
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Live
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
