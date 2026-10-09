import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Source.SourceGeneratedPointerEffect
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.GeneratedPointerJoint
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Dynamics.FiniteSpectrumUnitaryPulse

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open Propagation.Producer Collision
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

abbrev PointerIndex := Current.FullIndex ⊕ Current.FullIndex
abbrev PointerJoint := Matrix PointerIndex PointerIndex ℂ

def sourceUnitary : Matrix.unitaryGroup PointerIndex ℂ :=
  dilation sourceEffect sourceEffect_lawful.1 sourceEffect_lawful.2

def sourceHamiltonian : PointerJoint :=
  Charging.Pulse.pulseHamiltonian sourceUnitary (nativeClockStep : ℝ)

theorem sourceHamiltonian_hermitian : sourceHamiltonian.IsHermitian :=
  Charging.Pulse.pulseHamiltonian_hermitian _ _

theorem sourceHamiltonian_generates :
    NormedSpace.exp ((nativeClockStep : ℝ) • (-Complex.I • sourceHamiltonian)) = (sourceUnitary : PointerJoint) :=
  Charging.Pulse.pulseHamiltonian_generates sourceUnitary (nativeClockStep : ℝ)
    Load.Producer.StrictThermal.nativeClock_small.1.ne'

def sourceInitial : PointerJoint := prepared received.joint

def sourceTarget : PointerJoint :=
  instrumentJoint sourceEffect sourceEffect_lawful.1 sourceEffect_lawful.2 received.joint

theorem sourceInitial_positive : sourceInitial.PosSemidef := prepared_positive _ received.positive
theorem sourceInitial_trace : sourceInitial.trace = 1 := (prepared_trace _).trans received.normalized

theorem sourceTarget_positive : sourceTarget.PosSemidef :=
  instrumentJoint_positive _ _ _ _ received.positive

theorem sourceTarget_trace : sourceTarget.trace = 1 :=
  (instrumentJoint_trace _ _ _ _).trans received.normalized

theorem sourceTarget_generated : sourceTarget = Quantum.conjugation sourceUnitary sourceInitial := rfl

theorem sourceTarget_zero : zeroRead sourceTarget = energy sourceEffect received.joint :=
  instrumentJoint_zero _ _ _ _

theorem sourceTarget_one : oneRead sourceTarget = energy (1 - sourceEffect) received.joint :=
  instrumentJoint_one _ _ _ _

theorem sourceTarget_memory :
    Measurement.sourceMeasurementDecode Load.Source.loadTotalHamiltonian (zeroRead sourceTarget) =
      energy Load.Source.loadTotalHamiltonian Source.received.joint := by
  rw [sourceTarget_zero]
  exact sourceEffect_actual_read

theorem sourceTarget_backreaction :
    bodyRead sourceTarget = effectRoot sourceEffect * received.joint * effectRoot sourceEffect +
      complementRoot sourceEffect * received.joint * complementRoot sourceEffect :=
  instrumentJoint_backreaction _ _ _ _

theorem sourceTarget_entropy :
    Quantum.spectralEntropy sourceTarget sourceTarget_positive sourceTarget_trace =
      Quantum.spectralEntropy received.joint received.positive received.normalized :=
  instrumentJoint_entropy _ _ _ _ received.positive received.normalized

theorem sourceTarget_binary :
    0 ≤ zeroRead sourceTarget ∧ 0 ≤ oneRead sourceTarget ∧ zeroRead sourceTarget + oneRead sourceTarget = 1 :=
  instrumentJoint_binary sourceEffect sourceEffect_lawful.1 sourceEffect_lawful.2
    received.joint received.positive received.normalized

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
