import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Pointer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Sectors.Energy

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

attribute [local irreducible] Weak.execution Weak.origin afterInstrumentNine afterInstrumentEleven
  sourceTarget sourceInitial numericPointer

def gainObservable (O : PointerJoint) : PointerJoint :=
  Quantum.conjugation (star afterInstrumentEleven) O-Quantum.conjugation (star afterInstrumentNine) O

private theorem energy_pulled {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    energy O (Quantum.conjugation U rho)=energy (Quantum.conjugation (star U) O) rho := by
  exact Load.Producer.StrictThermal.energy_pullback O rho U

theorem gain_read (O rho : PointerJoint) :
    energy O (Quantum.conjugation afterInstrumentEleven rho)-energy O (Quantum.conjugation afterInstrumentNine rho)=
      energy (gainObservable O) rho := by
  rw [energy_pulled,energy_pulled,gainObservable,Load.Producer.HeatProbability.energy_sub_left]

theorem original_gain_read (O : PointerJoint) :
    energy O Weak.execution.joint-energy O Weak.origin.joint=energy (gainObservable O) sourceTarget := by
  rw [original_eleven_from_instrument,original_nine_from_instrument,gain_read]

theorem original_gain_instrument_error (O : PointerJoint) :
    |(energy O Weak.execution.joint-energy O Weak.origin.joint)-
      (energy O (approximatedEleven originalFrameNumericOutput original_frame_numeric_hermitian)-
       energy O (approximatedNine originalFrameNumericOutput original_frame_numeric_hermitian))| ≤
      (56/10^6 : ℝ)*‖gainObservable O‖ := by
  rw [original_gain_read]
  unfold approximatedEleven approximatedNine
  rw [gain_read]
  have paid := original_numeric_pointer_observable (gainObservable O)
  unfold numericPointer at paid
  exact paid

theorem original_PC_gain_instrument_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      (Resource.pcEnergyOf (bodyRead (approximatedEleven originalFrameNumericOutput original_frame_numeric_hermitian))-
       Resource.pcEnergyOf (bodyRead (approximatedNine originalFrameNumericOutput original_frame_numeric_hermitian)))| ≤
      (56/10^6 : ℝ)*‖gainObservable Sectors.pointerPCObservable‖ := by
  simpa only [Sectors.pointerPCObservable_energy] using original_gain_instrument_error Sectors.pointerPCObservable

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
