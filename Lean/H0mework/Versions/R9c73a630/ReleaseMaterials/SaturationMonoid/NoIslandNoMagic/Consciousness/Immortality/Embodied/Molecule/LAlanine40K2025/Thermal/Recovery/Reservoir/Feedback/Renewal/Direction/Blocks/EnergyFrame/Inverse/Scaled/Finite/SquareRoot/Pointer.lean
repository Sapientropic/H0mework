import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Frame
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.FiniteGain

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open Collision Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def finiteBodyEffect : Current.FullJoint := Incidence.bodyObservable originalFrameEffect

theorem finite_body_lawful : finiteBodyEffect.PosSemidef ∧ (1-finiteBodyEffect).PosSemidef :=
  bodyObservable_lawful originalFrameEffect original_frame_lawful.1 original_frame_lawful.2

def finitePointer : Matrix.unitaryGroup PointerIndex ℂ := dilation finiteBodyEffect finite_body_lawful.1 finite_body_lawful.2

theorem original_finite_pointer_error : ‖(sourceUnitary : PointerJoint)-(finitePointer : PointerJoint)‖ ≤ (28/10^6 : ℝ) := by
  have ha := sourceOutputObservable_hermitian loadTotalHamiltonian loadTotalHamiltonian_hermitian
  change ‖dilationMatrix sourceEffect-dilationMatrix finiteBodyEffect‖ ≤ _
  apply (pointer_dilation_error _ _).trans
  have first : ‖effectRoot sourceEffect-effectRoot finiteBodyEffect‖ ≤ (14/10^6 : ℝ) :=
    (body_root_error _ _ (boundedEffect_positive _ ha) original_frame_lawful.1).trans original_frame_root_error
  have second : ‖complementRoot sourceEffect-complementRoot finiteBodyEffect‖ ≤ (14/10^6 : ℝ) := by
    change ‖CFC.sqrt (1-Incidence.bodyObservable (boundedEffect _))-CFC.sqrt (1-Incidence.bodyObservable originalFrameEffect)‖ ≤ _
    rw [bodyObservable_complement,bodyObservable_complement]
    exact (body_root_error _ _ (boundedEffect_complement_positive _ ha) original_frame_lawful.2).trans original_frame_complement_error
  linarith

theorem original_finite_pointer_observable (O : PointerJoint) :
    |energy O sourceTarget-energy O (Quantum.conjugation finitePointer sourceInitial)| ≤ (56/10^6 : ℝ)*‖O‖ := by
  rw [sourceTarget_generated]
  have paid := Exchange.unitary_observable_error O sourceInitial sourceInitial_positive sourceInitial_trace sourceUnitary finitePointer
  change |energy O (Quantum.conjugation sourceUnitary sourceInitial)-energy O (Quantum.conjugation finitePointer sourceInitial)| ≤ _ at paid
  exact paid.trans (by nlinarith [mul_le_mul_of_nonneg_left original_finite_pointer_error (norm_nonneg O)])

def finiteNine : PointerJoint := Quantum.conjugation afterInstrumentNine (Quantum.conjugation finitePointer sourceInitial)
def finiteEleven : PointerJoint := Quantum.conjugation afterInstrumentEleven (Quantum.conjugation finitePointer sourceInitial)

theorem original_finite_PC_gain_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      (Resource.pcEnergyOf (bodyRead finiteEleven)-Resource.pcEnergyOf (bodyRead finiteNine))| ≤ (7/10^6 : ℝ) := by
  have paid := original_finite_pointer_observable (gainObservable Sectors.pointerPCObservable)
  have same : (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      (Resource.pcEnergyOf (bodyRead finiteEleven)-Resource.pcEnergyOf (bodyRead finiteNine))=
      energy (gainObservable Sectors.pointerPCObservable) sourceTarget-
      energy (gainObservable Sectors.pointerPCObservable) (Quantum.conjugation finitePointer sourceInitial) := by
    simp only [← Sectors.pointerPCObservable_energy,original_gain_read,finiteEleven,finiteNine,gain_read]
  rw [same]
  exact paid.trans (by nlinarith [original_net_PC_norm])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
