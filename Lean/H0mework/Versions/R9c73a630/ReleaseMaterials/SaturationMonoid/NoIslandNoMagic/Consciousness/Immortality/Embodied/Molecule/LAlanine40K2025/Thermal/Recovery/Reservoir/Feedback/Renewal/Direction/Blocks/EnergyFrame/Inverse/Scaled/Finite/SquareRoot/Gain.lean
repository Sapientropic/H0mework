import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Approximation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def approximatedTarget (R S : LoadedJoint) : PointerJoint := rawConjugation (approximatedPointer R S) sourceInitial
def approximatedNine (R S : LoadedJoint) : PointerJoint := Quantum.conjugation afterInstrumentNine (approximatedTarget R S)
def approximatedEleven (R S : LoadedJoint) : PointerJoint := Quantum.conjugation afterInstrumentEleven (approximatedTarget R S)

theorem approximated_pointer_norm (R S : LoadedJoint)
    (first : ‖CFC.sqrt finiteEffect-R‖ ≤ (2/10^7 : ℝ))
    (second : ‖CFC.sqrt (1-finiteEffect)-S‖ ≤ (2/10^7 : ℝ)) :
    ‖approximatedPointer R S‖ ≤ 1+(4/10^7 : ℝ) := by
  have distance := finite_approximated_pointer_error R S first second
  calc
    _ = ‖(approximatedPointer R S-(finitePointer : PointerJoint))+(finitePointer : PointerJoint)‖ := by rw [sub_add_cancel]
    _ ≤ ‖approximatedPointer R S-(finitePointer : PointerJoint)‖+‖(finitePointer : PointerJoint)‖ := norm_add_le _ _
    _ ≤ _ := by rw [norm_sub_rev,CStarRing.norm_coe_unitary]; linarith

theorem finite_approximated_PC_gain_error (R S : LoadedJoint)
    (first : ‖CFC.sqrt finiteEffect-R‖ ≤ (2/10^7 : ℝ))
    (second : ‖CFC.sqrt (1-finiteEffect)-S‖ ≤ (2/10^7 : ℝ)) :
    |(Resource.pcEnergyOf (bodyRead finiteEleven)-Resource.pcEnergyOf (bodyRead finiteNine))-
      (Resource.pcEnergyOf (bodyRead (approximatedEleven R S))-Resource.pcEnergyOf (bodyRead (approximatedNine R S)))| ≤ (1/10^7 : ℝ) := by
  have paid := raw_observable_error (gainObservable Sectors.pointerPCObservable) sourceInitial sourceInitial_positive sourceInitial_trace finitePointer (approximatedPointer R S)
  have read : (Resource.pcEnergyOf (bodyRead finiteEleven)-Resource.pcEnergyOf (bodyRead finiteNine))-
      (Resource.pcEnergyOf (bodyRead (approximatedEleven R S))-Resource.pcEnergyOf (bodyRead (approximatedNine R S)))=
      energy (gainObservable Sectors.pointerPCObservable) (Quantum.conjugation finitePointer sourceInitial)-
      energy (gainObservable Sectors.pointerPCObservable) (approximatedTarget R S) := by
    simp only [← Sectors.pointerPCObservable_energy,finiteEleven,finiteNine,approximatedEleven,approximatedNine,gain_read]
  rw [read]
  apply paid.trans
  calc
    _ ≤ (1+(1+(4/10^7 : ℝ)))*(123/1000 : ℝ)*(4/10^7 : ℝ) := by
      gcongr
      · exact approximated_pointer_norm R S first second
      · exact original_net_PC_norm
      · exact finite_approximated_pointer_error R S first second
    _ ≤ _ := by norm_num

theorem original_approximated_PC_gain_error (R S : LoadedJoint)
    (first : ‖CFC.sqrt finiteEffect-R‖ ≤ (2/10^7 : ℝ))
    (second : ‖CFC.sqrt (1-finiteEffect)-S‖ ≤ (2/10^7 : ℝ)) :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      (Resource.pcEnergyOf (bodyRead (approximatedEleven R S))-Resource.pcEnergyOf (bodyRead (approximatedNine R S)))| ≤ (71/10^7 : ℝ) := by
  calc
    _ ≤ |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
        (Resource.pcEnergyOf (bodyRead finiteEleven)-Resource.pcEnergyOf (bodyRead finiteNine))|+
      |(Resource.pcEnergyOf (bodyRead finiteEleven)-Resource.pcEnergyOf (bodyRead finiteNine))-
        (Resource.pcEnergyOf (bodyRead (approximatedEleven R S))-Resource.pcEnergyOf (bodyRead (approximatedNine R S)))| := abs_sub_le _ _ _
    _ ≤ (7/10^6 : ℝ)+(1/10^7 : ℝ) := add_le_add original_finite_PC_gain_error (finite_approximated_PC_gain_error R S first second)
    _ = _ := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
