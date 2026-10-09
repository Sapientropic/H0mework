import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions.Received

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
open Collision Propagation.Interface Load.Source Powered.Dynamics Powered.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem reframe_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W U : Matrix.unitaryGroup ι ℂ) (rho : Matrix ι ι ℂ) :
    Quantum.conjugation W (Quantum.conjugation U rho)=
      Quantum.conjugation (reframeUnitary W U) (Quantum.conjugation W rho) := by
  rw [Environment.conjugation_comp,Environment.conjugation_comp]
  simp only [reframeUnitary,mul_assoc,Unitary.star_mul_self,mul_one]

theorem preparation_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix.unitaryGroup ι ℂ) (rho : JointMatrix ι) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    Quantum.conjugation (spectatorFrame (controllerFrame W)) (Matrix.kronecker (chargedInput rho) B)=
      Matrix.kronecker (chargedInput (Quantum.localConjugation W W rho)) B := by
  rw [spectator_conjugation]
  exact congrArg (fun A => Matrix.kronecker A B) (controller_tensor_covariant W rho excitedController)

def preparedInput : LoadedJoint := Matrix.kronecker (chargedInput Input.finitePair) environmentState

theorem received_read_in_calculated_frame (O : LoadedJoint) (rho : JointMatrix Basis) :
    energy (Prepared.receivedObservable O) rho=
      energy (Quantum.conjugation installedLoadFrame O)
        (Quantum.conjugation calculatedReceivedWord (Matrix.kronecker (chargedInput rho) environmentState)) := by
  let frame := Quantum.localUnitary originalToCalculated originalToCalculated
  let back := (Unitary.conjStarAlgAut ℂ (JointMatrix Basis) frame).symm rho
  have forward : Quantum.localConjugation originalToCalculated originalToCalculated back=rho :=
    StarAlgEquiv.apply_symm_apply (Unitary.conjStarAlgAut ℂ (JointMatrix Basis) frame) rho
  have pairEnergy := Prepared.local_energy originalToCalculated originalToCalculated
    (Prepared.preparationObservable (Quantum.conjugation (star Input.receivedWord) O)) back
  rw [forward] at pairEnergy
  calc
    _ = energy (Prepared.preparationObservable (Quantum.conjugation (star Input.receivedWord) O)) back := pairEnergy
    _ = energy O (Quantum.conjugation Input.receivedWord (Matrix.kronecker (chargedInput back) environmentState)) := by
      have pull : energy O (Quantum.conjugation Input.receivedWord (Matrix.kronecker (chargedInput back) environmentState))=
          energy (Quantum.conjugation (star Input.receivedWord) O) (Matrix.kronecker (chargedInput back) environmentState) :=
        energy_pullback O _ _
      rw [pull,Prepared.preparation_energy]
    _ = energy (Quantum.conjugation installedLoadFrame O)
        (Quantum.conjugation installedLoadFrame (Quantum.conjugation Input.receivedWord (Matrix.kronecker (chargedInput back) environmentState))) :=
      (Work.Capacity.energy_unitary_conjugation O _ installedLoadFrame).symm
    _ = _ := by
      rw [reframe_action]
      change energy (Quantum.conjugation installedLoadFrame O)
        (Quantum.conjugation calculatedReceivedWord
          (Quantum.conjugation (spectatorFrame (controllerFrame originalToCalculated))
            (Matrix.kronecker (chargedInput back) environmentState)))=_
      rw [preparation_covariance,forward]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
