import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.PointerResponse

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exchange_source_flow (time : ℝ) :
    (Exchange.exchangeUnitary (ι := ι) time : JointMatrix ι)=hamiltonianFlow swapOperator time := by
  unfold hamiltonianFlow
  have scalar : time • (-Complex.I • (swapOperator : JointMatrix ι))=
      (-Complex.I*(time : ℂ)) • (swapOperator : JointMatrix ι) := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
    ring
  rw [scalar]
  exact (Thermal.Dynamics.swap_exponential time).symm

theorem exchange_unitary_distance [Nonempty ι] (time : ℝ) :
    ‖(Exchange.exchangeUnitary (ι := ι) time : JointMatrix ι)-1‖ ≤ |time| := by
  have h := hamiltonian_flow_error (swapOperator : JointMatrix ι) 0 swap_adjoint Matrix.isHermitian_zero time
  rw [← exchange_source_flow] at h
  simpa only [hamiltonianFlow,smul_zero,NormedSpace.exp_zero,sub_zero,swap_norm,mul_one] using h

theorem exchange_observable_response [Nonempty ι] (time : ℝ) (O : JointMatrix ι) :
    ‖Quantum.conjugation (star (Exchange.exchangeUnitary time)) O-O‖ ≤ 2*|time| * ‖O‖ := by
  have paid := conjugation_action_error (star (Exchange.exchangeUnitary time)) 1 O
  have distance : ‖(star (Exchange.exchangeUnitary (ι := ι) time) : JointMatrix ι)-(1 : JointMatrix ι)‖ ≤ |time| := by
    have same : star (Exchange.exchangeUnitary (ι := ι) time : JointMatrix ι)-1=
        star ((Exchange.exchangeUnitary (ι := ι) time : JointMatrix ι)-1) := by rw [star_sub,star_one]
    rw [same,norm_star]
    exact exchange_unitary_distance (ι := ι) time
  have fixed : Quantum.conjugation (1 : Matrix.unitaryGroup (ι × ι) ℂ) O=O := by
    simp only [Quantum.conjugation_apply,OneMemClass.coe_one,star_one,Matrix.one_mul,Matrix.mul_one]
  rw [fixed] at paid
  simp only [Unitary.coe_star,OneMemClass.coe_one] at paid
  exact paid.trans (by nlinarith [mul_le_mul_of_nonneg_right distance (norm_nonneg O)])

theorem original_free_PC_observable (time : ℝ) :
    Quantum.conjugation (star (Native.freePCUnitary time)) Powered.Producer.poweredTotalHamiltonian=
      Powered.Producer.poweredTotalHamiltonian := by
  have commute := Powered.Dynamics.observable_commutes_with_flow Work.Drive.fieldBaseline 2
    Powered.Source.sourceInteraction Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian time
    Powered.Producer.poweredTotalHamiltonian (Commute.refl _)
  change Commute Powered.Producer.poweredTotalHamiltonian (Native.freePCUnitary time : Matrix PairController PairController ℂ) at commute
  rw [Quantum.conjugation_apply,Unitary.coe_star,star_star,Matrix.mul_assoc,commute.eq,← Matrix.mul_assoc,
    Unitary.star_mul_self_of_mem (Native.freePCUnitary time).property,Matrix.one_mul]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
