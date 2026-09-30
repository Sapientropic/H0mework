import H0mework.Physics.LowEnergy.PacketDynamics.AdjointFlow

/-! The full adjoint history retains the bounded one-way Yukawa commutator in the original Dirac graph. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace SpatialGreen Triangular Retarded
open YangMills.FullPairing Stage9C.Material.SpinPair
noncomputable section

def skewFiber : FiberOperators :=
  operator (interactionHamiltonian actual 0)-(operator (interactionHamiltonian actual 0)).adjoint

theorem fullHamiltonian_skew (frequency : Position) :
    fullHamiltonian frequency-(fullHamiltonian frequency).adjoint=skewFiber := by
  rw [fullHamiltonian,hamiltonian_split,operator_add]
  change _-star (_+_)=_
  rw [star_add,original_freeHamiltonian_selfAdjoint]
  unfold skewFiber
  abel

theorem hamiltonian_adjoint_flow (frequency : Position) (time : ℝ) :
    fullHamiltonian frequency*adjointMatrices time frequency=
      adjointMatrices time frequency*fullHamiltonian frequency+
        (skewFiber*adjointMatrices time frequency-adjointMatrices time frequency*skewFiber) := by
  have commutes := congrArg star (fullHamiltonian_flow frequency time)
  simp only [star_mul] at commutes
  change adjointMatrices time frequency*(fullHamiltonian frequency).adjoint=
    (fullHamiltonian frequency).adjoint*adjointMatrices time frequency at commutes
  rw [← fullHamiltonian_skew frequency,sub_mul,mul_sub,commutes]
  abel

theorem kernel_adjoint_flow (energy damping : ℝ) (frequency : Position) (time : ℝ) :
    (spectralParameter energy damping • (1 : FiberOperators)-fullHamiltonian frequency)*adjointMatrices time frequency=
      adjointMatrices time frequency*(spectralParameter energy damping • (1 : FiberOperators)-fullHamiltonian frequency)-
        (skewFiber*adjointMatrices time frequency-adjointMatrices time frequency*skewFiber) := by
  rw [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,hamiltonian_adjoint_flow]
  abel

theorem symbol_adjoint_flow (energy damping : ℝ) (frequency : Position) (time : ℝ) :
    symbol 0 energy damping frequency*adjointMatrices time frequency=
      temporal*adjointMatrices time frequency*temporalInverse*symbol 0 energy damping frequency+
        Complex.I • (temporal*(skewFiber*adjointMatrices time frequency-adjointMatrices time frequency*skewFiber)) := by
  rw [symbol_factor,smul_mul_assoc,mul_smul_comm]
  have factor : temporal*adjointMatrices time frequency*temporalInverse*
      (temporal*(spectralParameter energy damping • (1 : FiberOperators)-fullHamiltonian frequency))=
        temporal*(adjointMatrices time frequency*
          (spectralParameter energy damping • (1 : FiberOperators)-fullHamiltonian frequency)) := by
    simp only [mul_assoc,← mul_assoc temporalInverse temporal,temporal_inverse,one_mul]
  rw [factor,mul_assoc,kernel_adjoint_flow,mul_sub,smul_sub]
  simp only [neg_smul,sub_neg_eq_add]
  congr 1
  exact (neg_smul (R := ℂ) (M := FiberOperators) Complex.I _).symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
