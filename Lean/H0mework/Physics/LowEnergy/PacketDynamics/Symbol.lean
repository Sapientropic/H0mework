import H0mework.Physics.LowEnergy.PacketNoise.Integration

/-! The original full inverse flow transports the same Dirac graph, with its temporal principal retained on the load side. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace SpatialGreen Triangular Retarded
open YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open StageNineCurrentCoframeMatterTemporalPrincipal
noncomputable section

def temporal : FiberOperators := operator (currentCoframeMatterTemporalPrincipal (actual.coframe 0))
def temporalInverse : FiberOperators := operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0))

theorem temporal_inverse : temporalInverse*temporal=1 := by
  have original : currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0)*
      currentCoframeMatterTemporalPrincipal (actual.coframe 0)=1 := by
    apply LinearMap.ext
    intro field
    exact currentCoframeMatterTemporalPrincipalInverse_left _ (actual_noncharacteristic 0) field
  rw [temporalInverse,temporal,← operator_mul,original]
  ext field
  simp [operator]

def fullHamiltonian (frequency : Position) : FiberOperators :=
  operator (hamiltonian actual 0 (physicalMomentum frequency))

theorem fullHamiltonian_flow (frequency : Position) (time : ℝ) :
    fullHamiltonian frequency*fullMatrices 0 time frequency=
      fullMatrices 0 time frequency*fullHamiltonian frequency := by
  rw [fullHamiltonian,hamiltonian,operator_smul,smul_mul_assoc,mul_smul_comm]
  exact congrArg (fun A : FiberOperators => Complex.I • A)
    (evolution_commutes actual 0 (physicalMomentum frequency) time).symm

theorem symbol_factor (energy damping : ℝ) (frequency : Position) :
    symbol 0 energy damping frequency=(-Complex.I) •
      (temporal*((spectralParameter energy damping) • 1-fullHamiltonian frequency)) := by
  rw [symbol,diracKernel_factor actual 0 _ _ (actual_noncharacteristic 0),operator_smul,operator_mul]
  congr 2
  ext field
  simp [fullKernel,fullHamiltonian,operator]

theorem symbol_flow (energy damping : ℝ) (frequency : Position) (time : ℝ) :
    symbol 0 energy damping frequency*fullMatrices 0 time frequency=
      temporal*fullMatrices 0 time frequency*temporalInverse*symbol 0 energy damping frequency := by
  rw [symbol_factor]
  have commute : (spectralParameter energy damping • (1 : FiberOperators)-fullHamiltonian frequency)*
      fullMatrices 0 time frequency=fullMatrices 0 time frequency*
        (spectralParameter energy damping • (1 : FiberOperators)-fullHamiltonian frequency) := by
    rw [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,fullHamiltonian_flow]
  rw [smul_mul_assoc,mul_smul_comm]
  congr 1
  calc
    _ = temporal*(fullMatrices 0 time frequency*
        (spectralParameter energy damping • (1 : FiberOperators)-fullHamiltonian frequency)) := by
      rw [mul_assoc,commute]
    _ = _ := by simp only [mul_assoc,← mul_assoc temporalInverse temporal,temporal_inverse,one_mul]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
