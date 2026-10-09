import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalRuntime.GeneratedPoweredCapacity
import H0mework.Chemistry.LAlanineEntropy.QuantumGibbsBound

/-! # An actual finite Gibbs environment couples without removing the previous PC interaction -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Source

open scoped Matrix ComplexOrder

noncomputable section

abbrev PairController := (Propagation.Interface.Basis × Propagation.Interface.Basis) × Fin 2
abbrev Pair := Propagation.Interface.Basis × Propagation.Interface.Basis
abbrev LoadedJoint := Matrix (PairController × Fin 2) (PairController × Fin 2) ℂ

def environmentEnergies : Fin 2 → ℝ := ![0, 2]

def environmentPMF := Population.gibbsPMF environmentEnergies 1

def environmentState : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => ((environmentPMF i).toReal : ℂ))

theorem environmentState_positive : environmentState.PosSemidef := Quantum.diagonal_pmf_positive environmentPMF

theorem environmentState_trace : environmentState.trace = 1 := Quantum.diagonal_pmf_trace environmentPMF

def controllerEnvironmentExchange : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.single (0, 1) (1, 0) 1 + Matrix.single (1, 0) (0, 1) 1

theorem exchange_hermitian : controllerEnvironmentExchange.IsHermitian := by
  change controllerEnvironmentExchangeᴴ = controllerEnvironmentExchange
  simp [controllerEnvironmentExchange, Matrix.conjTranspose_single, add_comm]

def loadInteraction : LoadedJoint :=
  (Matrix.kronecker (1 : Matrix Pair Pair ℂ) controllerEnvironmentExchange).submatrix
    (Equiv.prodAssoc Pair (Fin 2) (Fin 2)) (Equiv.prodAssoc Pair (Fin 2) (Fin 2))

theorem loadInteraction_hermitian : loadInteraction.IsHermitian := by
  have tensor : (Matrix.kronecker (1 : Matrix Pair Pair ℂ) controllerEnvironmentExchange).IsHermitian := by
    change _ᴴ = _
    simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, exchange_hermitian.eq]
  exact tensor.submatrix _

def loadTotalHamiltonian : LoadedJoint :=
  Powered.Dynamics.totalHamiltonian Powered.Producer.poweredTotalHamiltonian 2 loadInteraction

theorem loadTotalHamiltonian_hermitian : loadTotalHamiltonian.IsHermitian :=
  Powered.Dynamics.totalHamiltonian_hermitian _ _ _
    Powered.Producer.poweredTotalHamiltonian_hermitian loadInteraction_hermitian

def loadAdvance (elapsed : ℝ) (current : LoadedJoint) : LoadedJoint :=
  Powered.Dynamics.coupledNext Powered.Producer.poweredTotalHamiltonian 2 loadInteraction
    Powered.Producer.poweredTotalHamiltonian_hermitian loadInteraction_hermitian elapsed current

theorem loadAdvance_positive (elapsed : ℝ) (current : LoadedJoint) (positive : current.PosSemidef) :
    (loadAdvance elapsed current).PosSemidef := Powered.Dynamics.coupledNext_positive _ _ _ _ _ _ _ positive

theorem loadAdvance_trace (elapsed : ℝ) (current : LoadedJoint) : (loadAdvance elapsed current).trace = current.trace :=
  Powered.Dynamics.coupledNext_trace _ _ _ _ _ _ _

theorem loadAdvance_add (elapsed next : ℝ) (current : LoadedJoint) :
    loadAdvance (elapsed + next) current = loadAdvance elapsed (loadAdvance next current) :=
  Powered.Dynamics.coupledNext_add _ _ _ _ _ _ _ _

def loadUnitary (elapsed : ℝ) : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  Powered.Dynamics.flowUnitary Powered.Producer.poweredTotalHamiltonian 2 loadInteraction
    Powered.Producer.poweredTotalHamiltonian_hermitian loadInteraction_hermitian elapsed


end

end LAlanine40K2025.Thermal.Load.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
