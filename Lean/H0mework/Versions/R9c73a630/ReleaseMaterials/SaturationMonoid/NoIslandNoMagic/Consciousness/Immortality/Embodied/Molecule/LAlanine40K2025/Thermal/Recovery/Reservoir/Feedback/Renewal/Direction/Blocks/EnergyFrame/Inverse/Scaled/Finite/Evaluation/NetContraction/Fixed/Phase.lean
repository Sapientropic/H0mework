import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.PC
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Algebra

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Propagation.Producer Powered.Dynamics
open scoped Matrix BigOperators

def phaseQ : Scalar.QComplex :=
  (SquareRoot.Full.sine^2-SquareRoot.Full.cosine^2,-2*SquareRoot.Full.cosine*SquareRoot.Full.sine)

def couplingQ : Scalar.QComplex := Scalar.multiply (3/5,-4/5) phaseQ

theorem phaseQ_value : Scalar.value phaseQ=Phase.pointerPhase := by
  have c : (SquareRoot.Full.cosine : ℂ)=(cosineHat : ℂ) := by exact_mod_cast SquareRoot.Full.cosine_cast
  have s : (SquareRoot.Full.sine : ℂ)=(sineHat : ℂ) := by exact_mod_cast SquareRoot.Full.sine_cast
  simp only [phaseQ,Scalar.value,Rat.cast_sub,Rat.cast_pow,Rat.cast_mul,Rat.cast_neg,Rat.cast_ofNat,c,s,Phase.pointerPhase]
  push_cast
  ring

theorem couplingQ_value : Scalar.value couplingQ=Input.finiteCouplingPhase := by
  rw [couplingQ,Scalar.value_multiply,phaseQ_value]
  simp only [Scalar.value,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Input.finiteCouplingPhase,
    Input.initialPhase,Thermal.Source.exchangeCosine,Thermal.Source.exchangeSine]
  push_cast
  ring

def environmentSeedQ (time : ℚ) (i : Fin 2) : Scalar.QComplex := (0,-time*(if i=0 then 0 else 2))
def environmentFlowQ (time : ℚ) : MatrixQ (Fin 2) (Fin 2) :=
  diagonalQ (fun i => Scalar.polynomial (environmentSeedQ time i) 14)

theorem environment_seed (time : ℚ) :
    (time : ℝ) • (-Complex.I • controllerHamiltonian 2)=Matrix.diagonal (fun i => Scalar.value (environmentSeedQ time i)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [environmentSeedQ,Scalar.value,controllerHamiltonian,Matrix.smul_apply,Matrix.diagonal_apply,smul_eq_mul,Complex.real_smul]
  all_goals ring

theorem environmentFlowQ_value (time : ℚ) : qvalue (environmentFlowQ time)=Phase.flowPolynomial (controllerHamiltonian 2) (time : ℝ) := by
  rw [environmentFlowQ,diagonalQ_value,Phase.flowPolynomial,environment_seed,Diagonal.matrix_polynomial_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  exact Scalar.value_polynomial _ _

def freeEnvironmentQ : MatrixQ (Fin 2) (Fin 2) := environmentFlowQ Diagonal.clock

def recoveryEnvironmentQ : MatrixQ (Fin 2) (Fin 2) := environmentFlowQ (3*Diagonal.clock)

theorem freeEnvironmentQ_value : qvalue freeEnvironmentQ=Phase.environmentPolynomial := by
  rw [freeEnvironmentQ,environmentFlowQ_value,Diagonal.clock_original]
  rfl

theorem recoveryEnvironmentQ_value : qvalue recoveryEnvironmentQ=Actions.recoveryEnvironmentPolynomial := by
  rw [recoveryEnvironmentQ,environmentFlowQ_value,Diagonal.clock_original]
  norm_num only [Rat.cast_mul,Rat.cast_ofNat]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
