import H0mework.Physics.LowEnergyMatterSpace.Phase
import H0mework.Physics.LowEnergyMatterSpace.LocalOperator

/-! The original local T/B operators commute with the source graded phase by their actual matrices. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.ResponsePhase
open Fermion Stage9C.Material.SpinPair SU7MotherLieAlgebra DiracCliffordRepresentation
noncomputable section
attribute [local instance] instLinearOrderSourceIndex
local instance : NormedAlgebra ℚ (MatterFiber →L[ℂ] MatterFiber) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

theorem gaugeCurrent_commutes_charge (data : LorentzianIndex → P286LieBlockData) :
    sourceCharge*gaugeCurrentMatrix data=gaugeCurrentMatrix data*sourceCharge := by
  rw [gaugeCurrentMatrix_weight]
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  calc
    sourceCharge*(sourceCharge*gaugeHamiltonianMatrix data)=
        sourceCharge*(gaugeHamiltonianMatrix data*sourceCharge) := by rw [gaugeHamiltonian_commutes_charge]
    _ = (sourceCharge*gaugeHamiltonianMatrix data)*sourceCharge := (mul_assoc _ _ _).symm

private theorem finitePhase_matrix (A : SourceMatrix) (commutes : sourceCharge*A=A*sourceCharge) (t : ℝ) :
    timeEvolution phaseHamiltonian t*hamiltonianOperator A=
      hamiltonianOperator A*timeEvolution phaseHamiltonian t := by
  have matrices : phaseHamiltonian*A=A*phaseHamiltonian := by
    simp only [phaseHamiltonian,Matrix.smul_mul,Matrix.mul_smul,commutes]
  have operators : hamiltonianOperator phaseHamiltonian*hamiltonianOperator A=
      hamiltonianOperator A*hamiltonianOperator phaseHamiltonian := by
    unfold hamiltonianOperator
    rw [← map_mul,← map_mul,matrices]
  have scaled : Commute (t • timeGenerator phaseHamiltonian) (hamiltonianOperator A) := by
    change (t • timeGenerator phaseHamiltonian)*hamiltonianOperator A=
      hamiltonianOperator A*(t • timeGenerator phaseHamiltonian)
    ext v i
    have point := congrArg (fun op : MatterFiber →L[ℂ] MatterFiber => op v i) operators
    simp only [mul_apply_eq_comp] at point
    simp [timeGenerator,point]
  exact scaled.exp_left.eq

private theorem localMatrix_phase (profile : BoundedProfile) (A : SourceMatrix)
    (commutes : sourceCharge*A=A*sourceCharge) (t : ℝ) (u : MatterL2) :
    phaseRead t (localMatrixOperator profile A u)=localMatrixOperator profile A (phaseRead t u) := by
  apply Lp.ext
  filter_upwards [phaseRead_ae t (localMatrixOperator profile A u),localMatrixOperator_ae profile A u,
    localMatrixOperator_ae profile A (phaseRead t u),phaseRead_ae t u] with x hp ha hpa hu
  rw [hp,ha,hpa,hu,map_smul]
  have finite := congrArg (fun op : MatterFiber →L[ℂ] MatterFiber => op (u x)) (finitePhase_matrix A commutes t)
  exact congrArg (fun v : MatterFiber => profile x • v) finite

theorem localGauge_phase (profile : BoundedProfile) (data : LorentzianIndex → P286LieBlockData)
    (t : ℝ) (u : MatterL2) :
    phaseRead t (localGaugeHamiltonian profile data u)=localGaugeHamiltonian profile data (phaseRead t u) :=
  localMatrix_phase profile _ (gaugeHamiltonian_commutes_charge data) t u

theorem localCurrent_phase (profile : BoundedProfile) (data : LorentzianIndex → P286LieBlockData)
    (t : ℝ) (u : MatterL2) :
    phaseRead t (localCurrentOperator profile data u)=localCurrentOperator profile data (phaseRead t u) :=
  localMatrix_phase profile _ (gaugeCurrent_commutes_charge data) t u

theorem phaseRead_pair (t : ℝ) (u v : MatterL2) :
    inner ℂ (phaseRead t u) (phaseRead t v)=inner ℂ u v := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [phaseRead_ae t u,phaseRead_ae t v] with x hu hv
  rw [hu,hv]
  exact timeEvolution_pair phaseHamiltonian phaseHamiltonian_hermitian t (u x) (v x)

theorem localCurrent_phase_pair (profile : BoundedProfile) (data : LorentzianIndex → P286LieBlockData)
    (t : ℝ) (u v : MatterL2) :
    inner ℂ (phaseRead t u) (localCurrentOperator profile data (phaseRead t v))=
      inner ℂ u (localCurrentOperator profile data v) := by
  rw [← localCurrent_phase,phaseRead_pair]

theorem finitePhase_free (k : Momentum) (r t : ℝ) :
    timeEvolution phaseHamiltonian r*timeEvolution (sourceHamiltonian k) t=
      timeEvolution (sourceHamiltonian k) t*timeEvolution phaseHamiltonian r := by
  have operators := finitePhase_matrix (sourceHamiltonian k) (sourceHamiltonian_commutes_charge k) r
  have scaled : Commute (timeEvolution phaseHamiltonian r) (t • timeGenerator (sourceHamiltonian k)) := by
    change timeEvolution phaseHamiltonian r*(t • timeGenerator (sourceHamiltonian k))=
      (t • timeGenerator (sourceHamiltonian k))*timeEvolution phaseHamiltonian r
    ext v i
    have point := congrArg (fun op : MatterFiber →L[ℂ] MatterFiber => op v i) operators
    simp only [mul_apply_eq_comp] at point
    simp [timeGenerator,point]
  exact scaled.exp_right.eq

theorem spatialUnitary_phase (r t : ℝ) (u : MatterL2) :
    phaseRead r (spatialUnitary t u)=spatialUnitary t (phaseRead r u) := by
  apply fourier.injective
  rw [phaseRead_fourier,spatialUnitary_fourier,spatialUnitary_fourier,phaseRead_fourier]
  apply Lp.ext
  filter_upwards [phaseRead_ae r (momentumUnitary t (fourier u)),
    applyFlow_ae volume actualFourierHamiltonian actualFourierHamiltonian_continuous
      actualFourierHamiltonian_hermitian t (fourier u),
    applyFlow_ae volume actualFourierHamiltonian actualFourierHamiltonian_continuous
      actualFourierHamiltonian_hermitian t (phaseRead r (fourier u)),phaseRead_ae r (fourier u)]
    with x hp hf hpf hphase
  change phaseRead r (momentumUnitary t (fourier u)) x=
    applyFlow volume actualFourierHamiltonian actualFourierHamiltonian_continuous
      actualFourierHamiltonian_hermitian t (phaseRead r (fourier u)) x
  rw [hp,hpf,hphase]
  change timeEvolution phaseHamiltonian r
    (applyFlow volume actualFourierHamiltonian actualFourierHamiltonian_continuous
      actualFourierHamiltonian_hermitian t (fourier u) x)=_
  rw [hf]
  exact congrArg (fun op : MatterFiber →L[ℂ] MatterFiber => op (fourier u x))
    (finitePhase_free (fun j => 2*Real.pi*x j) r t)

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.ResponsePhase
