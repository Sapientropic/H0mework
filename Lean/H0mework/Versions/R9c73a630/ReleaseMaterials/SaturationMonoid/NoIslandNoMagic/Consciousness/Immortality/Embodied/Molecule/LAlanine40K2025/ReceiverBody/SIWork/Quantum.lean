import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Receiver

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
open FiniteContinuation Propagation.Interface Thermal.Quantum Thermal.Collision
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def liouvilleSI {ι : Type} [Fintype ι] (hamiltonian state : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1/hbarJouleSecond : ℝ) • (-Complex.I • (hamiltonian*state-state*hamiltonian))

theorem liouville_units {ι : Type} [Fintype ι] (hamiltonian state : Matrix ι ι ℂ) :
    (1/timeSecond : ℝ) • (-Complex.I • (hamiltonian*state-state*hamiltonian))=
      liouvilleSI (energyJoule • hamiltonian) state := by
  have rate : 1/timeSecond=(1/hbarJouleSecond)*energyJoule := by
    unfold timeSecond
    field_simp
  rw [rate,mul_smul,smul_comm energyJoule (-Complex.I)]
  simp only [liouvilleSI,smul_mul_assoc,mul_smul_comm,← smul_sub]

def gammaSI (current : Material) (phase : Phase) (second : ℝ) : Matrix Basis Basis ℂ :=
  gammaPath current phase (second/timeSecond)

def gammaHamiltonianSI (phase : Phase) (second : ℝ) : Matrix Basis Basis ℂ :=
  energyJoule • FiniteActuation.electronHamiltonian (FiniteActuation.electronicRate phase (second/timeSecond))

def quantumSI (current : Material) (phase : Phase) (second : ℝ) : PointerJoint :=
  quantumPath current phase (second/timeSecond)

def quantumHamiltonianSI : PointerJoint := energyJoule • Pointer.baselineHamiltonian

theorem gamma_equation_si (current : Material) (phase : Phase) (second : ℝ) :
    HasDerivAt (gammaSI current phase) (liouvilleSI (gammaHamiltonianSI phase second) (gammaSI current phase second)) second := by
  have generated := (gamma_equation current phase (second/timeSecond)).scomp second ((hasDerivAt_id second).div_const timeSecond)
  unfold gammaSI gammaHamiltonianSI
  rw [← liouville_units]
  exact generated

theorem quantum_equation_si (current : Material) (phase : Phase) (second : ℝ) :
    HasDerivAt (quantumSI current phase) (liouvilleSI quantumHamiltonianSI (quantumSI current phase second)) second := by
  have generated := (quantum_equation current phase (second/timeSecond)).scomp second ((hasDerivAt_id second).div_const timeSecond)
  unfold quantumSI quantumHamiltonianSI
  rw [← liouville_units]
  exact generated

theorem gamma_integral_si (current : Material) (phase : Phase) :
    gammaSI current phase segmentSeconds-gammaSI current phase 0=
      ∫ second in (0 : ℝ)..segmentSeconds, liouvilleSI (gammaHamiltonianSI phase second) (gammaSI current phase second) := by
  have state : Continuous (gammaSI current phase) :=
    continuous_iff_continuousAt.mpr fun t => (gamma_equation_si current phase t).continuousAt
  have generator : Continuous (gammaHamiltonianSI phase) := by
    unfold gammaHamiltonianSI FiniteActuation.electronHamiltonian FiniteActuation.electronicRate
      FiniteActuation.onRate FiniteActuation.offRate
    cases phase <;> fun_prop
  have regular := (((generator.mul state).sub (state.mul generator)).const_smul (-Complex.I)).const_smul (1/hbarJouleSecond : ℝ)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun second _ => gamma_equation_si current phase second) (regular.intervalIntegrable 0 segmentSeconds)).symm

theorem quantum_integral_si (current : Material) (phase : Phase) :
    quantumSI current phase segmentSeconds-quantumSI current phase 0=
      ∫ second in (0 : ℝ)..segmentSeconds, liouvilleSI quantumHamiltonianSI (quantumSI current phase second) := by
  have state : Continuous (quantumSI current phase) :=
    continuous_iff_continuousAt.mpr fun t => (quantum_equation_si current phase t).continuousAt
  have regular := (((state.const_mul quantumHamiltonianSI).sub
    (state.mul_const quantumHamiltonianSI)).const_smul (-Complex.I)).const_smul (1/hbarJouleSecond : ℝ)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun second _ => quantum_equation_si current phase second) (regular.intervalIntegrable 0 segmentSeconds)).symm

theorem gamma_residual_si (current : Material) (valid : Admissible current) (phase : Phase) (second : ℝ) :
    gammaSI current phase second=
      FiniteActuation.electronFlow current.body.held (FiniteActuation.electronicTime phase (second/timeSecond))+
      FiniteActuation.electronFlow current.body.inheritedResidual (FiniteActuation.electronicTime phase (second/timeSecond))+
      FiniteActuation.electronFlow current.body.newNumericalResidual (FiniteActuation.electronicTime phase (second/timeSecond)) :=
  gamma_residual_retained current valid phase (second/timeSecond)

theorem gamma_endpoints_si (current : Material) (valid : Admissible current) :
    gammaSI current .enter 0=current.body.realized ∧
    gammaSI current .leave segmentSeconds=(nextMaterial current).body.realized := by
  constructor
  · simp only [gammaSI,zero_div]
    exact (source_endpoints current valid (0,0)).2.2.2.1
  · simp only [gammaSI,segmentSeconds,mul_div_cancel_right₀ _ time_positive.ne']
    exact (target_endpoints current valid (0,0)).2.2.2.1

theorem quantum_endpoints_si (current : Material) (valid : Admissible current) :
    quantumSI current .enter 0=current.body.resource.quantum.joint ∧
    quantumSI current .leave segmentSeconds=(nextMaterial current).body.resource.quantum.joint := by
  constructor
  · simp only [quantumSI,zero_div]
    exact (source_endpoints current valid (0,0)).2.2.2.2
  · simp only [quantumSI,segmentSeconds,mul_div_cancel_right₀ _ time_positive.ne']
    exact (target_endpoints current valid (0,0)).2.2.2.2

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
