import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Flip
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
open Collision Quantum Load.Producer.StrictThermal Propagation.Producer Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def controlHamiltonian : PointerJoint := (Real.pi/(2*(nativeClockStep : ℝ))) • (flip (ι := Current.FullIndex) : PointerJoint)

theorem control_hermitian : controlHamiltonian.IsHermitian :=
  (flip_hermitian (ι := Current.FullIndex)).smul (show IsSelfAdjoint (Real.pi/(2*(nativeClockStep : ℝ))) from rfl)

def offset : ℝ := ‖Pointer.baselineHamiltonian‖+‖controlHamiltonian‖+1

def coupledHamiltonian : PointerJoint := controlHamiltonian-offset • (1 : PointerJoint)

theorem coupled_hermitian : coupledHamiltonian.IsHermitian :=
  control_hermitian.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint offset from rfl))

def pulse (time : ℝ) : Matrix.unitaryGroup PointerIndex ℂ :=
  ⟨NormedSpace.exp ((-Complex.I*(time : ℂ)) • coupledHamiltonian),by
    let : NormedAlgebra ℚ PointerJoint := .restrictScalars ℚ ℂ _
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    apply coupled_hermitian.isSelfAdjoint.smul_mem_skewAdjoint
    change star (-Complex.I*(time : ℂ)) = -(-Complex.I*(time : ℂ))
    simp⟩

def phase (time : ℝ) : unitary ℂ :=
  ⟨NormedSpace.exp (Complex.I*(offset : ℂ)*(time : ℂ)),by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp only [star_mul,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
    ring⟩

private theorem shifted_generator {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H : Matrix κ κ ℂ) (c time : ℝ) :
    (-Complex.I*(time : ℂ)) • (H-c • (1 : Matrix κ κ ℂ))=
      (-Complex.I*(time : ℂ)) • H+(Complex.I*(c : ℂ)*(time : ℂ)) • (1 : Matrix κ κ ℂ) := by
  ext i j
  simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,smul_eq_mul,Complex.real_smul]
  ring

attribute [local irreducible] flip controlHamiltonian coupledHamiltonian offset Pointer.baselineHamiltonian

theorem unshifted_pulse_clock :
    NormedSpace.exp ((-Complex.I*(nativeClockStep : ℂ)) • controlHamiltonian)=(-Complex.I) • (flip (ι := Current.FullIndex) : PointerJoint) := by
  have input : (-Complex.I*(nativeClockStep : ℂ)) • controlHamiltonian=
      (-Complex.I*((Real.pi/2 : ℝ) : ℂ)) • (flip (ι := Current.FullIndex) : PointerJoint) := by
    unfold controlHamiltonian
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,Complex.ofReal_div,
      Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_ratCast]
    have hqc : (nativeClockStep : ℂ) ≠ 0 := by exact_mod_cast nativeClockStep_positive.ne'
    field_simp
  rw [input]
  exact flip_half_pi (ι := Current.FullIndex)

theorem pulse_at_clock :
    (pulse (nativeClockStep : ℝ) : PointerJoint)=
      ((phase (nativeClockStep : ℝ) : ℂ)*(-Complex.I)) • (flip (ι := Current.FullIndex) : PointerJoint) := by
  change NormedSpace.exp ((-Complex.I*((nativeClockStep : ℝ) : ℂ)) • coupledHamiltonian)=_
  rw [coupledHamiltonian,shifted_generator,Pointer.exp_scalar_shift]
  rw [show ((nativeClockStep : ℝ) : ℂ)=(nativeClockStep : ℂ) by norm_cast,unshifted_pulse_clock]
  rw [smul_smul]
  rfl

theorem pulse_clock_density (rho : PointerJoint) :
    conjugation (pulse (nativeClockStep : ℝ)) rho=conjugation flip rho := by
  rw [conjugation_apply,pulse_at_clock,star_smul]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,star_mul]
  have scalar : star ((phase (nativeClockStep : ℝ) : ℂ)*(-Complex.I))*
      ((phase (nativeClockStep : ℝ) : ℂ)*(-Complex.I))=1 := by
    simp only [star_mul,star_neg,Complex.star_def,Complex.conj_I,neg_neg]
    have norm := Unitary.star_mul_self_of_mem (phase (nativeClockStep : ℝ)).property
    change star (phase (nativeClockStep : ℝ) : ℂ)*(phase (nativeClockStep : ℝ) : ℂ)=1 at norm
    calc
      Complex.I*(star (phase (nativeClockStep : ℝ) : ℂ))*((phase (nativeClockStep : ℝ) : ℂ)*(-Complex.I))
          = (Complex.I*(-Complex.I))*(star (phase (nativeClockStep : ℝ) : ℂ)*(phase (nativeClockStep : ℝ) : ℂ)) := by ring
      _ = 1 := by rw [norm]; simp
  rw [← star_mul,scalar,one_smul]
  exact (conjugation_apply (flip (ι := Current.FullIndex)) rho).symm

private theorem scalar_generator_commutes {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H : Matrix κ κ ℂ) (z : ℂ) : Commute H (NormedSpace.exp (z • H)) :=
  ((Commute.refl H).smul_right z).exp_right

theorem pulse_conserves (time : ℝ) (rho : PointerJoint) :
    energy coupledHamiltonian (conjugation (pulse time) rho)=energy coupledHamiltonian rho := by
  have commute : Commute coupledHamiltonian (pulse time : PointerJoint) :=
    scalar_generator_commutes coupledHamiltonian (-Complex.I*(time : ℂ))
  simpa only [conjugation_apply] using
    PreparationEnergy.commuting_energy coupledHamiltonian rho (pulse time) commute


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
