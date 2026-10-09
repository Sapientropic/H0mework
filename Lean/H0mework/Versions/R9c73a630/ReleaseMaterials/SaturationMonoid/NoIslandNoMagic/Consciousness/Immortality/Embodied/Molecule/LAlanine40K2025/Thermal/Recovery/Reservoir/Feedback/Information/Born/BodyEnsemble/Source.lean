import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedConditionalResourceIncidence
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Control.Mutual.Source

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble

open Collision Load.Producer.HeatProbability SourceGeneratedWorkInformation SourceGeneratedConditionalWork
open scoped Matrix ComplexOrder
noncomputable section

attribute [local irreducible] Current.loadPulse Current.pulse Live.State.joint
  sourceTarget receivedState firstState contrast

def p0 : ℝ := zeroRead receivedState.joint
def p1 : ℝ := oneRead receivedState.joint
def sigma0 : Current.FullJoint := Resource.loadBlock receivedState
def sigma1 : Current.FullJoint := Resource.suppliedBlock receivedState
def rho0 : Current.FullJoint := (p0⁻¹ : ℝ) • sigma0
def rho1 : Current.FullJoint := (p1⁻¹ : ℝ) • sigma1

private theorem left_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (positive : joint.PosSemidef) :
    joint.toBlocks₁₁.trace = (zeroRead joint : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (positive.submatrix Sum.inl).trace_nonneg).2.symm

private theorem right_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (positive : joint.PosSemidef) :
    joint.toBlocks₂₂.trace = (oneRead joint : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (positive.submatrix Sum.inr).trace_nonneg).2.symm

theorem weighted_unnormalize {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (p : ℝ) (hp : 0 < p) :
    (p : ℂ) • ((p⁻¹ : ℝ) • M) = M := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  have h : (p : ℂ) * ((p⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hp.ne']
    norm_num
  simp only [← mul_assoc, h, one_mul]

theorem p0_pos : 0 < p0 := by
  rw [p0, receivedState_joint]
  exact sourceTarget_strict.1

theorem p1_pos : 0 < p1 := by
  change 0 < oneRead receivedState.joint
  rw [receivedState_joint]
  exact Resource.source_one_strict.1

theorem sigma0_trace : sigma0.trace = (p0 : ℂ) := by
  simpa only [sigma0, p0, Resource.loadBlock] using
    left_trace receivedState.joint receivedState.positive

theorem sigma1_trace : sigma1.trace = (p1 : ℂ) := by
  simpa only [sigma1, p1, Resource.suppliedBlock] using
    right_trace receivedState.joint receivedState.positive

theorem rho0_positive : rho0.PosSemidef :=
  (Resource.loadBlock_positive receivedState).smul (inv_nonneg.mpr p0_pos.le)

theorem rho1_positive : rho1.PosSemidef :=
  (Resource.suppliedBlock_positive receivedState).smul (inv_nonneg.mpr p1_pos.le)

theorem rho0_trace : rho0.trace = 1 := by
  rw [rho0, Matrix.trace_smul, sigma0_trace, Complex.real_smul, ← Complex.ofReal_mul]
  simp [inv_mul_cancel₀ p0_pos.ne']

theorem rho1_trace : rho1.trace = 1 := by
  rw [rho1, Matrix.trace_smul, sigma1_trace, Complex.real_smul, ← Complex.ofReal_mul]
  simp [inv_mul_cancel₀ p1_pos.ne']

theorem source_mixture : (p0 : ℂ) • rho0 + (p1 : ℂ) • rho1 =
    bodyRead receivedState.joint := by
  have left : (p0 : ℂ) • rho0 = sigma0 := weighted_unnormalize sigma0 p0 p0_pos
  have right : (p1 : ℂ) • rho1 = sigma1 := weighted_unnormalize sigma1 p1 p1_pos
  rw [left, right]
  exact (Resource.body_blocks receivedState).symm

theorem source_defect_conditional :
    signedDefect receivedState =
      p0 * p1 * (energy contrast rho0 - energy contrast rho1) := by
  have h0 : sigma0 = (p0 : ℂ) • rho0 := (weighted_unnormalize sigma0 p0 p0_pos).symm
  have h1 : sigma1 = (p1 : ℂ) • rho1 := (weighted_unnormalize sigma1 p1 p1_pos).symm
  calc
    signedDefect receivedState =
        p1 * energy contrast sigma0 - p0 * energy contrast sigma1 := by
      simpa only [p0, p1, sigma0, sigma1, Resource.loadBlock, Resource.suppliedBlock] using
        signed_defect_blocks receivedState
    _ = p0 * p1 * (energy contrast rho0 - energy contrast rho1) := by
      rw [h0, h1, energy_smul_right, energy_smul_right]
      ring


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
