import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.ProjectedOrbit
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.Pulse

open Complex NormedSpace selfAdjoint Unitary
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finite_spectrum_arg_continuous (U : Matrix.unitaryGroup ι ℂ) :
    ContinuousOn Complex.arg (spectrum ℂ (U : Matrix ι ι ℂ)) :=
  (Matrix.finite_spectrum (U : Matrix ι ι ℂ)).continuousOn _

theorem matrixUnitary_arg_generates (U : Matrix.unitaryGroup ι ℂ) :
    selfAdjoint.expUnitary (Unitary.argSelfAdjoint U) = U := by
  have continuous : ContinuousOn (fun z : ℂ => (z.arg : ℂ)) (spectrum ℂ (U : Matrix ι ι ℂ)) :=
    (Matrix.finite_spectrum (U : Matrix ι ι ℂ)).continuousOn _
  apply Subtype.ext
  rw [selfAdjoint.expUnitary_coe, Unitary.argSelfAdjoint_coe,
    ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ)]
  rw [← cfc_comp_smul I (NormedSpace.exp : ℂ → ℂ)
    (cfc (fun z : ℂ => (z.arg : ℂ)) (U : Matrix ι ι ℂ))]
  rw [← cfc_comp' (fun z : ℂ => NormedSpace.exp (I • z))
    (fun z : ℂ => (z.arg : ℂ)) (U : Matrix ι ι ℂ) (hf := continuous)]
  conv_rhs => rw [← cfc_id' ℂ (U : Matrix ι ι ℂ)]
  apply cfc_congr
  intro z hz
  have norm := spectrum.norm_eq_one_of_unitary U.property hz
  have phase : Complex.I * z.arg = Complex.log z :=
    Complex.ext (by simp [Complex.log_re, norm]) (by simp [Complex.log_im])
  simpa [← Complex.exp_eq_exp_ℂ, phase] using Complex.exp_log (by aesop)

def pulseHamiltonian (U : Matrix.unitaryGroup ι ℂ) (duration : ℝ) : Matrix ι ι ℂ :=
  -(duration⁻¹ : ℂ) • (Unitary.argSelfAdjoint U : Matrix ι ι ℂ)

theorem pulseHamiltonian_hermitian (U : Matrix.unitaryGroup ι ℂ) (duration : ℝ) :
    (pulseHamiltonian U duration).IsHermitian := by
  apply (show ((Unitary.argSelfAdjoint U : selfAdjoint (Matrix ι ι ℂ)) : Matrix ι ι ℂ).IsHermitian from
    (Unitary.argSelfAdjoint U).property).smul
  simp [isSelfAdjoint_iff]

theorem pulseHamiltonian_generates (U : Matrix.unitaryGroup ι ℂ) (duration : ℝ)
    (nonzero : duration ≠ 0) :
    NormedSpace.exp (duration • (-Complex.I • pulseHamiltonian U duration)) = (U : Matrix ι ι ℂ) := by
  have phase : duration • (-Complex.I • pulseHamiltonian U duration) =
      Complex.I • (Unitary.argSelfAdjoint U : Matrix ι ι ℂ) := by
    unfold pulseHamiltonian
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    field_simp
  rw [phase]
  exact congrArg Subtype.val (matrixUnitary_arg_generates U)

end
end LAlanine40K2025.Thermal.Recovery.Charging.Pulse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
