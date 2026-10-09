import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Covariance
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hamiltonianFlow (H : Matrix ι ι ℂ) (time : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp (time • (-Complex.I • H))

theorem hamiltonianFlow_unitary (H : Matrix ι ι ℂ) (hermitian : H.IsHermitian) (time : ℝ) :
    hamiltonianFlow H time ∈ Matrix.unitaryGroup ι ℂ := by
  let : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp only [star_smul,star_neg,Complex.star_def,Complex.conj_I,neg_neg,
    hermitian.isSelfAdjoint.star_eq,star_trivial]
  module

theorem hamiltonianFlow_derivative (H : Matrix ι ι ℂ) (time : ℝ) :
    HasDerivAt (hamiltonianFlow H) (hamiltonianFlow H time*(-Complex.I • H)) time :=
  hasDerivAt_exp_smul_const _ _

def relativeFlow (H K : Matrix ι ι ℂ) (time : ℝ) : Matrix ι ι ℂ :=
  hamiltonianFlow H time*star (hamiltonianFlow K time)

theorem relativeFlow_derivative (H K : Matrix ι ι ℂ) (hK : K.IsHermitian) (time : ℝ) :
    HasDerivAt (relativeFlow H K)
      (hamiltonianFlow H time*(-Complex.I • (H-K))*star (hamiltonianFlow K time)) time := by
  have derivative := (hamiltonianFlow_derivative H time).mul (hamiltonianFlow_derivative K time).star
  apply derivative.congr_deriv
  simp only [star_mul,star_smul,hK.isSelfAdjoint.star_eq,star_neg,Complex.star_def,Complex.conj_I,
    neg_neg,smul_mul_assoc,mul_smul_comm,smul_sub,mul_sub,sub_mul,mul_assoc]
  module

theorem relativeFlow_derivative_norm (H K : Matrix ι ι ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (time : ℝ) : ‖hamiltonianFlow H time*(-Complex.I • (H-K))*star (hamiltonianFlow K time)‖ = ‖H-K‖ := by
  have right : star (hamiltonianFlow K time) ∈ unitary (Matrix ι ι ℂ) := by
    have member := hamiltonianFlow_unitary K hK time
    exact Unitary.star_mem member
  rw [CStarRing.norm_mul_mem_unitary _ right,CStarRing.norm_mem_unitary_mul _ (hamiltonianFlow_unitary H hH time),
    norm_smul,norm_neg,Complex.norm_I,one_mul]

/-- Original unitary flow stability is paid by the Hamiltonian difference, without commuting assumptions. -/
theorem hamiltonian_flow_error (H K : Matrix ι ι ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) (time : ℝ) :
    ‖hamiltonianFlow H time-hamiltonianFlow K time‖ ≤ |time| *‖H-K‖ := by
  have estimate := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := (0 : ℝ)) (y := time)
    (fun t _ => (relativeFlow_derivative H K hK t).hasDerivWithinAt)
    (fun t _ => (relativeFlow_derivative_norm H K hH hK t).le)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ 0) (Set.mem_univ time)
  have origin : relativeFlow H K 0 = 1 := by simp [relativeFlow,hamiltonianFlow]
  rw [origin,sub_zero,Real.norm_eq_abs] at estimate
  have factor : hamiltonianFlow H time-hamiltonianFlow K time =
      (relativeFlow H K time-1)*hamiltonianFlow K time := by
    have unit := (hamiltonianFlow_unitary K hK time).1
    simp only [relativeFlow,sub_mul,Matrix.one_mul,Matrix.mul_assoc,unit,Matrix.mul_one]
  rw [factor,CStarRing.norm_mul_mem_unitary _ (hamiltonianFlow_unitary K hK time)]
  simpa only [mul_comm] using estimate

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
