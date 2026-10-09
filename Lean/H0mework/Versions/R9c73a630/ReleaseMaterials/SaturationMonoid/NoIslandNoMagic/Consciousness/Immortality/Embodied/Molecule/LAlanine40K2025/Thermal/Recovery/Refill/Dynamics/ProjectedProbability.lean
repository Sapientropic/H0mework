import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.ProjectedOrbit
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.QuadraticEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.ControllerVacancy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.ProjectedProbability

open Collision Powered.Dynamics ProjectedOrbit QuadraticEnergy Load.Producer.StrictThermal
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem support_energy {κ : Type*} [Fintype κ]
    (P A rho : Matrix κ κ ℂ) (left : P * rho = rho) (right : rho * P = rho) :
    energy (P * A * P) rho = energy A rho := by
  unfold energy
  rw [mul_assoc (P * A), left, Matrix.trace_mul_cycle, right, Matrix.trace_mul_comm]

theorem projected_probability_lower (V : ControllerJoint ι) (hV : V.IsHermitian)
    (Q P rho : ControllerJoint ι) (hQ : Q.IsHermitian) (hP : P.IsHermitian)
    (idempotent : Q * Q = Q) (contractive : ‖Q‖ ≤ 1)
    (disjoint : Q * P = 0) (receives : Q * V * P = V * P)
    (positive : rho.PosSemidef) (left : P * rho = rho) (right : rho * P = rho)
    (t : ℝ) (ht : 0 ≤ t) (small : t * ‖V‖ ≤ 1 / 2) :
    t ^ 2 / 4 * energy (Vᴴ * V) rho ≤
      energy Q (Unitary.conjStarAlgAut ℂ (ControllerJoint ι) (interactionUnitary (ι := ι) V hV t) rho) := by
  let U := interactionUnitary V hV t
  let F := Q * (U : ControllerJoint ι) * P
  let G := V * P
  have bounded (x : Space ι) : t / 2 * ‖operator G x‖ ≤ ‖operator F x‖ := by
    have empty : op Q (op P x) = 0 := by
      rw [← mul_apply_eq_comp, ← map_mul, disjoint, map_zero, zero_apply]
    have received : op Q (op V (op P x)) = op V (op P x) := by
      have equality := congrArg (fun A : ControllerJoint ι => op A x) receives
      simpa only [op, map_mul, mul_apply_eq_comp] using equality
    simpa only [F, G, operator, map_mul, mul_apply_eq_comp, U] using
      projected_orbit_lower V hV Q contractive (op P x) empty received t ht small
  have lower := norm_domination_energy F G rho positive (t / 2) (by positivity) bounded
  have Gsquare : Gᴴ * G = P * (Vᴴ * V) * P := by
    simp only [G, Matrix.conjTranspose_mul, hP.eq, mul_assoc]
  have Fsquare : Fᴴ * F = P * ((U : ControllerJoint ι)ᴴ * Q * (U : ControllerJoint ι)) * P := by
    simp only [F, Matrix.conjTranspose_mul, hP.eq, hQ.eq]
    simp only [mul_assoc, ← mul_assoc Q Q, idempotent]
  rw [Gsquare, Fsquare, support_energy P _ rho left right, support_energy P _ rho left right] at lower
  have read : energy ((U : ControllerJoint ι)ᴴ * Q * (U : ControllerJoint ι)) rho =
      energy Q (Unitary.conjStarAlgAut ℂ (ControllerJoint ι) U rho) := by
    have pulled := energy_pullback Q rho U
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at pulled ⊢
    exact pulled.symm
  rw [read] at lower
  convert lower using 1
  ring

end
end LAlanine40K2025.Thermal.Recovery.ProjectedProbability
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
