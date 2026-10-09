import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.RaisingMoment
import H0mework.Chemistry.LAlanineThermalDynamics.PairFlowFactorization
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.FlowReadout
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.EnvironmentAlgebra
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.PairPerturbation

open Collision Load.Producer.StrictThermal
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pairUnitary_hasDerivAt (H : SystemMatrix ι) (g t : ℝ) :
    HasDerivAt (pairPropagatorMatrix H g)
      (pairPropagatorMatrix H g t * (-Complex.I • pairH H g)) t := by
  have exponential (s : ℝ) : pairPropagatorMatrix H g s =
      NormedSpace.exp (s • (-Complex.I • pairH H g)) := by
    rw [pairPropagatorMatrix_eq_exp]
    congr 1
    ext i j
    simp [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, mul_left_comm, mul_comm, mul_assoc]
  change HasDerivAt (fun s => pairPropagatorMatrix H g s) _ t
  simpa only [exponential] using hasDerivAt_exp_smul_const (-Complex.I • pairH H g) t

theorem pairAdvance_hasDerivAt (H : SystemMatrix ι) (g t : ℝ) (rho : JointMatrix ι) :
    HasDerivAt (fun s => pairAdvance H g s rho)
      (-Complex.I • (pairH H g * pairAdvance H g t rho - pairAdvance H g t rho * pairH H g)) t := by
  have backward := (pairUnitary_hasDerivAt H g (-t)).scomp t ((hasDerivAt_id t).neg)
  have derivative := ((pairUnitary_hasDerivAt H g t).mul_const rho).mul backward
  simp only [Function.comp_apply, neg_smul, one_smul, mul_neg] at derivative
  apply derivative.congr_deriv
  have commute := (pairPropagatorMatrix_commute H g t (pairH H g) (Commute.refl _)).eq
  simp only [pairAdvance, neg_neg, neg_smul, neg_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [← commute]
  simp only [mul_assoc]
  module

theorem pairEnergy_hasDerivAt (H : SystemMatrix ι) (g t : ℝ) (O rho : JointMatrix ι) :
    HasDerivAt (fun s => energy O (pairAdvance H g s rho))
      (energy (-Complex.I • (O * pairH H g - pairH H g * O)) (pairAdvance H g t rho)) t := by
  have derivative := (energyCLM O).hasFDerivAt.comp_hasDerivAt t (pairAdvance_hasDerivAt H g t rho)
  apply derivative.congr_deriv
  simp only [energyCLM_apply, energy, Matrix.mul_smul, Matrix.trace_smul, trace_energy_commutator,
    Matrix.smul_mul]

theorem energy_drift (H Href : SystemMatrix ι) (hH : H.IsHermitian)
    (g t : ℝ) (ht : 0 ≤ t) (O rho : JointMatrix ι)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1)
    (commutes : Commute O (pairH Href g)) :
    |energy O (pairAdvance H g t rho) - energy O rho| ≤
      2 * ‖O‖ * ‖pairH H g - pairH Href g‖ * t := by
  have commutator : O * pairH H g - pairH H g * O =
      O * (pairH H g - pairH Href g) - (pairH H g - pairH Href g) * O := by
    simp only [mul_sub, sub_mul, commutes.eq]
    abel
  have bound (s : ℝ) :
      ‖energy (-Complex.I • (O * pairH H g - pairH H g * O)) (pairAdvance H g s rho)‖ ≤
        2 * ‖O‖ * ‖pairH H g - pairH Href g‖ := by
    rw [Real.norm_eq_abs]
    apply (energy_abs_le_norm _ _ (pairAdvance_posSemidef H hH g s rho positive)
      ((pairAdvance_trace H hH g s rho).trans normalized)).trans
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul, commutator]
    calc
      _ ≤ ‖O * (pairH H g - pairH Href g)‖ + ‖(pairH H g - pairH Href g) * O‖ := norm_sub_le _ _
      _ ≤ ‖O‖ * ‖pairH H g - pairH Href g‖ + ‖pairH H g - pairH Href g‖ * ‖O‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = _ := by ring
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := t)
    (fun s _ => (pairEnergy_hasDerivAt H g s O rho).hasDerivWithinAt)
    (fun s _ => bound s) t ⟨ht, le_rfl⟩
  simpa only [pairAdvance_zero H hH, sub_zero, Real.norm_eq_abs] using estimate

end
end LAlanine40K2025.Thermal.Recovery.PairPerturbation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
