import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.TailPositive.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformGainConsumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem positive_norm_le_trace_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) :
    ‖rho‖ ≤ rho.trace.re := by
  let hH := positive.isHermitian
  have same := StarAlgEquiv.norm_map
    (Unitary.conjStarAlgAut ℂ _ (star hH.eigenvectorUnitary)) rho
  rw [hH.conjStarAlgAut_star_eigenvectorUnitary,
    Matrix.l2_opNorm_diagonal] at same
  have trace : (∑ j, hH.eigenvalues j)=rho.trace.re := by
    rw [hH.trace_eq_sum_eigenvalues,Complex.re_sum]
    simp
  have traceNonneg : (0 : ℝ) ≤ rho.trace.re := by
    rw [← trace]
    exact Finset.sum_nonneg (fun j _ => positive.eigenvalues_nonneg j)
  rw [← same]
  apply pi_norm_le_iff_of_nonneg traceNonneg |>.mpr
  intro i
  have bound : hH.eigenvalues i ≤ ∑ j,hH.eigenvalues j :=
    Finset.single_le_sum (fun j _ => positive.eigenvalues_nonneg j)
      (Finset.mem_univ i)
  rw [trace] at bound
  simpa only [Function.comp_apply,RCLike.norm_ofReal,Real.norm_eq_abs,
    abs_of_nonneg (positive.eigenvalues_nonneg i)] using bound

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
