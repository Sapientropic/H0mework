import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformGainWeighted
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

private theorem ordinary_quadratic_error (a b : Basis) (ordered : a < b)
    (WI : MatrixInt (Fin 2 × Fin 2) (OrdinaryFull ⊕ OrdinaryFull))
    (VI : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2))
    (V : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2))
    (eW eV : ℝ)
    (weightedError : ‖value WI-(qvalue V)ᴴ *
      qvalue (ordinaryPCPointerQ a b)‖ ≤ eW)
    (inputError : ‖value VI-qvalue V‖ ≤ eV)
    (inputNorm : ‖qvalue V‖ ≤ (24 : ℝ)) :
    ‖value (multiply WI VI)-
      ((qvalue V)ᴴ * qvalue (ordinaryPCPointerQ a b)) * qvalue V‖ ≤
      (64/10^30 : ℝ)+eW*(24+eV)+2136*eV := by
  have weightedNorm : ‖(qvalue V)ᴴ * qvalue (ordinaryPCPointerQ a b)‖ ≤
      (2136 : ℝ) := by
    have adjNorm : ‖(qvalue V)ᴴ‖ ≤ (24 : ℝ) := by
      simpa only [Matrix.l2_opNorm_conjTranspose] using inputNorm
    exact (Matrix.l2_opNorm_mul _ _).trans
      ((mul_le_mul adjNorm (source_ordinary_pc_norm a b ordered)
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 24)).trans (by norm_num))
  have paid := rectangular_int_mul_error WI VI
    ((qvalue V)ᴴ * qvalue (ordinaryPCPointerQ a b)) (qvalue V)
    (by norm_num) (by norm_num) eW eV weightedError inputError
  have ewNonnegative : 0 ≤ eW := le_trans (norm_nonneg _) weightedError
  have evNonnegative : 0 ≤ eV := le_trans (norm_nonneg _) inputError
  apply paid.trans
  gcongr

theorem source_ordinary_quadratic_errors (a b : Basis) (ordered : a < b) :
    ‖value (multiply
        (multiply (adjoint (sourceOrdinaryNineSelectedInt a b ordered))
          (sourceOrdinaryPCInt a b))
        (sourceOrdinaryNineSelectedInt a b ordered))-
      ((qvalue ((ordinaryNineColumnsQ a b ordered).submatrix id chargedInjection))ᴴ *
        qvalue (ordinaryPCPointerQ a b)) *
        qvalue ((ordinaryNineColumnsQ a b ordered).submatrix id chargedInjection)‖ ≤
      (3/10^10 : ℝ) ∧
    ‖value (multiply
        (multiply (adjoint (sourceOrdinaryElevenSelectedInt a b ordered))
          (sourceOrdinaryPCInt a b))
        (sourceOrdinaryElevenSelectedInt a b ordered))-
      ((qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection))ᴴ *
        qvalue (ordinaryPCPointerQ a b)) *
        qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection)‖ ≤
      (5/10^9 : ℝ) := by
  have weighted := source_ordinary_weighted_errors a b ordered
  have selected := source_ordinary_selected_errors a b ordered
  have norm := source_ordinary_selected_norms_24 a b ordered
  constructor
  · have h := ordinary_quadratic_error a b ordered
      (multiply (adjoint (sourceOrdinaryNineSelectedInt a b ordered))
        (sourceOrdinaryPCInt a b)) (sourceOrdinaryNineSelectedInt a b ordered)
      ((ordinaryNineColumnsQ a b ordered).submatrix id chargedInjection)
      (5/10^12) (4/10^14) weighted.1 selected.1 norm.1
    exact h.trans (by norm_num)
  · have h := ordinary_quadratic_error a b ordered
      (multiply (adjoint (sourceOrdinaryElevenSelectedInt a b ordered))
        (sourceOrdinaryPCInt a b)) (sourceOrdinaryElevenSelectedInt a b ordered)
      ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection)
      (1/10^10) (1/10^12) weighted.2 selected.2 norm.2
    exact h.trans (by norm_num)

theorem source_ordinary_net_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryNetInt a b ordered)-
      sourceOrdinaryQNet a b ordered‖ ≤ (6/10^9 : ℝ) := by
  rw [sourceOrdinaryNetInt,value_sub,sourceOrdinaryQNet]
  have split (A B C D : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      (A-B)-(C-D)=(A-C)-(B-D) := by abel
  rw [split]
  have errors := source_ordinary_quadratic_errors a b ordered
  exact (norm_sub_le _ _).trans
    ((add_le_add errors.2 errors.1).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
