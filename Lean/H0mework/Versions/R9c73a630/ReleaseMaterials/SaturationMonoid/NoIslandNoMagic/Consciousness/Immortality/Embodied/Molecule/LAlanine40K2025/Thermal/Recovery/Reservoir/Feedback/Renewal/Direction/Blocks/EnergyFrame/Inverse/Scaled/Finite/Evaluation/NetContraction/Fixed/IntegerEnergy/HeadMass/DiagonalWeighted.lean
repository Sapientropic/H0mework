import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.DiagonalSelected
set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Collision Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

private theorem diagonal_weighted_error (a : Basis) (different : a ≠ 97)
    (VI : MatrixInt (DiagonalFull ⊕ DiagonalFull) (Fin 2))
    (V : MatrixQ (DiagonalFull ⊕ DiagonalFull) (Fin 2))
    (e n : ℝ) (inputError : ‖value VI-qvalue V‖ ≤ e)
    (inputNorm : ‖qvalue V‖ ≤ n) :
    ‖value (multiply (adjoint VI) (sourceDiagonalPCInt a different))-
      (qvalue V)ᴴ*qvalue (coordinatePCQ (s(a,a))
        (diagonalFullEquiv a different))‖ ≤
      (64/10^30 : ℝ)+e*(89+64/10^30)+n*(64/10^30) := by
  have adjError : ‖value (adjoint VI)-(qvalue V)ᴴ‖ ≤ e := by
    rw [value_adjoint,← Matrix.conjTranspose_sub,Matrix.l2_opNorm_conjTranspose]
    exact inputError
  have paid := rectangular_int_mul_error (adjoint VI)
    (sourceDiagonalPCInt a different) ((qvalue V)ᴴ)
    (qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different)))
    (by norm_num) (by norm_num [DiagonalFull]) e (64/10^30)
    adjError (source_diagonal_pc_int_error a different)
  have eNonnegative : 0 ≤ e := le_trans (norm_nonneg _) inputError
  apply paid.trans
  gcongr
  · exact source_diagonal_pc_norm a different
  · simpa only [Matrix.l2_opNorm_conjTranspose] using inputNorm

theorem source_diagonal_weighted_errors (a : Basis) (different : a ≠ 97) :
    ‖value (multiply (adjoint (sourceDiagonalNineSelectedInt a different))
        (sourceDiagonalPCInt a different))-
      (qvalue (sourceDiagonalNineSelectedQ a different))ᴴ *
        qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))‖ ≤
      (2/10^23 : ℝ) ∧
    ‖value (multiply (adjoint (sourceDiagonalElevenSelectedInt a different))
        (sourceDiagonalPCInt a different))-
      (qvalue (sourceDiagonalElevenSelectedQ a different))ᴴ *
        qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))‖ ≤
      (5/10^22 : ℝ) := by
  have selected := source_diagonal_selected_errors a different
  have norm := source_diagonal_selected_norms a different
  constructor
  · exact (diagonal_weighted_error a different
      (sourceDiagonalNineSelectedInt a different)
      (sourceDiagonalNineSelectedQ a different) (2/10^25) 384
      selected.1 norm.1).trans (by norm_num)
  · exact (diagonal_weighted_error a different
      (sourceDiagonalElevenSelectedInt a different)
      (sourceDiagonalElevenSelectedQ a different) (5/10^24) 6144
      selected.2 norm.2).trans (by norm_num)

private theorem diagonal_quadratic_error (a : Basis) (different : a ≠ 97)
    (WI : MatrixInt (Fin 2) (DiagonalFull ⊕ DiagonalFull))
    (VI : MatrixInt (DiagonalFull ⊕ DiagonalFull) (Fin 2))
    (V : MatrixQ (DiagonalFull ⊕ DiagonalFull) (Fin 2))
    (eW eV n : ℝ)
    (weightedError : ‖value WI-(qvalue V)ᴴ *
      qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))‖ ≤ eW)
    (inputError : ‖value VI-qvalue V‖ ≤ eV)
    (inputNorm : ‖qvalue V‖ ≤ n) :
    ‖value (multiply WI VI)-
      ((qvalue V)ᴴ * qvalue (coordinatePCQ (s(a,a))
        (diagonalFullEquiv a different))) * qvalue V‖ ≤
      (64/10^30 : ℝ)+eW*(n+eV)+(89*n)*eV := by
  have weightedNorm : ‖(qvalue V)ᴴ *
      qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))‖ ≤
      89*n := by
    have adjNorm : ‖(qvalue V)ᴴ‖ ≤ n := by
      simpa only [Matrix.l2_opNorm_conjTranspose] using inputNorm
    calc
      _ ≤ ‖(qvalue V)ᴴ‖ *
        ‖qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ n*89 := mul_le_mul adjNorm (source_diagonal_pc_norm a different)
        (norm_nonneg _) (le_trans (norm_nonneg _) inputNorm)
      _ = 89*n := by ring
  have paid := rectangular_int_mul_error WI VI
    ((qvalue V)ᴴ * qvalue (coordinatePCQ (s(a,a))
      (diagonalFullEquiv a different))) (qvalue V)
    (by norm_num) (by norm_num) eW eV weightedError inputError
  have ewNonnegative : 0 ≤ eW := le_trans (norm_nonneg _) weightedError
  have evNonnegative : 0 ≤ eV := le_trans (norm_nonneg _) inputError
  apply paid.trans
  gcongr

theorem source_diagonal_quadratic_errors (a : Basis) (different : a ≠ 97) :
    ‖value (multiply
        (multiply (adjoint (sourceDiagonalNineSelectedInt a different))
          (sourceDiagonalPCInt a different))
        (sourceDiagonalNineSelectedInt a different))-
      ((qvalue (sourceDiagonalNineSelectedQ a different))ᴴ *
        qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))) *
        qvalue (sourceDiagonalNineSelectedQ a different)‖ ≤
      (2/10^20 : ℝ) ∧
    ‖value (multiply
        (multiply (adjoint (sourceDiagonalElevenSelectedInt a different))
          (sourceDiagonalPCInt a different))
        (sourceDiagonalElevenSelectedInt a different))-
      ((qvalue (sourceDiagonalElevenSelectedQ a different))ᴴ *
        qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))) *
        qvalue (sourceDiagonalElevenSelectedQ a different)‖ ≤
      (6/10^18 : ℝ) := by
  have weighted := source_diagonal_weighted_errors a different
  have selected := source_diagonal_selected_errors a different
  have norm := source_diagonal_selected_norms a different
  constructor
  · exact (diagonal_quadratic_error a different
      (multiply (adjoint (sourceDiagonalNineSelectedInt a different))
        (sourceDiagonalPCInt a different))
      (sourceDiagonalNineSelectedInt a different)
      (sourceDiagonalNineSelectedQ a different)
      (2/10^23) (2/10^25) 384 weighted.1 selected.1 norm.1).trans
        (by norm_num)
  · exact (diagonal_quadratic_error a different
      (multiply (adjoint (sourceDiagonalElevenSelectedInt a different))
        (sourceDiagonalPCInt a different))
      (sourceDiagonalElevenSelectedInt a different)
      (sourceDiagonalElevenSelectedQ a different)
      (5/10^22) (5/10^24) 6144 weighted.2 selected.2 norm.2).trans
        (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
