import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerColumns.Base
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator

noncomputable section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq ι] in
theorem rectangular_int_mul_error (AI : MatrixInt ι κ) (BI : MatrixInt κ ν)
    (A : Matrix ι κ ℂ) (B : Matrix κ ν ℂ)
    (rows : Fintype.card ι ≤ 64) (cols : Fintype.card ν ≤ 64)
    (eA eB : ℝ) (ha : ‖value AI-A‖ ≤ eA) (hb : ‖value BI-B‖ ≤ eB) :
    ‖value (multiply AI BI)-A*B‖ ≤
      (64/10^30 : ℝ)+eA*(‖B‖+eB)+‖A‖*eB := by
  have biBound : ‖value BI‖ ≤ ‖B‖+eB := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub (value BI) B 0
    simp only [sub_zero] at triangle
    linarith only [triangle,hb]
  have split : value AI*value BI-A*B=(value AI-A)*value BI+A*(value BI-B) := by
    simp only [Matrix.sub_mul,Matrix.mul_sub]
    abel
  have ae : 0 ≤ eA := le_trans (norm_nonneg _) ha
  have product : ‖value AI*value BI-A*B‖ ≤ eA*(‖B‖+eB)+‖A‖*eB := by
    rw [split]
    calc
      _ ≤ ‖(value AI-A)*value BI‖+‖A*(value BI-B)‖ := norm_add_le _ _
      _ ≤ ‖value AI-A‖*‖value BI‖+‖A‖*‖value BI-B‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
      _ ≤ _ := by gcongr
  calc
    _ ≤ ‖value (multiply AI BI)-value AI*value BI‖+
      ‖value AI*value BI-A*B‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (64/10^30 : ℝ)+(eA*(‖B‖+eB)+‖A‖*eB) :=
      add_le_add (multiply_error AI BI rows cols) product
    _ = _ := by ring

theorem submatrix_error_le {α μ ν : Type*} [Fintype α] [DecidableEq α]
    [Fintype μ] [Fintype ν] [DecidableEq ν]
    (M N : Matrix α α ℂ) (f : μ → α) (g : ν → α)
    (rows : Fintype.card μ ≤ 64) (cols : Fintype.card ν ≤ 64)
    (eps : ℝ) (paid : ‖M-N‖ ≤ eps) :
    ‖M.submatrix f g-N.submatrix f g‖ ≤ 64*eps := by
  have nonnegative : 0 ≤ eps := le_trans (norm_nonneg _) paid
  apply norm_from_entries _ eps nonnegative rows cols
  intro i j
  change ‖(M-N) (f i) (g j)‖ ≤ eps
  exact (matrix_entry_norm_le (M-N) _ _).trans paid

theorem submatrix_norm_le64 {α μ ν : Type*} [Fintype α] [DecidableEq α]
    [Fintype μ] [Fintype ν] [DecidableEq ν]
    (M : Matrix α α ℂ) (f : μ → α) (g : ν → α)
    (rows : Fintype.card μ ≤ 64) (cols : Fintype.card ν ≤ 64) :
    ‖M.submatrix f g‖ ≤ 64*‖M‖ :=
  norm_from_entries _ ‖M‖ (norm_nonneg _) rows cols
    (fun i j => matrix_entry_norm_le M (f i) (g j))
end


end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
