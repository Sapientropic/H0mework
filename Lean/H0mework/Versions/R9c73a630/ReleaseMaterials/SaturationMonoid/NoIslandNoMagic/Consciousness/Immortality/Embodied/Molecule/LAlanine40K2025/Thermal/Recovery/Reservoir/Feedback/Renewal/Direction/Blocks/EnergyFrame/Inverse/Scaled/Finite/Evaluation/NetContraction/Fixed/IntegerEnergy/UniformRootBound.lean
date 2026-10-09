import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerRoot.Core
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.OrdinaryPair
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem factor_norm_two_of_effect {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℚ} (G : SquareRoot.RootGram A B)
    (positive : 0 ≤ cast A B) (complement : 0 ≤ (1 : Matrix ι ι ℂ)-cast A B) :
    ‖qvalue (factorQ G)‖ ≤ (2 : ℝ) := by
  let E := cast A B
  let F := qvalue (factorQ G)
  have leOne : E ≤ 1 := sub_nonneg.mp complement
  have normE : ‖E‖ ≤ (1 : ℝ) :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg E positive).mpr leOne
  have sqrtNorm : ‖CFC.sqrt E‖ ≤ (1 : ℝ) := by
    rw [CFC.norm_sqrt E positive]
    exact Real.sqrt_le_one.mpr normE
  have rootError : ‖CFC.sqrt E-G.value‖ ≤ (2/10^7 : ℝ) := G.error positive
  have normG : ‖G.value‖ ≤ (2 : ℝ) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub G.value (CFC.sqrt E) 0
    simp only [sub_zero] at triangle
    rw [norm_sub_rev] at triangle
    linarith only [triangle,rootError,sqrtNorm]
  have same : G.value=F*Fᴴ := by
    rfl
  have square : ‖F‖*‖F‖ ≤ (2 : ℝ) := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self Fᴴ
    simp only [Matrix.conjTranspose_conjTranspose,
      Matrix.l2_opNorm_conjTranspose] at h
    rw [same] at normG
    linarith only [h,normG]
  nlinarith [norm_nonneg F]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
