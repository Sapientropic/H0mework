import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformGainSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SourceNorms
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

theorem source_ordinary_pc_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (ordinaryPCPointerQ a b)‖ ≤ (89 : ℝ) := by
  rw [← ordinary_pc_pointer_source a b ordered,qvalue_submatrix,
    Spec.pcObservable_value]
  have inj := source_ordinary_pointer_address_injective a b ordered
  exact (submatrix_norm_le Post.finitePCObservable _ _ inj inj).trans
    Post.finite_PC_observable_norm

private theorem ordinary_local_action_norm (a b : Basis) (ordered : a < b)
    (P : PointerJoint) (kept : Preserves Sectors.pointerOrbit P)
    (bound : ‖P‖ ≤ (4 : ℝ)) :
    ‖(restrict Sectors.pointerOrbit (donorSector (s(a,b))) P).submatrix
      (coordinatePointer (s(a,b)) (ordinaryFullEquiv a b ordered.ne))
      (coordinatePointer (s(a,b)) (ordinaryFullEquiv a b ordered.ne))‖ ≤
      (4 : ℝ) := by
  rw [Finite.reindex_norm]
  exact ((norm_le_iff_block_norm_le kept 4 (by norm_num)).mp bound) _

theorem source_ordinary_nine_norm_24 (a b : Basis) (ordered : a < b) :
    ‖qvalue (ordinaryNineColumnsQ a b ordered)‖ ≤ (24 : ℝ) := by
  rw [ordinary_nine_columns_value a b ordered]
  let k := s(a,b)
  let body := Scaled.Order.offDiagonalPCEEquiv a b ordered.ne
  let full := ordinaryFullEquiv a b ordered.ne
  have same : nineColumns k body full ordinaryInjection =
      ((localNine k).submatrix (coordinatePointer k full)
        (coordinatePointer k full))*entranceColumns k body full ordinaryInjection := by
    rw [coordinate_nine]
    simp only [nineColumns,Matrix.mul_assoc]
  rw [same]
  have action : ‖(localNine k).submatrix (coordinatePointer k full)
      (coordinatePointer k full)‖ ≤ (4 : ℝ) :=
    ordinary_local_action_norm a b ordered LoadExecution.nine nine_preserves
      LoadExecution.nine_norm
  have entrance : ‖entranceColumns k body full ordinaryInjection‖ ≤ (6 : ℝ) := by
    rw [← ordinary_entrance_value a b ordered]
    exact source_ordinary_entrance_norm a b ordered
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul action entrance (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 4)).trans (by norm_num))

theorem source_ordinary_eleven_norm_24 (a b : Basis) (ordered : a < b) :
    ‖qvalue (ordinaryElevenColumnsQ a b ordered)‖ ≤ (24 : ℝ) := by
  rw [ordinary_eleven_columns_value a b ordered]
  let k := s(a,b)
  let body := Scaled.Order.offDiagonalPCEEquiv a b ordered.ne
  let full := ordinaryFullEquiv a b ordered.ne
  have same : elevenColumns k body full ordinaryInjection =
      ((localEleven k).submatrix (coordinatePointer k full)
        (coordinatePointer k full))*entranceColumns k body full ordinaryInjection := by
    rw [coordinate_eleven,coordinate_nine]
    simp only [elevenColumns,nineColumns,Matrix.mul_assoc]
  rw [same]
  have action : ‖(localEleven k).submatrix (coordinatePointer k full)
      (coordinatePointer k full)‖ ≤ (4 : ℝ) :=
    ordinary_local_action_norm a b ordered LoadExecution.eleven eleven_preserves
      LoadExecution.eleven_norm
  have entrance : ‖entranceColumns k body full ordinaryInjection‖ ≤ (6 : ℝ) := by
    rw [← ordinary_entrance_value a b ordered]
    exact source_ordinary_entrance_norm a b ordered
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul action entrance (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 4)).trans (by norm_num))

theorem source_ordinary_selected_norms_24 (a b : Basis) (ordered : a < b) :
    ‖qvalue ((ordinaryNineColumnsQ a b ordered).submatrix id chargedInjection)‖ ≤
      (24 : ℝ) ∧
    ‖qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection)‖ ≤
      (24 : ℝ) := by
  constructor <;> rw [qvalue_submatrix]
  · exact (submatrix_columns_norm_le _ chargedInjection
      charged_injection_injective).trans (source_ordinary_nine_norm_24 a b ordered)
  · exact (submatrix_columns_norm_le _ chargedInjection
      charged_injection_injective).trans (source_ordinary_eleven_norm_24 a b ordered)

theorem source_ordinary_pair_address_injective (a b : Basis) (ordered : a < b) :
    Function.Injective (pairAddress a b) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [pairAddress,ordered.ne] at h ⊢

theorem source_ordinary_body_norm_10 (a b : Basis) (ordered : a < b) :
    ‖qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)‖ ≤ (10 : ℝ) := by
  rw [qvalue_kron,ordinary_pair_block_value,environmentQ_value]
  have pairNorm : ‖InputProducts.pair‖ ≤ (5 : ℝ) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub InputProducts.pair
      Field.computedPair 0
    simp only [sub_zero] at triangle
    rw [norm_sub_rev] at triangle
    linarith only [triangle,InputProducts.pair_error,PCExecution.field_pair_norm]
  have blockNorm : ‖originalPairBlock a b‖ ≤ (5 : ℝ) := by
    rw [originalPairBlock]
    have inj := source_ordinary_pair_address_injective a b ordered
    exact (submatrix_norm_le InputProducts.pair _ _ inj inj).trans pairNorm
  exact (kronecker_norm_le _ _).trans
    ((mul_le_mul blockNorm Diagonal.finite_environment_norm (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 5)).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
