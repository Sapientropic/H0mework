import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Second.Assembly
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Nondegenerate
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Overlap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData OriginalMetric
open scoped Matrix BigOperators
noncomputable section

theorem recorded_gram_entry (i j : Basis) :
    (realInverse.transpose*realRecorded*realInverse) i j = (Second.retainedGram i j : ℝ) := by
  rw [Second.retainedGram_computed]
  simp only [secondProduct,First.retainedProduct_computed,firstProduct,Rat.cast_sum,Rat.cast_mul]
  rw [Matrix.mul_assoc,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.transpose_apply,Matrix.mul_apply,realInverse,realRecorded]

theorem recorded_gram_error (i j : Basis) :
    |(realInverse.transpose*realRecorded*realInverse) i j-(if i=j then 1 else 0)| ≤ (1/10^10 : ℝ) := by
  rw [recorded_gram_entry]
  have bound := Second.retainedGram_error i j
  by_cases same : i=j
  · simp only [if_pos same] at bound ⊢
    have realBound : ((|Second.retainedGram i j-1| : ℚ) : ℝ) ≤ ((1/10^10 : ℚ) : ℝ) := Rat.cast_le.mpr bound
    norm_num only [Rat.cast_abs,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at realBound
    norm_num at realBound ⊢
    exact realBound
  · simp only [if_neg same] at bound ⊢
    have realBound : ((|Second.retainedGram i j-0| : ℚ) : ℝ) ≤ ((1/10^10 : ℚ) : ℝ) := Rat.cast_le.mpr bound
    norm_num only [Rat.cast_abs,Rat.cast_sub,Rat.cast_zero,Rat.cast_one,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at realBound
    norm_num at realBound ⊢
    exact realBound

theorem actual_gram_entry_error (i j : Basis) : |(actualGram-1) i j| ≤ (2/10^9 : ℝ) := by
  have sourceError := actual_gram_error (1/10^12)
    (fun b c => by
      simpa only [realRecorded,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using original_overlap_error b c) i j
  have first : (columnSize i : ℝ) ≤ 40 := by exact_mod_cast First.columnSize_bound i
  have second : (columnSize j : ℝ) ≤ 40 := by exact_mod_cast First.columnSize_bound j
  have nonnegative (b : Basis) : 0 ≤ (columnSize b : ℝ) := by
    unfold columnSize
    positivity
  have actual : |actualGram i j-(realInverse.transpose*realRecorded*realInverse) i j| ≤ (16/10^10 : ℝ) := by
    apply sourceError.trans
    nlinarith [mul_le_mul first second (nonnegative j) (by norm_num : (0 : ℝ) ≤ 40)]
  have recorded := recorded_gram_error i j
  have triangle := abs_sub_le (actualGram i j) ((realInverse.transpose*realRecorded*realInverse) i j)
    (if i=j then 1 else 0)
  simp only [Matrix.sub_apply,Matrix.one_apply]
  linarith

theorem actual_gram_positive : actualGram.PosDef :=
  positive_of_entry_error actualGram actual_gram_symmetric (2/10^9) (by norm_num)
    (by norm_num [Fintype.card_fin]) actual_gram_entry_error

theorem actual_original_metric_positive : originalMetric.PosDef := original_metric_positive actual_gram_positive

theorem actual_original_inverse_injective : Function.Injective realInverse.mulVec :=
  inverse_injective_from_actual_gram actual_gram_positive

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
