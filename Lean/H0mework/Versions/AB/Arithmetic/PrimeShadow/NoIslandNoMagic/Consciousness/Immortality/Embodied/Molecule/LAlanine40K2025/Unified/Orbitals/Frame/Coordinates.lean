import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Orbitals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient
open scoped Matrix BigOperators
noncomputable section

/-- The dual comes from the actual spatial metric and the source-generated normalized frame. -/
def sourceDualFrame : Matrix Basis Basis ℝ := normalizedSourceFrame.transpose * originalMetric

theorem dual_mul_frame (positive : actualGram.PosDef) :
    sourceDualFrame * normalizedSourceFrame = 1 := normalized_original_metric positive

theorem normalized_frame_isUnit (positive : actualGram.PosDef) : IsUnit normalizedSourceFrame :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse (dual_mul_frame positive))

theorem frame_mul_dual (positive : actualGram.PosDef) :
    normalizedSourceFrame * sourceDualFrame = 1 := by
  have invertible := (normalized_frame_isUnit positive).invertible
  have dual : sourceDualFrame = normalizedSourceFrame⁻¹ := by
    calc
      _ = sourceDualFrame * normalizedSourceFrame * normalizedSourceFrame⁻¹ := by simp
      _ = normalizedSourceFrame⁻¹ := by rw [dual_mul_frame positive,Matrix.one_mul]
  rw [dual]
  simp

theorem normalized_expansion (v : Basis → ℝ) (x : Point) :
    ∑ b : Basis, v b * normalizedOrbital b x = expansion (normalizedSourceFrame *ᵥ v) x := by
  simp only [normalizedOrbital,expansion,Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem original_expansion_recovered (positive : actualGram.PosDef) (v : Basis → ℝ) (x : Point) :
    ∑ b : Basis, (sourceDualFrame *ᵥ v) b * normalizedOrbital b x = expansion v x := by
  rw [normalized_expansion,Matrix.mulVec_mulVec,frame_mul_dual positive,Matrix.one_mulVec]

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
