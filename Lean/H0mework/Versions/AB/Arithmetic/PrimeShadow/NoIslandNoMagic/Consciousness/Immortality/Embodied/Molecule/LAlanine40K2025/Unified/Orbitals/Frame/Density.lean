import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Coordinates
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Metric.Charge

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient MeasureTheory
open scoped Matrix BigOperators
noncomputable section

variable {n : Type*} [Fintype n]

theorem congruence_bilinear (D T : Matrix n n ℝ) (u v : n → ℝ) :
    u ⬝ᵥ (T * D * T.transpose) *ᵥ v =
      (T.transpose *ᵥ u) ⬝ᵥ D *ᵥ (T.transpose *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose]

/-- The same D3 is retained in the new basis; no new occupation or positivity is supplied. -/
def normalizedDensityMatrix : Matrix Basis Basis ℝ :=
  sourceDualFrame * Matrix.of (fun b c => (densityMatrix b c : ℝ)) * sourceDualFrame.transpose

def normalizedDensity (x : Point) : ℝ :=
  (fun b => normalizedOrbital b x) ⬝ᵥ normalizedDensityMatrix *ᵥ (fun b => normalizedOrbital b x)

theorem normalized_value_vector (x : Point) :
    (fun b => normalizedOrbital b x) = normalizedSourceFrame.transpose *ᵥ (fun b => ao b x) := rfl

theorem original_value_vector (positive : actualGram.PosDef) (x : Point) :
    sourceDualFrame.transpose *ᵥ (fun b => normalizedOrbital b x) = (fun b => ao b x) := by
  rw [normalized_value_vector,Matrix.mulVec_mulVec,← Matrix.transpose_mul,frame_mul_dual positive,
    Matrix.transpose_one,Matrix.one_mulVec]

theorem actual_density_preserved (positive : actualGram.PosDef) (x : Point) :
    normalizedDensity x = sourceDensity x := by
  unfold normalizedDensity normalizedDensityMatrix
  rw [congruence_bilinear,original_value_vector positive]
  simp only [dotProduct,Matrix.mulVec,sourceDensity,SourceGaussianModel.density,bilinear,
    Finset.mul_sum,ao,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  change orbital (sourceTerms b) (fun _ => 0) x * ((densityMatrix b c : ℝ) *
    orbital (sourceTerms c) (fun _ => 0) x) = _
  ring

theorem actual_density_integral_preserved (positive : actualGram.PosDef) :
    (∫ x : Point, normalizedDensity x) = ∫ x : Point, sourceDensity x := by
  simp_rw [actual_density_preserved positive]

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
