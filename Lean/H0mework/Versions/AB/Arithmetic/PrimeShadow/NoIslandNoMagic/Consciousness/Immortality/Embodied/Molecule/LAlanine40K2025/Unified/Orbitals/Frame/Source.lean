import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Recorded
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Metric.Congruence

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData OriginalMetric
open scoped BigOperators Matrix
noncomputable section

def firstProduct (i j : Basis) : ℚ := ∑ k : Basis, recordedOverlap i k * recordedInverse k j
def columnSize (i : Basis) : ℚ := ∑ k : Basis, |recordedInverse k i|
def realInverse : Matrix Basis Basis ℝ := fun i j => (recordedInverse i j : ℝ)
def realRecorded : Matrix Basis Basis ℝ := fun i j => (recordedOverlap i j : ℝ)
def originalMetric : Matrix Basis Basis ℝ := Matrix.of overlap
def actualGram : Matrix Basis Basis ℝ := realInverse.transpose * originalMetric * realInverse

theorem actual_gram_symmetric : actualGram.IsHermitian := by
  have original : originalMetric.IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial]
    exact overlap_symmetric j i
  have transpose : realInverse.conjTranspose = realInverse.transpose := by
    ext i j
    simp only [Matrix.conjTranspose_apply,Matrix.transpose_apply,star_trivial]
  simpa only [actualGram,transpose] using
    Matrix.isHermitian_conjTranspose_mul_mul realInverse original

theorem actual_gram_error (error : ℝ) (paid : ∀ i j, |overlap i j-realRecorded i j| ≤ error)
    (i j : Basis) :
    |actualGram i j-(realInverse.transpose*realRecorded*realInverse) i j| ≤
      error*(columnSize i : ℝ)*(columnSize j : ℝ) := by
  have result := Metric.congruence_error originalMetric realRecorded realInverse error paid i j
  simpa only [actualGram,originalMetric,Matrix.of_apply,realInverse,columnSize,Rat.cast_sum,Rat.cast_abs] using result

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
