import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Bridge

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel
open scoped Matrix
noncomputable section

def d3AO : Matrix Basis Basis ℝ := Matrix.of (fun i k => (densityMatrix i k : ℝ))
def trueFirst : Matrix Basis Basis ℝ := originalMetric * realInverse
def recordedFirst : Matrix Basis Basis ℝ := realRecorded * realInverse
def firstDefect : Matrix Basis Basis ℝ := trueFirst - recordedFirst
def trueD3 : Matrix Basis Basis ℝ := trueFirst.transpose * d3AO * trueFirst
def recordedD3 : Matrix Basis Basis ℝ := recordedFirst.transpose * d3AO * recordedFirst
def actualCorrection : Matrix Basis Basis ℝ := metricCorrection actualGram

theorem metric_symmetric : originalMetric.transpose = originalMetric := by
  ext i k
  simpa only [originalMetric,Matrix.of_apply,Matrix.transpose_apply] using overlap_symmetric k i

theorem source_dual_factor :
    sourceDualFrame = actualCorrection.transpose * trueFirst.transpose := by
  unfold sourceDualFrame normalizedSourceFrame actualCorrection trueFirst
  rw [Matrix.transpose_mul,Matrix.transpose_mul,metric_symmetric]
  simp only [Matrix.mul_assoc]

theorem source_dual_transpose :
    sourceDualFrame.transpose = trueFirst * actualCorrection := by
  rw [source_dual_factor,Matrix.transpose_mul,Matrix.transpose_transpose,
    Matrix.transpose_transpose]

theorem actual_D3_factor : normalizedDensityMatrix =
    actualCorrection.transpose * trueD3 * actualCorrection := by
  unfold normalizedDensityMatrix trueD3 d3AO
  rw [source_dual_transpose,source_dual_factor]
  simp only [Matrix.mul_assoc]

theorem first_defect_source :
    firstDefect = (originalMetric - realRecorded) * realInverse := by
  simp only [firstDefect,trueFirst,recordedFirst,Matrix.sub_mul]

theorem raw_D3_difference : trueD3 - recordedD3 =
    firstDefect.transpose * d3AO * trueFirst +
      recordedFirst.transpose * d3AO * firstDefect := by
  unfold trueD3 recordedD3 firstDefect
  simp only [Matrix.transpose_sub]
  noncomm_ring

theorem actual_recorded_D3_difference : normalizedDensityMatrix - recordedD3 =
    (actualCorrection.transpose * trueD3 * actualCorrection - trueD3) +
      (firstDefect.transpose * d3AO * trueFirst +
        recordedFirst.transpose * d3AO * firstDefect) := by
  rw [actual_D3_factor,← raw_D3_difference]
  abel

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
