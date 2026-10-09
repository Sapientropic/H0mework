import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction.Bound
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

structure Material where
  parent : Interaction.Material
  trueFirst : Matrix Basis Basis ℝ
  recordedFirst : Matrix Basis Basis ℝ
  firstDefect : Matrix Basis Basis ℝ
  correction : Matrix Basis Basis ℝ
  trueD3 : Matrix Basis Basis ℝ
  recordedD3 : Matrix Basis Basis ℝ

def material : Material where
  parent := Interaction.material
  trueFirst := trueFirst
  recordedFirst := recordedFirst
  firstDefect := firstDefect
  correction := actualCorrection
  trueD3 := trueD3
  recordedD3 := recordedD3

theorem parent_identity : material.parent = Interaction.material := rfl
theorem first_source : material.trueFirst = originalMetric * realInverse ∧
    material.recordedFirst = realRecorded * realInverse := ⟨rfl,rfl⟩
theorem first_error (i j : Basis) :
    |material.firstDefect i j| ≤ (4 / 10^11 : ℝ) := first_defect_entry_error i j
theorem correction_error :
    ‖complexMatrix material.correction - 1‖ ≤ (392 / 10^9 : ℝ) :=
  correction_complex_norm_error
theorem actual_D3_from_source :
    normalizedDensityMatrix = material.correction.transpose *
      material.trueD3 * material.correction := actual_D3_factor
theorem true_recorded_difference : material.trueD3 - material.recordedD3 =
    material.firstDefect.transpose * d3AO * material.trueFirst +
      material.recordedFirst.transpose * d3AO * material.firstDefect :=
  raw_D3_difference
theorem total_D3_difference : normalizedDensityMatrix - material.recordedD3 =
    (material.correction.transpose * material.trueD3 * material.correction -
      material.trueD3) +
      (material.firstDefect.transpose * d3AO * material.trueFirst +
        material.recordedFirst.transpose * d3AO * material.firstDefect) :=
  actual_recorded_D3_difference

structure Closure : Prop where
  parent : Interaction.Closure
  parentIdentity : type_of% parent_identity
  firstSource : type_of% first_source
  firstError : type_of% first_error
  correctionError : type_of% correction_error
  actualD3 : type_of% actual_D3_from_source
  recordedDifference : type_of% true_recorded_difference
  totalDifference : type_of% total_D3_difference

theorem sourceGeneratedClosure : Closure :=
  ⟨Interaction.sourceGeneratedClosure,parent_identity,first_source,first_error,
    correction_error,actual_D3_from_source,true_recorded_difference,
    total_D3_difference⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
