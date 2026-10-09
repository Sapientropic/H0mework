import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.ChangeVariables
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Flow.Speed
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
open SourceGaussianModel GlobalSource GlobalSource.Differential Set MeasureTheory
noncomputable section

structure Test where
  value : Point → ℝ
  smooth : ContDiff ℝ 1 value
  compact : HasCompactSupport value

def Test.derivative (test : Test) : Point → Point →L[ℝ] ℝ := fderiv ℝ test.value

theorem Test.hasFDerivAt (test : Test) (x : Point) : HasFDerivAt test.value (test.derivative x) x :=
  (test.smooth.differentiable (by norm_num) x).hasFDerivAt

theorem Test.integrable (test : Test) : Integrable test.value :=
  test.smooth.continuous.integrable_of_hasCompactSupport test.compact

theorem Test.derivative_continuous (test : Test) : Continuous test.derivative :=
  test.smooth.continuous_fderiv (by norm_num)

theorem Test.bounds (test : Test) : ∃ R > 0, ∃ A ≥ 0, ∃ B ≥ 0,
    (∀ x, ‖test.value x‖ ≤ A) ∧ (∀ x, ‖test.derivative x‖ ≤ B) ∧
    (∀ x, R < ‖x‖ → test.value x = 0 ∧ test.derivative x = 0) := by
  obtain ⟨R,positive,region⟩ := test.compact.isBounded.exists_pos_norm_le
  obtain ⟨A,value⟩ := test.compact.exists_bound_of_continuous test.smooth.continuous
  obtain ⟨B,derivative⟩ := (test.compact.fderiv ℝ).exists_bound_of_continuous test.derivative_continuous
  refine ⟨R,positive,max A 0,le_max_right _ _,max B 0,le_max_right _ _,
    fun x => (value x).trans (le_max_left _ _),fun x => (derivative x).trans (le_max_left _ _),?_⟩
  intro x outside
  have notIn : x ∉ tsupport test.value := fun member => (region x member).not_gt outside
  exact ⟨image_eq_zero_of_notMem_tsupport notIn,
    image_eq_zero_of_notMem_tsupport (fun member => notIn (tsupport_fderiv_subset ℝ member))⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
