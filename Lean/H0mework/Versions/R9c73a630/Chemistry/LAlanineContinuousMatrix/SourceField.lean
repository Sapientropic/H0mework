import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousMatrix.IntegerDataComplete
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousMatrix.Readouts
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOComplete
import H0mework.Versions.AB.Chemistry.LAlanineContinuousSource.RK4ReplayData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedMatrix

open SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData SourceRectangleChecks
open ContinuousGradient SourceMatrixField SourceIntegerMatrix IntervalParameterMap SourceCellGeometry

noncomputable section

theorem actual_bilinear_bounds : BilinearBounds (actualBox 0) calculatedBilinear := by
  intro left right x inside
  rw [bilinear_commutes]
  exact bilinearPair_contains (calculatedAO left) (calculatedAO right) densityMatrix sourceTerms
    (multiindex left) (multiindex right) x
    (fun basis => calculatedAO_contains left basis x inside)
    (fun basis => calculatedAO_contains right basis x inside)

theorem actual_first_field (x : Point) (inside : InRectangle (actualBox 0) x) :
    FieldHolds (SourceRK4Replay.recordedField 0) x := by
  constructor
  · intro axis
    change Holds (reportedDensity 0 (firstIndex axis)) (sourceGradient x axis)
    rw [← gradient_eq_source_report]
    exact gradient_contains _ _ actual_bilinear_bounds x inside axis
  · intro axis direction
    change Holds (reportedDensity 0 (secondIndex axis direction)) (sourceHessian x axis direction)
    rw [← hessian_eq_source_report]
    exact hessian_contains _ _ actual_bilinear_bounds x inside axis direction

theorem actual_laplacian (x : Point) (inside : InRectangle (actualBox 0) x) :
    Holds sourceLaplacianBox (SourceGaussianModel.laplacian sourceTerms densityMatrix x) :=
  laplacian_contains _ _ actual_bilinear_bounds x inside

theorem actual_gradient_directions (x : Point) (inside : InRectangle (actualBox 0) x) :
    (47 / 10000 : ℝ) < sourceGradient x 0 ∧
    sourceGradient x 1 < (-56 / 1000 : ℝ) ∧
    (75 / 1000 : ℝ) < sourceGradient x 2 := by
  have h0 := (gradient_contains _ _ actual_bilinear_bounds x inside 0).1
  have h1 := (gradient_contains _ _ actual_bilinear_bounds x inside 1).2
  have h2 := (gradient_contains _ _ actual_bilinear_bounds x inside 2).1
  have lower0 : (47 / 10000 : ℝ) < ((sourceGradientBox 0).1 : ℝ) := by
    have casted : (((47 / 10000 : ℚ) : ℝ)) < ((sourceGradientBox 0).1 : ℝ) :=
      Rat.cast_lt.mpr first_gradient_strictly_positive
    simpa only [Rat.cast_div, Rat.cast_ofNat] using casted
  have upper1 : ((sourceGradientBox 1).2 : ℝ) < (-56 / 1000 : ℝ) := by
    exact_mod_cast second_gradient_strictly_negative
  have lower2 : (75 / 1000 : ℝ) < ((sourceGradientBox 2).1 : ℝ) := by
    have casted : (((75 / 1000 : ℚ) : ℝ)) < ((sourceGradientBox 2).1 : ℝ) :=
      Rat.cast_lt.mpr third_gradient_strictly_positive
    simpa only [Rat.cast_div, Rat.cast_ofNat] using casted
  exact ⟨lower0.trans_le h0, h1.trans_lt upper1, lower2.trans_le h2⟩

theorem actual_no_critical_point (x : Point) (inside : InRectangle (actualBox 0) x) :
    sourceGradient x ≠ 0 := by
  intro zero
  have positive := (actual_gradient_directions x inside).1
  rw [zero, Pi.zero_apply] at positive
  norm_num at positive

theorem actual_negative_laplacian (x : Point) (inside : InRectangle (actualBox 0) x) :
    SourceGaussianModel.laplacian sourceTerms densityMatrix x < (-16 / 100 : ℝ) :=
  (actual_laplacian x inside).2.trans_lt (by exact_mod_cast source_laplacian_strictly_negative)

def sourceWitness : Point := ContinuousParameterMap.initialMap 0 4 (fun i => (cellLowerQ i : ℝ))

theorem sourceWitness_in_rectangle : InRectangle (actualBox 0) sourceWitness := by
  apply cell_initial_position
  exact ⟨le_rfl, fun i => Rat.cast_le.mpr (cell_ordered i).le⟩

def firstFieldClosure : Prop :=
  BilinearBounds (actualBox 0) calculatedBilinear ∧
  (∀ x, InRectangle (actualBox 0) x → FieldHolds (SourceRK4Replay.recordedField 0) x) ∧
  (∀ x, InRectangle (actualBox 0) x → sourceGradient x ≠ 0) ∧
  (∀ x, InRectangle (actualBox 0) x →
    SourceGaussianModel.laplacian sourceTerms densityMatrix x < (-16 / 100 : ℝ)) ∧
  InRectangle (actualBox 0) sourceWitness

theorem sourceGeneratedActualFirstField : firstFieldClosure :=
  ⟨actual_bilinear_bounds, actual_first_field, actual_no_critical_point, actual_negative_laplacian,
    sourceWitness_in_rectangle⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedMatrix
