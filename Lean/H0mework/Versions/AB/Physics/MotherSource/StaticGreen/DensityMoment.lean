import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.SourceMoment

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb GlobalSource SourceFiniteData ContinuousGradient
noncomputable section

def orbitalMomentBound (terms : List Term) (order : MultiIndex) : ℝ :=
  (terms.map (fun term => termMomentBound term order)).sum

theorem orbital_moment_uniform (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (order : MultiIndex) (point : Point) :
    ‖point‖*‖orbital terms order point‖ ≤ orbitalMomentBound terms order := by
  induction terms with
  | nil => simp [orbital, orbitalMomentBound]
  | cons term rest induction =>
    simp only [orbital, orbitalMomentBound, List.map_cons, List.sum_cons]
    apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg point)).trans
    rw [mul_add]
    exact add_le_add (term_moment_uniform term (positive term (by simp)) order point)
      (induction (fun other member => positive other (by simp [member])))

theorem orbital_moment_integrable (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (order : MultiIndex) : Integrable (fun point : Point => ‖point‖*‖orbital terms order point‖) := by
  induction terms with
  | nil => simp [orbital]
  | cons term rest induction =>
    apply ((term_moment_integrable term (positive term (by simp)) order).add
      (induction (fun other member => positive other (by simp [member])))).mono'
      (continuous_norm.mul (orbital_contDiff (term::rest) order 0).continuous.norm).aestronglyMeasurable
    filter_upwards [] with point
    simp only [Pi.mul_apply, norm_mul, norm_norm, orbital, List.map_cons, List.sum_cons, Pi.add_apply]
    exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg point)).trans_eq (mul_add _ _ _)

def densityMomentEnvelope (left right : MultiIndex) (point : Point) : ℝ :=
  ∑ first : Basis, ∑ second : Basis, |(densityMatrix first second : ℝ)| *(sourceOrbitalBound left first : ℝ)*
    (‖point‖*‖orbital (sourceTerms second) right point‖)

def densityMomentBound (left right : MultiIndex) : ℝ :=
  ∑ first : Basis, ∑ second : Basis, |(densityMatrix first second : ℝ)| *(sourceOrbitalBound left first : ℝ)*
    orbitalMomentBound (sourceTerms second) right

theorem density_moment_envelope (left right : MultiIndex) (point : Point) :
    ‖point‖*‖bilinear sourceTerms densityMatrix left right point‖ ≤ densityMomentEnvelope left right point := by
  unfold bilinear densityMomentEnvelope
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg point)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro first _
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg point)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro second _
  simp only [norm_mul, Real.norm_eq_abs]
  have original := mul_le_mul_of_nonneg_right (source_orbital_uniform_bound left first point)
    (show 0 ≤ ‖point‖*|(densityMatrix first second : ℝ)| *|orbital (sourceTerms second) right point| by positivity)
  nlinarith

theorem density_moment_envelope_integrable (left right : MultiIndex) : Integrable (densityMomentEnvelope left right) := by
  unfold densityMomentEnvelope
  apply integrable_finsetSum
  intro first _
  apply integrable_finsetSum
  intro second _
  exact (orbital_moment_integrable (sourceTerms second) (source_exponents_positive second) right).const_mul _

theorem density_moment_integrable (left right : MultiIndex) :
    Integrable (fun point : Point => ‖point‖*‖bilinear sourceTerms densityMatrix left right point‖) := by
  apply (density_moment_envelope_integrable left right).mono'
    (continuous_norm.mul (bilinear_contDiff sourceTerms densityMatrix left right 0).continuous.norm).aestronglyMeasurable
  filter_upwards [] with point
  simpa only [Pi.mul_apply, norm_mul, norm_norm] using density_moment_envelope left right point

theorem density_moment_uniform (left right : MultiIndex) (point : Point) :
    ‖point‖*‖bilinear sourceTerms densityMatrix left right point‖ ≤ densityMomentBound left right := by
  apply (density_moment_envelope left right point).trans
  unfold densityMomentEnvelope densityMomentBound
  apply Finset.sum_le_sum
  intro first _
  apply Finset.sum_le_sum
  intro second _
  exact mul_le_mul_of_nonneg_left
    (orbital_moment_uniform (sourceTerms second) (source_exponents_positive second) right point) (by positivity)

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
