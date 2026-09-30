import H0mework.Chemistry.LAlanineWholeCell.ReplayProducer
import H0mework.Chemistry.LAlanineWholeCell.PartitionIntegral
import H0mework.Chemistry.LAlanineContinuousSource.SpatialIntegral

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellSpatial

open SourceGaussianModel SourceSignedEvaluator SourceFiniteData WholeCellPartition WholeCellReplay
open ContinuousParameterMap IntervalParameterMap Set MeasureTheory
open scoped BigOperators

noncomputable section
attribute [local irreducible] parameterMap parameterJacobian

def fullPatch : Set Point := parameterMap 0 4 '' fullDomain
def fullLaplacianIntegral : ℝ := ∫ x in fullPatch, laplacian sourceTerms densityMatrix x
def quarterIntegralInterval (q : Quarter) : Pair :=
  integralPair (generatedTargetIntegrand q) (quarterLowerQ q) (quarterUpperQ q)
def fullIntegralInterval : Pair :=
  (∑ q : Quarter, (quarterIntegralInterval q).1, ∑ q : Quarter, (quarterIntegralInterval q).2)

theorem fullPatch_compact : IsCompact fullPatch :=
  full_compact.image (parameterMap_contDiff 0 4 0).continuous
theorem fullPatch_nonempty : fullPatch.Nonempty := full_nonempty.image _
theorem fullPatch_measurable : MeasurableSet fullPatch := fullPatch_compact.isClosed.measurableSet
theorem fullPatch_laplacian_integrable : IntegrableOn (laplacian sourceTerms densityMatrix) fullPatch :=
  (laplacian_contDiff sourceTerms densityMatrix 0).continuous.continuousOn.integrableOn_compact fullPatch_compact

theorem full_spatial_integral_commutes (fields : SourceFieldLaw) :
    fullLaplacianIntegral = fullSignedIntegral := by
  unfold fullLaplacianIntegral fullPatch fullSignedIntegral
  refine (integral_image_eq_integral_abs_det_fderiv_smul volume full_measurable
    (fun p _ => (parameterMap_hasFDerivAt 0 4 p).hasFDerivWithinAt) (actual_chart_injOn fields) _).trans ?_
  apply setIntegral_congr_fun full_measurable
  intro p hp
  dsimp only
  rw [SourceChart.linearDet_eq_matrixDet, abs_of_pos (full_jacobian_positive fields p hp)]
  simp only [signedLaplacian, smul_eq_mul, mul_comm]

theorem full_spatial_integral_eq_four (fields : SourceFieldLaw) :
    fullLaplacianIntegral = ∑ q : Quarter, quarterSignedIntegral q :=
  (full_spatial_integral_commutes fields).trans full_signed_integral_eq_quarters

theorem full_spatial_integral_enclosure (fields : SourceFieldLaw) :
    Holds fullIntegralInterval fullLaplacianIntegral := by
  rw [full_spatial_integral_eq_four fields]
  have each (q : Quarter) : Holds (quarterIntegralInterval q) (quarterSignedIntegral q) :=
    quarter_integral_from_source_fields fields q
  constructor
  · change ((∑ q : Quarter, (quarterIntegralInterval q).1 : ℚ) : ℝ) ≤ _
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum (fun q _ => (each q).1)
  · change _ ≤ ((∑ q : Quarter, (quarterIntegralInterval q).2 : ℚ) : ℝ)
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum (fun q _ => (each q).2)

theorem source_integral_bounds :
    (-623 / 10000000000 : ℚ) < fullIntegralInterval.1 ∧
      fullIntegralInterval.2 < (-39 / 10000000000 : ℚ) := by
  unfold fullIntegralInterval quarterIntegralInterval
  simp only [target_integrand_recomputed]
  decide +kernel

theorem full_spatial_integral_strict (fields : SourceFieldLaw) :
    (-623 / 10000000000 : ℝ) < fullLaplacianIntegral ∧
      fullLaplacianIntegral < (-39 / 10000000000 : ℝ) := by
  have measured := full_spatial_integral_enclosure fields
  have low : (-623 / 10000000000 : ℝ) < (fullIntegralInterval.1 : ℝ) := by
    exact_mod_cast source_integral_bounds.1
  have high : (fullIntegralInterval.2 : ℝ) < (-39 / 10000000000 : ℝ) := by
    exact_mod_cast source_integral_bounds.2
  exact ⟨low.trans_le measured.1, measured.2.trans_lt high⟩

end
end LAlanine40K2025.BasinRefinement.WholeCellSpatial
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
