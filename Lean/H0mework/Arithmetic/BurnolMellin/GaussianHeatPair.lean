import H0mework.Arithmetic.BurnolMellin.GaussianFourierKernel
import H0mework.Arithmetic.BurnolPhysical.PhysicalityProjection
import Mathlib.Analysis.MellinTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

def burnolGenericGaussianHeatPairTotal
    (value : BurnolL2) (scale : ℝ) : ℂ :=
  if positive : 0 < scale then
    inner ℂ (burnolGaussianL2 scale positive) value
  else 0

def burnolGenericGaussianPositivePair
    (value : BurnolL2) (scale : ℝ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 0, value x * burnolGaussianRaw scale x

theorem burnolGenericGaussianHeatPair_eq_two_mul_positivePair
    {radius : ℝ} (value : EvenBurnolPhysicalCarrier radius)
    {scale : ℝ} (positive : 0 < scale) :
    burnolGenericGaussianHeatPairTotal (value : BurnolL2) scale =
      2 * burnolGenericGaussianPositivePair (value : BurnolL2) scale := by
  rw [burnolGenericGaussianHeatPairTotal, dif_pos positive,
    inner_burnolGaussianL2_eq_integral]
  let raw : ℝ → ℂ := fun x =>
    (value : BurnolL2) x * burnolGaussianRaw scale x
  have rawIntegrable : Integrable raw := by
    exact (L2.integrable_inner
      (burnolGaussianL2 scale positive) (value : BurnolL2)).congr (by
        filter_upwards [burnolGaussianL2_coeFn scale positive] with x gaussianRead
        rw [gaussianRead, RCLike.inner_apply, starRingEnd_apply,
          star_burnolGaussianRaw])
  have reflected := Lp.coeFn_compMeasurePreserving
    (value : BurnolL2) negMeasurePreserving
  have valueEven : ∀ᵐ x ∂volume,
      (value : BurnolL2) (-x) = (value : BurnolL2) x := by
    filter_upwards [reflected] with x reflection
    calc
      (value : BurnolL2) (-x) = reflectL2 (value : BurnolL2) x :=
        reflection.symm
      _ = (value : BurnolL2) x := congrArg
        (fun state : BurnolL2 => state x)
          (mem_evenL2ClosedFace_iff.mp value.property.2)
  have negative : (∫ x : ℝ in Set.Iic 0, raw x) =
      ∫ x : ℝ in Set.Ioi 0, raw x := by
    calc
      _ = ∫ x : ℝ in Set.Iic 0, raw (-x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae valueEven] with x valueRead
        unfold raw
        rw [valueRead]
        congr 1
        simp [burnolGaussianRaw]
      _ = _ := by simpa only [neg_zero] using integral_comp_neg_Iic 0 raw
  change (∫ x : ℝ, raw x) = _
  rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      rawIntegrable.integrableOn rawIntegrable.integrableOn,
    negative]
  unfold burnolGenericGaussianPositivePair
  ring

theorem burnolGaussianReciprocalScale_eq_cpow_neg_half
    {scale : ℝ} (positive : 0 < scale) :
    burnolGaussianReciprocalScale scale =
      (scale : ℂ) ^ (-(1 / 2 : ℂ)) := by
  rw [burnolGaussianReciprocalScale_eq positive, Complex.cpow_neg]
  simp [div_eq_mul_inv]

/-- Ordinary Fourier transports the same heat pairing by inverse scale and
the half-density factor. -/
theorem burnolGenericGaussianHeatPairTotal_fourier
    {radius : ℝ} (value : EvenBurnolPhysicalCarrier radius)
    (scale : ℝ) :
    burnolGenericGaussianHeatPairTotal
        (fourierL2 (value : BurnolL2)) scale =
      (scale : ℂ) ^ (-(1 / 2 : ℂ)) *
        burnolGenericGaussianHeatPairTotal
          (value : BurnolL2) scale⁻¹ := by
  by_cases positive : 0 < scale
  · rw [burnolGenericGaussianHeatPairTotal, dif_pos positive,
      inner_burnolGaussianL2_eq_integral,
      burnolGaussian_fourierL2_pairing (value : BurnolL2) positive,
      burnolGenericGaussianHeatPairTotal,
      dif_pos (inv_pos.mpr positive),
      inner_burnolGaussianL2_eq_integral,
      burnolGaussianReciprocalScale_eq_cpow_neg_half positive]
  · have inverseNonpositive : ¬0 < scale⁻¹ := by
      exact not_lt_of_ge (inv_nonpos.mpr (le_of_not_gt positive))
    rw [burnolGenericGaussianHeatPairTotal, dif_neg positive,
      burnolGenericGaussianHeatPairTotal, dif_neg inverseNonpositive, mul_zero]

/-- Mellin homogeneity of the same Gaussian pairing under ordinary Fourier. -/
theorem burnolGenericGaussianFourierHomogeneousIdentity
    {radius : ℝ} (value : EvenBurnolPhysicalCarrier radius)
    (s : ℂ) :
    mellin (burnolGenericGaussianHeatPairTotal
        (fourierL2 (value : BurnolL2))) (s / 2) =
      mellin (burnolGenericGaussianHeatPairTotal (value : BurnolL2))
        ((1 - s) / 2) := by
  rw [show burnolGenericGaussianHeatPairTotal
      (fourierL2 (value : BurnolL2)) = fun scale : ℝ =>
        (scale : ℂ) ^ (-(1 / 2 : ℂ)) •
          burnolGenericGaussianHeatPairTotal
            (value : BurnolL2) scale⁻¹ by
    funext scale
    simpa only [smul_eq_mul] using
      burnolGenericGaussianHeatPairTotal_fourier value scale]
  rw [mellin_cpow_smul, mellin_comp_inv]
  congr 2
  ring

end


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
