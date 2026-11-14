import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.CayleyLogClock

open Filter MeasureTheory Set

local notation "μ₊" => Measure.restrict (volume : Measure ℝ) (Ioi (0 : ℝ))

theorem positive_time_triangle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E)
    (joint : Integrable (fun p : ℝ × ℝ => f (p.1 + p.2)) (Measure.prod μ₊ μ₊)) :
    (∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), f (s + t)) =
      ∫ r in Ioi (0 : ℝ), r • f r := by
  let shear := MeasurableEquiv.shearAddRight ℝ
  let triangle : Set (ℝ × ℝ) := {p | p.1 < p.2}
  have triangleMeas : MeasurableSet triangle := measurableSet_lt measurable_fst measurable_snd
  have preserve : MeasurePreserving shear (Measure.prod μ₊ volume) (Measure.prod μ₊ volume) :=
    measurePreserving_prod_add μ₊ volume
  have preimage : (shear : ℝ × ℝ → ℝ × ℝ) ⁻¹' triangle = univ ×ˢ Ioi (0 : ℝ) := by
    ext p
    change p.1 < p.1 + p.2 ↔ p.1 ∈ (univ : Set ℝ) ∧ 0 < p.2
    simp
  have restricted := preserve.restrict_preimage_emb shear.measurableEmbedding triangle
  rw [preimage, ← Measure.prod_restrict, Measure.restrict_univ] at restricted
  have triangleInt : IntegrableOn (fun p : ℝ × ℝ => f p.2) triangle (Measure.prod μ₊ volume) :=
    (restricted.integrable_comp_emb shear.measurableEmbedding).mp joint
  calc
    _ = ∫ p : ℝ × ℝ, f (p.1 + p.2) ∂(Measure.prod μ₊ μ₊) := (integral_prod _ joint).symm
    _ = ∫ p : ℝ × ℝ in triangle, f p.2 ∂(Measure.prod μ₊ volume) :=
      restricted.integral_comp' (fun p : ℝ × ℝ => f p.2)
    _ = ∫ r : ℝ, ∫ s : ℝ, triangle.indicator (fun p : ℝ × ℝ => f p.2) (s, r) ∂μ₊ := by
      rw [← integral_indicator triangleMeas]
      exact integral_prod_symm _ (triangleInt.integrable_indicator triangleMeas)
    _ = _ := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with r
      change (∫ s : ℝ, (Iio r).indicator (fun _ : ℝ => f r) s ∂μ₊) = _
      rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      have slice : Iio r ∩ Ioi (0 : ℝ) = Ioo 0 r := by
        ext s
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
      rw [slice, setIntegral_const, Real.volume_real_Ioo, sub_zero]
      by_cases hr : 0 < r
      · rw [max_eq_left hr.le, indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr)]
      · rw [max_eq_right (le_of_not_gt hr), zero_smul,
          indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr)]

end OriginalRSourceJointContact.CayleyLogClock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
