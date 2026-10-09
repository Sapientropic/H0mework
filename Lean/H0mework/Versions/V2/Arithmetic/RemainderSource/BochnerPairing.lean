import H0mework.Versions.V2.Arithmetic.RiemannDivision.RightDivisionRepresentative

/-! The original L² inner product reads a Bochner source family through its actual measurable representative. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem burnolL2Bochner_pairing_raw (μ : Measure ℝ) [SFinite μ]
    (family : ℝ → BurnolL2) (integrable : Integrable family μ) (raw : ℝ × ℝ → ℂ)
    (rawMeasurable : Measurable raw) (rawRead : ∀ᵐ u ∂μ, (family u : ℝ → ℂ) =ᵐ[volume]
      fun x => raw (u, x)) (test : BurnolL2) :
    Integrable (fun x : ℝ => inner ℂ (test x) (∫ u, raw (u, x) ∂μ)) ∧
      inner ℂ test (∫ u, family u ∂μ) =
        ∫ x : ℝ, inner ℂ (test x) (∫ u, raw (u, x) ∂μ) := by
  let kernel : ℝ × ℝ → ℂ := fun point => inner ℂ (test point.2) (raw point)
  have measured : AEStronglyMeasurable kernel (μ.prod volume) :=
    ((Lp.stronglyMeasurable test).comp_measurable measurable_snd).inner
      rawMeasurable.stronglyMeasurable |>.aestronglyMeasurable
  have sections : ∀ᵐ u ∂μ, (fun x => kernel (u, x)) =ᵐ[volume]
      fun x => inner ℂ (test x) (family u x) := by
    filter_upwards [rawRead] with u hu
    exact hu.mono (fun x hx => congrArg (inner ℂ (test x)) hx.symm)
  have joint : Integrable kernel (μ.prod volume) := by
    rw [integrable_prod_iff measured]
    constructor
    · filter_upwards [sections] with u hu
      exact (L2.integrable_inner (𝕜 := ℂ) test (family u)).congr hu.symm
    · apply (integrable.norm.const_mul ‖test‖).mono' measured.norm.integral_prod_right'
      filter_upwards [sections] with u hu
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc
        _ = ∫ x : ℝ, ‖inner ℂ (test x) (family u x)‖ :=
          integral_congr_ae (hu.mono (fun _ hx => congrArg norm hx))
        _ ≤ ‖test‖ * ‖family u‖ := integral_norm_inner_L2_le volume test (family u)
  have pointwise : (fun x : ℝ => ∫ u, kernel (u, x) ∂μ) =
      fun x : ℝ => inner ℂ (test x) (∫ u, raw (u, x) ∂μ) := by
    funext x
    simp only [kernel, RCLike.inner_apply]
    rw [integral_mul_const]
  refine ⟨?_, ?_⟩
  · simpa only [pointwise] using joint.integral_prod_right
  rw [← integral_inner integrable test]
  have reads : (∫ u, inner ℂ test (family u) ∂μ) = ∫ u, (∫ x : ℝ, kernel (u, x)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [sections] with u hu
    rw [L2.inner_def]
    exact integral_congr_ae hu.symm
  rw [reads, ← integral_prod _ joint, integral_prod_symm _ joint]
  rw [pointwise]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
