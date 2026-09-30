import H0mework.NavierStokes.Heat.PulseDilation
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeHeatPulseContinuity

open Set Filter MeasureTheory
open NativeHeatPulseDilation NativeTemporalActionCompression

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem joint_continuous (rate : ℝ) (positive : 0 < rate) :
    Continuous (fun pair : ℝ × E => translation E pair.1 (embed rate positive pair.2)) := by
  let shifts : C(ℝ, C(ℝ, ℝ)) :=
    (⟨fun pair : ℝ × ℝ => pair.2 + pair.1, continuous_snd.add continuous_fst⟩ : C(ℝ × ℝ, ℝ)).curry
  have input : Continuous (fun pair : ℝ × E => embed rate positive pair.2) :=
    (embed rate positive).continuous.comp continuous_snd
  have shift : Continuous (fun pair : ℝ × E => shifts pair.1) := shifts.continuous.comp continuous_fst
  exact input.compMeasurePreservingLp shift (fun pair => measurePreserving_add_right volume pair.1)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)

theorem orbit_continuous (rate : ℝ) (positive : 0 < rate) (value : E) :
    Continuous (fun time : ℝ => translation E time (embed rate positive value)) :=
  (joint_continuous rate positive).comp (continuous_id.prodMk continuous_const)

theorem forced_lift_measurable (rate : ℝ) (positive : 0 < rate) (terminal : ℝ)
    {μ : Measure ℝ} {forcing : ℝ → E} (source : AEStronglyMeasurable forcing μ) :
    AEStronglyMeasurable (fun time => translation E (terminal - time) (embed rate positive (forcing time))) μ := by
  have timeContinuous : Continuous (fun time : ℝ => terminal - time) := continuous_const.sub continuous_id
  have coordinates : AEStronglyMeasurable (fun time => (terminal - time, forcing time)) μ :=
    timeContinuous.aestronglyMeasurable.prodMk source
  have lifted := (joint_continuous (E := E) rate positive).comp_aestronglyMeasurable coordinates
  change AEStronglyMeasurable (fun time : ℝ =>
    translation E (terminal - time) (embed rate positive (forcing time))) μ at lifted
  exact lifted

theorem forced_lift_integrable (rate : ℝ) (positive : 0 < rate) (terminal : ℝ)
    {μ : Measure ℝ} {forcing : ℝ → E} (source : Integrable forcing μ) :
    Integrable (fun time => translation E (terminal - time) (embed rate positive (forcing time))) μ := by
  apply (integrable_norm_iff (forced_lift_measurable rate positive terminal source.aestronglyMeasurable)).mp
  simpa only [LinearIsometry.norm_map] using source.norm

end
end SaturationMonoid.NavierStokes.NativeHeatPulseContinuity
