import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaResolventDetection
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaCorrectionDetection
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorYukawaNonzero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.YukawaResolventDetection
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open SourceQuantumConfigurationHilbert GaussYukawaOperator
open GaussCoreLabel NativeHistoryGrade GeneralThreeParticleResponse
open FullYSourceResolventGraphSplice SourceResolventBandLimit FullYDynamicResponse
open MixedSpectatorCandidate GaussDensityCore MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

/-- The actual bounded source factor forces a nonzero unforced correction
somewhere on each frequency line; no pointwise-frequency premise is inserted. -/
theorem actual_Y_correction_nonzero (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (hY : bounded (embed q) ≠ 0)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    ∃ω : ℝ, originalYCorrection F q advanced μ hμ ω ≠ 0 := by
  have hc : FullYPairedParseval.direction advanced * μ ≠ 0 := by
    cases advanced <;> simp [FullYPairedParseval.direction,hμ.ne']
  obtain ⟨ω,hω⟩ := exists_reader_resolvent_nonzero (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) bounded (embed q) hY
    (FullYPairedParseval.direction advanced * μ) hc
  exact ⟨ω,fun hz => hω (correction_zero_bounded_resolvent F q hq advanced μ hμ ω hz)⟩

private theorem correction_continuous (F : Index) (q : QuantumTest)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Continuous (originalYCorrection F q advanced μ hμ) := by
  have h := CompositeFullYBorn.actual_response_continuous F false q advanced μ hμ
  exact h.sub ((projection (3,0)).continuous.comp h)

/-- Paid whole/bottom integrability and the actual nonzero frequency produce
strictly positive integrated original-Y work on the same fixed input. -/
theorem actual_Y_correction_integral_pos (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (hY : bounded (embed q) ≠ 0)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    0 < ∫ω : ℝ, ‖originalYCorrection F q advanced μ hμ ω‖^2 := by
  obtain ⟨ω,hω⟩ := actual_Y_correction_nonzero F q hq hY advanced μ hμ
  apply integral_pos_of_integrable_nonneg_nonzero
    ((correction_continuous F q advanced μ hμ).norm.pow 2)
    (actual_unforced_frequency_balance F q hq advanced μ hμ).1
    (fun _ => sq_nonneg _) (x := ω)
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr hω)

theorem actual_Y_correction_measure_pos (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (hY : bounded (embed q) ≠ 0)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    0 < correctionMeasure F q advanced μ hμ Set.univ := by
  have hi := (actual_unforced_frequency_balance F q hq advanced μ hμ).1
  have hm : correctionMeasure F q advanced μ hμ Set.univ =
      ENNReal.ofReal (∫ω : ℝ, ‖originalYCorrection F q advanced μ hμ ω‖^2) := by
    unfold correctionMeasure
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun _ => sq_nonneg _))).symm
  rw [hm,ENNReal.ofReal_pos]
  exact actual_Y_correction_integral_pos F q hq hY advanced μ hμ

theorem actual_unforced_strict_excess (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (hY : bounded (embed q) ≠ 0)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    (Real.pi / μ) * ‖embed q‖^2 <
      ∫ω : ℝ, ‖embed (literalResponse F false q advanced μ hμ ω)‖^2 := by
  rw [(actual_unforced_frequency_balance F q hq advanced μ hμ).2.1]
  exact lt_add_of_pos_right _ (actual_Y_correction_integral_pos F q hq hY advanced μ hμ)

/-- The original chart and actual vacuum Y generate this source witness
before selecting F, cause or damping. The original unforced spectrum has
strictly positive Y excess for every one of those actual compressions. -/
theorem actual_generated_candidate_Y_excess (dual : Bool) :
    ∃f : ScalarTest, f GaussHistoryHilbert.sourcePoint.val = 1 ∧
      ∀F : Index, ∀advanced : Bool, ∀μ : ℝ, ∀hμ : 0 < μ,
      0 < correctionMeasure F (candidateTest dual f) advanced μ hμ Set.univ ∧
      (Real.pi / μ) * (2 * ‖scalarLp 3 f‖^2) <
        ∫ω : ℝ, ‖embed (literalResponse F false (candidateTest dual f) advanced μ hμ ω)‖^2 := by
  obtain ⟨f,hf,hq,hY⟩ := actual_generated_candidate_bounded_Y_source dual
  refine ⟨f,hf,?_⟩
  intro F advanced μ hμ
  refine ⟨actual_Y_correction_measure_pos F _ hq hY advanced μ hμ,?_⟩
  simpa only [actual_candidate_test_norm] using
    actual_unforced_strict_excess F _ hq hY advanced μ hμ

end LowEnergy.YukawaResolventDetection
