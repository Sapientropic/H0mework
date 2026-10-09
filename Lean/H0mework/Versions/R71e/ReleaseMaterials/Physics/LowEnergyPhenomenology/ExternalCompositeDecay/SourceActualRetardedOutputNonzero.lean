import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaResolventDetection
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYBornFrequency

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualRetardedOutputNonzero
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open SourceQuantumConfigurationHilbert FullYDynamicSource FullYDynamicResponse CompositeFullYBorn
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open Filter MeasureTheory
open scoped Topology InnerProductSpace ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] embed sourceReader literalCoreResolvent literalSharpResolvent sourceOrbit sourceSpace

/-- Only the actual source generator's boundedness and its original inverse
identity are used. It is not assumed self-adjoint. -/
theorem actual_source_scaled_limit (F : Index) (sharp : Bool) (q : QuantumTest)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (x : sourceSpace F sharp q) :
    Tendsto (fun w : ℝ => line (FullYPairedParseval.direction advanced*μ) w •
      sourceResolvent F sharp q (line (FullYPairedParseval.direction advanced*μ) w) x)
      atTop (𝓝 (-x)) := by
  let C := sourceGenerator F sharp q
  let c := FullYPairedParseval.direction advanced*μ
  have zero : Tendsto (fun w : ℝ => sourceResolvent F sharp q (line c w)) atTop (𝓝 0) :=
    YukawaResolventDetection.line_resolvent_tendsto_zero C c
  have hv := ((ContinuousLinearMap.apply ℂ (sourceSpace F sharp q) (C x)).continuous.tendsto 0).comp zero
  have h := hv.sub_const x
  have identity (w : ℝ) : sourceResolvent F sharp q (line c w) (C x)-x =
      line c w • sourceResolvent F sharp q (line c w) x := by
    have hleft := congrArg (fun T : sourceSpace F sharp q →L[ℂ] sourceSpace F sharp q => T x)
      (source_resolvent_inverse F sharp q (line c w)
        (causal_line_nonreal advanced μ w hμ)).1
    change sourceResolvent F sharp q (line c w) ((C-line c w • 1) x)=x at hleft
    simp only [sub_apply,_root_.smul_apply,one_apply_eq_self,map_sub,map_smul] at hleft
    linear_combination (norm := module) hleft
  simpa only [Function.comp_def,ContinuousLinearMap.apply_apply,zero_apply,zero_sub,identity] using h

private theorem response_source (F : Index) (sharp : Bool) (q : QuantumTest)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    embed (literalResponse F sharp q advanced μ hμ w) =
      (sourceResolvent F sharp q (line (FullYPairedParseval.direction advanced*μ) w)
        (sourceEquiv F sharp q ⟨q,sourceOrbit_input F sharp q⟩) : H) := by
  rw [literalResponse,←source_resolvent_literal_return]
  exact congrArg Subtype.val ((sourceEquiv F sharp q).apply_symm_apply _)

/-- High-frequency return of the original literal fullY/independent-sharp
response, on its own generated finite source carrier. -/
theorem actual_literal_scaled_limit (F : Index) (sharp : Bool) (q : QuantumTest)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Tendsto (fun w : ℝ => line (FullYPairedParseval.direction advanced*μ) w •
      embed (literalResponse F sharp q advanced μ hμ w)) atTop (𝓝 (-embed q)) := by
  let S := sourceSpace F sharp q
  let x : S := sourceEquiv F sharp q ⟨q,sourceOrbit_input F sharp q⟩
  have hx : (x : H) = embed q := rfl
  have he := S.subtypeL.continuous.tendsto _ |>.comp
    (actual_source_scaled_limit F sharp q advanced μ hμ x)
  have hr (w : ℝ) :
      (sourceResolvent F sharp q (line (FullYPairedParseval.direction advanced*μ) w) x : H) =
        embed (literalResponse F sharp q advanced μ hμ w) :=
    (response_source F sharp q advanced μ hμ w).symm
  simpa only [Function.comp_def,Submodule.subtypeL_apply,Submodule.coe_smul,
    Submodule.coe_neg,hx,hr] using he

/-- The paid sourceReader is bounded on exactly this generated orbit, even
when A is unbounded on the full Hilbert space. -/
theorem actual_output_scaled_limit (F : Index) (sharp : Bool) (q : QuantumTest) (A : End)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Tendsto (fun w : ℝ => line (FullYPairedParseval.direction advanced*μ) w •
      embed (A (literalResponse F sharp q advanced μ hμ w))) atTop (𝓝 (-embed (A q))) := by
  have h := (sourceReader F sharp q A).continuous.tendsto _ |>.comp
    (actual_literal_scaled_limit F sharp q advanced μ hμ)
  have each (w : ℝ) := source_reader_return F sharp q _ A
    (actual_response_orbit F sharp q advanced μ hμ w)
  have input := source_reader_return F sharp q q A (sourceOrbit_input F sharp q)
  simpa only [Function.comp_def,map_smul,map_neg,each,input] using h

theorem actual_output_continuous (F : Index) (sharp : Bool) (q : QuantumTest) (A : End)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Continuous (fun w : ℝ => embed (A (literalResponse F sharp q advanced μ hμ w))) := by
  apply ((sourceReader F sharp q A).continuous.comp
    (actual_response_continuous F sharp q advanced μ hμ)).congr
  intro w
  exact source_reader_return F sharp q _ A (actual_response_orbit F sharp q advanced μ hμ w)

/-- This is a conditional consumer of an already-generated nonzero A q.
The actual four-block elastic producer must supply that witness. -/
theorem actual_output_eventually_nonzero (F : Index) (sharp : Bool) (q : QuantumTest) (A : End)
    (hq : A q ≠ 0) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    ∀ᶠ w : ℝ in atTop, embed (A (literalResponse F sharp q advanced μ hμ w)) ≠ 0 := by
  have hn : -embed (A q) ≠ 0 := by
    rw [neg_ne_zero]
    intro h
    exact hq (embed_injective (h.trans (map_zero embed).symm))
  filter_upwards [(actual_output_scaled_limit F sharp q A advanced μ hμ).eventually_ne hn] with w hw
  intro hz
  exact hw (by rw [hz,smul_zero])

theorem actual_output_total_pos (F : Index) (sharp : Bool) (q : QuantumTest) (A : End)
    (hq : A q ≠ 0) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun w : ℝ => ‖embed (A (literalResponse F sharp q advanced μ hμ w))‖^2) ∧
      0 < ∫w : ℝ, ‖embed (A (literalResponse F sharp q advanced μ hμ w))‖^2 := by
  have hi := actual_core_word_square_integrable F sharp q advanced μ hμ A
  refine ⟨hi,?_⟩
  obtain ⟨w,hw⟩ := (actual_output_eventually_nonzero F sharp q A hq advanced μ hμ).exists
  exact integral_pos_of_integrable_nonneg_nonzero
    ((actual_output_continuous F sharp q A advanced μ hμ).norm.pow 2) hi
    (fun _ => sq_nonneg _) (pow_ne_zero _ (norm_ne_zero_iff.mpr hw))

/-- Every neighbourhood band of an actual nonzero output point has strictly
positive mass; mere membership in a measure-zero set is not enough. -/
theorem actual_output_neighbourhood_pos (F : Index) (sharp : Bool) (q : QuantumTest) (A : End)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ)
    (hw : embed (A (literalResponse F sharp q advanced μ hμ w)) ≠ 0)
    (B : Set ℝ) (hB : B ∈ 𝓝 w) :
    0 < ∫v in B, ‖embed (A (literalResponse F sharp q advanced μ hμ v))‖^2 := by
  have hi := actual_core_word_square_integrable F sharp q advanced μ hμ A
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun _ => sq_nonneg _)) hi.restrict).mpr
  have hs := ((actual_output_continuous F sharp q A advanced μ hμ).norm.pow 2).continuousAt.eventually_ne
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hw))
  exact Measure.measure_pos_of_mem_nhds volume (Filter.inter_mem hs hB)

end LowEnergy.ActualRetardedOutputNonzero
