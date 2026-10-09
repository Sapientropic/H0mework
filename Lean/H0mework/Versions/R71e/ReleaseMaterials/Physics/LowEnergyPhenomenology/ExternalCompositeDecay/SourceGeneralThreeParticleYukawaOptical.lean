import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaPositiveCorrection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace LowEnergy.GeneralThreeParticleYukawaOptical
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussFockPair
open FullYDynamicSource FullYDynamicResponse FullYSourceResolventGraphSplice CompositeFullYBorn
open SourceClockYukawaCubicCurrent SourceScalarPairedTransport GaussCoreLabel NativeHistoryGrade
open SourceResolventBandLimit SourceQuantumConfigurationHilbert GeneralThreeParticleResponse
open GaussYukawaOperator NamedColorQtNext GaussDensityCore MeasureTheory Filter
open scoped BigOperators InnerProductSpace ENNReal
attribute [local irreducible] embed sourcePair project projection literalCoreResolvent literalSharpResolvent

private theorem compression_embed (F : Index) (q : QuantumTest) :
    embed (compressionCore F q) = GaussGradedCompression.compression F (embed q) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_im (F : Index) (q : QuantumTest) :
    (sourcePair q (compressionCore F q)).im = 0 := by
  have h := congrArg Complex.im (GaussGradedCompression.compression_pair F (embed q) (embed q))
  have s := inner_im_symm (𝕜 := ℂ) (GaussGradedCompression.compression F (embed q)) (embed q)
  change (inner ℂ (GaussGradedCompression.compression F (embed q)) (embed q)).im =
    -(inner ℂ (embed q) (GaussGradedCompression.compression F (embed q))).im at s
  simp only [sourcePair, compression_embed]
  change (inner ℂ (GaussGradedCompression.compression F (embed q)) (embed q)).im =
    (inner ℂ (embed q) (GaussGradedCompression.compression F (embed q))).im at h
  linarith

private theorem base_right (F : Index) (z : ℂ) (hz : z.im ≠ 0) (q : QuantumTest) :
    compressionCore F (resolventCore F z hz q) - z • resolventCore F z hz q = q := by
  apply embed_injective
  have he : embed (resolventCore F z hz q) = finiteResolvent F z (embed q) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [map_sub, map_smul, compression_embed, he]
  exact congrArg (fun T : H →L[ℂ] H => T (embed q))
    (resolvent_right (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz)

private theorem projection_norm (u : H) :
    ‖u‖^2 = ‖projection (3,0) u‖^2 + ‖u-projection (3,0) u‖^2 := by
  have hp : projection (3,0) (projection (3,0) u) = projection (3,0) u := by
    have h := congrArg (fun A : H →L[ℂ] H => A u) (projection_product (3,0) (3,0))
    simpa only [if_true,mul_apply_eq_comp] using! h
  have hz : inner ℂ (projection (3,0) u) (u-projection (3,0) u) = 0 := by
    calc
      _ = inner ℂ u (projection (3,0) (u-projection (3,0) u)) := projection_symmetric (3,0) _ _
      _ = 0 := by rw [map_sub,hp,sub_self,inner_zero_right]
  simpa only [add_sub_cancel,pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (projection (3,0) u) (u-projection (3,0) u) hz

/-- The original unforced Y current is precisely the excess response intensity.
The sign follows the right-slot sourcePair convention and the actual fullY right inverse. -/
theorem actual_originalY_pointwise (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    let r := literalResponse F false q advanced μ hμ w
    (sourcePair r (originalAction r)).im =
      (FullYPairedParseval.direction advanced * μ) * ‖originalYCorrection F q advanced μ hμ w‖^2 := by
  let z := line (FullYPairedParseval.direction advanced * μ) w
  have hz : z.im ≠ 0 := causal_line_nonreal advanced μ w hμ
  let r := literalCoreResolvent F z hz q
  let b := resolventCore F z hz q
  have projected : project (3,0) r = b := by
    dsimp only [r,b]
    rw [actual_bottom_primal_projected_resolvent,hq]
  have samePair : sourcePair r q = sourcePair b q := by
    calc
      _ = sourcePair r (project (3,0) q) := by rw [hq]
      _ = sourcePair (project (3,0) r) q := project_pair _ _ _
      _ = _ := by rw [projected]
  have hfull := LinearMap.congr_fun (literal_core_right_inverse F z hz) q
  change compressionCore F r + originalAction r - z • r = q at hfull
  have fullIm := congrArg (fun x : QuantumTest => (sourcePair r x).im) hfull
  have hb := base_right F z hz q
  change compressionCore F b - z • b = q at hb
  have baseIm := congrArg (fun x : QuantumTest => (sourcePair b x).im) hb
  have cr := compression_im F r
  have cb := compression_im F b
  have pairIm := congrArg Complex.im samePair
  have pyth := projection_norm (embed r)
  have bottom : projection (3,0) (embed r) = embed b := by rw [←embed_project,projected]
  rw [bottom] at pyth
  have reSelf (v : H) : (inner ℂ v v).re = ‖v‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  have imSelf (v : H) : (inner ℂ v v).im = 0 := inner_self_im (𝕜 := ℂ) v
  simp only [sourcePair, map_add, map_sub, map_smul, inner_add_right, inner_sub_right,
    inner_smul_right, Complex.add_im, Complex.sub_im, Complex.mul_im,
    reSelf, imSelf,
    mul_zero] at fullIm baseIm cr cb pairIm
  change (sourcePair r (originalAction r)).im =
    (FullYPairedParseval.direction advanced * μ) * ‖embed r - projection (3,0) (embed r)‖^2
  rw [bottom]
  have zi : z.im = FullYPairedParseval.direction advanced * μ := line_im _ _
  simp only [sourcePair]
  rw [zi] at fullIm baseIm
  linear_combination fullIm - baseIm + pairIm - cr + cb +
    (FullYPairedParseval.direction advanced * μ) * pyth

def originalYCurrent (F : Index) (q : QuantumTest) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (w : ℝ) : ℝ :=
  let r := literalResponse F false q advanced μ hμ w
  (sourcePair r (originalAction r)).im

theorem actual_originalY_integrable (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (originalYCurrent F q advanced μ hμ) := by
  have h := (actual_unforced_frequency_balance F q hq advanced μ hμ).1
  apply (h.const_mul (FullYPairedParseval.direction advanced * μ)).congr
  exact Eventually.of_forall (fun w => (actual_originalY_pointwise F q hq advanced μ hμ w).symm)

/-- Every frequency band consumes the actual Y current, with no separately
supplied integrability or missing-frequency remainder. -/
theorem actual_originalY_band (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (B : Set ℝ) :
    (∫w in B, originalYCurrent F q advanced μ hμ w) =
      (FullYPairedParseval.direction advanced * μ) *
        ∫w in B, ‖originalYCorrection F q advanced μ hμ w‖^2 := by
  have h := integral_congr_ae (μ := volume.restrict B)
    (Eventually.of_forall (actual_originalY_pointwise F q hq advanced μ hμ))
  exact h.trans (integral_const_mul _ _)

theorem actual_originalY_band_measure (F : Index) (q : QuantumTest)
    (hq : project (3,0) q = q) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ENNReal.ofReal (FullYPairedParseval.direction advanced *
      (∫w in B, originalYCurrent F q advanced μ hμ w)) =
      ENNReal.ofReal μ * correctionMeasure F q advanced μ hμ B := by
  have hi := (actual_unforced_frequency_balance F q hq advanced μ hμ).1
  have hm : correctionMeasure F q advanced μ hμ B =
      ENNReal.ofReal (∫w in B, ‖originalYCorrection F q advanced μ hμ w‖^2) := by
    rw [correctionMeasure, withDensity_apply _ hB]
    exact (ofReal_integral_eq_lintegral_ofReal hi.restrict
      (Eventually.of_forall (fun _ => sq_nonneg _))).symm
  rw [hm, ←ENNReal.ofReal_mul hμ.le, actual_originalY_band F q hq]
  congr 1
  cases advanced <;> simp [FullYPairedParseval.direction]

/-- The same source-generated scalar test that produces strict unforced Y
excess now produces a nonzero signed integrated original-Y current, for every F. -/
theorem actual_generated_candidate_signed_current (dual : Bool) :
    ∃f : ScalarTest, f GaussHistoryHilbert.sourcePoint.val = 1 ∧
      ∀F : Index, ∀advanced : Bool, ∀μ : ℝ, ∀hμ : 0 < μ,
      Integrable (originalYCurrent F (MixedSpectatorCandidate.candidateTest dual f) advanced μ hμ) ∧
      0 < FullYPairedParseval.direction advanced *
        (∫w : ℝ, originalYCurrent F (MixedSpectatorCandidate.candidateTest dual f) advanced μ hμ w) := by
  obtain ⟨f,hf,hexcess⟩ := YukawaResolventDetection.actual_generated_candidate_Y_excess dual
  refine ⟨f,hf,?_⟩
  intro F advanced μ hμ
  have hq := MixedSpectatorCandidate.actual_candidate_test_sector dual f
  refine ⟨actual_originalY_integrable F _ hq advanced μ hμ,?_⟩
  have positive := (hexcess F advanced μ hμ).1
  have hm := actual_originalY_band_measure F _ hq advanced μ hμ Set.univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at hm
  apply ENNReal.ofReal_pos.mp
  rw [hm]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hμ).ne' positive.ne'

end LowEnergy.GeneralThreeParticleYukawaOptical
