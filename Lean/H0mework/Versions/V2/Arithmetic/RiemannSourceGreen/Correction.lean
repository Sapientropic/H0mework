import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.Euler
import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.ProjectedSourceClosedRange

/-! The generated Pa correction is bounded on the whole original Pa carrier; its compact inverse source is the actual weighted source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section
def burnolPaSourceCorrection (coordinate : BurnolCompletedMellinCoordinate) :
    burnolCompactCoPoissonClosedRange.toSubmodule →L[ℂ] BurnolPaAmbientCarrier :=
  let embed : burnolCompactCoPoissonClosedRange.toSubmodule →L[ℂ] BurnolL2 :=
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL.comp
      burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL
  let coefficient : burnolCompactCoPoissonClosedRange.toSubmodule →L[ℂ] ℂ :=
    (burnolPaResolventSourceCoefficient coordinate).comp
    burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL
  let principal : burnolCompactCoPoissonClosedRange.toSubmodule →L[ℂ] BurnolL2 :=
    (burnolDirectRightResolventCLM coordinate).comp embed
  let tail : burnolCompactCoPoissonClosedRange.toSubmodule →L[ℂ] BurnolL2 :=
    coefficient.smulRight (burnolUnitTailResponse coordinate 4)
  let raw : burnolCompactCoPoissonClosedRange.toSubmodule →L[ℂ] BurnolL2 := principal - tail
  raw.codRestrict (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule (by
    intro p
    obtain ⟨c, _, same⟩ := Submodule.mem_map.mp
      (burnolPaResolvent_source_correction coordinate (p : BurnolPaAmbientCarrier) p.property)
    change burnolDirectRightResolvent (coordinate.value / 2) (p : BurnolL2) -
      burnolPaResolventSourceCoefficient coordinate (p : BurnolPaAmbientCarrier) •
        burnolUnitTailResponse coordinate 4 ∈ _
    rw [← same]
    exact c.property)

theorem burnolPaSourceCorrection_mem (coordinate : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange) :
    burnolPaSourceCorrection coordinate p ∈ burnolCompactCoPoissonClosedRange := by
  obtain ⟨c, hc, same⟩ := Submodule.mem_map.mp
    (burnolPaResolvent_source_correction coordinate (p : BurnolPaAmbientCarrier) p.property)
  have equal : burnolPaSourceCorrection coordinate p = c := Subtype.ext same.symm
  rw [equal]
  exact hc

theorem burnolPaSourceCorrection_compact_wave (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    let p : burnolCompactCoPoissonClosedRange := ⟨burnolCompactAdditivePhysicalState source, by
      simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
        burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))⟩
    (burnolPaSourceCorrection coordinate p : BurnolL2) =
      (1 / 2 : ℂ) • burnolWeightedReciprocalStepWave (1 / 4) 4
        (burnolFirstSourceCoefficient coordinate source) (burnolFirstSourceCoefficientSlope coordinate source) := by
  change burnolDirectRightResolvent (coordinate.value / 2) (burnolCompactAdditiveL2 source) -
    burnolPaResolventSourceCoefficient coordinate (burnolCompactAdditivePhysicalState source) •
      burnolUnitTailResponse coordinate 4 = _
  rw [burnolPaResolventSourceCoefficient_compact]
  have split := burnolCompactFirstResponse_split coordinate source
  calc
    _ = (1 / 2 : ℂ) • ((2 : ℂ) • burnolDirectRightResolvent
      (coordinate.value / 2) (burnolCompactAdditiveL2 source)) -
      (burnolFirstSourceMellinCoefficient coordinate.value source / 2) •
        burnolUnitTailResponse coordinate 4 := by module
    _ = _ := by rw [split]; module

theorem burnolPaSourceCorrection_compact_source (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    let p : burnolCompactCoPoissonClosedRange := ⟨burnolCompactAdditivePhysicalState source, by
      simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
        burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))⟩
    burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate p) =
      (1 / 2 : ℂ) • burnolWeightedReciprocalStepSource (1 / 4) 4
        (burnolFirstSourceCoefficient coordinate source)
        (burnolFirstSourceCoefficientSlope coordinate source) := by
  let p : burnolCompactCoPoissonClosedRange := ⟨burnolCompactAdditivePhysicalState source, by
    simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
      burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))⟩
  let value : BurnolPaAmbientCarrier := (2 : ℂ) • burnolPaSourceCorrection coordinate p
  let weighted := burnolWeightedReciprocalStepSource (1 / 4) 4
    (burnolFirstSourceCoefficient coordinate source) (burnolFirstSourceCoefficientSlope coordinate source)
  have valueRead : (value : BurnolL2) = burnolWeightedReciprocalStepWave (1 / 4) 4
      (burnolFirstSourceCoefficient coordinate source)
      (burnolFirstSourceCoefficientSlope coordinate source) := by
    change (2 : ℂ) • (burnolPaSourceCorrection coordinate p : BurnolL2) = _
    rw [burnolPaSourceCorrection_compact_wave coordinate source]
    module
  have raw := burnolFirstSourceWeightedSource_coe coordinate source
  have even : reflectL2 weighted = weighted := burnolReflectL2_eq_of_even_raw weighted _ raw
    (fun x => by simp only [burnolReciprocalStepSourceRaw, abs_neg])
  have gap : (weighted : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))]
      fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae raw,
      ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))] with x hx inside
    rw [hx, burnolReciprocalStepSource_innerGap (1 / 4) 4 (by norm_num) (by norm_num)
      (by simpa using abs_le.mpr inside), mul_zero]
  have realizes (test : SchwartzMap ℝ ℂ) : burnolRemainderSourceRead weighted test =
      ∫ x : ℝ, test x * (value : BurnolL2) x := by
    rw [valueRead]
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply,
      smul_eq_mul] using burnolWeightedReciprocalStepSource_realizes (1 / 4) 4 _ _
        (by norm_num) (by norm_num) (by norm_num)
        (burnolFirstSourceCoefficientSlope_continuous coordinate source).continuousOn test
  have cutoff : burnolRadiusZeroExtension 4 (burnolRadiusRestriction 4 weighted) = weighted := by
    have restricted := (ae_restrict_iff' (measurableSet_symmetricInterval (4 : ℝ))).mp
      (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (4 : ℝ)) weighted)
    apply Lp.ext
    filter_upwards [burnolRadiusZeroExtension_coe (burnolRadiusRestriction 4 weighted),
      restricted, raw] with x extended read atX
    rw [extended]
    by_cases inside : x ∈ symmetricInterval (4 : ℝ)
    · rw [indicator_of_mem inside]
      exact read inside
    · rw [indicator_of_notMem inside, atX]
      have large : 4 < |x| := lt_of_not_ge (fun small => inside (abs_le.mp small))
      have inactive : ¬ ((1 / 4 : ℝ) ≤ |x|⁻¹ ∧ |x|⁻¹ < 4) := by
        intro active
        have bound : |x|⁻¹ < (1 / 4 : ℝ) := by
          simpa using (inv_lt_inv₀ (by linarith : 0 < |x|) (by norm_num : (0 : ℝ) < 4)).mpr large
        linarith [active.1]
      simp only [burnolReciprocalStepSourceRaw, if_neg inactive, mul_zero]
  have same := burnolRemainderSourceRead_cutoff_source weighted value even gap realizes
  rw [cutoff] at same
  change burnolMobiusSourceL2 ((2 : ℂ) • burnolPaSourceCorrection coordinate p) = weighted at same
  rw [map_smul] at same
  change burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate p) = (1 / 2 : ℂ) • weighted
  calc
    _ = (1 / 2 : ℂ) • ((2 : ℂ) • burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate p)) := by module
    _ = _ := by rw [same]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
