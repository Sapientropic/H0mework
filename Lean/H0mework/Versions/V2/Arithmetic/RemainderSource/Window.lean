import H0mework.Versions.V2.Arithmetic.RemainderSource.Recovery
import H0mework.Versions.V2.Arithmetic.MobiusSource.Tate

/-! The original finite Möbius read returns the actual full source's window restriction. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

/-- The existing finite Möbius read recovers a raw inner-gap source from the actual value.
Only the returned window is an L² source; no global L² hypothesis is imposed on the raw carrier. -/
theorem burnolMobiusWindowSourceRead_forward_raw (raw : ℝ → ℂ)
    (rawGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0)
    (constant : ℂ) (value : BurnolPaAmbientCarrier)
    (represents : (value : BurnolL2) =ᵐ[volume] fun x => burnolInnerGapForward raw x - constant) :
    (burnolMobiusWindowSourceRead value : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (4 : ℝ))] raw := by
  let coSum : ℝ → ℂ := fun x => burnolInnerGapForward raw x - constant
  have smallCoSum : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → coSum x = coSum 0 := by
    intro x small
    dsimp only [coSum]
    rw [burnolInnerGapForward_innerGap raw rawGap small,
      burnolInnerGapForward_innerGap raw rawGap (by norm_num)]
  have mean : burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value = coSum 0 := by
    by_contra different
    have bad : ∀ᵐ x : ℝ ∂volume.restrict (symmetricInterval (1 / 4 : ℝ)), False := by
      have physicalGap : (value : BurnolL2) =ᵐ[
          volume.restrict (symmetricInterval (1 / 4 : ℝ))]
            fun _ => burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value :=
        burnolAmbientGap_ae value
      filter_upwards [physicalGap, ae_restrict_of_ae represents,
        ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))] with x hgap hvalue inside
      have actual : (value : BurnolL2) x = coSum x := hvalue
      exact different (hgap.symm.trans (actual.trans (smallCoSum (abs_le.mpr inside))))
    have measureZero : (volume.restrict (symmetricInterval (1 / 4 : ℝ))) univ = 0 := by
      simpa only [ae_iff, not_false_eq_true, ofPred_true] using bad
    norm_num [symmetricInterval] at measureZero
  have scaled (m : ℕ+) : ∀ᵐ x : ℝ ∂volume,
      (value : BurnolL2) (x / (m : ℕ)) = coSum (x / (m : ℕ)) := by
    have positive : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
    have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := ((m : ℕ) : ℝ)⁻¹) (inv_ne_zero positive.ne')
    simpa only [coSum, smul_eq_mul, inv_mul_eq_div] using qmp.ae represents
  filter_upwards [burnolMobiusWindowSourceRead_coeFn value,
    ae_restrict_of_ae (ae_all_iff.mpr scaled),
    ae_restrict_mem (measurableSet_symmetricInterval (4 : ℝ))]
      with x hwindow hscaled inside
  rw [hwindow]
  calc
    _ = ∑ m ∈ burnolCenteredMobiusCutoffFinset 4,
        burnolCenteredMobiusSummand coSum x m := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hscaled m, mean]
      unfold burnolCenteredMobiusSummand
      ring
    _ = burnolCenteredMobiusInverse coSum x :=
      (burnolMobiusFixedWindow_sum coSum smallCoSum x (abs_le.mpr inside)).symm
    _ = raw x := burnolCenteredMobiusInverse_forward_innerGap raw rawGap _ x

/-- Zero-extension of the same finite read; the raw source is not promoted to a global L² carrier. -/
theorem burnolMobiusSourceL2_forward_raw (raw : ℝ → ℂ)
    (rawGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0)
    (constant : ℂ) (value : BurnolPaAmbientCarrier)
    (represents : (value : BurnolL2) =ᵐ[volume] fun x => burnolInnerGapForward raw x - constant) :
    (burnolMobiusSourceL2 value : ℝ → ℂ) =ᵐ[volume] (symmetricInterval (4 : ℝ)).indicator raw := by
  have window := (ae_restrict_iff' (measurableSet_symmetricInterval (4 : ℝ))).mp
    (burnolMobiusWindowSourceRead_forward_raw raw rawGap constant value represents)
  filter_upwards [window, burnolRadiusZeroExtension_coe (burnolMobiusWindowSourceRead value)] with x read extended
  change burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead value) x = _
  rw [extended]
  by_cases inside : x ∈ symmetricInterval (4 : ℝ)
  · rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside, read inside]
  · rw [Set.indicator_of_notMem inside, Set.indicator_of_notMem inside]

theorem burnolRemainderSourceRead_window_source (source : BurnolL2) (value : BurnolPaAmbientCarrier)
    (even : reflectL2 source = source)
    (gap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0)
    (realizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test =
      ∫ x : ℝ, test x * (value : BurnolL2) x) :
    burnolMobiusWindowSourceRead value = burnolRadiusRestriction 4 source := by
  obtain ⟨raw, sourceRep, rawGap, valueRep⟩ :=
    burnolRemainderSourceRead_realization_ae source (value : BurnolL2) even gap realizes
  have window := burnolMobiusWindowSourceRead_forward_raw raw rawGap _ value valueRep
  apply Lp.ext
  filter_upwards [window, ae_restrict_of_ae sourceRep,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (4 : ℝ)) source] with x read rawAt restrictionAt
  rw [read]
  exact rawAt.symm.trans restrictionAt.symm

theorem burnolRemainderSourceRead_cutoff_source (source : BurnolL2) (value : BurnolPaAmbientCarrier)
    (even : reflectL2 source = source)
    (gap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0)
    (realizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test =
      ∫ x : ℝ, test x * (value : BurnolL2) x) :
    burnolMobiusSourceL2 value =
      burnolRadiusZeroExtension 4 (burnolRadiusRestriction 4 source) :=
  congrArg (burnolRadiusZeroExtension 4)
    (burnolRemainderSourceRead_window_source source value even gap realizes)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
