import H0mework.Versions.V2.Arithmetic.RiemannResolvent.CompleteRemainder

/-! The actual Tate involution reads the full source resolvent as an expanding orbit. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

theorem burnolTateReciprocalL2_dilation_inverse (shift : ℝ) (value : BurnolL2) :
    burnolMultiplicativeDilation shift (burnolTateReciprocalL2 value) =
      burnolTateReciprocalL2 (burnolMultiplicativeDilation (-shift) value) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  have rawMem : MemLp (burnolL2RawNormalizedDilation (-shift) value) 2 volume :=
    (Lp.memLp (burnolMultiplicativeDilation (-shift) value)).ae_eq
      (burnolMultiplicativeDilation_coeFn (-shift) value)
  have pulled := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (burnolMultiplicativeDilation (-shift) value)) rawMem
    (burnolMultiplicativeDilation_coeFn (-shift) value)
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn shift (burnolTateReciprocalL2 value),
    qmp.ae (burnolTateReciprocalL2_coeFn value),
    burnolTateReciprocalL2_coeFn (burnolMultiplicativeDilation (-shift) value), pulled]
      with x hleft hscaled hright hsource
  rw [hleft, hright, hsource]
  unfold burnolL2RawNormalizedDilation
  rw [hscaled]
  unfold burnolTateReciprocalRaw
  rw [burnolSourceReciprocal_dilation_raw]
  ring

theorem burnolTateReciprocalL2_directRightResolvent (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : BurnolL2) :
    burnolTateReciprocalL2 (burnolDirectRightResolvent z value) =
      -∫ h : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (h / 2) (burnolTateReciprocalL2 value) := by
  unfold burnolDirectRightResolvent
  rw [map_neg, ← burnolTateReciprocalL2.integral_comp_comm
    (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter value)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h _
  dsimp only [burnolDirectRightResolventIntegrand]
  rw [map_smul]
  congr 1
  simpa only [neg_div] using (burnolTateReciprocalL2_dilation_inverse (h / 2) value).symm

theorem burnolCompleteRemainderSource_tateSeed (z : ℂ) (source : burnolCompactAnnulusSource) :
    burnolTateReciprocalL2 (burnolCompleteRemainderSource z source 0) =
      (2 : ℂ) • source.1.toLp 2 volume := by
  change burnolTateReciprocalL2 ((2 : ℂ) • burnolMobiusSourceL2
    (burnolCompactAdditivePhysicalState source)) = _
  rw [map_smul]
  congr 1
  have inPa : burnolCompactAdditivePhysicalState source ∈ burnolCompactCoPoissonClosedRange := by
    simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
      burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))
  rw [← burnolMobiusSource_fourier _ inPa]
  have sameSource : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolCompactAdditivePhysicalState source) =
        burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source) := by
    apply Subtype.ext
    exact burnolCompactFourierL2_eq_reciprocalL2 source
  rw [sameSource]
  apply Lp.ext
  filter_upwards [burnolMobiusSourceExtension_compact_coeFn
      (burnolCompactTateReciprocalSource source), source.1.coeFn_toLp 2 volume]
        with x hsource htarget
  have read : burnolMobiusSourceL2
      (burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source)) x =
        burnolCompactAdditiveSource (burnolCompactTateReciprocalSource source) x := hsource
  rw [read, burnolCompactTateReciprocalSource_additiveSource, htarget]

theorem burnolCompleteRemainderSource_tateFirst (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (source : burnolCompactAnnulusSource) :
    burnolTateReciprocalL2 (burnolCompleteRemainderSource z source 1) =
      -∫ h : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (h / 2) ((2 : ℂ) • source.1.toLp 2 volume) := by
  change burnolTateReciprocalL2
    (burnolDirectRightResolvent z (burnolCompleteRemainderSource z source 0)) = _
  rw [burnolTateReciprocalL2_directRightResolvent z rightQuarter, burnolCompleteRemainderSource_tateSeed]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
