import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.TwoMoments
import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.ColumnMass
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace

def originalB (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)

def innerBand (h : ℝ) : Set ℝ := {y | (1/4:ℝ)*Real.exp (-h) < |y| ∧ |y|≤(1/4:ℝ)}
def outerBand (h : ℝ) : Set ℝ := {x | (1/4:ℝ) < |x| ∧ |x|≤(1/4:ℝ)*Real.exp h}

 theorem original_B_supported (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalPaPhysicalGreen.originalPhysicalCutoff (1/4:ℝ) (originalB coordinate)=originalB coordinate := by
  change burnolRadiusZeroExtension (1/4:ℝ) (burnolRadiusRestriction (1/4:ℝ)
    (burnolRadiusZeroExtension (1/4:ℝ) (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))=_
  rw [burnolRadiusRestriction_zeroExtension]
  rfl

 theorem sampled_quarter_source_zero (value : BurnolL2)
    (supported : OriginalPaPhysicalGreen.originalPhysicalCutoff (1/4:ℝ) value=value) :
    burnolAnnulusSamplingL2 value 0=0 := by
  have source := OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn (1/4:ℝ) value
  rw [supported] at source
  apply Lp.ext
  filter_upwards [burnolAnnulusSamplingL2_coeFn value 0,source,Lp.coeFn_zero ℂ 2 volume] with x sampled source zero
  rw [sampled,zero]
  simp only [Pi.zero_apply,burnolAnnulusSamplingRaw,Nat.cast_zero,zero_add,one_mul]
  by_cases annulus : x∈burnolSamplingAnnulus
  · rw [indicator_of_mem annulus,source,indicator_of_notMem (show x∉symmetricInterval (1/4:ℝ) from fun h=>not_le_of_gt annulus.1 (abs_le.mpr h))]
  · rw [indicator_of_notMem annulus]

 theorem original_negative_sample_zero (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h) :
    burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate (-h)) 0=0 :=
  sampled_quarter_source_zero _ (OriginalRieszFinitePairing.fourierColumn_negative_quarter coordinate h nonnegative)

 theorem original_paired_sample_positive (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h) :
    OriginalPrimitiveRankBalance.pairedColumn coordinate h=
      burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0 := by
  rw [OriginalPrimitiveRankBalance.pairedColumn,original_negative_sample_zero coordinate h nonnegative,add_zero]

-- The first character term lives in the original quarter and disappears only under the actual annulus projection.
theorem original_positive_sample_raw (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0 : ℝ→ℂ)=ᵐ[volume]
      (outerBand h).indicator (fun x=>-(Real.exp (-h/2):ℂ)*originalB coordinate (Real.exp (-h)*x)) := by
  let B := originalB coordinate
  let chi := fullMellinTranslationCharacter (star coordinate.value) h
  have same := OriginalRieszFinitePairing.fourierColumn_action coordinate h
  change OriginalRieszFiniteColumns.fourierColumn coordinate h=chi • B-burnolMultiplicativeDilation (-h) B at same
  have support := OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn (1/4:ℝ) B
  rw [original_B_supported coordinate] at support
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ=>Real.exp (-h)*x) volume volume := by
    have actual : Measure.QuasiMeasurePreserving (fun x : ℝ=>Real.exp (-h) • x) volume volume :=
      Measure.quasiMeasurePreserving_smul (μ:=(volume : Measure ℝ)) (r:=Real.exp (-h)) (Real.exp_ne_zero _)
    exact actual
  have movedSupport := qmp.ae_eq support
  have scaleBound : (1/4:ℝ)*Real.exp h≤4 := by
    have scale := (Real.exp_le_exp.mpr bounded).trans_eq (Real.exp_log (by norm_num : (0:ℝ)<2))
    linarith
  have _sourceNonnegative := nonnegative
  filter_upwards [burnolAnnulusSamplingL2_coeFn (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0,
    Lp.coeFn_sub (chi • B) (burnolMultiplicativeDilation (-h) B),Lp.coeFn_smul chi B,
    burnolMultiplicativeDilation_coeFn (-h) B,support,movedSupport] with x sample difference scalar moved direct inverse
  rw [same] at sample
  change B x=(symmetricInterval (1/4:ℝ)).indicator (B : ℝ→ℂ) x at direct
  change B (Real.exp (-h)*x)=(symmetricInterval (1/4:ℝ)).indicator (B : ℝ→ℂ) (Real.exp (-h)*x) at inverse
  rw [same,sample]
  simp only [burnolAnnulusSamplingRaw,Nat.cast_zero,zero_add,one_mul]
  have radius : Real.exp (-h)*x∈symmetricInterval (1/4:ℝ) ↔ |x|≤(1/4:ℝ)*Real.exp h := by
    change -(1/4:ℝ)≤Real.exp (-h)*x ∧ Real.exp (-h)*x≤(1/4:ℝ) ↔ _
    rw [← abs_le,abs_mul,abs_of_pos (Real.exp_pos _),Real.exp_neg]
    rw [mul_comm ((Real.exp h)⁻¹) |x|,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos h)]
  by_cases band : x∈outerBand h
  · have annulus : x∈burnolSamplingAnnulus := ⟨band.1,band.2.trans scaleBound⟩
    rw [indicator_of_mem band,indicator_of_mem annulus,difference]
    change (chi • B : BurnolL2) x-burnolMultiplicativeDilation (-h) B x=_
    rw [scalar]
    change chi*B x-burnolMultiplicativeDilation (-h) B x=_
    rw [direct,indicator_of_notMem (show x∉symmetricInterval (1/4:ℝ) from fun h=>not_le_of_gt band.1 (abs_le.mpr h)),moved]
    simp only [mul_zero,zero_sub,burnolL2RawNormalizedDilation,neg_mul,neg_div]
    rfl
  · rw [indicator_of_notMem band]
    by_cases annulus : x∈burnolSamplingAnnulus
    · rw [indicator_of_mem annulus,difference]
      change (chi • B : BurnolL2) x-burnolMultiplicativeDilation (-h) B x=0
      rw [scalar]
      change chi*B x-burnolMultiplicativeDilation (-h) B x=0
      rw [direct,indicator_of_notMem (show x∉symmetricInterval (1/4:ℝ) from fun h=>not_le_of_gt annulus.1 (abs_le.mpr h)),moved]
      have outside : Real.exp (-h)*x∉symmetricInterval (1/4:ℝ) := by
        intro inside
        exact band ⟨annulus.1,radius.mp inside⟩
      unfold burnolL2RawNormalizedDilation
      rw [inverse,indicator_of_notMem outside]
      simp only [mul_zero,sub_self]
    · rw [indicator_of_notMem annulus]

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
