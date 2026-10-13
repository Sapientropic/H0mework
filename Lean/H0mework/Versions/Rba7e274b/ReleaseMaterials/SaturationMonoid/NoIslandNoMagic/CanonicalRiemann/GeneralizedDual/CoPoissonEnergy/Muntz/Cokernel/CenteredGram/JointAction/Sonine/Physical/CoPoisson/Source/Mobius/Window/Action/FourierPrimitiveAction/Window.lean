import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierPrimitiveAction.Profile
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierPrimitiveActionSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource

def fullFourierProfile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  anchoredFourierProfile coordinate |x|

theorem original_FP_full_profile (coordinate : BurnolCompletedMellinCoordinate) :
    (OriginalRieszFiniteSource.fourierPrimitive coordinate:ℝ→ℂ)=ᵐ[volume] fullFourierProfile coordinate := by
  filter_upwards [original_FP_read coordinate,volume.ae_ne (0:ℝ)] with x source nonzero
  rw [source]
  unfold fullFourierProfile
  by_cases positive : 0<x
  · rw [abs_of_pos positive,original_FP_anchored_profile coordinate x positive]
  · have negative : x<0 := lt_of_le_of_ne (le_of_not_gt positive) nonzero
    rw [abs_of_neg negative,← original_FP_even coordinate x,original_FP_anchored_profile coordinate (-x) (by linarith)]

 theorem actual_FP_profile_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fullFourierProfile coordinate) (symmetricInterval (1/4:ℝ)) := by
  apply ((Lp.memLp (OriginalRieszFiniteSource.fourierPrimitive coordinate)).locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_Icc) |>.congr
  exact ae_restrict_of_ae (original_FP_full_profile coordinate)

def sourceFourierMean (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  (2:ℂ)*(∫ x : ℝ in symmetricInterval (1/4:ℝ),fullFourierProfile coordinate x)

theorem original_FP_mean (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.actualMean (OriginalRieszFiniteSource.fourierPrimitive coordinate)=sourceFourierMean coordinate := by
  change (‖intervalConstant (1/4:ℝ)‖^2:ℂ)⁻¹*inner ℂ (intervalConstant (1/4:ℝ))
    (burnolRadiusRestriction (1/4:ℝ) (OriginalRieszFiniteSource.fourierPrimitive coordinate))=_
  rw [burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<1/4)]
  norm_num
  rw [L2.inner_def]
  unfold sourceFourierMean
  congr 1
  apply integral_congr_ae
  filter_upwards [intervalConstant_coeFn (1/4:ℝ),LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (1/4:ℝ)) (OriginalRieszFiniteSource.fourierPrimitive coordinate),
    ae_restrict_of_ae (original_FP_full_profile coordinate)] with x constant restricted source
  change burnolRadiusRestriction (1/4:ℝ) (OriginalRieszFiniteSource.fourierPrimitive coordinate) x=
    OriginalRieszFiniteSource.fourierPrimitive coordinate x at restricted
  rw [constant,restricted,source,RCLike.inner_apply]
  simp only [starRingEnd_apply,star_one,mul_one]

 theorem actual_full_FP_window (coordinate : BurnolCompletedMellinCoordinate) :
    (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate):ℝ→ℂ)=ᵐ[volume]
      (symmetricInterval 4).indicator (fun x=>∑ n∈burnolCenteredMobiusCutoffFinset 4,
        Paid.coefficient n*(fullFourierProfile coordinate (x/(n:ℕ))-sourceFourierMean coordinate)) := by
  have lower := (ae_restrict_iff' (measurableSet_symmetricInterval 4)).mp
    (FiniteMobiusResolventFlux.lower_window_read (OriginalRieszFiniteSource.fourierPrimitive coordinate))
  have pulled : ∀ᵐ x : ℝ ∂volume,∀ n : ℕ+,
      OriginalRieszFiniteSource.fourierPrimitive coordinate (x/(n:ℕ))=fullFourierProfile coordinate (x/(n:ℕ)) := by
    apply ae_all_iff.mpr
    intro n
    have qmp : Measure.QuasiMeasurePreserving (fun x:ℝ=>x/(n:ℕ)) volume volume := by
      simpa only [div_eq_mul_inv,mul_comm,smul_eq_mul] using
        Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=((n:ℕ):ℝ)⁻¹)
          (inv_ne_zero (by exact_mod_cast n.ne_zero))
    exact qmp.ae_eq (original_FP_full_profile coordinate)
  filter_upwards [lower,pulled,burnolRadiusZeroExtension_coe
    (FiniteMobiusResolventFlux.lowerWindow (OriginalRieszFiniteSource.fourierPrimitive coordinate))] with x lower pulled extended
  unfold Paid.M
  rw [ContinuousLinearMap.comp_apply,extended]
  by_cases inside : x∈symmetricInterval 4
  · simp only [indicator_of_mem inside]
    rw [lower inside,original_FP_mean]
    apply Finset.sum_congr rfl
    intro n _
    rw [pulled n]
  · simp only [indicator_of_notMem inside]
def fullMobiusFourierProfile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (symmetricInterval 4).indicator (fun x=>∑ n∈burnolCenteredMobiusCutoffFinset 4,
    Paid.coefficient n*(fullFourierProfile coordinate (x/(n:ℕ))-sourceFourierMean coordinate)) x

theorem original_MFP_profile (coordinate : BurnolCompletedMellinCoordinate) :
    (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate):ℝ→ℂ)=ᵐ[volume] fullMobiusFourierProfile coordinate :=
  actual_full_FP_window coordinate

 theorem actual_MFP_profile_memLp (coordinate : BurnolCompletedMellinCoordinate) :
    MemLp (fullMobiusFourierProfile coordinate) 2 volume :=
  (Lp.memLp (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))).ae_eq (original_MFP_profile coordinate)

def tateMobiusFourierProfile (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  burnolTateReciprocalRaw (fullMobiusFourierProfile coordinate)

theorem original_TMFP_profile (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolTateReciprocalL2 (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)):ℝ→ℂ)=ᵐ[volume]
      tateMobiusFourierProfile coordinate := by
  have raw := original_MFP_profile coordinate
  have moved := burnolTateReciprocalRaw_ae_congr (Lp.memLp (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate)))
    ((Lp.memLp (Paid.M (OriginalRieszFiniteSource.fourierPrimitive coordinate))).ae_eq raw) raw
  exact (burnolTateReciprocalL2_coeFn _).trans moved

end OriginalFourierPrimitiveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
