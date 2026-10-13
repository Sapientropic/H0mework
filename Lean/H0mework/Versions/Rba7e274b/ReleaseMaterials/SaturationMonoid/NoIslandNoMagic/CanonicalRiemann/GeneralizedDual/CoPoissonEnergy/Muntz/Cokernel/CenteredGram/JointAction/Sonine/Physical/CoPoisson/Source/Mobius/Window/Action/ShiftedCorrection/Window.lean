import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.Inverse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalInverseReturnActionSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource
local notation "q" => (1/4:ℝ)

def returnWindowProfile (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  (symmetricInterval q).indicator (burnolRieszReturnRaw coordinate)

theorem original_return_window_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (wholeReturn coordinate:ℝ→ℂ)=ᵐ[volume] returnWindowProfile coordinate := by
  have raw := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (Constructor.returnState_read coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe (Constructor.returnState coordinate:BurnolQuarterIntervalL2),raw] with x extended source
  change wholeReturn coordinate x=(symmetricInterval q).indicator
    (fun y=>(Constructor.returnState coordinate:BurnolQuarterIntervalL2) y) x at extended
  unfold returnWindowProfile
  rw [extended]
  by_cases inside : x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,source inside]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

theorem original_return_window_mean_zero (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.actualMean (wholeReturn coordinate)=0 := by
  change (‖intervalConstant q‖^2:ℂ)⁻¹*inner ℂ (intervalConstant q)
    (burnolRadiusRestriction q (burnolRadiusZeroExtension q (Constructor.returnState coordinate:BurnolQuarterIntervalL2)))=0
  rw [burnolRadiusRestriction_zeroExtension]
  have zero := (Constructor.returnState coordinate).property (intervalConstant q) (Submodule.mem_span_singleton_self _)
  rw [zero,mul_zero]

theorem original_inverse_return_mean_exact (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.actualMean (fourierL2 (wholeReturn coordinate))=returnMean coordinate := by
  change (‖intervalConstant q‖^2:ℂ)⁻¹*inner ℂ (intervalConstant q)
    (burnolRadiusRestriction q (fourierL2 (burnolRadiusZeroExtension q (Constructor.returnState coordinate:BurnolQuarterIntervalL2))))=returnMean coordinate
  unfold returnMean burnolQuarterMeanCoefficient
  simp only [div_eq_mul_inv,Complex.ofReal_pow]
  change (‖intervalConstant q‖^2:ℂ)⁻¹*inner ℂ (intervalConstant q) (burnolTruncatedFourier (Constructor.returnState coordinate:BurnolQuarterIntervalL2))=
    inner ℂ (intervalConstant q) (burnolTruncatedFourier (Constructor.returnState coordinate:BurnolQuarterIntervalL2))*(‖intervalConstant q‖^2:ℂ)⁻¹
  ring

 theorem original_inverse_mean_profile_exact (coordinate : BurnolCompletedMellinCoordinate) :
    inverseReturnMean coordinate=returnMean coordinate :=
  (original_inverse_return_mean coordinate).symm.trans (original_inverse_return_mean_exact coordinate)

-- The two actual fields supply their source-generated means before the finite programme acts.
theorem actual_full_window_profile (value : BurnolL2) (profile : ℝ→ℂ) (mean : ℂ)
    (source : (value:ℝ→ℂ)=ᵐ[volume] profile) (sourceMean : Paid.actualMean value=mean) :
    (Paid.M value:ℝ→ℂ)=ᵐ[volume] (symmetricInterval 4).indicator
      (fun x=>∑ n∈burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n*(profile (x/(n:ℕ))-mean)) := by
  have lower := (ae_restrict_iff' (measurableSet_symmetricInterval 4)).mp
    (FiniteMobiusResolventFlux.lower_window_read value)
  have pulled : ∀ᵐ x : ℝ ∂volume,∀ n : ℕ+,value (x/(n:ℕ))=profile (x/(n:ℕ)) := by
    apply ae_all_iff.mpr
    intro n
    have qmp : Measure.QuasiMeasurePreserving (fun x:ℝ=>x/(n:ℕ)) volume volume := by
      simpa only [div_eq_mul_inv,mul_comm,smul_eq_mul] using
        Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=((n:ℕ):ℝ)⁻¹)
          (inv_ne_zero (by exact_mod_cast n.ne_zero))
    exact qmp.ae_eq source
  filter_upwards [lower,pulled,burnolRadiusZeroExtension_coe (FiniteMobiusResolventFlux.lowerWindow value)] with x lower pulled extended
  unfold Paid.M
  rw [ContinuousLinearMap.comp_apply,extended]
  by_cases inside : x∈symmetricInterval 4
  · simp only [indicator_of_mem inside]
    rw [lower inside,sourceMean]
    apply Finset.sum_congr rfl
    intro n _
    rw [pulled n]
  · simp only [indicator_of_notMem inside]

def inverseMobiusProfile (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  (symmetricInterval 4).indicator (fun x=>∑ n∈burnolCenteredMobiusCutoffFinset 4,
    Paid.coefficient n*(burnolRieszSingleFourierSourceRaw coordinate (x/(n:ℕ))-Translator.ForcingWhole.raw coordinate (x/(n:ℕ))+Translator.ForcingMeanZero.mean coordinate))
def returnMobiusProfile (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  (symmetricInterval 4).indicator (fun x=>∑ n∈burnolCenteredMobiusCutoffFinset 4,
    Paid.coefficient n*returnWindowProfile coordinate (x/(n:ℕ)))

theorem original_inverse_M_return_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (Paid.M (fourierL2 (wholeReturn coordinate)):ℝ→ℂ)=ᵐ[volume] inverseMobiusProfile coordinate := by
  have source:=actual_full_window_profile _ _ _ (original_return_fourier_raw coordinate) (original_inverse_return_mean_exact coordinate)
  apply source.trans
  exact Filter.EventuallyEq.of_eq (by
    funext x
    unfold inverseMobiusProfile
    congr 1
    funext y
    apply Finset.sum_congr rfl
    intro n _
    unfold fullInverseReturnProfile
    ring)


theorem original_M_return_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (Paid.M (wholeReturn coordinate):ℝ→ℂ)=ᵐ[volume] returnMobiusProfile coordinate := by
  simpa only [sub_zero,returnMobiusProfile] using actual_full_window_profile _ _ _ (original_return_window_raw coordinate) (original_return_window_mean_zero coordinate)

def tateReturnMobiusProfile (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  burnolTateReciprocalRaw (returnMobiusProfile coordinate)

theorem original_TM_return_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolTateReciprocalL2 (Paid.M (wholeReturn coordinate)):ℝ→ℂ)=ᵐ[volume] tateReturnMobiusProfile coordinate := by
  have raw:=original_M_return_raw coordinate
  have moved:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (Paid.M (wholeReturn coordinate)))
    ((Lp.memLp (Paid.M (wholeReturn coordinate))).ae_eq raw) raw
  exact (burnolTateReciprocalL2_coeFn _).trans moved
end OriginalInverseReturnActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
