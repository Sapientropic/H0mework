import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.NativeGramPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualNativePreparedLegPriceOwn
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussDensityCore GaussComposite.SourceGraph
open CanonicalScalarPreparation PreparationChartGuard PreparationScalarCoordinates
open CanonicalPreparationCreation CanonicalPreparationCore.Completed
open CanonicalGradedSpatial (Localizer)
open GaussHistoryHilbert (physicalChart)
open MeasureTheory Set Filter
open scoped Topology ContDiff Distributions ENNReal

abbrev nativePhi := actualNativeLocalizer

theorem original_native_cutoff_gram_price (z : SourceCoordinateSlice) :
    gramWeight z * (nativePhi z)^2 ≤ 169 * (nativePhi z)^2 := by
  by_cases zero : nativePhi z = 0
  · simp [zero]
  · have inside : z ∈ tsupport actualNativeLocalizer := subset_tsupport _ zero
    exact mul_le_mul_of_nonneg_right ((original_native_gramWeight_bound z inside).trans
      (by norm_num : (151 : ℝ) ≤ 169)) (sq_nonneg _)

theorem original_native_relative_eLpNorm (f : physicalChart → ℂ) :
    eLpNorm (fun z : physicalChart => (nativePhi z : ℂ) * f z) 2 graphMeasure ≤
      eLpNorm (fun z : physicalChart => (13 : ℂ) * ((nativePhi z : ℂ) * f z)) 2
        (GaussHistoryHilbert.numberMeasure 1) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  have measurableWeight : Measurable (fun z : physicalChart => ENNReal.ofReal (gramWeight z)) :=
    (gramWeight_continuous.comp continuous_subtype_val).measurable.ennreal_ofReal
  rw [graphMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _ measurableWeight
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply lintegral_mono
  intro z
  have point := mul_le_mul_of_nonneg_right (original_native_cutoff_gram_price z) (sq_nonneg ‖f z‖)
  simp only [Pi.mul_apply, ENNReal.rpow_two, ← ofReal_norm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (gramWeight_pos z).le]
  apply ENNReal.ofReal_le_ofReal
  have norm13 : ‖(13 : ℂ)‖ = (13 : ℝ) := by norm_num
  simpa only [norm_mul, norm13, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc,
    show (13 : ℝ) ^ 2 = 169 by norm_num] using point

theorem original_native_cutCore_relative_bound (f : ScalarTest) :
    ‖core (cutCore nativePhi f)‖ ≤ 13 * ‖scalarCore (cutCore nativePhi f)‖ := by
  have estimate := original_native_relative_eLpNorm (fun z : physicalChart => f z)
  have normRead : eLpNorm (fun z : physicalChart => (nativePhi z : ℂ) * f z) 2
      (GaussHistoryHilbert.numberMeasure 1) = ENNReal.ofReal ‖scalarCore (cutCore nativePhi f)‖ := by
    rw [ofReal_norm, Lp.enorm_def]
    exact (eLpNorm_congr_ae (scalarLp_ae 1 (cutCore nativePhi f))).symm
  have right : eLpNorm (fun z : physicalChart => (13 : ℂ) * ((nativePhi z : ℂ) * f z)) 2
      (GaussHistoryHilbert.numberMeasure 1) =
      ENNReal.ofReal (13 * ‖scalarCore (cutCore nativePhi f)‖) := by
    rw [show (fun z : physicalChart => (13 : ℂ) * ((nativePhi z : ℂ) * f z)) =
      (13 : ℂ) • (fun z : physicalChart => (nativePhi z : ℂ) * f z) from rfl,
      eLpNorm_const_smul, ← ofReal_norm, normRead]
    norm_num [ENNReal.ofReal_mul]
  have left : ENNReal.ofReal ‖core (cutCore nativePhi f)‖ =
      eLpNorm (fun z : physicalChart => (nativePhi z : ℂ) * f z) 2 graphMeasure := by
    rw [ofReal_norm, Lp.enorm_def]
    exact eLpNorm_congr_ae (coreProfile_ae (cutCore nativePhi f))
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 13 * ‖scalarCore (cutCore nativePhi f)‖)).mp
  rw [left]
  exact estimate.trans_eq right

theorem original_native_double_cutCore (f : ScalarTest) :
    cutCore (outerCutoff nativePhi) (cutCore nativePhi f) = cutCore nativePhi f := by
  apply DFunLike.ext
  intro z
  change ((outerCutoff nativePhi z : ℂ) * ((nativePhi z : ℂ) * f z)) = (nativePhi z : ℂ) * f z
  rw [← mul_assoc, ← Complex.ofReal_mul, outerCutoff_retains]

theorem original_native_localized_profile_bound (f : localizedSpace nativePhi) :
    ‖localizedProfile nativePhi f‖ ≤ 13 * ‖f‖ := by
  have closed : IsClosed {u : ScalarSpace |
      ‖localProfile (outerCutoff nativePhi) u‖ ≤ 13 * ‖u‖} := isClosed_le (by fun_prop) (by fun_prop)
  apply closure_minimal ?_ closed f.property
  rintro _ ⟨u, rfl⟩
  change ‖localProfile (outerCutoff nativePhi) (scalarCutoff nativePhi u)‖ ≤
    13 * ‖scalarCutoff nativePhi u‖
  refine scalarCore_dense.induction_on u (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [scalarCutoff_core, localProfile_core, original_native_double_cutCore]
  exact original_native_cutCore_relative_bound g

theorem original_native_zeroLocalized_profile_bound (f : zeroLocalizedSpace nativePhi) :
    ‖zeroLocalizedProfile nativePhi f‖ ≤ 13 * ‖f‖ :=
  (original_native_localized_profile_bound (localizedNumberRaise nativePhi f)).trans_eq
    (by rw [(localizedNumberRaise nativePhi).norm_map])

end LowEnergy.ActualNativePreparedLegPriceOwn
