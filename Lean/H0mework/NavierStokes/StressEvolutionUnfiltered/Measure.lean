import H0mework.NavierStokes.StressTimeControl.UnfilteredBudget
import H0mework.NavierStokes.StressEvolutionWhole.WholeH1ShiftedSource

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalTimeMeasure

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeResolventCompactness NativeWholeResolvent
open NativeOriginalResolventInput NativeOriginalGradientTime NativeWholeH1Mixed NativeOriginalNegativeOneBudget

noncomputable section

theorem interval_integrable_of_common {E : Type*} [NormedAddCommGroup E]
    {value : Icc (0 : ℝ) 1 → E} (integrable : Integrable value (commonTimeMeasure 1)) :
    IntervalIntegrable (fun time => value (projIcc 0 1 zero_le_one time)) volume 0 1 := by
  have common : commonTimeMeasure 1 = Measure.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one,
    integrableOn_iff_comap_subtypeVal measurableSet_Icc, ← common]
  simpa only [Function.comp_def, projIcc_val] using integrable

theorem shifted_integrable {E : Type*} [NormedAddCommGroup E] {value : ℝ → E}
    (integrable : IntervalIntegrable value volume 0 1) {left right shift : ℝ}
    (leftInside : left + shift ∈ Icc (0 : ℝ) 1) (rightInside : right + shift ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun time => value (time + shift)) volume left right := by
  rw [IntervalIntegrable.comp_add_right_iff]
  apply integrable.mono_set
  rw [uIcc_of_le zero_le_one]
  exact uIcc_subset_Icc leftInside rightInside

theorem shifted_integral_bound {value : ℝ → ℝ} {bound : ℝ}
    (integrable : IntervalIntegrable value volume 0 1) (nonnegative : ∀ time, 0 ≤ value time)
    (budget : (∫ time in 0..1, value time) ≤ bound) {left right shift : ℝ}
    (ordered : left ≤ right) (leftInside : 0 ≤ left + shift) (rightInside : right + shift ≤ 1) :
    (∫ time in left..right, value (time + shift)) ≤ bound := by
  rw [intervalIntegral.integral_comp_add_right]
  exact (intervalIntegral.integral_mono_interval leftInside (add_le_add ordered le_rfl) rightInside
    (Eventually.of_forall nonnegative) integrable).trans budget

theorem shifted_pair_ae {P : Icc (0 : ℝ) 1 → Prop} {left right shift : ℝ}
    (source : ∀ᵐ time ∂commonTimeMeasure 1, P time)
    (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    ∀ᵐ time ∂volume.restrict (Icc left right),
      P (projIcc 0 1 zero_le_one time) ∧ P (projIcc 0 1 zero_le_one (time + shift)) := by
  have common : commonTimeMeasure 1 = Measure.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  have interval : ∀ᵐ time ∂volume.restrict (Icc (0 : ℝ) 1), P (projIcc 0 1 zero_le_one time) := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).mpr
    rw [common] at source
    simpa only [projIcc_val] using source
  have extended := (ae_restrict_iff' measurableSet_Icc).mp interval
  have translated := (measurePreserving_add_right (volume : Measure ℝ) shift).quasiMeasurePreserving.ae extended
  filter_upwards [ae_restrict_of_ae extended, ae_restrict_of_ae translated, ae_restrict_mem measurableSet_Icc]
    with time first last inside
  exact ⟨first (firstInside inside), last (lastInside inside)⟩

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def physical (source : StressAt escape) (pointLe : point ≤ 1) (time : ℝ) : wholePhysical :=
  meanInput source pointLe (.fixed (projIcc 0 1 zero_le_one time))

def gradient (source : StressAt escape) (pointLe : point ≤ 1) (time : ℝ) : ℝ :=
  gradientMass (physical source pointLe time)

theorem physical_bound (source : StressAt escape) (pointLe : point ≤ 1) (time : ℝ) :
    ‖physical source pointLe time‖ ≤ ‖ledger.family.endpointReceipt.velocityEndpoint‖ :=
  NativeRecoveryEscapeCarrier.endpoint_norm_bound _

theorem physical_integrable (source : StressAt escape) (pointLe : point ≤ 1) :
    IntervalIntegrable (fun time => (physical source pointLe time).1) volume 0 1 :=
  interval_integrable_of_common (Integrable.of_bound (mean_measurable source pointLe)
    ‖ledger.family.endpointReceipt.velocityEndpoint‖ (Eventually.of_forall fun time => NativeRecoveryEscapeCarrier.endpoint_norm_bound time))

theorem gradient_integrable (source : StressAt escape) (pointLe : point ≤ 1) :
    IntervalIntegrable (gradient source pointLe) volume 0 1 :=
  interval_integrable_of_common (NativeOriginalGradientTime.gradient_integrable source pointLe)

theorem gradient_nonnegative (source : StressAt escape) (pointLe : point ≤ 1) (time : ℝ) :
    0 ≤ gradient source pointLe time := tsum_nonneg (NativeWholeH1Mixed.gradient_nonnegative _)

theorem gradient_budget (source : StressAt escape) (pointLe : point ≤ 1) :
    (∫ time in 0..1, gradient source pointLe time) ≤ gradientBudget receipt := by
  rw [← commonTime_integral_eq_intervalIntegral 1 zero_le_one]
  simpa only [gradient, physical, projIcc_val] using gradient_integral_bound source pointLe

end
end SaturationMonoid.NavierStokes.NativeOriginalTimeMeasure
