import H0mework.NavierStokes.StressEvolutionUnfiltered.Stress

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalMomentumTime

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeResolventCompactness NativeOriginalResolventInput NativeOriginalStressAction
open NativeCompleteStressAction NativeOriginalTimeMeasure NativeOriginalPhysicalTime NativeOriginalStressTime
open NativeOriginalPhysicalTimeBudget NativeOriginalNegativeOneBudget

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def actionDifference (source : StressAt escape) (pointLe : point ≤ 1) (shift time : ℝ) : State :=
  NativeUnifiedSourceActionFeed.action source pointLe (time + shift) -
    NativeUnifiedSourceActionFeed.action source pointLe time

theorem action_original (source : StressAt escape) (pointLe : point ≤ 1) (shift time : ℝ) :
    actionDifference source pointLe shift time = divergenceCLM (stressDifference source pointLe shift time) -
      viscousCLM nu (difference source pointLe shift time).1 := by
  unfold actionDifference NativeUnifiedSourceActionFeed.action
  rw [← NativeOriginalNegativeOneRate.original_writer source pointLe,
    ← NativeOriginalNegativeOneRate.original_writer source pointLe]
  change (divergenceCLM (originalStress source pointLe (.fixed (projIcc 0 1 zero_le_one (time + shift)))) -
    viscousCLM nu (physical source pointLe (time + shift)).1) -
    (divergenceCLM (originalStress source pointLe (.fixed (projIcc 0 1 zero_le_one time))) -
      viscousCLM nu (physical source pointLe time).1) = _
  rw [stressDifference, map_sub]
  change _ = _ - viscousCLM nu ((physical source pointLe (time + shift)).1 - (physical source pointLe time).1)
  rw [map_sub]
  abel

def coefficient (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) : ℝ :=
  ‖divergenceCLM‖ * stressCoefficient receipt + ‖viscousCLM nu‖

theorem coefficient_nonnegative : 0 ≤ coefficient receipt :=
  add_nonneg (mul_nonneg (norm_nonneg _) stressCoefficient_nonnegative) (norm_nonneg _)

theorem action_bound_ae (source : StressAt escape) (pointLe : point ≤ 1)
    (left right shift : ℝ) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    ∀ᵐ time ∂volume.restrict (Icc left right), ‖actionDifference source pointLe shift time‖ ≤
      coefficient receipt * ‖difference source pointLe shift time‖ := by
  filter_upwards [difference_bound_ae source pointLe left right shift firstInside lastInside] with time paid
  rw [action_original]
  have stress := (divergenceCLM.le_opNorm _).trans (mul_le_mul_of_nonneg_left paid (norm_nonneg _))
  have viscous := (viscousCLM nu).le_opNorm (difference source pointLe shift time).1
  change ‖viscousCLM nu (difference source pointLe shift time).1‖ ≤ ‖viscousCLM nu‖ * ‖difference source pointLe shift time‖ at viscous
  exact (norm_sub_le _ _).trans ((add_le_add stress viscous).trans_eq (by
    unfold coefficient
    ring))

theorem action_measurable (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    AEStronglyMeasurable (actionDifference source pointLe shift) (volume.restrict (Icc left right)) := by
  have original := (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mp
    (difference_integrable source pointLe ordered firstInside lastInside)
  have stress := divergenceCLM.continuous.comp_aestronglyMeasurable (difference_measurable source pointLe ordered firstInside lastInside)
  have viscous := (viscousCLM nu).continuous.comp_aestronglyMeasurable original.aestronglyMeasurable
  apply (stress.sub viscous).congr
  exact Eventually.of_forall fun time => (action_original source pointLe shift time).symm

theorem action_square_bound_ae (source : StressAt escape) (pointLe : point ≤ 1)
    (left right shift : ℝ) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    ∀ᵐ time ∂volume.restrict (Icc left right), ‖actionDifference source pointLe shift time‖ ^ 2 ≤
      coefficient receipt ^ 2 * ‖difference source pointLe shift time‖ ^ 2 := by
  filter_upwards [action_bound_ae source pointLe left right shift firstInside lastInside] with time paid
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) paid 2

theorem action_mass_integrable (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    Integrable (fun time => ‖actionDifference source pointLe shift time‖ ^ 2) (volume.restrict (Icc left right)) := by
  apply (NativeOriginalPhysicalTimeBudget.difference_mass_integrable source pointLe ordered firstInside lastInside).const_mul
    (coefficient receipt ^ 2) |>.mono' (action_measurable source pointLe ordered firstInside lastInside |>.norm.pow 2)
  filter_upwards [action_square_bound_ae source pointLe left right shift firstInside lastInside] with time paid
  change ‖‖actionDifference source pointLe shift time‖ ^ 2‖ ≤ _
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using paid

theorem source_action_integral (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (positive : 0 ≤ shift) (leftInside : 0 ≤ left)
    (rightInside : right + shift ≤ 1) :
    (∫ time in left..right, ‖actionDifference source pointLe shift time‖ ^ 2) ^ 2 ≤
      coefficient receipt ^ 4 *
        (8 * ‖ledger.family.endpointReceipt.velocityEndpoint‖ * (2 * Real.pi) ^ 2 *
          gradientBudget receipt * budget receipt * shift) := by
  have firstInside : Icc left right ⊆ Icc (0 : ℝ) 1 :=
    fun time inside => ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1) :=
    fun time inside => ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have targetInt := action_mass_integrable source pointLe ordered firstInside lastInside
  have velocityInt := NativeOriginalPhysicalTimeBudget.difference_mass_integrable source pointLe ordered firstInside lastInside
  have bound := integral_mono_ae targetInt (velocityInt.const_mul (coefficient receipt ^ 2))
    (action_square_bound_ae source pointLe left right shift firstInside lastInside)
  rw [integral_const_mul] at bound
  have converted (f : ℝ → ℝ) : (∫ time in Icc left right, f time) = ∫ time in left..right, f time := by
    rw [intervalIntegral.integral_of_le ordered, ← integral_Icc_eq_integral_Ioc]
  rw [converted, converted] at bound
  have squared := pow_le_pow_left₀
    (intervalIntegral.integral_nonneg_of_forall ordered (fun time => sq_nonneg ‖actionDifference source pointLe shift time‖)) bound 2
  rw [mul_pow, ← pow_mul] at squared
  exact squared.trans (mul_le_mul_of_nonneg_left
    (source_physical_integral source pointLe ordered positive leftInside rightInside) (pow_nonneg coefficient_nonnegative 4))

end
end SaturationMonoid.NavierStokes.NativeOriginalMomentumTime
