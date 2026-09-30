import H0mework.NavierStokes.StressEvolutionUnfiltered.Control
import H0mework.NavierStokes.StressEvolutionUnfiltered.StressAlgebra

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalStressTime

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeOriginalResolventInput NativeOriginalStressAction
open NativeEndpointVelocityCarrier NativeCompleteStressBilinear NativeStressTimeAlgebra
open NativeOriginalTimeMeasure NativeOriginalPhysicalTime NativeOriginalPhysicalTimeBudget NativeOriginalNegativeOneBudget

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def stressDifference (source : StressAt escape) (pointLe : point ≤ 1) (shift time : ℝ) : NativeCompleteStressCarrier.Space :=
  originalStress source pointLe (.fixed (projIcc 0 1 zero_le_one (time + shift))) -
    originalStress source pointLe (.fixed (projIcc 0 1 zero_le_one time))

def stressCoefficient (_receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) : ℝ :=
  2 * ‖ledger.family.endpointReceipt.velocityEndpoint‖ * ‖mixedCLM‖

theorem stressCoefficient_nonnegative : 0 ≤ stressCoefficient receipt := by unfold stressCoefficient; positivity

theorem stress_original_ae (source : StressAt escape) (pointLe : point ≤ 1) :
    ∀ᵐ time ∂commonTimeMeasure 1, originalStress source pointLe (.fixed time) =
      quadratic (meanInput source pointLe (.fixed time)).1 := by
  filter_upwards [NativeRecoveryTimeGramMeasured.source_stress_ae source pointLe] with time original
  apply NativeCompleteStressCarrier.read_injective
  rw [originalStress, NativeCompleteStressCarrier.read_ofBound, original]
  change _ = NativeCompleteStressCarrier.read (mixed (wholeVelocity (meanInput source pointLe (.fixed time)).1)
    (wholeVelocity (meanInput source pointLe (.fixed time)).1))
  rw [mixed_read, NativeHigherTimeJets.mixedFlux_diagonal, NativeOriginalGradientTime.mean_whole source pointLe time]

theorem difference_original_ae (source : StressAt escape) (pointLe : point ≤ 1)
    (left right shift : ℝ) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    ∀ᵐ time ∂volume.restrict (Icc left right), stressDifference source pointLe shift time =
      quadratic (physical source pointLe (time + shift)).1 - quadratic (physical source pointLe time).1 := by
  filter_upwards [shifted_pair_ae (stress_original_ae source pointLe) firstInside lastInside] with time same
  exact congrArg₂ (fun first last => last - first) same.1 same.2

theorem difference_bound_ae (source : StressAt escape) (pointLe : point ≤ 1)
    (left right shift : ℝ) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    ∀ᵐ time ∂volume.restrict (Icc left right), ‖stressDifference source pointLe shift time‖ ≤
      stressCoefficient receipt * ‖difference source pointLe shift time‖ := by
  filter_upwards [difference_original_ae source pointLe left right shift firstInside lastInside] with time same
  rw [same]
  change ‖quadratic (physical source pointLe (time + shift)).1 - quadratic (physical source pointLe time).1‖ ≤
    stressCoefficient receipt * ‖(physical source pointLe (time + shift)).1 - (physical source pointLe time).1‖
  have bound := add_le_add (physical_bound source pointLe (time + shift)) (physical_bound source pointLe time)
  have actual := (quadratic_difference (physical source pointLe time).1 (physical source pointLe (time + shift)).1).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bound (norm_nonneg mixedCLM)) (norm_nonneg _))
  exact actual.trans_eq (by unfold stressCoefficient; ring)

theorem difference_measurable (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    AEStronglyMeasurable (stressDifference source pointLe shift) (volume.restrict (Icc left right)) := by
  have firstInt := shifted_integrable (physical_integrable source pointLe) (left := left) (right := right) (shift := 0)
    (by simpa only [add_zero] using firstInside (left_mem_Icc.mpr ordered))
    (by simpa only [add_zero] using firstInside (right_mem_Icc.mpr ordered))
  have lastInt := shifted_integrable (physical_integrable source pointLe)
    (lastInside (left_mem_Icc.mpr ordered)) (lastInside (right_mem_Icc.mpr ordered))
  simp only [add_zero] at firstInt
  have first := (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mp firstInt
  have last := (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mp lastInt
  have actual := (quadratic_continuous.comp_aestronglyMeasurable last.aestronglyMeasurable).sub
    (quadratic_continuous.comp_aestronglyMeasurable first.aestronglyMeasurable)
  apply actual.congr
  filter_upwards [difference_original_ae source pointLe left right shift firstInside lastInside] with time same
  exact same.symm

theorem difference_square_bound_ae (source : StressAt escape) (pointLe : point ≤ 1)
    (left right shift : ℝ) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    ∀ᵐ time ∂volume.restrict (Icc left right), ‖stressDifference source pointLe shift time‖ ^ 2 ≤
      stressCoefficient receipt ^ 2 * ‖difference source pointLe shift time‖ ^ 2 := by
  filter_upwards [difference_bound_ae source pointLe left right shift firstInside lastInside] with time paid
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) paid 2

theorem difference_mass_integrable (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    Integrable (fun time => ‖stressDifference source pointLe shift time‖ ^ 2) (volume.restrict (Icc left right)) := by
  apply (NativeOriginalPhysicalTimeBudget.difference_mass_integrable source pointLe ordered firstInside lastInside).const_mul
    (stressCoefficient receipt ^ 2) |>.mono' (difference_measurable source pointLe ordered firstInside lastInside |>.norm.pow 2)
  filter_upwards [difference_square_bound_ae source pointLe left right shift firstInside lastInside] with time paid
  change ‖‖stressDifference source pointLe shift time‖ ^ 2‖ ≤ _
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using paid

theorem source_stress_integral (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (positive : 0 ≤ shift) (leftInside : 0 ≤ left)
    (rightInside : right + shift ≤ 1) :
    (∫ time in left..right, ‖stressDifference source pointLe shift time‖ ^ 2) ^ 2 ≤
      stressCoefficient receipt ^ 4 *
        (8 * ‖ledger.family.endpointReceipt.velocityEndpoint‖ * (2 * Real.pi) ^ 2 *
          gradientBudget receipt * budget receipt * shift) := by
  have firstInside : Icc left right ⊆ Icc (0 : ℝ) 1 :=
    fun time inside => ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1) :=
    fun time inside => ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have targetInt := difference_mass_integrable source pointLe ordered firstInside lastInside
  have velocityInt := NativeOriginalPhysicalTimeBudget.difference_mass_integrable source pointLe ordered firstInside lastInside
  have bound := integral_mono_ae targetInt (velocityInt.const_mul (stressCoefficient receipt ^ 2))
    (difference_square_bound_ae source pointLe left right shift firstInside lastInside)
  rw [integral_const_mul] at bound
  have converted (f : ℝ → ℝ) : (∫ time in Icc left right, f time) = ∫ time in left..right, f time := by
    rw [intervalIntegral.integral_of_le ordered, ← integral_Icc_eq_integral_Ioc]
  rw [converted, converted] at bound
  have squared := pow_le_pow_left₀
    (intervalIntegral.integral_nonneg_of_forall ordered (fun time => sq_nonneg ‖stressDifference source pointLe shift time‖)) bound 2
  rw [mul_pow, ← pow_mul] at squared
  exact squared.trans (mul_le_mul_of_nonneg_left
    (source_physical_integral source pointLe ordered positive leftInside rightInside) (pow_nonneg stressCoefficient_nonnegative 4))

end
end SaturationMonoid.NavierStokes.NativeOriginalStressTime
