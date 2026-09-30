import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.NormalForm
import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Sum
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Kernel
import H0mework.Versions.X.NavierStokes.UnheatedWriterHalf.Source

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeInput
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeEndpointVelocityCarrier NativeUnheatedTreeTime
open NativeUnheatedHalfNonlinear (quarter quarter_nonnegative)
noncomputable section
variable {nu : Viscosity} {n : ℕ}

def input (seed : GeneratedWholeRestartCurrent nu) (position index : Fin (n+1)) (time : ℝ) : NativeUnheatedTriadSum.E :=
  wholeVelocityCLM (if index=position then NativeUnheatedHalfNonlinear.source seed time
    else (NativeUnifiedCompleteSource.source seed time).fst)

theorem input_bound (seed : GeneratedWholeRestartCurrent nu) (position index : Fin (n+1)) (time : ℝ) :
    ‖input seed position index time‖ ≤ if index=position
      then NativeUnheatedHalfNonlinear.coefficient*NativeUnheatedSourceGradient.mass seed time else NativeUnifiedCompleteSource.budget seed := by
  by_cases same : index=position
  · simp only [input, if_pos same]
    exact (wholeVelocity_norm_le _).trans (NativeUnheatedHalfNonlinear.source_bound seed time)
  · simp only [input, if_neg same]
    exact (wholeVelocity_norm_le _).trans (NativeUnheatedSourceWeightedTail.velocity_bound seed time)

theorem input_product (seed : GeneratedWholeRestartCurrent nu) (position : Fin (n+1)) (time : ℝ) :
    (∏ index : Fin (n+1), ‖input seed position index time‖) ≤
      NativeUnheatedHalfNonlinear.coefficient*NativeUnheatedSourceGradient.mass seed time*NativeUnifiedCompleteSource.budget seed^n := by
  have paid := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin (n+1))))
    (fun index _ => norm_nonneg (input seed position index time)) (fun index _ => input_bound seed position index time)
  apply paid.trans_eq
  rw [Fin.prod_univ_succAbove _ position]
  simp only [if_true, Fin.succAbove_ne, if_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem product_action (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot)
    (position : Fin (n+1)) (time : ℝ) :
    (quarter (slots position).1 : ℂ)*(∏ number : Fin (n+1), input seed position number time (slots number).1 (slots number).2) =
      NativeUnheatedTriadRows.action seed time (slots position).1 (slots position).2*cofactor seed slots position time := by
  rw [← Finset.mul_prod_erase Finset.univ (fun number => input seed position number time (slots number).1 (slots number).2)
    (Finset.mem_univ position)]
  have remaining : (∏ number ∈ Finset.univ.erase position, input seed position number time (slots number).1 (slots number).2) =
      cofactor seed slots position time := by
    apply Finset.prod_congr rfl
    intro number inside
    simp only [input, if_neg (Finset.mem_erase.mp inside).1, wholeVelocityCLM_apply, NativeUnheatedTriadRows.velocity_original]
  rw [remaining, ← mul_assoc]
  simp only [input, if_true, wholeVelocityCLM_apply, NativeUnheatedHalfNonlinear.source_action, Complex.real_smul]

theorem forcing_original (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (time : ℝ) :
    forcing seed slots time = ∑ position : Fin (n+1), (quarter (slots position).1 : ℂ)*
      (∏ number : Fin (n+1), input seed position number time (slots number).1 (slots number).2) := by
  simp only [product_action, forcing]

def kernel (nu : Viscosity) (slots : Fin (n+1) → Slot) (base : ℂ) (position : Fin (n+1)) : ℂ :=
  NativeUnheatedTreeNormalForm.normalizer nu slots base*(quarter (slots position).1 : ℂ)

def multilinear (inputs : Fin (n+1) → NativeUnheatedTriadSum.E) (nu : Viscosity)
    (slots : Fin (n+1) → Slot) (base : ℂ) (position : Fin (n+1)) : ℂ :=
  kernel nu slots base position*∏ number : Fin (n+1), inputs number (slots number).1 (slots number).2

theorem multilinear_norm (inputs : Fin (n+1) → NativeUnheatedTriadSum.E) (slots : Fin (n+1) → Slot)
    (base : ℂ) (position : Fin (n+1)) :
    ‖multilinear inputs nu slots base position‖ ≤ ‖kernel nu slots base position‖*(∏ number : Fin (n+1), ‖inputs number‖) := by
  rw [multilinear, norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun number _ =>
    (norm_le_pi_norm _ (slots number).2).trans (lp.norm_apply_le_norm (by norm_num) (inputs number) (slots number).1))

def term (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (base : ℂ)
    (position : Fin (n+1)) (time : ℝ) : ℂ :=
  multilinear (fun number => input seed position number time) nu slots base position

theorem term_bound (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot)
    (base : ℂ) (position : Fin (n+1)) (time : ℝ) :
    ‖term seed slots base position time‖ ≤ ‖kernel nu slots base position‖*
      (NativeUnheatedHalfNonlinear.coefficient*NativeUnheatedSourceGradient.mass seed time*NativeUnifiedCompleteSource.budget seed^n) :=
  (multilinear_norm _ slots base position).trans (mul_le_mul_of_nonneg_left (input_product seed position time) (norm_nonneg _))

theorem next_original (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (base : ℂ) (time : ℝ) :
    NativeUnheatedTreeNormalForm.nextForcing seed slots base time = ∑ position : Fin (n+1), term seed slots base position time := by
  rw [NativeUnheatedTreeNormalForm.nextForcing, forcing_original, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro position _
  simp only [term, multilinear, kernel, mul_assoc]

theorem input_measurable (seed : GeneratedWholeRestartCurrent nu) (position index : Fin (n+1)) :
    AEStronglyMeasurable (input seed position index) (volume : Measure ℝ) := by
  change AEStronglyMeasurable (fun time => wholeVelocityCLM (if index=position then
    NativeUnheatedHalfNonlinear.source seed time else (NativeUnifiedCompleteSource.source seed time).fst)) volume
  by_cases same : index=position
  · simpa only [input, if_pos same] using! wholeVelocityCLM.continuous.comp_aestronglyMeasurable
      (NativeUnheatedHalfNonlinear.source_measurable seed)
  · simpa only [input, if_neg same] using! wholeVelocityCLM.continuous.comp_aestronglyMeasurable
      (NativeUnheatedSourceWeightedTail.velocity_measurable seed)

theorem term_measurable (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot)
    (base : ℂ) (position : Fin (n+1)) : AEStronglyMeasurable (term seed slots base position) (volume : Measure ℝ) := by
  have measured (number : Fin (n+1)) : AEStronglyMeasurable
      (fun time => input seed position number time (slots number).1 (slots number).2) (volume : Measure ℝ) := by
    let evaluate := (ContinuousLinearMap.proj (slots number).2 : (Coordinate → ℂ) →L[ℝ] ℂ).comp
      (lp.evalCLM ℝ (fun _ : IntegerWavevector => Coordinate → ℂ) 2 (slots number).1)
    exact evaluate.continuous.comp_aestronglyMeasurable (input_measurable seed position number)
  exact (Finset.aestronglyMeasurable_fun_prod Finset.univ (fun number _ => measured number)).const_mul (kernel nu slots base position)

theorem term_integrable (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot)
    (base : ℂ) (position : Fin (n+1)) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (term seed slots base position) (volume.restrict (Icc 0 horizon)) := by
  apply ((NativeUnheatedSourceGradient.mass_integrable seed horizon nonnegative).const_mul
    (‖kernel nu slots base position‖*NativeUnheatedHalfNonlinear.coefficient*NativeUnifiedCompleteSource.budget seed^n)).mono'
    (term_measurable seed slots base position).restrict
  exact Eventually.of_forall fun time => (term_bound seed slots base position time).trans_eq (by ring)

theorem input_next (seed : GeneratedWholeRestartCurrent nu) (position index : Fin (n+1))
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    input seed position index (response.2.clockAdvance+time) = input response.1 position index time := by
  simp only [input, NativeUnheatedHalfNonlinear.source_next seed response generated time nonnegative,
    NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]

theorem term_next (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (base : ℂ) (position : Fin (n+1))
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    term seed slots base position (response.2.clockAdvance+time) = term response.1 slots base position time := by
  simp only [term, multilinear, input_next seed position _ response generated time nonnegative]

theorem newest_quarter (slots : Fin (n+1) → Slot) (position : Fin (n+1)) :
    quarter (slots position).1^4*(sumRate nu slots)⁻¹ ≤ nu.coeff⁻¹ := by
  rw [NativeUnheatedQuinticKernel.quarter_fourth]
  apply NativeUnheatedQuinticWeights.paid_inverse (NativeUnheatedTreeOutput.rate_nonnegative slots) (inv_nonneg.mpr nu.coeff_pos.le)
  have paid := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (n+1))))
    (fun number _ => NativeUnheatedTriadKernel.multiplier_nonnegative (slots number).1) (Finset.mem_univ position)
  simpa only [sumRate, ← mul_assoc, inv_mul_cancel₀ nu.coeff_pos.ne', one_mul] using paid

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeInput
