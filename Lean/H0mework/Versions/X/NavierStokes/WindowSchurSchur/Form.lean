import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.HeatDual
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.TemporalControl
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Mean
import Mathlib.Algebra.QuadraticDiscriminant

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalFourier
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanAction (creation meanValue meanOperator)
open NativeWindowHistoryMeanBlocks (diffusion)
open NativeWindowHistoryMeanDrift (drift)
open NativeWindowHistorySchurAction (effective feedback response cost)
open NativeWindowHistorySchurWeakPairing (potential)
open NativeWindowHistoryCreationGeometry (square transport)
open NativeWindowHistoryHeatDual (energy form)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def potentialCap (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  1+NativeWindowHistoryCreationSource.budget seed horizon nu.coeff

theorem potentialCap_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ potentialCap seed horizon :=
  add_nonneg (by norm_num) (NativeWindowHistoryCreationSource.budget_nonnegative seed horizon nu.coeff nu.coeff_pos)

private theorem gradient_nonnegative (M : ℕ) (v : physicalSpace (modes M)) : 0 ≤ curlPair (modes M) v.1 v.1 := by
  rw [← NativeDualCurlResolvent.gradient_norm_sq (modes M) (modes_zero M)]
  exact sq_nonneg _

private theorem energy_budget (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) (B : ℝ) (B0 : 0 ≤ B) :
    nu.coeff*curlPair (modes M) v.1 v.1+B*pairing (modes M) v v ≤ (1+B)*energy nu M v := by
  have mass:pairing (modes M) v v=‖coefficients (modes M) v‖^2:=real_inner_self_eq_norm_sq (coefficients (modes M) v)
  have gradient:=mul_nonneg nu.coeff_pos.le (gradient_nonnegative M v)
  have extra:=mul_nonneg B0 gradient
  rw [mass]
  unfold energy
  nlinarith only [extra,sq_nonneg ‖coefficients (modes M) v‖]

theorem covariance_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    potential seed M time v ≤ potentialCap seed horizon*energy nu M v :=
  (NativeWindowHistorySchurWeakPairing.source_potential_bound seed horizon nu.coeff nu.coeff_pos M time inside v).trans
    (energy_budget nu M v _ (NativeWindowHistoryCreationSource.budget_nonnegative seed horizon nu.coeff nu.coeff_pos))

def meanPotential (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) : ℝ :=
  ∫ point : Torus,square (modes M) (meanValue seed M time) point*square (modes M) v point

theorem meanPotential_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    meanPotential seed M time v ≤ potentialCap seed horizon*energy nu M v := by
  have viscosity:0 < nu.coeff:=nu.coeff_pos
  let S:=NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M)
  have compared:meanPotential seed M time v ≤ ∫ point : Torus,S point*square (modes M) v point := by
    apply integral_mono
      (((square (modes M) (meanValue seed M time)).continuous.mul (square (modes M) v).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      ((S.continuous.mul (square (modes M) v).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro point
    simp only [Pi.mul_apply]
    apply mul_le_mul_of_nonneg_right (NativeWindowHistoryMeanDrift.mean_square_le_stress seed M time inside.1 point)
    simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have absorbed:=NativeWindowHistoryCreationGeometry.square_absorption S (modes M) (modes_zero M) (modes_closed M) v nu.coeff nu.coeff_pos
  have power:=pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryCreationSource.trace_bound seed M time horizon inside)
      (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  have cap:NativeWindowHistoryCreationForm.budget ‖NativeWindowStressHeatSource.physical S‖ (nu.coeff*(2*Real.pi)^2) ≤
      NativeWindowHistoryCreationSource.budget seed horizon nu.coeff :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))
  have mass0:0 ≤ pairing (modes M) v v:=real_inner_self_nonneg (x := coefficients (modes M) v)
  exact (compared.trans absorbed).trans ((add_le_add le_rfl (mul_le_mul_of_nonneg_right cap mass0)).trans
    (energy_budget nu M v _ (NativeWindowHistoryCreationSource.budget_nonnegative seed horizon nu.coeff nu.coeff_pos)))

private theorem young_square (b p q : ℝ) (source : ∀ a : ℝ,2*a*b ≤ a^2*p+q) : b^2 ≤ p*q := by
  have bound:=discrim_le_zero (a := p) (b := -2*b) (c := q) (fun a => by have paid:=source a; nlinarith only [paid])
  unfold discrim at bound
  nlinarith only [bound]

private theorem square_root_bound (b D e f : ℝ) (D0 : 0 ≤ D) (e0 : 0 ≤ e)
    (bound : b^2 ≤ D*(e*f)) : |b| ≤ Real.sqrt D*Real.sqrt e*Real.sqrt f := by
  have paid:=Real.sqrt_le_sqrt bound
  simpa only [Real.sqrt_sq_eq_abs,Real.sqrt_mul D0,Real.sqrt_mul e0,mul_assoc] using paid

theorem drift_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u v : physicalSpace (modes M)) :
    inner ℝ (includeCLM (modes M) (modes_closed M) u) (drift seed M time (includeCLM (modes M) (modes_closed M) v))=
      pairing (modes M) u (transport (modes M) (modes_zero M) (modes_closed M) nu (meanValue seed M time) v) := by
  rw [NativeWindowHistoryMeanDrift.drift_original,restrict_include,include_inner (modes M) (modes_zero M),restrict_include]

theorem source_drift_pairing (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (u v : physicalSpace (modes M)) :
    |inner ℝ (includeCLM (modes M) (modes_closed M) u) (drift seed M time (includeCLM (modes M) (modes_closed M) v))| ≤
      Real.sqrt (potentialCap seed horizon/nu.coeff)*Real.sqrt (energy nu M u)*Real.sqrt (energy nu M v) := by
  rw [drift_pairing]
  have square:=young_square _ (meanPotential seed M time u) (curlPair (modes M) v.1 v.1)
    (NativeWindowHistorySchurWeakPairing.transport_young (modes M) (modes_zero M) (modes_closed M) nu (meanValue seed M time) u v)
  have gradient:curlPair (modes M) v.1 v.1 ≤ energy nu M v/nu.coeff := by
    apply (le_div_iff₀ nu.coeff_pos).mpr
    unfold energy
    nlinarith only [sq_nonneg ‖coefficients (modes M) v‖]
  have paid:=square.trans (mul_le_mul (meanPotential_bound seed horizon M time inside u) gradient
    (gradient_nonnegative M v) (mul_nonneg (potentialCap_nonnegative seed horizon) (NativeWindowHistoryHeatDual.energy_nonnegative nu M u)))
  have normalized : potentialCap seed horizon*energy nu M u*(energy nu M v/nu.coeff)=
      (potentialCap seed horizon/nu.coeff)*(energy nu M u*energy nu M v) := by ring
  exact square_root_bound _ _ _ _ (div_nonneg (potentialCap_nonnegative seed horizon) nu.coeff_pos.le)
    (NativeWindowHistoryHeatDual.energy_nonnegative nu M u) (paid.trans_eq normalized)

theorem response_gradient (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    NativeWindowTraceWholeHistory.gradient M (response seed M time (includeCLM (modes M) (modes_closed M) v)) ≤
      (potentialCap seed horizon/nu.coeff^2)*energy nu M v := by
  let z:=response seed M time (includeCLM (modes M) (modes_closed M) v)
  have paid:=mul_le_mul_of_nonneg_left (NativeWindowHistorySchurTemporalControl.cost_potential seed M time v) nu.coeff_pos.le
  have normalized:nu.coeff*(nu.coeff⁻¹*potential seed M time v)=potential seed M time v := by rw [← mul_assoc,mul_inv_cancel₀ nu.coeff_pos.ne',one_mul]
  rw [normalized] at paid
  change nu.coeff*(‖z‖^2+nu.coeff*NativeWindowTraceWholeHistory.gradient M z) ≤ _ at paid
  have source:=covariance_bound seed horizon M time inside v
  have positive:0 < nu.coeff^2:=sq_pos_of_pos nu.coeff_pos
  have cancel:nu.coeff^2*((potentialCap seed horizon/nu.coeff^2)*energy nu M v)=potentialCap seed horizon*energy nu M v := by
    rw [← mul_assoc,mul_div_cancel₀ _ positive.ne']
  nlinarith only [paid,source,cancel,mul_nonneg nu.coeff_pos.le (sq_nonneg ‖z‖),positive]

theorem source_feedback_pairing (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (u v : physicalSpace (modes M)) :
    |inner ℝ (includeCLM (modes M) (modes_closed M) u) (feedback seed M time (includeCLM (modes M) (modes_closed M) v))| ≤
      (potentialCap seed horizon/nu.coeff)*Real.sqrt (energy nu M u)*Real.sqrt (energy nu M v) := by
  let z:=response seed M time (includeCLM (modes M) (modes_closed M) v)
  have square:=young_square _ (potential seed M time u) (NativeWindowTraceWholeHistory.gradient M z)
    (NativeWindowHistorySchurWeakPairing.creation_young seed M time u z)
  have gradient0:=NativeWindowHistoryMeanGradient.gradient_nonnegative seed M z
  have paid:=square.trans (mul_le_mul (covariance_bound seed horizon M time inside u) (response_gradient seed horizon M time inside v)
    gradient0 (mul_nonneg (potentialCap_nonnegative seed horizon) (NativeWindowHistoryHeatDual.energy_nonnegative nu M u)))
  have normalized : potentialCap seed horizon*energy nu M u*((potentialCap seed horizon/nu.coeff^2)*energy nu M v)=
      (potentialCap seed horizon/nu.coeff)^2*(energy nu M u*energy nu M v) := by field_simp
  have result:=square_root_bound _ _ _ _ (sq_nonneg (potentialCap seed horizon/nu.coeff))
    (NativeWindowHistoryHeatDual.energy_nonnegative nu M u) (paid.trans_eq normalized)
  rw [Real.sqrt_sq (div_nonneg (potentialCap_nonnegative seed horizon) nu.coeff_pos.le)] at result
  rw [NativeWindowHistorySchurAction.feedback_pairing,abs_neg]
  exact result

def cap (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  1+Real.sqrt (potentialCap seed horizon/nu.coeff)+potentialCap seed horizon/nu.coeff

theorem cap_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ cap seed horizon :=
  add_nonneg (add_nonneg (by norm_num) (Real.sqrt_nonneg _)) (div_nonneg (potentialCap_nonnegative seed horizon) nu.coeff_pos.le)

theorem heat_pairing (nu : Viscosity) (M : ℕ) (u v : physicalSpace (modes M)) :
    inner ℝ (includeCLM (modes M) (modes_closed M) u)
      (includeCLM (modes M) (modes_closed M) v-diffusion nu M (includeCLM (modes M) (modes_closed M) v))=form nu M u v := by
  rw [NativeWindowMetricGraphMean.diffusion_laplacian]
  change inner ℝ (includeCLM (modes M) (modes_closed M) u)
    (includeCLM (modes M) (modes_closed M) v-(-nu.coeff) •
      NativeWindowHistoryOseen.lift M (LinearMap.toContinuousLinearMap (NativeWindowOperatorGreen.laplacian
        (modes M) (modes_zero M) (modes_closed M) nu)) (includeCLM (modes M) (modes_closed M) v))=_
  rw [NativeWindowHistoryOseen.lift_included,neg_smul,sub_neg_eq_add,← map_smul,← map_add,include_inner (modes M) (modes_zero M),restrict_include]
  rfl

theorem source_form_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (u v : physicalSpace (modes M)) :
    |inner ℝ (includeCLM (modes M) (modes_closed M) u)
      (includeCLM (modes M) (modes_closed M) v-effective seed M time (includeCLM (modes M) (modes_closed M) v))| ≤
      cap seed horizon*Real.sqrt (energy nu M u)*Real.sqrt (energy nu M v) := by
  have read:includeCLM (modes M) (modes_closed M) v-effective seed M time (includeCLM (modes M) (modes_closed M) v)=
      (includeCLM (modes M) (modes_closed M) v-diffusion nu M (includeCLM (modes M) (modes_closed M) v))-
        drift seed M time (includeCLM (modes M) (modes_closed M) v)-feedback seed M time (includeCLM (modes M) (modes_closed M) v) := by
    simp only [effective,drift,sub_apply,add_apply]
    abel
  rw [read,inner_sub_right,inner_sub_right,heat_pairing]
  let b:=inner ℝ (includeCLM (modes M) (modes_closed M) u) (drift seed M time (includeCLM (modes M) (modes_closed M) v))
  let c:=inner ℝ (includeCLM (modes M) (modes_closed M) u) (feedback seed M time (includeCLM (modes M) (modes_closed M) v))
  have paid:|form nu M u v-b-c| ≤ (|form nu M u v|+|b|)+|c| :=
    (abs_sub (form nu M u v-b) c).trans (add_le_add (abs_sub (form nu M u v) b) le_rfl)
  exact paid.trans ((add_le_add (add_le_add (NativeWindowHistoryHeatDual.form_bound nu M u v)
    (source_drift_pairing seed horizon M time inside u v)) (source_feedback_pairing seed horizon M time inside u v)).trans_eq
      (by unfold cap; ring))

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurForm
