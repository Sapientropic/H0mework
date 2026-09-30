import H0mework.Versions.X.NavierStokes.WindowSchurSchur.WeakPairing
import H0mework.Versions.X.NavierStokes.WindowSchurMean.Gradient
import H0mework.Versions.X.NavierStokes.WindowSchurMean.ForcingTest

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurTemporalControl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action rateHistory forcingHistory)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistorySchurAction (response cost temporalInput remainder)
open NativeWindowHistoryBathResolvent (resolve)
open NativeWindowHistorySchurWeakPairing (potential)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
noncomputable section
variable {nu : Viscosity}
local notation "Q" => NativeWindowHistoryMeanProjection.residual

theorem cost_potential (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    cost seed M time (includeCLM (modes M) (modes_closed M) v) ≤ nu.coeff⁻¹*potential seed M time v := by
  let z:=response seed M time (includeCLM (modes M) (modes_closed M) v)
  have young:=NativeWindowHistorySchurWeakPairing.creation_young seed M time v z nu.coeff⁻¹
  have pair:=NativeWindowHistorySchurAction.cost_energy seed M time (includeCLM (modes M) (modes_closed M) v)
  have symmetric:=real_inner_comm (F := H) z (NativeWindowHistoryMeanAction.creation seed M time (includeCLM (modes M) (modes_closed M) v))
  have read:inner ℝ (NativeWindowHistoryMeanAction.creation seed M time (includeCLM (modes M) (modes_closed M) v)) z=
      cost seed M time (includeCLM (modes M) (modes_closed M) v) := symmetric.trans pair.symm
  rw [read] at young
  have paid:=mul_le_mul_of_nonneg_left young (sq_nonneg nu.coeff)
  have left (c : ℝ) : nu.coeff^2*(2*nu.coeff⁻¹*c)=2*nu.coeff*c := by field_simp [nu.coeff_pos.ne']
  have right (p d : ℝ) : nu.coeff^2*((nu.coeff⁻¹)^2*p+d)=p+nu.coeff^2*d := by field_simp [nu.coeff_pos.ne']
  rw [left,right] at paid
  change 2*nu.coeff*(‖z‖^2+nu.coeff*gradient M z) ≤ potential seed M time v+nu.coeff^2*gradient M z at paid
  apply (show cost seed M time (includeCLM (modes M) (modes_closed M) v) ≤ potential seed M time v/nu.coeff from ?_).trans_eq
    (by ring)
  apply (le_div_iff₀ nu.coeff_pos).mpr
  change (‖z‖^2+nu.coeff*gradient M z)*nu.coeff ≤ _
  nlinarith only [paid,mul_nonneg nu.coeff_pos.le (sq_nonneg ‖z‖)]

def formBudget (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) : ℝ :=
  nu.coeff⁻¹*NativeWindowHistoryCreationSource.budget seed horizon (nu.coeff*epsilon)

theorem formBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0 < epsilon) :
    0 ≤ formBudget seed horizon epsilon :=
  mul_nonneg (inv_nonneg.mpr nu.coeff_pos.le) (NativeWindowHistoryCreationSource.budget_nonnegative seed horizon _ (mul_pos nu.coeff_pos positive))

theorem source_form_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0 < epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    cost seed M time (includeCLM (modes M) (modes_closed M) v) ≤
      epsilon*curlPair (modes M) v.1 v.1+formBudget seed horizon epsilon*pairing (modes M) v v := by
  have paid:=(cost_potential seed M time v).trans (mul_le_mul_of_nonneg_left
    (NativeWindowHistorySchurWeakPairing.source_potential_bound seed horizon (nu.coeff*epsilon)
      (mul_pos nu.coeff_pos positive) M time inside v) (inv_nonneg.mpr nu.coeff_pos.le))
  exact paid.trans_eq (by unfold formBudget; field_simp [nu.coeff_pos.ne'])

def energy (nu : Viscosity) (M : ℕ) (v : H) : ℝ := ‖v‖^2+nu.coeff*gradient M v

theorem energy_nonnegative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : H) : 0 ≤ energy nu M v :=
  add_nonneg (sq_nonneg _) (mul_nonneg nu.coeff_pos.le (NativeWindowHistoryMeanGradient.gradient_nonnegative seed M v))

private theorem quadratic_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (positive : ∀ v,0 ≤ inner ℝ v (L v)) (v w : E) :
    inner ℝ (v-w) (L (v-w)) ≤ 2*inner ℝ v (L v)+2*inner ℝ w (L w) := by
  have nonnegative:=positive (v+w)
  simp only [map_sub,map_add,inner_sub_left,inner_sub_right,inner_add_left,inner_add_right] at nonnegative ⊢
  linarith only [nonnegative]

theorem energy_sub (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v w : H) :
    energy nu M (v-w) ≤ 2*energy nu M v+2*energy nu M w := by
  let L:=(ContinuousLinearMap.id ℝ H)-action seed M 0
  have read (u : H) : inner ℝ u (L u)=energy nu M u := by
    change inner ℝ u (u-action seed M 0 u)=_
    rw [inner_sub_right (𝕜 := ℝ) u,real_inner_self_eq_norm_sq (x := u),NativeWindowHistoryOseenGap.action_energy]
    unfold energy
    ring
  have positive (u : H) : 0 ≤ inner ℝ u (L u) := (energy_nonnegative seed M u).trans_eq (read u).symm
  simpa only [read] using! quadratic_sub (E := H) L positive v w

def massBudget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  NativeWindowFiniteStressUniform.kernelBound 0*(NativeUnifiedCompleteSource.budget seed)^2

def gradientBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  max 0 (NativeWindowAugmentedPayment.graphBudget seed 0 horizon)

def responseBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  gradientBudget seed horizon+formBudget seed horizon 1*massBudget seed

def temporalBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  2*(massBudget seed+nu.coeff*gradientBudget seed horizon)+2*responseBudget seed horizon

theorem massBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ massBudget seed :=
  mul_nonneg (NativeWindowFiniteStressUniform.kernelBound_positive 0).le (sq_nonneg _)

theorem temporalBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ temporalBudget seed horizon := by
  have first:=massBudget_nonnegative seed
  have second:=formBudget_nonnegative seed horizon 1 (by norm_num)
  have visc:=nu.coeff_pos.le
  unfold temporalBudget responseBudget gradientBudget
  positivity

theorem source_mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    ‖finiteHistory seed time M‖^2 ≤ massBudget seed := by
  rw [NativeWindowHistoryForcingWork.mass_original]
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (NativeWindowHistoryForcingWork.mass_bound seed M 0 time nonnegative))

theorem source_gradient (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    gradient M (finiteHistory seed time M) ≤ gradientBudget seed horizon := by
  rw [NativeWindowHistoryForcingWork.gradient_original seed M time inside.1]
  exact ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le
    (NativeWindowAugmentedPayment.graphJet_bound seed (modes M) 0 time horizon inside))).trans (le_max_right _ _)

theorem source_residual_energy (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    energy nu M (Q (finiteHistory seed time M)) ≤ massBudget seed+nu.coeff*gradientBudget seed horizon := by
  have split:=NativeWindowHistoryMeanProjection.energy_split (finiteHistory seed time M)
  have below:‖Q (finiteHistory seed time M)‖^2 ≤ ‖finiteHistory seed time M‖^2 := by
    nlinarith only [split,sq_nonneg ‖NativeWindowHistoryMeanProjection.projection (finiteHistory seed time M)‖]
  have mass:‖Q (finiteHistory seed time M)‖^2 ≤ massBudget seed :=
    below.trans (source_mass seed M time inside.1)
  exact add_le_add mass (mul_le_mul_of_nonneg_left
    ((NativeWindowHistoryMeanGradient.gradient_residual_le seed M (finiteHistory seed time M)).trans
      (source_gradient seed horizon M time inside)) nu.coeff_pos.le)

theorem source_response_energy (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    energy nu M (response seed M time (mean (finiteHistory seed time M))) ≤ responseBudget seed horizon := by
  let v:=NativeWindowHistoryMeanGradient.meanValue M (finiteHistory seed time M)
  have projected:=congrArg mean (NativeWindowHistoryMeanGradient.source_projection seed M time)
  have original:mean (finiteHistory seed time M)=includeCLM (modes M) (modes_closed M) v := by
    simpa only [NativeWindowHistoryMeanProjection.projection,ContinuousLinearMap.comp_apply,
      NativeWindowHistoryMeanProjection.mean_embed] using projected
  have split:=NativeWindowHistoryMeanProjection.energy_split (finiteHistory seed time M)
  have mass:pairing (modes M) v v ≤ massBudget seed := by
    have same:‖NativeWindowHistoryMeanProjection.projection (finiteHistory seed time M)‖^2=pairing (modes M) v v := by
      change ‖embed (mean (finiteHistory seed time M))‖^2=_
      rw [NativeWindowHistoryMeanProjection.embed_norm,original,include_norm (modes M) (modes_zero M)]
      exact (real_inner_self_eq_norm_sq _).symm
    have bound:=source_mass seed M time inside.1
    nlinarith only [split,same,bound,sq_nonneg ‖Q (finiteHistory seed time M)‖]
  have gbound:curlPair (modes M) v.1 v.1 ≤ gradientBudget seed horizon :=
    (NativeWindowHistoryMeanGradient.source_mean_budget seed horizon M time inside).trans (le_max_right _ _)
  change cost seed M time (mean (finiteHistory seed time M)) ≤ _
  rw [original]
  have paid:=source_form_bound seed horizon 1 (by norm_num) M time inside v
  rw [one_mul] at paid
  exact paid.trans (add_le_add gbound (mul_le_mul_of_nonneg_left mass (formBudget_nonnegative seed horizon 1 (by norm_num))))

def temporalResponse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  resolve seed M time (temporalInput seed M time)

theorem temporal_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    temporalResponse seed M time=Q (finiteHistory seed time M)-response seed M time (mean (finiteHistory seed time M)) := by
  have source:=NativeWindowHistorySchurAction.source_residual seed M time
  change Q (finiteHistory seed time M)=response seed M time (mean (finiteHistory seed time M))+temporalResponse seed M time at source
  rw [source]
  abel

theorem source_temporal_energy (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    energy nu M (temporalResponse seed M time) ≤ temporalBudget seed horizon := by
  rw [temporal_original]
  exact (energy_sub seed M _ _).trans (add_le_add
    (mul_le_mul_of_nonneg_left (source_residual_energy seed horizon M time inside) (by norm_num))
    (mul_le_mul_of_nonneg_left (source_response_energy seed horizon M time inside) (by norm_num)))

theorem temporal_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    inner ℝ (includeCLM (modes M) (modes_closed M) v) (remainder seed M time-mean (forcingHistory seed M time))=
      -inner ℝ (NativeWindowHistoryMeanAction.creation seed M time (includeCLM (modes M) (modes_closed M) v))
        (temporalResponse seed M time) := by
  have source:=NativeWindowHistoryMeanBlocks.coupling_green seed M time (includeCLM (modes M) (modes_closed M) v)
    (temporalResponse seed M time)
  have read:remainder seed M time-mean (forcingHistory seed M time)=
      NativeWindowHistoryMeanBlocks.annihilation seed M time (temporalResponse seed M time) := by
    change mean (forcingHistory seed M time)+NativeWindowHistoryMeanBlocks.annihilation seed M time (temporalResponse seed M time)-
      mean (forcingHistory seed M time)=_
    abel
  rw [read]
  linarith only [source]

theorem temporal_work_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0 < epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    |inner ℝ (includeCLM (modes M) (modes_closed M) v) (remainder seed M time-mean (forcingHistory seed M time))| ≤
      (epsilon/2)*curlPair (modes M) v.1 v.1+(NativeWindowHistoryCreationSource.budget seed horizon epsilon/2)*pairing (modes M) v v+
        temporalBudget seed horizon/(2*nu.coeff) := by
  have pos:=NativeWindowHistorySchurWeakPairing.creation_young seed M time v (temporalResponse seed M time) 1
  have neg:=NativeWindowHistorySchurWeakPairing.creation_young seed M time v (temporalResponse seed M time) (-1)
  have absolute:|inner ℝ (NativeWindowHistoryMeanAction.creation seed M time (includeCLM (modes M) (modes_closed M) v))
      (temporalResponse seed M time)| ≤ (potential seed M time v+gradient M (temporalResponse seed M time))/2 := by
    rw [abs_le]
    constructor <;> nlinarith only [pos,neg]
  have grad:gradient M (temporalResponse seed M time) ≤ temporalBudget seed horizon/nu.coeff := by
    apply (le_div_iff₀ nu.coeff_pos).mpr
    have paid:=source_temporal_energy seed horizon M time inside
    unfold energy at paid
    nlinarith only [paid,sq_nonneg ‖temporalResponse seed M time‖]
  rw [temporal_pairing,abs_neg]
  exact absolute.trans ((div_le_div_of_nonneg_right (add_le_add
    (NativeWindowHistorySchurWeakPairing.source_potential_bound seed horizon epsilon positive M time inside v) grad)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

theorem source_remainder_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,∀ v : physicalSpace (modes M),
      |inner ℝ (includeCLM (modes M) (modes_closed M) v) (remainder seed M time)| ≤
        epsilon*curlPair (modes M) v.1 v.1+C*(pairing (modes M) v v+1) := by
  obtain ⟨low,small⟩:=NativeWindowHistoryMeanForcingTest.source_effect_small seed horizon nonnegative epsilon positive
  let K:=NativeWindowHistoryCreationSource.budget seed horizon epsilon/2
  let D:=epsilon/2+temporalBudget seed horizon/(2*nu.coeff)
  have K0:0 ≤ K:=div_nonneg (NativeWindowHistoryCreationSource.budget_nonnegative seed horizon epsilon positive) (by norm_num)
  have D0:0 ≤ D:=add_nonneg (div_nonneg positive.le (by norm_num))
    (div_nonneg (temporalBudget_nonnegative seed horizon) (mul_nonneg (by norm_num) nu.coeff_pos.le))
  refine ⟨low,K+D,add_nonneg K0 D0,fun M above time inside v => ?_⟩
  have g0:0 ≤ curlPair (modes M) v.1 v.1 := by
    rw [← NativeDualCurlResolvent.gradient_norm_sq (modes M) (modes_zero M)]
    exact sq_nonneg _
  have sqrtBound:Real.sqrt (curlPair (modes M) v.1 v.1) ≤ (curlPair (modes M) v.1 v.1+1)/2 := by
    nlinarith [Real.sq_sqrt g0,sq_nonneg (Real.sqrt (curlPair (modes M) v.1 v.1)-1)]
  have meanBound:|inner ℝ (includeCLM (modes M) (modes_closed M) v) (mean (forcingHistory seed M time))| ≤
      (epsilon/2)*curlPair (modes M) v.1 v.1+epsilon/2 := by
    rw [← NativeWindowHistoryMeanProjection.embed_pairing]
    exact ((small M above time inside v).trans (mul_le_mul_of_nonneg_left sqrtBound positive.le)).trans_eq (by ring)
  have remainderBound:=temporal_work_bound seed horizon epsilon positive M time inside v
  have read:inner ℝ (includeCLM (modes M) (modes_closed M) v) (remainder seed M time)=
      inner ℝ (includeCLM (modes M) (modes_closed M) v) (mean (forcingHistory seed M time))+
        inner ℝ (includeCLM (modes M) (modes_closed M) v) (remainder seed M time-mean (forcingHistory seed M time)) := by
    rw [inner_sub_right]
    ring
  rw [read]
  have paid:=(abs_add_le _ _).trans (add_le_add meanBound remainderBound)
  have mass0:0 ≤ pairing (modes M) v v := real_inner_self_nonneg (x := coefficients (modes M) v)
  change _ ≤ epsilon*curlPair (modes M) v.1 v.1+(K+D)*(pairing (modes M) v v+1)
  have widened:epsilon*curlPair (modes M) v.1 v.1+K*pairing (modes M) v v+D ≤
      epsilon*curlPair (modes M) v.1 v.1+(K+D)*(pairing (modes M) v v+1) := by nlinarith [mul_nonneg D0 mass0]
  exact paid.trans (show (epsilon/2)*curlPair (modes M) v.1 v.1+epsilon/2+
      ((epsilon/2)*curlPair (modes M) v.1 v.1+K*pairing (modes M) v v+temporalBudget seed horizon/(2*nu.coeff)) ≤ _ from
        (by dsimp only [D] at widened ⊢; nlinarith only [widened]))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem temporal_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    temporalResponse seed M (step.2.clockAdvance+time)=temporalResponse step.1 M time := by
  simp only [temporalResponse,temporalInput,
    NativeWindowHistoryBathResolvent.resolve_next seed M step generated time nonnegative,
    NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M,
    NativeWindowHistoryOseen.rateHistory_next seed M step generated time nonnegative,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurTemporalControl
