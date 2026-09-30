import H0mework.NavierStokes.WindowSchurSchur.Resolvent
import H0mework.NavierStokes.WindowHistoryCreation.Source

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action rateHistory forcingHistory)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryMeanAction (creation meanOperator)
open NativeWindowHistoryMeanBlocks (annihilation bath)
open NativeWindowHistoryBathResolvent (resolve)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
noncomputable section
variable {nu : Viscosity}
local notation "Q" => NativeWindowHistoryMeanProjection.residual

def response (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical →L[ℝ] H :=
  (resolve seed M time).comp (creation seed M time)

def feedback (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  (annihilation seed M time).comp (response seed M time)

def effective (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  meanOperator seed M time+feedback seed M time

def cost (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) : ℝ :=
  ‖response seed M time v‖^2+nu.coeff*gradient M (response seed M time v)

theorem creation_centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    Q (creation seed M time v)=creation seed M time v := NativeWindowHistoryBathResolvent.residual_square _

theorem response_centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    Q (response seed M time v)=response seed M time v :=
  (NativeWindowHistoryBathResolvent.resolve_residual seed M time (creation seed M time v)).trans
    (congrArg (resolve seed M time) (creation_centered seed M time v))

theorem response_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    response seed M time v-bath seed M time (response seed M time v)=creation seed M time v :=
  NativeWindowHistoryBathResolvent.resolve_equation seed M time (creation seed M time v)

theorem cost_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    cost seed M time v=inner ℝ (response seed M time v) (creation seed M time v) := by
  have paid:=NativeWindowHistoryBathResolvent.energy seed M time (creation seed M time v)
  change ‖response seed M time v‖^2+nu.coeff*gradient M (Q (response seed M time v))=_ at paid
  rw [response_centered] at paid
  exact paid

theorem feedback_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    inner ℝ v (feedback seed M time v)=-cost seed M time v := by
  have green:=NativeWindowHistoryMeanBlocks.coupling_green seed M time v (response seed M time v)
  have symmetric:=real_inner_comm (F := H) (creation seed M time v) (response seed M time v)
  change inner ℝ v (feedback seed M time v)+inner ℝ (creation seed M time v) (response seed M time v)=0 at green
  linarith only [green,symmetric,cost_energy seed M time v]

theorem feedback_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u v : wholePhysical) :
    inner ℝ u (feedback seed M time v)=-inner ℝ (creation seed M time u) (response seed M time v) := by
  have green:=NativeWindowHistoryMeanBlocks.coupling_green seed M time u (response seed M time v)
  change inner ℝ u (feedback seed M time v)+inner ℝ (creation seed M time u) (response seed M time v)=0 at green
  linarith only [green]

theorem feedback_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u v : wholePhysical) :
    |inner ℝ u (feedback seed M time v)| ≤ ‖creation seed M time u‖*‖creation seed M time v‖ := by
  rw [feedback_pairing,abs_neg]
  exact (abs_real_inner_le_norm (creation seed M time u) (response seed M time v)).trans
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryBathResolvent.norm_bound seed M time (creation seed M time v))
      (norm_nonneg (creation seed M time u)))

theorem cost_nonnegative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    0 ≤ cost seed M time v := by
  have first:=NativeWindowHistoryOseenGap.gradient_gap nu M (response seed M time v)
  have nonnegative:0 ≤ gradient M (response seed M time v) := (by positivity :
    0 ≤ (2*Real.pi)^2*‖NativeWindowTraceWholeHistory.projected M (response seed M time v)‖^2).trans first
  exact add_nonneg (sq_nonneg _) (mul_nonneg nu.coeff_pos.le nonnegative)

theorem cost_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    cost seed M time v ≤ ‖creation seed M time v‖^2 := by
  have paid:=NativeWindowHistoryBathResolvent.energy_bound seed M time (creation seed M time v)
  change ‖response seed M time v‖^2+nu.coeff*gradient M (Q (response seed M time v)) ≤ _ at paid
  rw [response_centered] at paid
  exact paid

theorem source_cost_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0 < epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : wholePhysical) :
    let vM:=restrictCLM (modes M) (modes_zero M) (modes_closed M) v
    cost seed M time v ≤ epsilon*pairing (modes M)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu vM)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu vM)+
        NativeWindowHistoryCreationSource.budget seed horizon epsilon*curlPair (modes M) vM.1 vM.1 :=
  (cost_bound seed M time v).trans
    (NativeWindowHistoryCreationSource.source_whole_bound seed horizon epsilon positive M time inside v)

theorem mean_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    inner ℝ v (meanOperator seed M time v)=-nu.coeff*gradient M (embed v) := by
  have read:=NativeWindowHistoryMeanProjection.embed_pairing v (action seed M time (embed v))
  rw [NativeWindowHistoryMeanAction.mean_action] at read
  exact read.symm.trans (NativeWindowHistoryOseenGap.action_energy seed M time (embed v))

theorem effective_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    inner ℝ v (effective seed M time v)=-nu.coeff*gradient M (embed v)-cost seed M time v := by
  change inner ℝ v (meanOperator seed M time v+feedback seed M time v)=_
  rw [inner_add_right,mean_energy,feedback_energy]
  ring

/-- The time derivative and residual forcing stay in this single actual input. -/
def temporalInput (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  Q (finiteHistory seed time M+forcingHistory seed M time-rateHistory seed M time)

def remainder (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical :=
  mean (forcingHistory seed M time)+annihilation seed M time (resolve seed M time (temporalInput seed M time))

private theorem residual_algebra {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (h f rate c d : E) (equation : P rate=c+d+P f) :
    P h-d=c+P (h+f-rate) := by
  rw [map_sub,map_add]
  rw [equation]
  abel

theorem source_residual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Q (finiteHistory seed time M)=response seed M time (mean (finiteHistory seed time M))+
      resolve seed M time (temporalInput seed M time) := by
  have actual:=congrArg Q (NativeWindowHistoryOseen.source_equation seed M time)
  have mapped:=(Q).map_add (action seed M time (finiteHistory seed time M)) (forcingHistory seed M time)
  have blocks:=NativeWindowHistoryMeanBlocks.residual_action_split seed M time (finiteHistory seed time M)
  have equation:=actual.trans (mapped.trans (congrArg (fun v : H => v+Q (forcingHistory seed M time)) blocks))
  have identity:=residual_algebra (E := H) Q (finiteHistory seed time M) (forcingHistory seed M time)
    (rateHistory seed M time) (creation seed M time (mean (finiteHistory seed time M)))
    (bath seed M time (finiteHistory seed time M)) equation
  have recognized:Q (finiteHistory seed time M)-bath seed M time (Q (finiteHistory seed time M))=
      creation seed M time (mean (finiteHistory seed time M))+temporalInput seed M time :=
    (congrArg (fun v : H => Q (finiteHistory seed time M)-v)
      (NativeWindowHistoryBathResolvent.bath_residual seed M time (finiteHistory seed time M))).trans identity
  exact (NativeWindowHistoryBathResolvent.resolve_unique seed M time _ _ recognized).trans
    ((resolve seed M time).map_add _ _)

theorem source_rate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    mean (rateHistory seed M time)=effective seed M time (mean (finiteHistory seed time M))+remainder seed M time := by
  have actual:=congrArg mean (NativeWindowHistoryOseen.source_equation seed M time)
  have mapped:=mean.map_add (action seed M time (finiteHistory seed time M)) (forcingHistory seed M time)
  have blocks:=NativeWindowHistoryMeanBlocks.mean_action_split seed M time (finiteHistory seed time M)
  have equation:=actual.trans (mapped.trans (congrArg (fun v : wholePhysical => v+mean (forcingHistory seed M time)) blocks))
  have center:annihilation seed M time (Q (finiteHistory seed time M))=annihilation seed M time (finiteHistory seed time M) := by
    change mean (action seed M time (Q (Q (finiteHistory seed time M))))=_
    rw [NativeWindowHistoryBathResolvent.residual_square]
    rfl
  have responseRead:annihilation seed M time (finiteHistory seed time M)=
      feedback seed M time (mean (finiteHistory seed time M))+
        annihilation seed M time (resolve seed M time (temporalInput seed M time)) :=
    center.symm.trans ((congrArg (annihilation seed M time) (source_residual seed M time)).trans
      ((annihilation seed M time).map_add _ _))
  change mean (rateHistory seed M time)=meanOperator seed M time (mean (finiteHistory seed time M))+
    feedback seed M time (mean (finiteHistory seed time M))+
      (mean (forcingHistory seed M time)+annihilation seed M time (resolve seed M time (temporalInput seed M time)))
  exact equation.trans ((congrArg (fun v : wholePhysical => meanOperator seed M time (mean (finiteHistory seed time M))+
    v+mean (forcingHistory seed M time)) responseRead).trans (by abel))

theorem source_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (fun t => mean (finiteHistory seed t M))
      (effective seed M time (mean (finiteHistory seed time M))+remainder seed M time) time := by
  have actual : HasDerivAt (fun t => mean (finiteHistory seed t M)) (mean (rateHistory seed M time)) time :=
    mean.hasFDerivAt.comp_hasDerivAt (F := H) (E := wholePhysical) time
      (by exact NativeWindowHistoryOseen.history_hasDerivAt seed M time)
  simpa only [Function.comp_def,source_rate] using! actual

theorem source_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => effective seed M t (mean (finiteHistory seed t M))+remainder seed M t) volume a b := by
  have actual:=NativeWindowHistoryOseen.rateHistory_integrable seed M a b
  have mapped : IntervalIntegrable (fun t => mean (rateHistory seed M t)) volume a b :=
    ⟨by simpa only [] using! (mean.integrable_comp (H := H) (E := wholePhysical) (𝕜 := ℝ) (𝕜' := ℝ)
          (σ := RingHom.id ℝ) actual.1),
      by simpa only [] using! (mean.integrable_comp (H := H) (E := wholePhysical) (𝕜 := ℝ) (𝕜' := ℝ)
          (σ := RingHom.id ℝ) actual.2)⟩
  exact ⟨mapped.1.congr (Eventually.of_forall fun t => source_rate seed M t),
    mapped.2.congr (Eventually.of_forall fun t => source_rate seed M t)⟩

theorem source_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    mean (finiteHistory seed b M)-mean (finiteHistory seed a M)=
      ∫ t in a..b,effective seed M t (mean (finiteHistory seed t M))+remainder seed M t := by
  have actual:=congrArg mean (NativeWindowHistoryOseen.history_write seed M a b)
  have mapped:=mean.intervalIntegral_comp_comm (E := H) (F := wholePhysical) (𝕜 := ℝ)
    (NativeWindowHistoryOseen.rateHistory_integrable seed M a b)
  exact (mean.map_sub (finiteHistory seed b M) (finiteHistory seed a M)).symm.trans
    (actual.trans (mapped.symm.trans (intervalIntegral.integral_congr fun t _ => source_rate seed M t)))

private theorem mass_derivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℝ → E) (q : E) (time : ℝ) (actual : HasDerivAt f q time) :
    HasDerivAt (fun t => (1/2 : ℝ)*‖f t‖^2) (inner ℝ (f time) q) time := by
  convert actual.norm_sq.const_mul (1/2 : ℝ) using 1 <;> first | rfl | ring

theorem source_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (fun t => (1/2 : ℝ)*‖mean (finiteHistory seed t M)‖^2)
      (-nu.coeff*gradient M (embed (mean (finiteHistory seed time M)))-cost seed M time (mean (finiteHistory seed time M))+
        inner ℝ (mean (finiteHistory seed time M)) (remainder seed M time)) time := by
  have actual:=mass_derivative (E := wholePhysical) (fun t => mean (finiteHistory seed t M))
    (effective seed M time (mean (finiteHistory seed time M))+remainder seed M time) time (source_action seed M time)
  have read:inner ℝ (mean (finiteHistory seed time M))
      (effective seed M time (mean (finiteHistory seed time M))+remainder seed M time)=
        -nu.coeff*gradient M (embed (mean (finiteHistory seed time M)))-cost seed M time (mean (finiteHistory seed time M))+
          inner ℝ (mean (finiteHistory seed time M)) (remainder seed M time) := by
    exact (inner_add_right (𝕜 := ℝ) (mean (finiteHistory seed time M))
      (effective seed M time (mean (finiteHistory seed time M))) (remainder seed M time)).trans
        (congrArg (fun v : ℝ => v+inner ℝ (mean (finiteHistory seed time M)) (remainder seed M time))
          (effective_energy seed M time (mean (finiteHistory seed time M))))
  exact read ▸ actual

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem action_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    (effective seed M (step.2.clockAdvance+time),remainder seed M (step.2.clockAdvance+time))=
      (effective step.1 M time,remainder step.1 M time) := by
  have blocks:=NativeWindowHistoryMeanBlocks.blocks_next seed M step generated time nonnegative
  have one:=congrArg Prod.fst blocks
  have two:=congrArg (fun x => x.2.1) blocks
  have three:=congrArg (fun x => x.2.2.1) blocks
  dsimp only at one two three
  simp only [effective,feedback,response,remainder,temporalInput,one,two,three,
    NativeWindowHistoryBathResolvent.resolve_next seed M step generated time nonnegative,
    NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M,
    NativeWindowHistoryOseen.rateHistory_next seed M step generated time nonnegative,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurAction
