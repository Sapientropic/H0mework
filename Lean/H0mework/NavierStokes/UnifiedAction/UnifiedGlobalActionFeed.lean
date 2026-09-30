import H0mework.NavierStokes.UnifiedAction.UnifiedActionHistory
import H0mework.NavierStokes.UnifiedAction.UnifiedMacroActionFeed

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedGlobalActionFeed

open Set Filter MeasureTheory
open SourceGeneratedNativeResponseDisposition SourceGeneratedNativeBoundedRun
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeFiniteMacroPhysical NativeEventualTailControl NativeFiniteMacroEvolution
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator

noncomputable section

variable {nu : Viscosity} {seed current : GeneratedWholeRestartCurrent nu}

def action (seed : GeneratedWholeRestartCurrent nu) : ℝ → WholeRestartVelocityEndpointState :=
  NativeUnifiedActionHistory.global (fun {_ _} => NativeUnifiedMacroActionFeed.action) (terminal seed)

theorem action_ae (seed : GeneratedWholeRestartCurrent nu) :
    action seed =ᵐ[volume] NativeGlobalHilbertAction.sourceAction seed :=
  NativeUnifiedActionHistory.global_ae _ (fun step => NativeUnifiedMacroActionFeed.action_ae step) (terminal seed)

def historyBudget : {current : GeneratedWholeRestartCurrent nu} →
    NativeReachable seed generatedWholeRestartEndpointMacroRespond current → ℝ
  | _, .initial => ‖NativeUnifiedActionHistory.initialAction seed‖
  | _, .step (response := response) arrival _ => max (historyBudget arrival) (NativeUnifiedMacroActionFeed.budget response.2)

theorem history_bound (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) (time : ℝ) :
    ‖NativeUnifiedActionHistory.historyAction (fun {_ _} => NativeUnifiedMacroActionFeed.action) arrival time‖ ≤ historyBudget arrival := by
  induction arrival generalizing time with
  | initial => rfl
  | @step prior arrival response generated previous =>
      change ‖endpointSplice _ _ _ time‖ ≤ max (historyBudget arrival) (NativeUnifiedMacroActionFeed.budget response.2)
      by_cases before : time ≤ clock arrival
      · rw [endpointSplice_of_le _ _ _ _ before]
        exact (previous time).trans (le_max_left _ _)
      · rw [endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)]
        exact (NativeUnifiedMacroActionFeed.action_bound response.2 _).trans (le_max_right _ _)

def budget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  max (historyBudget (terminal seed).arrival) (NativeGlobalHilbertAction.sourceBudget seed)

theorem action_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ‖action seed time‖ ≤ budget seed := by
  by_cases before : time ≤ clock (terminal seed).arrival
  · rw [action, NativeUnifiedActionHistory.global, endpointSplice_of_le _ _ _ _ before]
    exact (history_bound (terminal seed).arrival time).trans (le_max_left _ _)
  · have later : clock (terminal seed).arrival < time := lt_of_not_ge before
    rw [action, NativeUnifiedActionHistory.global, endpointSplice_of_lt _ _ _ _ later]
    have value : NativeFiniteMacroGlobal.tail (terminal seed) (time - clock (terminal seed).arrival) =
        NativeAbsoluteEventualControl.velocity seed time := by
      rw [NativeAbsoluteEventualControl.velocity, NativeFiniteMacroGlobal.globalPath,
        endpointSplice_of_lt _ _ _ _ later]
    rw [value]
    exact (NativeGlobalHilbertAction.sourceAction_bound seed time).trans (le_max_right _ _)

theorem action_Linfty (seed : GeneratedWholeRestartCurrent nu) :
    MemLp (action seed) ∞ (volume.restrict (Ici (0 : ℝ))) :=
  (NativeGlobalHilbertAction.sourceAction_Linfty seed).1.ae_eq (ae_restrict_of_ae (action_ae seed).symm)

theorem action_intervalIntegrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) :
    IntervalIntegrable (action seed) volume 0 time :=
  (NativeGlobalHilbertAction.sourceAction_intervalIntegrable seed time nonnegative).congr_ae
    (ae_restrict_of_ae (action_ae seed).symm)

theorem source_integral (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) :
    NativeGlobalHilbertAction.sourceState seed b - NativeGlobalHilbertAction.sourceState seed a =
      ∫ time in a..b, action seed time := by
  rw [intervalIntegral.integral_congr_ae ((action_ae seed).mono fun _ same _ => same)]
  exact NativeGlobalHilbertAction.source_integral_write seed a b a_nonnegative b_nonnegative

def profile (seed : GeneratedWholeRestartCurrent nu) (point : BasePoint) : WholeRestartVelocityEndpointState :=
  action seed (canonicalTimeProjection point)

def generatedState (seed : GeneratedWholeRestartCurrent nu) (point : BasePoint) : WholeRestartVelocityEndpointState :=
  NativeGlobalHilbertAction.sourceState seed 0 + canonicalTimePrimitive (profile seed) point

theorem generatedState_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (space : StageNineSpatialPoint) :
    generatedState seed (canonicalCauchySlicePoint time space) = NativeGlobalHilbertAction.sourceState seed time := by
  simpa [generatedState, profile, canonicalTimePrimitive, add_comm] using
    (eq_add_of_sub_eq (source_integral seed 0 time le_rfl nonnegative)).symm

theorem source_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (NativeGlobalHilbertAction.sourceState seed) (action seed time) time := by
  filter_upwards [NativeUnifiedSourceDerivative.global_hasDerivAt_ae seed, action_ae seed] with time derivative same
  intro positive
  rw [same]
  exact derivative positive

theorem source_after_arrival (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    action seed (clock arrival + time) = action current time := by
  have same := terminal_unique (terminal seed) (prependTerminal arrival (terminal current))
  unfold action
  rw [same]
  exact NativeUnifiedActionHistory.global_after_arrival _
    (fun step => NativeUnifiedMacroActionFeed.action_terminal step) arrival (terminal current) time nonnegative

theorem source_generated_next (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    action seed (response.2.clockAdvance + time) = action response.1 time := by
  simpa only [clock, zero_add] using source_after_arrival (.step .initial generated) time nonnegative

theorem generatedState_next (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) (space : StageNineSpatialPoint) :
    generatedState seed (canonicalCauchySlicePoint (response.2.clockAdvance + time) space) =
      generatedState response.1 (canonicalCauchySlicePoint time space) := by
  rw [generatedState_original seed _ (add_nonneg response.2.clockAdvance_pos.le nonnegative),
    generatedState_original response.1 time nonnegative]
  unfold NativeGlobalHilbertAction.sourceState
  rw [NativeFiniteMacroEvolution.source_generated_next_evolution response generated time nonnegative]

theorem source_step_read (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (positive : 0 < time) (before : time ≤ response.2.clockAdvance) :
    action seed time = NativeUnifiedMacroActionFeed.action response.2 time := by
  let first : NativeReachable seed generatedWholeRestartEndpointMacroRespond response.1 := .step .initial generated
  have same := terminal_unique (terminal seed) (prependTerminal first (terminal response.1))
  have clockFirst : clock first = response.2.clockAdvance := by simp only [first, clock, zero_add]
  have clockWhole : clock (prependTerminal first (terminal response.1)).arrival =
      clock first + clock (terminal response.1).arrival := clock_append first (terminal response.1).arrival
  unfold action
  rw [same, NativeUnifiedActionHistory.global, endpointSplice_of_le _ _ _ _
    (by rw [clockWhole, clockFirst]; linarith [clock_nonnegative (terminal response.1).arrival])]
  change NativeUnifiedActionHistory.historyAction (fun {_ _} => NativeUnifiedMacroActionFeed.action)
    (BoundedRun.prependNativeReachable first (terminal response.1).arrival) time = _
  rw [NativeUnifiedActionHistory.prefix_append_preserves (fun {_ _} => NativeUnifiedMacroActionFeed.action)
    first (terminal response.1).arrival time (by rwa [clockFirst])]
  change endpointSplice 0 _ _ time = _
  rw [endpointSplice_of_lt _ _ _ _ positive, sub_zero]

theorem source_cofinal_read (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) :
    action seed (wholeRestartVelocityAccumulationTime seed) = NativeUnifiedCofinalActionFeed.actionAt seed := by
  rw [source_step_read response generated _ (NativeMacroMomentumIntegral.accumulation_positive response.2)
    (by rw [NativeMacroMomentumIntegral.clock_split]; linarith [(NativeMacroMomentumIntegral.recoveryTime_mem response.2).1]),
    NativeUnifiedMacroActionFeed.action_cofinal]

theorem source_recovery_read (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (NativeMacroMomentumIntegral.recoveryTime response.2)) :
    action seed (wholeRestartVelocityAccumulationTime seed + time) = NativeUnifiedRootActionFeed.action seed time := by
  rw [source_step_read response generated _
    (by linarith [NativeMacroMomentumIntegral.accumulation_positive response.2, inside.1])
    (by rw [NativeMacroMomentumIntegral.clock_split]; linarith [inside.2]),
    NativeUnifiedMacroActionFeed.action_recovery response.2 time inside]

end
end SaturationMonoid.NavierStokes.NativeUnifiedGlobalActionFeed
