import H0mework.Versions.X.NavierStokes.WindowHistory.SpatialWords
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.Action
import H0mework.Versions.X.NavierStokes.WindowSchurMean.Time


set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderWord
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowTraceWholeHistory (H finiteHistory gradient)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistorySpatialWords (fiber)
open NativeWindowHistorySchurAction (effective remainder cost)
open PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy (FixedMatterSpatialWordIndex)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
variable {nu : Viscosity}

def value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (time : ℝ) : wholePhysical :=
  fiber M word (mean (finiteHistory seed time M))

theorem value_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (time : ℝ) :
    value seed M word time=mean (NativeWindowHistorySpatialWords.history seed M word time) :=
  (NativeWindowHistoryMeanProjection.mean_comp (fiber M word) (finiteHistory seed time M)).symm

def bracket (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (time : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  (fiber M word).comp (effective seed M time)-(effective seed M time).comp (fiber M word)

def retained (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (time : ℝ) : wholePhysical :=
  bracket seed M word time (mean (finiteHistory seed time M))+fiber M word (remainder seed M time)

private theorem linear_action {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D A : E →L[ℝ] E) (v f : E) : D (A v+f)=A (D v)+(D.comp A-A.comp D) v+D f := by
  simp only [map_add,sub_apply,ContinuousLinearMap.comp_apply]
  abel

theorem value_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (time : ℝ) :
    HasDerivAt (value seed M word)
      (effective seed M time (value seed M word time)+retained seed M word time) time := by
  have actual:=(fiber M word).hasFDerivAt.comp_hasDerivAt time (NativeWindowHistorySchurAction.source_action seed M time)
  have same:=linear_action (fiber M word) (effective seed M time)
    (mean (finiteHistory seed time M)) (remainder seed M time)
  apply actual.congr_deriv
  exact same.trans (add_assoc _ _ _)

def energy (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,‖value seed M word.toList time‖^2

def dissipation (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,gradient M (embed (value seed M word.toList time))

def feedbackCost (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,cost seed M time (value seed M word.toList time)

def retainedWork (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,2*inner ℝ (value seed M word.toList time) (retained seed M word.toList time)

theorem word_energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (time : ℝ) :
    HasDerivAt (fun t => ‖value seed M word t‖^2)
      (-2*nu.coeff*gradient M (embed (value seed M word time))-
        2*cost seed M time (value seed M word time)+
        2*inner ℝ (value seed M word time) (retained seed M word time)) time := by
  have actual:=(value_hasDerivAt seed M word time).norm_sq
  apply actual.congr_deriv
  rw [inner_add_right,NativeWindowHistorySchurAction.effective_energy]
  ring

theorem source_energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (energy seed M order)
      (-2*nu.coeff*dissipation seed M order time-2*feedbackCost seed M order time+retainedWork seed M order time) time := by
  have actual:=HasDerivAt.sum (u := Finset.univ) fun word : FixedMatterSpatialWordIndex order =>
    fun _ => word_energy_hasDerivAt seed M word.toList time
  have source : (∑ word : FixedMatterSpatialWordIndex order,
      fun t => ‖value seed M word.toList t‖^2)=energy seed M order := by
    funext t
    exact Finset.sum_apply _ _ _
  rw [source] at actual
  simpa only [dissipation,feedbackCost,retainedWork,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] using actual

theorem source_one_sided (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    deriv (energy seed M order) time+2*nu.coeff*dissipation seed M order time≤retainedWork seed M order time := by
  rw [(source_energy_hasDerivAt seed M order time).deriv]
  have paid : 0≤feedbackCost seed M order time :=
    Finset.sum_nonneg fun word _ => NativeWindowHistorySchurAction.cost_nonnegative seed M time _
  linarith only [paid]

end

variable {nu : Viscosity}

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem value_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    value seed M word (step.2.clockAdvance + time) = value step.1 M word time := by
  unfold value
  exact congrArg (fiber M word ∘ NativeWindowHistoryMeanProjection.mean)
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M)

theorem retained_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    retained seed M word (step.2.clockAdvance + time) = retained step.1 M word time := by
  have finite := NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M
  have blocks := NativeWindowHistorySchurAction.action_next seed M step generated time nonnegative
  have effectiveNext : effective seed M (step.2.clockAdvance + time) = effective step.1 M time := by
    simpa only using congrArg Prod.fst blocks
  have remainderNext : NativeWindowHistorySchurAction.remainder seed M
      (step.2.clockAdvance + time) = NativeWindowHistorySchurAction.remainder step.1 M time := by
    simpa only using congrArg Prod.snd blocks
  unfold retained bracket
  rw [effectiveNext, remainderNext, finite]

theorem dissipation_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
  (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    dissipation seed M order (step.2.clockAdvance + time) = dissipation step.1 M order time := by
  unfold dissipation
  apply Finset.sum_congr rfl
  intro word _
  rw [value_next seed M word.toList step generated time nonnegative]

theorem feedbackCost_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    feedbackCost seed M order (step.2.clockAdvance + time) = feedbackCost step.1 M order time := by
  have resolveNext := NativeWindowHistoryBathResolvent.resolve_next seed M step generated time nonnegative
  have creationNext := NativeWindowHistoryMeanBlocks.creation_next seed M step generated time nonnegative
  have responseNext : NativeWindowHistorySchurAction.response seed M
      (step.2.clockAdvance + time) = NativeWindowHistorySchurAction.response step.1 M time := by
    unfold NativeWindowHistorySchurAction.response
    rw [resolveNext, creationNext]
  unfold feedbackCost
  apply Finset.sum_congr rfl
  intro word _
  rw [value_next seed M word.toList step generated time nonnegative]
  simp only [cost, responseNext]

theorem retainedWork_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    retainedWork seed M order (step.2.clockAdvance + time) = retainedWork step.1 M order time := by
  unfold retainedWork
  apply Finset.sum_congr rfl
  intro word _
  rw [value_next seed M word.toList step generated time nonnegative,
    retained_next seed M word.toList step generated time nonnegative]

theorem derivative_energy_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    deriv (energy seed M order) (step.2.clockAdvance + time) =
      deriv (energy step.1 M order) time := by
  rw [(source_energy_hasDerivAt seed M order (step.2.clockAdvance + time)).deriv,
    (source_energy_hasDerivAt step.1 M order time).deriv,
    dissipation_next seed M order step generated time nonnegative,
    feedbackCost_next seed M order step generated time nonnegative,
    retainedWork_next seed M order step generated time nonnegative]


open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem energy_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    energy seed M order (step.2.clockAdvance + time) = energy step.1 M order time := by
  unfold energy
  apply Finset.sum_congr rfl
  intro word _
  rw [value_next seed M word.toList step generated time nonnegative]

end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderWord
