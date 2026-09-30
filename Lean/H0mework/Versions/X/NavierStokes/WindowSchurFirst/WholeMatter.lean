import H0mework.Versions.X.NavierStokes.WindowHistoryAction.Green
import H0mework.Versions.X.NavierStokes.WindowHistory.SpatialWords
import H0mework.Versions.X.NavierStokes.WindowHistoryRecovery.Covariance

set_option autoImplicit false
open scoped BigOperators Matrix Topology
namespace SaturationMonoid.NavierStokes.NativeWindowStageTenWholeFirstJet
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open PhysicsCore.DiracCliffordRepresentation PhysicsCore.DiracExteriorMatterAction
open PhysicsCore.StageNineHolonomicField PhysicsCore.Stage9C.Material.SpinPair
open PhysicsCore.StageNineDynamicBreakingVacuum
open NativeWindowHistoryGNS (Spinor HistoryHilbert)
open NativeWindowWholeActionMatter (assemble)
open NativeWindowTraceWholeHistory (H history finiteHistory component)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def componentMap (wave : IntegerWavevector) (i : Coordinate) : H →L[ℝ] HistoryHilbert :=
  (component (wave,i)).compLpL 2 averageMeasure

def linear (wave : IntegerWavevector) : H →L[ℝ] Spinor :=
  ContinuousLinearMap.pi fun spin => ContinuousLinearMap.pi
    (!![0,0;0,0;
      (1/4 : ℂ) • componentMap wave 2,
      (1/4 : ℂ) • (componentMap wave 0-Complex.I • componentMap wave 1);
      (1/4 : ℂ) • (componentMap wave 0+Complex.I • componentMap wave 1),
      -(1/4 : ℂ) • componentMap wave 2] spin)

theorem linear_apply (wave : IntegerWavevector) (value : H) :
    linear wave value=assemble 0 (fun i => componentMap wave i value) := by
  funext spin color
  fin_cases spin <;> fin_cases color <;> simp [linear,assemble]

def vacuum (wave : IntegerWavevector) : Spinor :=
  assemble (NativeWindowHistoryGNS.constant (lp.single 2 wave (1 : ℂ))) (fun _ => 0)

def read (wave : IntegerWavevector) (value : H) : Spinor := vacuum wave+linear wave value

theorem read_assemble (wave : IntegerWavevector) (value : H) :
    read wave value=assemble (NativeWindowHistoryGNS.constant (lp.single 2 wave (1 : ℂ)))
      (fun i => componentMap wave i value) := by
  rw [read,linear_apply]
  funext spin color
  change vacuum wave spin color+(assemble 0 (fun i => componentMap wave i value)) spin color=_
  fin_cases spin <;> fin_cases color <;> simp [vacuum,assemble,sub_eq_add_neg]

theorem read_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    read wave (history seed time)=NativeWindowHistoryGNS.matter seed time wave := by
  rw [read_assemble,NativeWindowWholeActionMatter.matter_original]
  simp only [componentMap,NativeWindowTraceWholeHistory.component_original]

def coefficient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector) : Spinor :=
  read wave (finiteHistory seed time M)

def temporal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector) : Spinor :=
  linear wave (NativeWindowHistoryOseen.rateHistory seed M time)

theorem coefficient_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (wave : IntegerWavevector) :
    HasDerivAt (fun t => coefficient seed M t wave) (temporal seed M time wave) time :=
  ((linear wave).hasFDerivAt.comp_hasDerivAt (E := Spinor) (F := H) time
    (NativeWindowHistoryOseen.history_hasDerivAt seed M time)).const_add (vacuum wave)

theorem temporal_actual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector) :
    temporal seed M time wave=
      linear wave (NativeWindowHistoryOseen.action seed M time (finiteHistory seed time M))+
        linear wave (NativeWindowHistoryOseen.forcingHistory seed M time) := by
  exact (congrArg (linear wave) (NativeWindowHistoryOseen.source_equation seed M time)).trans
    ((linear wave).map_add _ _)

theorem coefficient_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (wave : IntegerWavevector) :
    coefficient seed M (-2) wave=read wave
      ((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure
        (NativeWindowTraceWholeHistory.constant (NativeWindowTraceWholeHistory.original seed 0))) := by
  rw [coefficient,finiteHistory,NativeWindowTraceWholeHistory.history_preparation]

theorem coefficient_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    Tendsto (fun M => coefficient seed M time wave) atTop
      (𝓝 (NativeWindowHistoryGNS.matter seed time wave)) := by
  have actual:=((linear wave).continuous.tendsto (history seed time)).comp
    (NativeWindowHistoryWholeRecovery.projected_tendsto (history seed time))
  have complete:=actual.const_add (vacuum wave)
  change Tendsto (fun M => read wave (NativeWindowTraceWholeHistory.projected M (history seed time))) atTop
    (𝓝 (NativeWindowHistoryGNS.matter seed time wave))
  rw [← read_original seed time wave]
  simpa only [read,Function.comp_apply] using complete

def spatial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (j : Coordinate) : Spinor :=
  linear wave (NativeWindowHistorySpatialWords.history seed M [j] time)

private theorem component_include (M : ℕ) (wave k : IntegerWavevector) (i : Coordinate)
    (v : NativeFiniteActionResolvent.physicalSpace (NativeWholeH1Mixed.modes M)) :
    component (wave,i) (NativePhysicalPairing.includeCLM (NativeWholeH1Mixed.modes M)
      (NativeWholeH1Mixed.modes_closed M) v) k=v.1 (k-wave) i := by
  change NativeEndpointVelocityCarrier.wholeVelocity
    (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.puncturedEuclideanize v.1) (k-wave) i=_
  rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
    (NativeFiniteActionResolvent.physical_supported v 0 (NativeWholeH1Mixed.modes_zero M))]

theorem component_spatial_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (j i : Coordinate) :
    HasDerivAt (fun displacement => NativeWindowHistoryTranslation.action wave j displacement
      (componentMap wave i (finiteHistory seed time M)))
      (componentMap wave i (NativeWindowHistorySpatialWords.history seed M [j] time)) 0 := by
  apply NativeWindowHistoryTranslation.action_hasDerivAt_zero
  filter_upwards [(component (wave,i)).coeFn_compLpL (NativeWindowHistorySpatialWords.history seed M [j] time),
    (component (wave,i)).coeFn_compLpL (finiteHistory seed time M),
    NativeWindowHistorySpatialWords.history_original seed M [j] time,
    NativeWindowHistoryOseen.history_original seed M time] with lag derivative original source state
  intro k
  change componentMap wave i (NativeWindowHistorySpatialWords.history seed M [j] time) lag=
    component (wave,i) (NativeWindowHistorySpatialWords.history seed M [j] time lag) at derivative
  change componentMap wave i (finiteHistory seed time M) lag=
    component (wave,i) (finiteHistory seed time M lag) at original
  change componentMap wave i (NativeWindowHistorySpatialWords.history seed M [j] time) lag k=_
  rw [derivative,original,source,state]
  change component (wave,i) (NativePhysicalPairing.includeCLM _ _ _) k=
    NativePhysicalGradient.multiplier (k-wave) j * component (wave,i) (NativePhysicalPairing.includeCLM _ _ _) k
  rw [component_include,component_include]
  change (NativeWindowStageNineWords.word (NativeWholeH1Mixed.modes M) (NativeWholeH1Mixed.modes_zero M)
    (NativeWholeH1Mixed.modes_closed M) [j] (NativeWindowTraceAdjoint.value seed M (time-lag))).1 (k-wave) i=_
  rw [NativeWindowStageNineWords.word_row]
  simp only [NativeWindowStageNineWords.multiplier,mul_one,Pi.smul_apply,smul_eq_mul]

theorem coefficient_spatial_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (j : Coordinate) :
    HasDerivAt (fun displacement => NativeWindowWholeActionMatter.translate wave j displacement
      (coefficient seed M time wave)) (spatial seed M time wave j) 0 := by
  simp only [coefficient,read_assemble,NativeWindowWholeActionMatter.translate_assemble,
    NativeWindowWholeActionMatter.translate_background,spatial,linear_apply]
  exact NativeWindowWholeActionMatter.assemble_hasDerivAt (hasDerivAt_const _ _)
    (fun i => component_spatial_derivative seed M time wave j i)

def firstJet (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (wave : IntegerWavevector) : Fin 4 → Spinor :=
  Fin.cases (temporal seed M time wave) (spatial seed M time wave)

def materialBasis (spin : Fin 4) (color : Fin 2) : DiracExteriorMatterCarrier :=
  sourceColorDiracMatter (Pi.single spin (Pi.single color 1))

abbrev WholeMatter := MatterCoordinateIndex → HistoryHilbert

def includeMatter (field : Spinor) : WholeMatter :=
  fun index => ∑ spin : Fin 4,∑ color : Fin 2,
    (matterCoordinateEquiv (materialBasis spin color) index) • field spin color

def connection (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (field : Spinor) : WholeMatter :=
  fun index => ∑ spin : Fin 4,∑ color : Fin 2,
    (matterCoordinateEquiv (NativeCanonicalFriedrichsAction.lower velocity jet
      (materialBasis spin color)) index) • field spin color

def kinetic (velocity : PhysicalSpace) (jet : Fin 4 → Spinor) : Spinor :=
  ∑ direction,NativeWindowHistoryGNS.action (NativeCanonicalFriedrichsPrincipal.normalized velocity direction) (jet direction)

theorem kinetic_split (velocity : PhysicalSpace) (first : Spinor) (spatial : Coordinate → Spinor) :
    kinetic velocity (Fin.cases first spatial)=first+
      ∑ j : Coordinate,NativeWindowHistoryGNS.action
        (NativeCanonicalFriedrichsPrincipal.normalized velocity j.succ) (spatial j) := by
  rw [kinetic,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,NativeCanonicalFriedrichsPrincipal.normalized_time]
  have identity : NativeWindowHistoryGNS.action 1 first=first := by
    funext spin color
    simp [NativeWindowHistoryGNS.action,Matrix.one_apply]
  rw [identity]

-- The complete first-jet action is retained as an actual source term; it is not set to zero.
def motherAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector)
    (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : WholeMatter :=
  includeMatter (kinetic velocity (firstJet seed M time wave))+connection velocity jet (coefficient seed M time wave)

theorem actual_first_jet (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector)
    (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    motherAction seed M time wave velocity jet=
      includeMatter (linear wave (NativeWindowHistoryOseen.action seed M time (finiteHistory seed time M))+
      linear wave (NativeWindowHistoryOseen.forcingHistory seed M time)+
      (∑ j : Coordinate,NativeWindowHistoryGNS.action
        (NativeCanonicalFriedrichsPrincipal.normalized velocity j.succ) (spatial seed M time wave j)))+
      connection velocity jet (coefficient seed M time wave) := by
  apply congrArg (fun v : WholeMatter => v+connection velocity jet (coefficient seed M time wave))
  apply congrArg includeMatter
  exact (kinetic_split velocity (temporal seed M time wave) (spatial seed M time wave)).trans
    (congrArg (fun v : Spinor => v+∑ j : Coordinate,NativeWindowHistoryGNS.action
      (NativeCanonicalFriedrichsPrincipal.normalized velocity j.succ) (spatial seed M time wave j))
        (temporal_actual seed M time wave))

local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def sourceJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (point : NativePhysicalFourier.Torus) : Fin 4 → PhysicalSpace :=
  Fin.cases
    (NativePhysicalFourier.realField
      (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowEvolution.velocityJet seed 1 time)) point)
    (fun j => WithLp.toLp 2 fun i => (NativeWindowHistoryFirstJet.physicalJet seed time valid j i point).re)

def sourceMotherAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (point : NativePhysicalFourier.Torus) : WholeMatter :=
  motherAction seed M time wave (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time point)
    (sourceJet seed time valid point)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem coefficient_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (wave : IntegerWavevector) :
    coefficient seed M (step.2.clockAdvance+time) wave=coefficient step.1 M time wave :=
  congrArg (read wave) (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M)

theorem temporal_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (wave : IntegerWavevector) :
    temporal seed M (step.2.clockAdvance+time) wave=temporal step.1 M time wave :=
  congrArg (linear wave) (NativeWindowHistoryOseen.rateHistory_next seed M step generated time nonnegative)

theorem spatial_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (wave : IntegerWavevector) (j : Coordinate) :
    spatial seed M (step.2.clockAdvance+time) wave j=spatial step.1 M time wave j :=
  congrArg (linear wave) (NativeWindowHistorySpatialWords.history_next seed M [j] step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowStageTenWholeFirstJet
