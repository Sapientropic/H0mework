import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Bridge
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Gradient
import H0mework.Versions.X.NavierStokes.SourcePairing.RecoveryTimeCanonicalWrite
import H0mework.Versions.X.NavierStokes.WindowHistoryAction.Matter
import H0mework.Versions.X.NavierStokes.WindowSchurFirst.WholeMatter

set_option autoImplicit false
open scoped BigOperators Matrix Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeGNS
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open PhysicsCore.DiracCliffordRepresentation
open NativePhysicalFourier (ScalarSequence)
open NativeWindowKernelHalfDensity (rootKernel)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowAbsoluteTimeIsometry (map)
open NativeWindowAbsoluteTimeSource (H history rate)
open NativeRecoveryTimeCanonical (gamma canonicalDual matterProgram)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}

abbrev Scalar := Lp ScalarSequence 2 (volume : Measure ℝ)
abbrev Spinor := NativeRecoveryTimeCanonical.Spinor Scalar

local instance spinorSeminormed : SeminormedAddCommGroup Spinor :=
  (inferInstance : NormedAddCommGroup Spinor).toSeminormedAddCommGroup
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup

def scalarMap (time : ℝ) : NativeWindowHistoryGNS.HistoryHilbert →ₗᵢ[ℂ] Scalar where
  toFun := map ScalarSequence time
  map_add' u v := (map ScalarSequence time).map_add u v
  map_smul' c v := NativeWindowAbsoluteTimeIsometry.map_scalar ScalarSequence time c v
  norm_map' := (map ScalarSequence time).norm_map

def spinorMap (time : ℝ) (field : NativeWindowHistoryGNS.Spinor) : Spinor :=
  fun spin color => scalarMap time (field spin color)

theorem gamma_map (time : ℝ) (matrix : DiracMatrix) (field : NativeWindowHistoryGNS.Spinor) :
    gamma matrix (spinorMap time field)=spinorMap time (NativeWindowHistoryGNS.action matrix field) := by
  funext spin color
  simp only [gamma,spinorMap,NativeWindowHistoryGNS.action,map_sum,map_smul]
  rfl

theorem dual_map (time : ℝ) (u v : NativeWindowHistoryGNS.Spinor) :
    canonicalDual (spinorMap time u) (spinorMap time v)=NativeWindowHistoryGNS.canonicalDual u v := by
  change (∑ spin : Fin 4,∑ color : Fin 2,inner ℂ
    (gamma PhysicsCore.StageNineFullDiracAdjointMaterial.diracAdjointSpinSwap (spinorMap time u) spin color)
    (spinorMap time v spin color))=_
  rw [gamma_map]
  simp only [spinorMap,(scalarMap time).inner_map_map]
  rfl

def component (wave : IntegerWavevector) (i : Coordinate) : H →L[ℝ] Scalar :=
  (NativeWindowTraceWholeHistory.component (wave,i)).compLpL 2 (volume : Measure ℝ)

theorem component_source (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (i : Coordinate) :
    component wave i (history seed time)=scalarMap time (NativeWindowHistoryGNS.history seed time (wave,i)) := by
  have natural:=NativeWindowAbsoluteTimeIsometry.naturality NativeWholeResolvent.wholePhysical
    (NativeWindowTraceWholeHistory.component (wave,i)) time (NativeWindowTraceWholeHistory.history seed time)
  rw [NativeWindowTraceWholeHistory.component_original,NativeWindowAbsoluteTimeBridge.source_map] at natural
  exact natural.symm

def background (wave : IntegerWavevector) (time : ℝ) : Scalar :=
  NativeWindowAbsoluteTimeCarrier.field rootKernel (NativeWindowKernelHalfDensity.root_memLp 2)
    (fun _ => lp.single 2 wave (1 : ℂ)) (memLp_top_const _) time

def backgroundRate (wave : IntegerWavevector) (time : ℝ) : Scalar :=
  NativeWindowAbsoluteTimeCarrier.field (deriv rootKernel) (NativeWindowKernelHalfDensity.derivative_memLp 2)
    (fun _ => lp.single 2 wave (1 : ℂ)) (memLp_top_const _) time

theorem background_source (wave : IntegerWavevector) (time : ℝ) :
    background wave time=scalarMap time (NativeWindowHistoryGNS.constant (lp.single 2 wave (1 : ℂ))) := by
  apply Lp.ext
  have weighted:=NativeWindowAbsoluteTimeIsometry.weighted_ae ScalarSequence
    (NativeWindowHistoryGNS.constant_ae (lp.single 2 wave (1 : ℂ)))
  have shifted:=(Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae weighted
  filter_upwards [NativeWindowAbsoluteTimeCarrier.field_ae rootKernel (NativeWindowKernelHalfDensity.root_memLp 2)
    (fun _ => (lp.single 2 wave (1 : ℂ) : ScalarSequence)) (memLp_top_const _) time,
    NativeWindowAbsoluteTimeIsometry.map_ae ScalarSequence time (NativeWindowHistoryGNS.constant (lp.single 2 wave (1 : ℂ))),shifted]
    with s field mapped actual
  change background wave time s=_ at field
  change scalarMap time (NativeWindowHistoryGNS.constant (lp.single 2 wave (1 : ℂ))) s=_ at mapped
  rw [field,mapped]
  exact actual.symm

theorem background_hasDerivAt (wave : IntegerWavevector) (time : ℝ) :
    HasDerivAt (background wave) (backgroundRate wave time) time := by
  obtain ⟨A,A0,slopes⟩:=NativeWindowKernelHalfDensity.shift_quotient_bound
  obtain ⟨B,B0,point⟩:=NativeWindowKernelHalfDensity.source_derivative_bound
  exact NativeWindowAbsoluteTimeCarrier.field_hasDerivAt rootKernel (deriv rootKernel)
    (NativeWindowKernelHalfDensity.root_memLp 2) (NativeWindowKernelHalfDensity.derivative_memLp 2)
    NativeWindowKernelHalfDensity.shifted_derivative (A+B) (add_nonneg A0 B0)
    (fun t s d => (slopes t s d).trans (le_add_of_nonneg_right B0))
    (fun x => (point x).trans (le_add_of_nonneg_left A0))
    NativeWindowAbsoluteTimeSource.root_zero_outside NativeWindowAbsoluteTimeSource.rate_zero_outside
    (fun _ => (lp.single 2 wave (1 : ℂ) : ScalarSequence)) (memLp_top_const _)
    ‖(lp.single 2 wave (1 : ℂ) : ScalarSequence)‖ (fun _ => le_rfl) time

def backgroundCLM : Scalar →L[ℂ] Spinor :=
  ContinuousLinearMap.pi fun spin => ContinuousLinearMap.pi
    (!![0,0;0,0;ContinuousLinearMap.id ℂ Scalar,0;0,ContinuousLinearMap.id ℂ Scalar] spin)

def componentCLM (wave : IntegerWavevector) : H →L[ℝ] Spinor :=
  (NativeRecoveryTimeCanonicalWrite.matterCLM (H := Scalar)).restrictScalars ℝ |>.comp
    (ContinuousLinearMap.pi fun i => component wave i)

def matter (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) : Spinor :=
  backgroundCLM (background wave time)+componentCLM wave (history seed time)

def matterRate (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) : Spinor :=
  backgroundCLM (backgroundRate wave time)+componentCLM wave (rate seed time)

theorem matter_program (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    matter seed time wave=matterProgram (fun k => background k time) (fun k i => component k i (history seed time)) wave := by
  funext spin color
  change backgroundCLM (background wave time) spin color+
    NativeRecoveryTimeCanonicalWrite.matterCLM (fun i => component wave i (history seed time)) spin color=_
  fin_cases spin <;> fin_cases color <;>
    simp [backgroundCLM,NativeRecoveryTimeCanonicalWrite.matterCLM_apply,
      NativeRecoveryTimeCanonicalWrite.matterMatrix,matterProgram,Fin.sum_univ_three] <;> module

theorem matter_source (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    matter seed time wave=spinorMap time (NativeWindowHistoryGNS.matter seed time wave) := by
  rw [matter_program,NativeWindowWholeActionMatter.matter_original]
  simp only [background_source,component_source]
  funext spin color
  fin_cases spin <;> fin_cases color <;>
    simp [matterProgram,spinorMap,NativeWindowWholeActionMatter.assemble,map_add,map_sub,map_smul]

theorem matter_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    HasDerivAt (fun t => matter seed t wave) (matterRate seed time wave) time :=
  ((backgroundCLM.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (E := Spinor) (F := Scalar) time
    (background_hasDerivAt wave time)).add
      ((componentCLM wave).hasFDerivAt.comp_hasDerivAt (E := Spinor) (F := H) time
        (NativeWindowAbsoluteTimeSource.source_hasDerivAt seed time))

theorem current_source (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    canonicalDual (matter seed time wave) (gamma (diracGamma direction) (matter seed time 0))=
      NativePairedCurrentFourier.coefficient
        (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst)
        (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd) direction wave := by
  rw [matter_source,matter_source,gamma_map,dual_map]
  exact NativeWindowHistoryGNS.current_read seed time direction wave

def spatialMatter (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ)
    (wave : IntegerWavevector) : Spinor :=
  componentCLM wave (NativeWindowAbsoluteTimeGradient.spatial M j (history seed time))

def spatialMatterRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ)
    (wave : IntegerWavevector) : Spinor :=
  componentCLM wave (NativeWindowAbsoluteTimeGradient.spatial M j (rate seed time))

theorem spatialMatter_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ)
    (wave : IntegerWavevector) :
    HasDerivAt (fun t => spatialMatter seed M j t wave) (spatialMatterRate seed M j time wave) time :=
  (componentCLM wave).hasFDerivAt.comp_hasDerivAt (E := Spinor) (F := H) time
    (NativeWindowAbsoluteTimeGradient.source_spatial_hasDerivAt seed M j time)

theorem source_spatial_rate_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (wave : IntegerWavevector) :
    ∃ C : ℝ,0≤C ∧∀ M j,∀ time∈Icc 0 horizon,‖spatialMatterRate seed M j time wave‖^2≤C := by
  obtain ⟨B,B0,paid⟩:=NativeWindowAbsoluteTimeGradient.source_rate_spatial_bound seed horizon
  refine ⟨‖componentCLM wave‖^2*B,mul_nonneg (sq_nonneg _) B0,fun M j time inside => ?_⟩
  have normed:=(componentCLM wave).le_opNorm (NativeWindowAbsoluteTimeGradient.spatial M j (rate seed time))
  exact (pow_le_pow_left₀ (norm_nonneg _) normed 2).trans
    (by rw [mul_pow]; exact mul_le_mul_of_nonneg_left (paid M j time inside) (sq_nonneg _))

def finiteMatter (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector) : Spinor :=
  backgroundCLM (background wave time)+componentCLM wave (NativeWindowAbsoluteTimeBridge.finiteHistory seed M time)

def finiteMatterRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector) : Spinor :=
  backgroundCLM (backgroundRate wave time)+componentCLM wave (NativeWindowAbsoluteTimeBridge.finiteRate seed M time)

theorem finiteMatter_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector) :
    HasDerivAt (fun t => finiteMatter seed M t wave) (finiteMatterRate seed M time wave) time :=
  ((backgroundCLM.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (E := Spinor) (F := Scalar) time
    (background_hasDerivAt wave time)).add
      ((componentCLM wave).hasFDerivAt.comp_hasDerivAt (E := Spinor) (F := H) time
        (NativeWindowAbsoluteTimeBridge.finite_hasDerivAt seed M time))

theorem finiteMatterRate_actual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector) :
    finiteMatterRate seed M time wave=backgroundCLM (backgroundRate wave time)+
      componentCLM wave (NativeWindowAbsoluteTimeBridge.absoluteAction seed M time
        (NativeWindowAbsoluteTimeBridge.finiteHistory seed M time))+
      componentCLM wave (map NativeWholeResolvent.wholePhysical time (NativeWindowHistoryOseen.forcingHistory seed M time))-
      componentCLM wave (NativeWindowAbsoluteTimeBridge.sampleDerivative seed M time) := by
  have actual := congrArg (componentCLM wave) (NativeWindowAbsoluteTimeBridge.source_equation seed M time)
  rw [map_sub,map_add] at actual
  have lifted := congrArg (fun v : Spinor => backgroundCLM (backgroundRate wave time)+v) actual
  simpa only [finiteMatterRate,add_sub_assoc,add_assoc] using lifted

open PhysicsCore.StageNineHolonomicField PhysicsCore.DiracExteriorMatterAction
local instance : Fintype MatterCoordinateIndex := Fintype.ofFinite MatterCoordinateIndex
abbrev WholeMatter := MatterCoordinateIndex → Scalar

def extend (A : Module.End ℂ DiracExteriorMatterCarrier) : Spinor →L[ℝ] WholeMatter :=
  ContinuousLinearMap.pi fun index => ∑ spin : Fin 4,∑ color : Fin 2,
    (matterCoordinateEquiv (A (NativeWindowStageTenWholeFirstJet.materialBasis spin color)) index) •
      (ContinuousLinearMap.proj color : (Fin 2 → Scalar) →L[ℝ] Scalar).comp
        (ContinuousLinearMap.proj spin : Spinor →L[ℝ] (Fin 2 → Scalar))

def fullMatter (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) : WholeMatter :=
  extend LinearMap.id (matter seed time wave)

def spaceAndConnection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector)
    (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : WholeMatter :=
  (∑ j : Coordinate,extend (diracMatrixMatterAction (NativeCanonicalFriedrichsPrincipal.normalized velocity j.succ))
    (spatialMatter seed M j time wave))+
      extend (NativeCanonicalFriedrichsAction.lower velocity jet) (matter seed time wave)

def motherAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector)
    (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : WholeMatter :=
  (∑ direction : Fin 4,extend (diracMatrixMatterAction (NativeCanonicalFriedrichsPrincipal.normalized velocity direction))
    (Fin.cases (matterRate seed time wave) (fun j => spatialMatter seed M j time wave) direction))+
      extend (NativeCanonicalFriedrichsAction.lower velocity jet) (matter seed time wave)

def finiteMotherAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector)
    (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : WholeMatter :=
  (∑ direction : Fin 4,extend (diracMatrixMatterAction (NativeCanonicalFriedrichsPrincipal.normalized velocity direction))
    (Fin.cases (finiteMatterRate seed M time wave) (fun j => spatialMatter seed M j time wave) direction))+
      extend (NativeCanonicalFriedrichsAction.lower velocity jet) (finiteMatter seed M time wave)

theorem finite_actual_first_jet (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector)
    (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    finiteMotherAction seed M time wave velocity jet=
      extend LinearMap.id (backgroundCLM (backgroundRate wave time)+
        componentCLM wave (NativeWindowAbsoluteTimeBridge.absoluteAction seed M time
          (NativeWindowAbsoluteTimeBridge.finiteHistory seed M time))+
        componentCLM wave (map NativeWholeResolvent.wholePhysical time (NativeWindowHistoryOseen.forcingHistory seed M time))-
        componentCLM wave (NativeWindowAbsoluteTimeBridge.sampleDerivative seed M time))+
      (∑ j : Coordinate,extend (diracMatrixMatterAction (NativeCanonicalFriedrichsPrincipal.normalized velocity j.succ))
        (spatialMatter seed M j time wave))+
      extend (NativeCanonicalFriedrichsAction.lower velocity jet) (finiteMatter seed M time wave) := by
  have unit : diracMatrixMatterAction (1 : DiracMatrix)=LinearMap.id := by
    apply LinearMap.ext
    intro field
    funext spin
    simp [diracMatrixMatterAction,Matrix.one_apply]
  simp only [finiteMotherAction,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,
    NativeCanonicalFriedrichsPrincipal.normalized_time,unit,finiteMatterRate_actual]

theorem motherAction_time (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector)
    (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    motherAction seed M time wave velocity jet=extend LinearMap.id (matterRate seed time wave)+
      spaceAndConnection seed M time wave velocity jet := by
  have unit : diracMatrixMatterAction (1 : DiracMatrix)=LinearMap.id := by
    apply LinearMap.ext
    intro field
    funext spin
    simp [diracMatrixMatterAction,Matrix.one_apply]
  simp only [motherAction,spaceAndConnection,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,
    NativeCanonicalFriedrichsPrincipal.normalized_time,unit]
  abel

theorem fullMatter_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (wave : IntegerWavevector)
    (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    HasDerivAt (fun t => fullMatter seed t wave)
      (motherAction seed M time wave velocity jet-spaceAndConnection seed M time wave velocity jet) time := by
  have actual := (extend LinearMap.id).hasFDerivAt.comp_hasDerivAt (E := WholeMatter) (F := Spinor) time
    (matter_hasDerivAt seed time wave)
  rw [motherAction_time,add_sub_cancel_right]
  exact actual

theorem source_first_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (point : NativePhysicalFourier.Torus) :
    HasDerivAt (fun t => fullMatter seed t wave)
      (motherAction seed M time wave (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time point)
        (NativeWindowStageTenWholeFirstJet.sourceJet seed time valid point)-
      spaceAndConnection seed M time wave (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time point)
        (NativeWindowStageTenWholeFirstJet.sourceJet seed time valid point)) time :=
  fullMatter_hasDerivAt seed M time wave _ _

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem matter_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (wave : IntegerWavevector) :
    matter seed (step.2.clockAdvance+time) wave=fun spin color =>
      NativeWindowAbsoluteTimeIsometry.clock ScalarSequence step.2.clockAdvance (matter step.1 time wave spin color) := by
  have original : NativeWindowHistoryGNS.matter seed (step.2.clockAdvance+time) wave=
      NativeWindowHistoryGNS.matter step.1 time wave := by
    rw [NativeWindowWholeActionMatter.matter_original,NativeWindowWholeActionMatter.matter_original]
    simp only [NativeWindowHistoryGNS.history_next seed step generated time nonnegative]
  rw [matter_source,matter_source,original]
  funext spin color
  exact NativeWindowAbsoluteTimeIsometry.map_clock ScalarSequence time step.2.clockAdvance _

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeGNS
