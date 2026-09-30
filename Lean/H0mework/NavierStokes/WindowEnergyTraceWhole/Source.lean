import H0mework.NavierStokes.WindowHistory.Current
import H0mework.NavierStokes.WindowSourcePreparation.Source
import H0mework.NavierStokes.WindowEnergyTraceEndpoint.Window
import H0mework.NavierStokes.StressWeakInput.PhysicalPairing

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceWholeHistory
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativeEndpointVelocityCarrier
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

abbrev H := Lp wholePhysical 2 averageMeasure

def original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : wholePhysical := by
  refine ⟨(NativeUnifiedCompleteSource.source seed time).fst,?_,(NativeCompletePairedAction.source seed time).reality⟩
  intro wave
  have transverse : WholeStateTransverse (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := by
    by_cases nonnegative : 0 ≤ time
    · exact NativeCompleteVelocityCurl.source_transverse seed time nonnegative
    · rw [NativeWindowPreparationSource.complete_nonpositive seed time (le_of_not_ge nonnegative)]
      exact NativeCompleteVelocityCurl.source_transverse seed 0 le_rfl
  have same : wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave.1=
      fun i => (NativeUnifiedCompleteSource.source seed time).fst wave i := by
    funext i
    exact wholeVelocity_nonzero _ wave i
  exact same ▸ transverse wave.1

theorem original_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖original seed time‖ ≤ NativeUnifiedCompleteSource.budget seed :=
  (WithLp.norm_fst_le _ _).trans (NativeUnifiedCompleteSource.source_bound seed time)

def sample (seed : GeneratedWholeRestartCurrent nu) (time shift : ℝ) : wholePhysical := original seed (time-shift)

theorem sample_memLp (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (p : ℝ≥0∞) :
    MemLp (sample seed time) p averageMeasure := by
  have original := NativeForwardWindowPairingReadout.original_integrable seed time
  have measured : AEStronglyMeasurable (sample seed time) averageMeasure := by
    apply Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp
    exact (NativeForwardWindowPairingReadout.meanRead.integrable_comp original).aestronglyMeasurable
  exact MemLp.of_bound measured (NativeUnifiedCompleteSource.budget seed)
    (Eventually.of_forall fun shift => original_bound seed (time-shift))

def history (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : H :=
  (sample_memLp seed time 2).toLp (sample seed time)

theorem history_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    history seed time =ᵐ[averageMeasure] sample seed time := (sample_memLp seed time 2).coeFn_toLp

def component (index : NativeCofinalStressPositivity.Index) : wholePhysical →L[ℝ] NativePhysicalFourier.ScalarSequence :=
  (NativePairedCarrierJets.shiftedCLM index.1 index.2).comp (wholeVelocityCLM.comp wholePhysical.subtypeL)

theorem component_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : NativeCofinalStressPositivity.Index) :
    (component index).compLpL 2 averageMeasure (history seed time)=NativeWindowHistoryGNS.history seed time index := by
  apply Lp.ext
  filter_upwards [(component index).coeFn_compLpL (history seed time),history_ae seed time,
    NativeWindowHistoryGNS.history_ae seed time index] with shift read raw previous
  rw [read,raw,previous]
  rfl

theorem mean_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    (∫ shift,history seed time shift ∂averageMeasure).1=(NativeForwardWindowSource.source seed time).fst := by
  have paid := (sample_memLp seed time 1).integrable le_rfl
  rw [integral_congr_ae (history_ae seed time)]
  have read := wholePhysical.subtypeL.integral_comp_comm paid
  change (∫ shift,(sample seed time shift).1 ∂averageMeasure)=(∫ shift,sample seed time shift ∂averageMeasure).1 at read
  rw [← read]
  exact (NativeForwardWindowPairingReadout.linear_probability_integral NativeForwardWindowPairingReadout.meanRead seed time).symm

def constant (value : wholePhysical) : H :=
  (memLp_const (μ := averageMeasure) (p := 2) value).toLp (fun _ => value)

theorem constant_ae (value : wholePhysical) : constant value =ᵐ[averageMeasure] fun _ => value :=
  (memLp_const (μ := averageMeasure) (p := 2) value).coeFn_toLp

theorem component_constant (index : NativeCofinalStressPositivity.Index) (value : wholePhysical) :
    (component index).compLpL 2 averageMeasure (constant value)=NativeWindowHistoryGNS.constant (component index value) := by
  apply Lp.ext
  filter_upwards [(component index).coeFn_compLpL (constant value),constant_ae value,
    NativeWindowHistoryGNS.constant_ae (component index value)] with shift read actual old
  rw [read,actual,old]

def centered (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : H :=
  history seed time-constant (∫ shift,history seed time shift ∂averageMeasure)

theorem component_centered (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : NativeCofinalStressPositivity.Index) :
    (component index).compLpL 2 averageMeasure (centered seed time)=NativeWindowHistoryGNS.vector seed time index := by
  rw [centered,map_sub,component_original,component_constant,NativeWindowHistoryGNS.vector]
  congr 2
  change NativePairedCarrierJets.shifted (wholeVelocity (∫ shift,history seed time shift ∂averageMeasure).1) index.1 index.2=_
  rw [mean_original]
  rfl

theorem stress_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    inner ℂ ((component (wave,output)).compLpL 2 averageMeasure (history seed time))
        ((component (0,input)).compLpL 2 averageMeasure (history seed time))=
      -NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input := by
  rw [component_original,component_original,NativeWindowHistoryGNS.stress_read]

theorem residual_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    inner ℂ ((component (wave,output)).compLpL 2 averageMeasure (centered seed time))
        ((component (0,input)).compLpL 2 averageMeasure (centered seed time))=
      -(NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input-
        NativeStressSource.quadraticFlux (wholeVelocity (NativeForwardWindowSource.source seed time).fst) wave output input) := by
  rw [component_centered,component_centered,NativeWindowHistoryGNS.residual_read]

theorem norm_square (value : H) : ‖value‖^2=∫ shift,‖value shift‖^2 ∂averageMeasure := by
  calc
    _ = inner ℝ value value := (real_inner_self_eq_norm_sq (x := value)).symm
    _ = _ := by rw [L2.inner_def]; simp only [real_inner_self_eq_norm_sq]

def projection (M : ℕ) : wholePhysical →L[ℝ] wholePhysical :=
  (includeCLM (NativeWholeH1Mixed.modes M) (NativeWholeH1Mixed.modes_closed M)).comp
    (restrictCLM (NativeWholeH1Mixed.modes M) (NativeWholeH1Mixed.modes_zero M) (NativeWholeH1Mixed.modes_closed M))

def finiteHistory (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M : ℕ) : H :=
  (projection M).compLpL 2 averageMeasure (history seed time)

theorem finiteHistory_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M : ℕ) :
    finiteHistory seed time M =ᵐ[averageMeasure] fun shift => projection M (original seed (time-shift)) := by
  filter_upwards [(projection M).coeFn_compLpL (history seed time),history_ae seed time] with shift read raw
  change ((projection M).compLpL 2 averageMeasure (history seed time)) shift=_
  rw [read,raw]
  rfl

theorem history_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖history seed time‖ ≤ NativeUnifiedCompleteSource.budget seed := by
  have positive := (norm_nonneg _).trans (original_bound seed time)
  have paid := Lp.norm_le_of_ae_bound positive (by
    filter_upwards [history_ae seed time] with shift actual
    rw [actual]
    exact original_bound seed (time-shift))
  simpa [measureUnivNNReal] using paid

theorem original_nonpositive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonpositive : time ≤ 0) :
    original seed time=original seed 0 := by
  apply Subtype.ext
  exact congrArg (fun v : NativeCompleteStressAction.FullSpace => v.fst)
    (NativeWindowPreparationSource.complete_nonpositive seed time nonpositive)

theorem history_preparation (seed : GeneratedWholeRestartCurrent nu) :
    history seed (-2)=constant (original seed 0) := by
  apply Lp.ext
  filter_upwards [history_ae seed (-2),constant_ae (original seed 0),NativeWindowTraceEndpointWindow.average_interval]
    with shift actual fixed support
  rw [actual,fixed,sample,original_nonpositive seed (-2-shift) (by linarith [support.1])]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem original_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    original seed (step.2.clockAdvance+time)=original step.1 time := by
  apply Subtype.ext
  exact congrArg (fun v : NativeCompleteStressAction.FullSpace => v.fst)
    (NativeUnifiedCompleteSource.source_generated_next seed step generated time nonnegative)

theorem history_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    history seed (step.2.clockAdvance+time)=history step.1 time := by
  apply Lp.ext
  filter_upwards [history_ae seed (step.2.clockAdvance+time),history_ae step.1 time,NativeWindowHistoryGNS.average_support]
    with shift first last support
  rw [first,last,sample,sample,add_sub_assoc,original_next seed step generated (time-shift) (by linarith)]

theorem finiteHistory_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) (M : ℕ) :
    finiteHistory seed (step.2.clockAdvance+time) M=finiteHistory step.1 time M := by
  rw [finiteHistory,finiteHistory,history_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceWholeHistory
