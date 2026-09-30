import H0mework.Versions.X.NavierStokes.WindowEnergyTraceEndpoint.Family
import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffOperatorKernel
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceAdjoint.Gap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceEndpointWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceEndpointFamily (endpoint endpoint_original endpoint_continuous)
open NativeWindowTraceAdjoint (value value_continuous)
open NativeWindowTraceAdjointGap (factor)
open NativeWindowTraceCutOperator (jointTest)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def terminal (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (sample : ℝ) : physicalSpace (modes M) :=
  jointTest seed observation (modes M) F radius (value seed M sample)

theorem terminal_continuous (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : Continuous (terminal seed observation M F radius) :=
  (LinearMap.toContinuousLinearMap (jointTest seed observation (modes M) F radius)).continuous.comp
    (value_continuous seed M)

theorem average_interval : ∀ᵐ shift : ℝ ∂averageMeasure,shift ∈ Icc (-2 : ℝ) (-1) := by
  change ∀ᵐ shift : ℝ ∂volume.withDensity (fun shift => (NativeForwardWindowPairingReadout.density shift : ℝ≥0∞)),_
  rw [ae_withDensity_iff NativeForwardWindowPairingReadout.density_measurable.coe_nnreal_ennreal]
  filter_upwards with shift nonzero
  apply NativeUnheatedWindowJensen.kernel_support 0 shift
  intro zero
  apply nonzero
  have original : NativeForwardWindowSource.kernel shift=0 := by
    simpa only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero] using zero
  simp only [NativeForwardWindowPairingReadout.density,original]
  rfl

def sample (observation shift : ℝ) : Icc observation (observation+2) :=
  projIcc observation (observation+2) (by linarith) (observation-shift)

theorem sample_original (observation : ℝ) : ∀ᵐ shift : ℝ ∂averageMeasure,
    (sample observation shift).1=observation-shift := by
  filter_upwards [average_interval] with shift support
  exact congrArg Subtype.val (projIcc_of_mem (by linarith : observation ≤ observation+2)
    (show observation-shift ∈ Icc observation (observation+2) by constructor <;> linarith [support.1,support.2]))

def response (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (shift : ℝ) : physicalSpace (modes M) :=
  endpoint seed M observation (observation+2) (by linarith) (sample observation shift).1
    (terminal seed observation M F radius (sample observation shift).1)

theorem response_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : ∀ᵐ shift : ℝ ∂averageMeasure,
      ∃ ordered : observation ≤ observation-shift,response seed observation M F radius shift=
        NativeWindowTraceAdjoint.backward seed M observation (observation-shift) ordered
          (terminal seed observation M F radius (observation-shift)) observation := by
  filter_upwards [sample_original observation,average_interval] with shift same support
  refine ⟨by linarith [support.2],?_⟩
  rw [response,same,endpoint_original seed M observation (observation+2) _ (observation-shift)
    (by constructor <;> linarith [support.1,support.2])]

theorem response_continuous (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : Continuous (response seed observation M F radius) := by
  have original := endpoint_continuous seed M observation (observation+2) (by linarith)
    (terminal seed observation M F radius) (terminal_continuous seed observation M F radius).continuousOn
  exact original.comp_continuous
    (continuous_subtype_val.comp (continuous_projIcc.comp (continuous_const.sub continuous_id)))
      (fun shift => (sample observation shift).2)

theorem response_memLp (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (p : ℝ≥0∞) :
    MemLp (response seed observation M F radius) p averageMeasure := by
  obtain ⟨bound,bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (endpoint_continuous seed M observation (observation+2) (by linarith)
      (terminal seed observation M F radius) (terminal_continuous seed observation M F radius).continuousOn)
  exact MemLp.of_bound (response_continuous seed observation M F radius).aestronglyMeasurable bound
    (Eventually.of_forall fun shift => bounded (sample observation shift).1 (sample observation shift).2)

theorem terminal_memLp (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (p : ℝ≥0∞) :
    MemLp (fun shift => terminal seed observation M F radius (observation-shift)) p averageMeasure := by
  obtain ⟨bound,bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((terminal_continuous seed observation M F radius).continuousOn (s := Icc observation (observation+2)))
  apply MemLp.of_bound ((terminal_continuous seed observation M F radius).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable bound
  filter_upwards [average_interval] with shift support
  exact bounded (observation-shift) (by constructor <;> linarith [support.1,support.2])

def energy (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : ℝ :=
  ∫shift,‖coefficients (modes M) (response seed observation M F radius shift)‖^2 ∂averageMeasure

def terminalEnergy (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : ℝ :=
  ∫shift,‖coefficients (modes M) (terminal seed observation M F radius (observation-shift))‖^2 ∂averageMeasure

def window (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : physicalSpace (modes M) :=
  ∫shift,response seed observation M F radius shift ∂averageMeasure

theorem source_contraction (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) :
    energy seed observation M F radius ≤ (factor nu)^2*terminalEnergy seed observation M F radius := by
  let co := LinearMap.toContinuousLinearMap (coefficients (modes M))
  have first := (co.comp_memLp' (response_memLp seed observation M F radius 2)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have last := (co.comp_memLp' (terminal_memLp seed observation M F radius 2)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have estimate := integral_mono_ae first (last.const_mul ((factor nu)^2)) (by
    filter_upwards [response_original seed observation M F radius,
      NativeWindowTraceAdjointGap.average_contraction seed M observation] with shift original contracted
    obtain ⟨ordered,same⟩ := original
    obtain ⟨_,bound⟩ := contracted
    change ‖coefficients (modes M) (response seed observation M F radius shift)‖^2 ≤ _
    rw [same]
    simpa only [co,Function.comp_def,mul_pow] using! pow_le_pow_left₀ (norm_nonneg _) (bound (terminal seed observation M F radius (observation-shift))) 2)
  simpa only [energy,terminalEnergy,co,Function.comp_def,integral_const_mul] using! estimate

theorem source_window_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) :
    ‖coefficients (modes M) (window seed observation M F radius)‖^2 ≤
      (factor nu)^2*terminalEnergy seed observation M F radius := by
  let co := LinearMap.toContinuousLinearMap (coefficients (modes M))
  have paid := (response_memLp seed observation M F radius 1).integrable le_rfl
  have square := (co.comp_memLp' (response_memLp seed observation M F radius 2)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have convex := (convexOn_norm (s := (univ : Set (EuclideanSpace ℂ (modes M × Coordinate)))) convex_univ).pow
    (fun _ _ => norm_nonneg _) 2
  have mean := convex.map_integral_le ((continuous_norm.pow 2).continuousOn) isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) (co.integrable_comp paid) square
  have read := (co.integral_comp_comm paid).symm
  change co (window seed observation M F radius)=_ at read
  change ‖∫ shift,co (response seed observation M F radius shift) ∂averageMeasure‖^2 ≤ energy seed observation M F radius at mean
  rw [← read] at mean
  exact mean.trans (source_contraction seed observation M F radius)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem terminal_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (observation : ℝ) (observed : 0 ≤ observation)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (sample : ℝ) (nonnegative : 0 ≤ sample) :
    terminal seed (step.2.clockAdvance+observation) M F radius (step.2.clockAdvance+sample)=
      terminal step.1 observation M F radius sample := by
  have original := congrArg Prod.fst (NativeWindowTraceAdjoint.source_next seed M step generated sample nonnegative)
  change value seed M (step.2.clockAdvance+sample)=value step.1 M sample at original
  rw [terminal,terminal,NativeWindowTraceCutOperator.jointTest_next seed step generated observation observed,original]

theorem response_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (observation : ℝ) (observed : 0 ≤ observation)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    response seed (step.2.clockAdvance+observation) M F radius =ᵐ[averageMeasure]
      response step.1 observation M F radius := by
  filter_upwards [response_original seed (step.2.clockAdvance+observation) M F radius,
    response_original step.1 observation M F radius,average_interval] with shift first last support
  obtain ⟨firstOrdered,firstRead⟩ := first
  obtain ⟨lastOrdered,lastRead⟩ := last
  rw [firstRead,lastRead]
  have sample0 : 0 ≤ observation-shift := by linarith [support.2]
  simp only [add_sub_assoc,terminal_next seed step generated observation observed M F radius (observation-shift) sample0]
  exact NativeWindowTraceCoupled.backward_next seed step generated M observation (observation-shift) lastOrdered observed
    (terminal step.1 observation M F radius (observation-shift)) (left_mem_Icc.mpr lastOrdered)

theorem whole_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (observation : ℝ) (observed : 0 ≤ observation)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    (window seed (step.2.clockAdvance+observation) M F radius,energy seed (step.2.clockAdvance+observation) M F radius,
      terminalEnergy seed (step.2.clockAdvance+observation) M F radius)=
      (window step.1 observation M F radius,energy step.1 observation M F radius,terminalEnergy step.1 observation M F radius) := by
  have same := response_next seed step generated observation observed M F radius
  have windowSame := integral_congr_ae same
  have energySame := integral_congr_ae (same.mono fun _ equal => congrArg (fun v => ‖coefficients (modes M) v‖^2) equal)
  have terminalSame : terminalEnergy seed (step.2.clockAdvance+observation) M F radius=terminalEnergy step.1 observation M F radius := by
    apply integral_congr_ae
    filter_upwards [average_interval] with shift support
    rw [add_sub_assoc,terminal_next seed step generated observation observed M F radius (observation-shift) (by linarith [support.2])]
  exact Prod.ext windowSame (Prod.ext energySame terminalSame)

end
end SaturationMonoid.NavierStokes.NativeWindowTraceEndpointWindow
