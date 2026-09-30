import H0mework.NavierStokes.EscapeAction.EscapeCarrier
import H0mework.NavierStokes.CofinalReadout.Positivity

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeRecoveryEscapeStress

open Set Filter Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeRecoveryCoverage NativeRecoveryEscapeCarrier NativeEndpointVelocityCarrier
open NativeStressSource NativeCofinalFluxPairing NativeCofinalStressPositivity NativeStressCurlAlgebra
open NativeRecoveryPhysical

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}

def actualStress (escape : SourceActionEscape receipt point) (index : ℕ) : NativeFluidStressFourierState :=
  quadraticFlux (wholeVelocity (velocity escape index))

theorem actualStress_bound (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (index : ℕ) (wave : IntegerWavevector) (output input : Coordinate) :
    ‖actualStress escape index wave output input‖ ≤ ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  have bound := quadraticFlux_norm_le_mass (wholeVelocity (velocity escape index)) wave output input
  rw [wholeVelocity_mass] at bound
  exact bound.trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (velocity_norm_bound escape pointLe index))

structure StressAt (escape : SourceActionEscape receipt point) where
  refinement : ℕ → ℕ
  refinement_strict : StrictMono refinement
  stress : NativeFluidStressFourierState
  stress_bound : ∀ wave output input, ‖stress wave output input‖ ≤ ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2
  stress_tendsto : Tendsto (fun index => actualStress escape (refinement index)) atTop (𝓝 stress)

def generatedStress (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) : StressAt escape := Classical.choice (by
  let radius := ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2
  let ball : Set NativeFluidStressFourierState := Set.pi Set.univ fun _ =>
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) radius
  have compact : IsCompact ball := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have belongs : ∀ index, actualStress escape index ∈ ball := by
    intro index wave _ output _ input _
    change dist _ 0 ≤ radius
    simpa only [dist_zero_right] using actualStress_bound escape pointLe index wave output input
  obtain ⟨stress, stressMem, refinement, strict, converges⟩ := compact.tendsto_subseq belongs
  exact ⟨{
    refinement := refinement
    refinement_strict := strict
    stress := stress
    stress_bound := fun wave output input => by
      have bound := stressMem wave (by trivial) output (by trivial) input (by trivial)
      simpa only [Metric.mem_closedBall, dist_zero_right] using bound
    stress_tendsto := converges }⟩)

variable {escape : SourceActionEscape receipt point}

def fixedEndpoint (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) : WholeRestartVelocityEndpointState :=
  endpoint receipt ⟨point, point_nonnegative escape, pointLe⟩

def fluctuation (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) : WholeRestartVelocityEndpointState :=
  velocity escape (stress.refinement index) - fixedEndpoint escape pointLe

def defect (stress : StressAt escape) (pointLe : point ≤ 1) : NativeFluidStressFourierState :=
  stress.stress - quadraticFlux (wholeVelocity (fixedEndpoint escape pointLe))

theorem fluctuation_stress_tendsto (stress : StressAt escape) (pointLe : point ≤ 1)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun index => quadraticFlux (wholeVelocity (fluctuation stress pointLe index)) wave output input) atTop
      (𝓝 (defect stress pointLe wave output input)) := by
  let sequence := fun index => velocity escape (stress.refinement index)
  let original := fixedEndpoint escape pointLe
  have weak (test) := (velocity_weak_tendsto escape pointLe test).comp stress.refinement_strict.tendsto_atTop
  have base := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp stress.stress_tendsto wave) output) input
  have mixedLeft := weak_bilinearFlux_left sequence original original weak wave output input
  have mixedRight := weak_bilinearFlux_right sequence original original weak wave output input
  have assembled := ((base.sub mixedLeft).sub mixedRight).add
    (tendsto_const_nhds (x := bilinearFlux original original wave output input))
  have limitEq : stress.stress wave output input - bilinearFlux original original wave output input -
      bilinearFlux original original wave output input + bilinearFlux original original wave output input =
        defect stress pointLe wave output input := by
    change _ = stress.stress wave output input - bilinearFlux original original wave output input
    ring
  rw [limitEq] at assembled
  convert assembled using 1
  funext index
  change bilinearFlux (sequence index - original) (sequence index - original) wave output input = _
  rw [bilinearFlux_sub_left, bilinearFlux_sub_right, bilinearFlux_sub_right]
  change _ = bilinearFlux (sequence index) (sequence index) wave output input -
    bilinearFlux (sequence index) original wave output input -
    bilinearFlux original (sequence index) wave output input + bilinearFlux original original wave output input
  ring

theorem fluctuation_reality (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) :
    WholeRestartVelocityEndpointReality (fluctuation stress pointLe index) := by
  intro wave coordinate
  change velocity escape (stress.refinement index) (nonzeroIntegerWavevectorNeg wave) coordinate -
      fixedEndpoint escape pointLe (nonzeroIntegerWavevectorNeg wave) coordinate =
    star (velocity escape (stress.refinement index) wave coordinate - fixedEndpoint escape pointLe wave coordinate)
  have originalReality : WholeRestartVelocityEndpointReality (fixedEndpoint escape pointLe) := endpoint_reality _
  rw [velocity_reality escape pointLe _, originalReality wave coordinate, star_sub]

def covariance (stress : StressAt escape) (pointLe : point ≤ 1) :
    Matrix NativeCofinalStressPositivity.Index NativeCofinalStressPositivity.Index ℂ :=
  fun left right => -defect stress pointLe (left.1 - right.1) left.2 right.2

theorem covariance_posSemidef (stress : StressAt escape) (pointLe : point ≤ 1) :
    Matrix.PosSemidef (covariance stress pointLe) := by
  let matrices := fun index => Matrix.gram ℂ (shiftedComponent (fluctuation stress pointLe index))
  have positive (index) : Matrix.PosSemidef (matrices index) := gram_posSemidef _
  have converges (left right : NativeCofinalStressPositivity.Index) :
      Tendsto (fun index => matrices index left right) atTop (𝓝 (covariance stress pointLe left right)) := by
    have actual := (fluctuation_stress_tendsto stress pointLe (left.1 - right.1) left.2 right.2).neg
    have same (index) : matrices index left right =
        -quadraticFlux (wholeVelocity (fluctuation stress pointLe index)) (left.1 - right.1) left.2 right.2 := by
      change inner ℂ (shiftedComponent (fluctuation stress pointLe index) left)
        (shiftedComponent (fluctuation stress pointLe index) right) = _
      rw [shiftedComponent_inner _ (fluctuation_reality stress pointLe index), bilinearFlux_diagonal]
    simpa only [same, covariance] using actual
  refine ⟨?_, ?_⟩
  · ext left right
    change star (covariance stress pointLe right left) = covariance stress pointLe left right
    have reflected := (converges right left).star
    have actual (index) : star (matrices index right left) = matrices index left right :=
      congrFun (congrFun (positive index).1 left) right
    simp only [actual] at reflected
    exact tendsto_nhds_unique reflected (converges left right)
  · intro coefficients
    have quadratic := tendsto_finsetSum coefficients.support (fun left _ =>
      tendsto_finsetSum coefficients.support (fun right _ =>
        ((tendsto_const_nhds (x := star (coefficients left))).mul (converges left right)).mul
          (tendsto_const_nhds (x := coefficients right))))
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds quadratic (fun index => (positive index).2 coefficients)

def kineticDefect (stress : StressAt escape) (pointLe : point ≤ 1) : ℝ :=
  -(∑ coordinate : Coordinate, (defect stress pointLe 0 coordinate coordinate).re)

theorem fluctuation_mass_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) :
    Tendsto (fun index => ‖fluctuation stress pointLe index‖ ^ 2) atTop (𝓝 (kineticDefect stress pointLe)) := by
  have converges := (tendsto_finsetSum (Finset.univ : Finset Coordinate)
    (fun coordinate _ => (Complex.continuous_re.tendsto _).comp
      (fluctuation_stress_tendsto stress pointLe 0 coordinate coordinate))).neg
  have same (index) : -(∑ coordinate : Coordinate,
      (quadraticFlux (wholeVelocity (fluctuation stress pointLe index)) 0 coordinate coordinate).re) =
        ‖fluctuation stress pointLe index‖ ^ 2 := by
    have trace := bilinearFlux_zero_trace _ (fluctuation_reality stress pointLe index)
    simp only [bilinearFlux_diagonal] at trace
    rw [trace, neg_neg]
  simpa only [Function.comp_def, same, kineticDefect] using converges

theorem kineticDefect_nonnegative (stress : StressAt escape) (pointLe : point ≤ 1) : 0 ≤ kineticDefect stress pointLe :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds (fluctuation_mass_tendsto stress pointLe) (fun _ => sq_nonneg _)

theorem defect_norm_le (stress : StressAt escape) (pointLe : point ≤ 1)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖defect stress pointLe wave output input‖ ≤ kineticDefect stress pointLe := by
  apply le_of_tendsto_of_tendsto' (fluctuation_stress_tendsto stress pointLe wave output input).norm
    (fluctuation_mass_tendsto stress pointLe)
  intro index
  exact (quadraticFlux_norm_le_mass (wholeVelocity (fluctuation stress pointLe index)) wave output input).trans_eq
    (wholeVelocity_mass _)

theorem kineticDefect_eq_trace_loss (stress : StressAt escape) (pointLe : point ≤ 1) :
    kineticDefect stress pointLe = -(∑ coordinate : Coordinate, (stress.stress 0 coordinate coordinate).re) -
      ‖fixedEndpoint escape pointLe‖ ^ 2 := by
  have originalReality : WholeRestartVelocityEndpointReality (fixedEndpoint escape pointLe) := endpoint_reality _
  have trace := bilinearFlux_zero_trace _ originalReality
  simp only [bilinearFlux_diagonal] at trace
  unfold kineticDefect defect
  simp only [Pi.sub_apply, Complex.sub_re, Finset.sum_sub_distrib]
  rw [trace]
  ring

theorem action_decomposition (stress : StressAt escape) (pointLe : point ≤ 1) :
    nativeFluidConstitutiveVorticityAction stress.stress =
      nativeFluidConstitutiveVorticityAction (quadraticFlux (wholeVelocity (fixedEndpoint escape pointLe))) +
      nativeFluidConstitutiveVorticityAction (defect stress pointLe) := by
  have same : stress.stress = quadraticFlux (wholeVelocity (fixedEndpoint escape pointLe)) + defect stress pointLe := by
    unfold defect
    abel
  change wholeStressActionCLM stress.stress = _
  rw [same, map_add]
  rfl

theorem fixedEndpoint_reads_original (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) :
    wholeVelocity (fixedEndpoint escape pointLe) = receipt.wholePath ⟨point, point_nonnegative escape, pointLe⟩ :=
  wholeVelocity_puncturedEuclideanize _ (wholeMild_zero ledger receipt _)

theorem original_action_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) :
    Tendsto (fun index wave => wholeStateVorticityNonlinearCoefficientAt (state escape (stress.refinement index)) wave)
      atTop (𝓝 (nativeFluidConstitutiveVorticityAction stress.stress)) := by
  have source := wholeStressActionCLM.continuous.continuousAt.tendsto.comp stress.stress_tendsto
  have same : (fun index => nativeFluidConstitutiveVorticityAction (actualStress escape (stress.refinement index))) =
      (fun index wave => wholeStateVorticityNonlinearCoefficientAt (state escape (stress.refinement index)) wave) := by
    funext index wave
    have physical := (ledger.family.stage (radius escape (stress.refinement index))).physical _
      (sampleTime escape pointLe (stress.refinement index)).2
    unfold actualStress velocity
    rw [wholeVelocity_punctured]
    exact quadraticFlux_biotSavart_action _
      (physical.2.1 0 (zero_not_mem_puncturedIntegerWaveFrequencyCube _)) physical.2.2.1 wave
  change Tendsto (fun index => nativeFluidConstitutiveVorticityAction
    (actualStress escape (stress.refinement index))) atTop
    (𝓝 (nativeFluidConstitutiveVorticityAction stress.stress)) at source
  rwa [same] at source

theorem refinement_preserves_action_escape (stress : StressAt escape) :
    Tendsto (fun index => escape.sample (stress.refinement index)) atTop (𝓝 point) ∧
      Tendsto (fun index => radius escape (stress.refinement index)) atTop atTop ∧
      Tendsto (fun index => highFrequencyEnstrophy ledger (radius escape (stress.refinement index))
        (wholeRestartModes (stress.refinement index)) (escape.sample (stress.refinement index))) atTop atTop ∧
      Tendsto (fun index => netEnstrophyWork ledger (radius escape (stress.refinement index)) escape.anchor
        (escape.sample (stress.refinement index))) atTop atTop :=
  ⟨escape.sample_tendsto.comp stress.refinement_strict.tendsto_atTop,
    escape.radius_tendsto.comp stress.refinement_strict.tendsto_atTop,
    escape.highFrequency_tendsto.comp stress.refinement_strict.tendsto_atTop,
    escape.actionWork_tendsto.comp stress.refinement_strict.tendsto_atTop⟩

def sourceStress (initial : GeneratedWholeRestartCurrent nu) (point : ℝ)
    (inside : point ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : point ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) :
    StressAt (sourceUncoveredAction initial point inside uncovered) :=
  generatedStress (sourceUncoveredAction initial point inside uncovered)
    (inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2)

theorem source_stress_actual_resolved_and_defect (initial : GeneratedWholeRestartCurrent nu) (point : ℝ)
    (inside : point ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : point ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) :
    let escape := sourceUncoveredAction initial point inside uncovered
    let stress := sourceStress initial point inside uncovered
    let pointLe := inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
    Matrix.PosSemidef (covariance stress pointLe) ∧
      (∀ test, Tendsto (fun index => inner ℂ (velocity escape (stress.refinement index)) test) atTop
        (𝓝 (inner ℂ (fixedEndpoint escape pointLe) test))) ∧
      nativeFluidConstitutiveVorticityAction stress.stress =
        nativeFluidConstitutiveVorticityAction (quadraticFlux
          ((sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath ⟨point, inside.1.le, pointLe⟩)) +
        nativeFluidConstitutiveVorticityAction (defect stress pointLe) := by
  dsimp only
  let escape := sourceUncoveredAction initial point inside uncovered
  let stress := sourceStress initial point inside uncovered
  have pointLe := inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
  refine ⟨covariance_posSemidef stress pointLe, ?_, ?_⟩
  · intro test
    exact (velocity_weak_tendsto escape pointLe test).comp stress.refinement_strict.tendsto_atTop
  · rw [action_decomposition stress pointLe, fixedEndpoint_reads_original escape pointLe]

end
end SaturationMonoid.NavierStokes.NativeRecoveryEscapeStress
