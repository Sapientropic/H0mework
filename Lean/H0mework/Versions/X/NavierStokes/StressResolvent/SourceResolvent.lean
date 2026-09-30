import H0mework.Versions.X.NavierStokes.StressResolvent.FiniteResolvent
import H0mework.NavierStokes.StressResolvent.ResolventCompactness

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeSourceResolvent

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeEndpointVelocityCarrier
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeRawStressAction
open NativeRecoveryTimeGramAction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open NativeRecoveryJointTimeKernel NativeResolventCompactness

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def modes (stress : StressAt escape) (index : ℕ) : Finset IntegerWavevector :=
  wholeRestartModes (NativeRecoveryEscapeCarrier.radius escape (stress.refinement index))

theorem modes_zero (stress : StressAt escape) (index : ℕ) : 0 ∉ modes stress index :=
  zero_not_mem_puncturedIntegerWaveFrequencyCube _

theorem modes_closed (stress : StressAt escape) (index : ℕ) : FiniteModeNegClosed (modes stress index) :=
  fun _ member => puncturedIntegerWaveFrequencyCube_waveNeg_mem _ member

def sample (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) : Icc (0 : ℝ) 1 :=
  timeAt escape pointLe (stress.refinement index) node

def advector (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    ComplexVorticityHilbertState := (stage stress index).trajectory (sample stress pointLe index node).1

theorem advector_reality (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    FiniteStateFourierReality (advector stress pointLe index node) :=
  ((stage stress index).physical _ (sample stress pointLe index node).2).2.2.2

def load (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    physicalSpace (modes stress index) := by
  let actual := (sample stress pointLe index node).1
  have physical := (stage stress index).physical actual (sample stress pointLe index node).2
  refine ofPhysical (modes stress index) (modes_zero stress index) (rawField stress index actual) ?_ ?_ ?_
  · intro wave outside
    rw [rawField, biotSavartCLM_apply, wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient,
      physical.2.1 wave outside]
    exact map_zero (biotSavartVelocityCLM wave)
  · intro wave _
    rw [rawField, biotSavartCLM_apply, wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient]
    exact complexWavevector_dot_biotSavartVelocityCoefficient wave _
  · intro wave
    simp only [rawField, biotSavartCLM_apply, wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient]
    rw [physical.2.2.2 wave, biotSavartVelocityCoefficient_waveNeg_vectorConj]

theorem load_norm_le (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    ‖coefficients (modes stress index) (load stress pointLe index node)‖ ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ := by
  have same : ‖coefficients (modes stress index) (load stress pointLe index node)‖ ^ 2 =
      ‖NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node‖ ^ 2 := by
    rw [coefficients_mass]
    change wholeVorticityEuclideanMass (rawField stress index (sample stress pointLe index node).1) = _
    rw [sample, rawField_node]
    exact wholeVelocity_mass _
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [same]
  exact pow_le_pow_left₀ (norm_nonneg _) (velocity_norm_bound escape pointLe (stress.refinement index) node) 2

def solve (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) : physicalSpace (modes stress index) :=
  physicalResolver (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index node) (advector_reality stress pointLe index node) step nonnegative
    (load stress pointLe index node)

theorem source_equation (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) :
    (solve stress pointLe index node step nonnegative).1 - step •
        sourceOperator stress index (sample stress pointLe index node).1
          (solve stress pointLe index node step nonnegative).1 =
      rawField stress index (sample stress pointLe index node).1 := by
  have original := resolver_write
    (physicalOperator (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
      (advector stress pointLe index node) (advector_reality stress pointLe index node))
    (pairing (modes stress index)) (pairing_faithful (modes stress index))
    (physicalOperator_dissipative (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
      (advector stress pointLe index node) (advector_reality stress pointLe index node)) step nonnegative
    (load stress pointLe index node)
  exact congrArg Subtype.val original

theorem source_budget (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) :
    let resolved := solve stress pointLe index node step nonnegative
    ‖coefficients (modes stress index) resolved‖ ^ 2 +
      ‖coefficients (modes stress index) (load stress pointLe index node - resolved)‖ ^ 2 +
        2 * step * nu.coeff * curlPair (modes stress index) resolved.1 resolved.1 ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  have original := physicalResolver_balance (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index node) (advector_reality stress pointLe index node) step nonnegative
    (load stress pointLe index node)
  exact original.symm.le.trans (pow_le_pow_left₀ (norm_nonneg _) (load_norm_le stress pointLe index node) 2)

def endpoint (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) : WholeRestartVelocityEndpointState :=
  puncturedEuclideanize (solve stress pointLe index node step nonnegative).1

theorem physical_curl_sum (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (value : physicalSpace frequencies) :
    (∑' wave : Wave, curlDensity (puncturedEuclideanize value.1) wave) = curlPair frequencies value.1 value.1 := by
  have row (wave : Wave) : curlDensity (puncturedEuclideanize value.1) wave =
      complexCoordinateRealInner (fourierCurlCoefficient wave.1 (value.1 wave.1))
        (fourierCurlCoefficient wave.1 (value.1 wave.1)) := by
    rw [curlDensity, puncturedEuclideanize_apply, euclideanCoordinateRow_norm_sq]
    rw [ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry.complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    rw [← complexCoordinateRealInner_self]
    exact curl_pair_row wave.1 wave.2 _ _
      (finiteTransverseSupportProjection_fixed_transverse value.2.1 wave.1)
      (finiteTransverseSupportProjection_fixed_transverse value.2.1 wave.1)
  let f (wave : IntegerWavevector) := complexCoordinateRealInner
    (fourierCurlCoefficient wave (value.1 wave)) (fourierCurlCoefficient wave (value.1 wave))
  have outsideZero (wave : Wave) (outside : wave ∉ frequencies.subtype (fun wave => wave ≠ 0)) : f wave.1 = 0 := by
    have notMem : wave.1 ∉ frequencies := by simpa only [Finset.mem_subtype] using outside
    dsimp only [f]
    rw [physical_supported value wave.1 notMem]
    simp [fourierCurlCoefficient, complexCoordinateRealInner]
  calc
    _ = ∑' wave : Wave, f wave.1 := tsum_congr row
    _ = ∑ wave ∈ frequencies.subtype (fun wave => wave ≠ 0), f wave.1 := tsum_eq_sum outsideZero
    _ = _ := Finset.sum_subtype_of_mem f (fun wave member zero => zeroNotMem (zero ▸ member))

theorem physical_curl_summable (frequencies : Finset IntegerWavevector) (value : physicalSpace frequencies) :
    Summable (curlDensity (puncturedEuclideanize value.1)) := by
  have supported (wave : Wave) (outside : wave ∉ frequencies.subtype (fun wave => wave ≠ 0)) :
      curlDensity (puncturedEuclideanize value.1) wave = 0 := by
    have notMem : wave.1 ∉ frequencies := by simpa only [Finset.mem_subtype] using outside
    change integerWaveViscousMultiplier wave.1 * ‖euclideanCoordinateRow (value.1 wave.1)‖ ^ 2 = 0
    rw [physical_supported value wave.1 notMem]
    simp [euclideanCoordinateRow]
  exact summable_of_ne_finset_zero supported

theorem source_curl_budget (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    (∑' wave : Wave, curlDensity (endpoint stress pointLe index node step positive.le) wave) ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 / (2 * step * nu.coeff) := by
  rw [endpoint, physical_curl_sum _ (modes_zero stress index)]
  apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) positive) nu.coeff_pos)).mpr
  have original := source_budget stress pointLe index node step positive.le
  dsimp only at original
  have first := sq_nonneg ‖coefficients (modes stress index) (solve stress pointLe index node step positive.le)‖
  have second := sq_nonneg ‖coefficients (modes stress index)
    (load stress pointLe index node - solve stress pointLe index node step positive.le)‖
  nlinarith

theorem source_strong_limit (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) :
    ∃ target : WholeRestartVelocityEndpointState,
      Tendsto (fun index => endpoint stress pointLe index node step positive.le)
        ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target) ∧
      Summable (curlDensity target) ∧ (∑' wave, curlDensity target wave) ≤
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 / (2 * step * nu.coeff) :=
  exists_strong_limit_of_sum _ (generated stress pointLe).refinement _
    (fun _ => physical_curl_summable _ _) (fun index => source_curl_budget stress pointLe index node step positive)

end
end SaturationMonoid.NavierStokes.NativeSourceResolvent
