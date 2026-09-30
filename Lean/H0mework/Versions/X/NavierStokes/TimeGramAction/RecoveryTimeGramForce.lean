import H0mework.Versions.X.NavierStokes.TimeGramAction.RecoveryTimeGramAction

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeGramForce

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeRecoveryTimeGramReadout NativeRecoveryTimeGramAction NativeStressSource NativeStressCurlAlgebra NativeTimeJetCarrier
open NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def stressWork (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) : NativeFluidStressCoefficient :=
  fun output input => -pairedWork escape pointLe index first last (wave, output) (0, input)

theorem stressWork_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode) (wave : IntegerWavevector) :
    Tendsto (fun index => stressWork escape pointLe (stress.refinement index) first last wave)
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (stressRead stress pointLe last wave - stressRead stress pointLe first wave)) := by
  apply tendsto_pi_nhds.mpr
  intro output
  apply tendsto_pi_nhds.mpr
  intro input
  exact source_stress_write stress pointLe first last wave output input

def velocityWork (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  fun coordinate => star (leftWork escape pointLe index first last 0 coordinate (.inl wave))

theorem velocityWork_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode) (wave : IntegerWavevector) :
    Tendsto (fun index => velocityWork escape pointLe (stress.refinement index) first last wave)
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (velocityRead stress pointLe last wave - velocityRead stress pointLe first wave)) := by
  apply tendsto_pi_nhds.mpr
  intro coordinate
  have flip (left right : Space stress pointLe) : star (inner ℂ left right) = inner ℂ right left := inner_conj_symm right left
  simpa only [velocityWork, velocityRead, Pi.sub_apply, star_sub, flip] using
    (source_left_work stress pointLe first last 0 coordinate (.inl wave)).star

def pressure (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) (wave : IntegerWavevector) : ℂ :=
  stressPressureCoefficient wave (stressRead stress pointLe node wave)

def momentum (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (stressRead stress pointLe node wave) -
    (nu.coeff * integerWaveViscousMultiplier wave) • velocityRead stress pointLe node wave

theorem source_anchor_pressure (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    pressure stress pointLe .anchor wave = stressPressureCoefficient wave (stress.stress wave) := by
  have tensor : stressRead stress pointLe .anchor wave = stress.stress wave :=
    funext fun output => funext fun input => source_anchor_stress stress pointLe wave output input
  rw [pressure, tensor]

theorem source_anchor_momentum (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    momentum stress pointLe .anchor wave = NativeRecoveryEscapeMomentum.momentum stress pointLe wave := by
  have tensor : stressRead stress pointLe .anchor wave = stress.stress wave :=
    funext fun output => funext fun input => source_anchor_stress stress pointLe wave output input
  have mean : velocityRead stress pointLe .anchor wave = wholeVelocity (fixedEndpoint escape pointLe) wave := by
    rw [fixedEndpoint_reads_original]
    exact funext fun coordinate => source_velocity stress pointLe .anchor wave coordinate
  rw [momentum, tensor, mean]
  rfl

theorem source_pressure_effect (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode) (wave : IntegerWavevector) :
    Tendsto (fun index => NativeCofinalStress.stressPressureCLM wave (stressWork escape pointLe (stress.refinement index) first last wave))
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (pressure stress pointLe last wave - pressure stress pointLe first wave)) := by
  have effect := (NativeCofinalStress.stressPressureCLM wave).continuous.tendsto _ |>.comp
    (stressWork_tendsto stress pointLe first last wave)
  simpa only [map_sub, NativeCofinalStress.stressPressureCLM_apply, pressure, Function.comp_def] using effect

theorem source_momentum_effect (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode) (wave : IntegerWavevector) :
    Tendsto (fun index => projectedDivergenceCLM wave (stressWork escape pointLe (stress.refinement index) first last wave) -
      (nu.coeff * integerWaveViscousMultiplier wave) • velocityWork escape pointLe (stress.refinement index) first last wave)
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (momentum stress pointLe last wave - momentum stress pointLe first wave)) := by
  have nonlinear := (projectedDivergenceCLM wave).continuous.tendsto _ |>.comp (stressWork_tendsto stress pointLe first last wave)
  have linear := (velocityWork_tendsto stress pointLe first last wave).const_smul (nu.coeff * integerWaveViscousMultiplier wave)
  convert! nonlinear.sub linear using 1
  simp only [map_sub, smul_sub, momentum]
  abel_nf

theorem stress_bound (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖stressRead stress pointLe node wave output input‖ ≤ bound receipt ^ 2 := by
  have limit := (pairing_tendsto stress pointLe (.inr (node, wave, output)) (.inr (node, 0, input))).norm
  have paid := le_of_tendsto' limit (fun index => gram_bound escape pointLe (stress.refinement index) (.inr (node, wave, output)) (.inr (node, 0, input)))
  simpa only [stressRead, norm_neg] using paid

theorem velocity_mass_le (pointLe : point ≤ 1) (node : TimeNode) :
    wholeVorticityEuclideanMass (receipt.wholePath (physicalTime escape pointLe node)) ≤ bound receipt ^ 2 := by
  have physical := NativeRecoveryPhysical.wholeMild_physical_identity ledger receipt (physicalTime escape pointLe node)
  have paid := (NativePhysicalFourier.realField_norm_sq _ (NativeRecoveryPhysical.wholeMild_reality ledger receipt _)).symm.trans_le physical.2.2.1
  exact paid.trans ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (le_max_right (1 : ℝ) _))).mpr (le_max_right _ _))

def correction (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) (modes : Finset IntegerWavevector) :
    PhysicalSpace → PhysicalSpace :=
  NativeJointStressFilterControl.physicalField modes (receipt.wholePath (physicalTime escape pointLe node)) (stressRead stress pointLe node)

theorem source_correction_all_order_Lp (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (modes : Finset IntegerWavevector) (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (correction stress pointLe node modes)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (correction stress pointLe node modes)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (NativeJointStressFilterControl.spatialBudget modes (bound receipt ^ 2) order) * volume domain ^ (1 / exponent.toReal) :=
  NativeJointStressFilterControl.spatial_Lp modes _ _ _ (sq_nonneg _) (stress_bound stress pointLe node)
    (velocity_mass_le pointLe node) order exponent compact

theorem source_generated_next_velocity (initial : GeneratedWholeRestartCurrent nu) (point : ℝ)
    (inside : point ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : point ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    let stress := sourceStress initial point inside uncovered
    let pointLe := inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
    velocityRead stress pointLe (.fixed (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time) wave coordinate =
      wholeBiotSavartVelocityState (NativeCofinalUnifiedField.target initial).initialState wave coordinate := by
  dsimp only
  rw [source_velocity]
  exact congrFun ((sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent initial).2.2 wave).symm coordinate

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeGramForce
