import H0mework.Versions.X.NavierStokes.TimeGramAction.RecoveryTimeGramAction
import H0mework.Versions.X.NavierStokes.ResolvedAction.ResolvedPairingTransfer

set_option autoImplicit false
open scoped BigOperators Matrix Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeCanonical

open Set Filter MeasureTheory
open PhysicsCore.DiracCliffordRepresentation
open PhysicsCore.StageNineFullDiracAdjointMaterial (diracAdjointSpinSwap)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeRecoveryTimeGramReadout NativeRecoveryTimeGramAction NativeEndpointVelocityCarrier NativePhysicalFourier
open NativeCofinalStressPositivity NativeStressSource

noncomputable section

abbrev Spinor (H : Type*) := Fin 4 → Fin 2 → H

section Algebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def gamma (matrix : DiracMatrix) : Spinor H →ₗ[ℂ] Spinor H where
  toFun value spin color := ∑ other : Fin 4, matrix spin other • value other color
  map_add' left right := by funext spin color; simp [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' scalar value := by
    funext spin color
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro other _
    rw [mul_comm]

def canonicalDual (value : Spinor H) : Module.Dual ℂ (Spinor H) where
  toFun candidate := ∑ spin : Fin 4, ∑ color : Fin 2,
    inner ℂ (gamma diracAdjointSpinSwap value spin color) (candidate spin color)
  map_add' left right := by simp only [Pi.add_apply, inner_add_right, Finset.sum_add_distrib]
  map_smul' scalar candidate := by
    simp only [Pi.smul_apply, inner_smul_right, Finset.mul_sum, RingHom.id_apply, smul_eq_mul]

def matterProgram (background : IntegerWavevector → H) (component : IntegerWavevector → Coordinate → H)
    (wave : IntegerWavevector) : Spinor H :=
  !![0, 0; 0, 0;
    background wave + (1 / 4 : ℂ) • component wave 2,
      (1 / 4 : ℂ) • (component wave 0 - Complex.I • component wave 1);
    (1 / 4 : ℂ) • (component wave 0 + Complex.I • component wave 1),
      background wave - (1 / 4 : ℂ) • component wave 2]

def currentProgram (background : IntegerWavevector → H) (component : IntegerWavevector → Coordinate → H)
    (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  canonicalDual (matterProgram background component wave)
    (gamma (diracGamma direction) (matterProgram background component 0))

def readBackground (value : Spinor H) : H := (1 / 2 : ℂ) • (value 2 0 + value 3 1)

def readComponent (value : Spinor H) (coordinate : Coordinate) : H :=
  ![(2 : ℂ) • (value 2 1 + value 3 0),
    (2 * Complex.I) • (value 2 1 - value 3 0), (2 : ℂ) • (value 2 0 - value 3 1)] coordinate

theorem readBackground_program (background : IntegerWavevector → H) (component : IntegerWavevector → Coordinate → H)
    (wave : IntegerWavevector) : readBackground (matterProgram background component wave) = background wave := by
  change (1 / 2 : ℂ) • ((background wave + (1 / 4 : ℂ) • component wave 2) +
    (background wave - (1 / 4 : ℂ) • component wave 2)) = background wave
  module

theorem readComponent_program (background : IntegerWavevector → H) (component : IntegerWavevector → Coordinate → H)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    readComponent (matterProgram background component wave) coordinate = component wave coordinate := by
  fin_cases coordinate <;> simp [readComponent, matterProgram, smul_add, smul_sub, smul_smul] <;>
    match_scalars <;> ring_nf
  all_goals simp [Complex.I_sq]

theorem currentProgram_eq (background : IntegerWavevector → H) (component : IntegerWavevector → Coordinate → H)
    (mean : NativeFluidVorticityTangent) (stress : NativeFluidStressFourierState)
    (backgroundPair : ∀ wave, NativePairedCurrentFourier.baseline wave = 2 * inner ℂ (background wave) (background 0))
    (backgroundComponent : ∀ wave coordinate, inner ℂ (background wave) (component 0 coordinate) = mean wave coordinate)
    (componentBackground : ∀ wave coordinate, inner ℂ (component wave coordinate) (background 0) = mean wave coordinate)
    (componentPair : ∀ wave output input, inner ℂ (component wave output) (component 0 input) = -stress wave output input)
    (symmetric : ∀ wave output input, stress wave output input = stress wave input output)
    (direction : Fin 4) (wave : IntegerWavevector) :
    currentProgram background component direction wave = NativePairedCurrentFourier.coefficient mean stress direction wave := by
  have reverse10 := symmetric wave 1 0
  have reverse20 := symmetric wave 2 0
  have reverse21 := symmetric wave 2 1
  have vacuum := backgroundPair wave
  refine Fin.cases ?_ (fun spatial => ?_) direction <;>
    simp only [NativePairedCurrentFourier.coefficient, Fin.cases_zero, Fin.cases_succ]
  all_goals try fin_cases spatial
  all_goals
    simp [currentProgram, canonicalDual, gamma, matterProgram, diracAdjointSpinSwap, diracGamma,
      diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree, Fin.sum_univ_four, Fin.sum_univ_two,
      inner_sub_right, inner_smul_right, backgroundComponent, componentBackground, componentPair,
      NativePairedCurrentFourier.trace, Fin.sum_univ_three, vacuum, reverse10, reverse20, reverse21]
  · linear_combination (stress wave 1 1 / 8) * Complex.I_sq
  · ring
  · linear_combination -(mean wave 1) * Complex.I_sq
  · ring

end Algebra

theorem program_original (data : NativeStressPairingCarrier.Data) (direction : Fin 4) (wave : IntegerWavevector) :
    currentProgram (NativeStressPairingCarrier.background data)
      (fun frequency coordinate => NativeStressPairingCarrier.component data (frequency, coordinate)) direction wave =
      NativeHilbertDiracCurrent.diracCurrent data direction wave := rfl

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def background (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) : Space stress pointLe :=
  NativeRecoveryJointTimeKernel.vector stress pointLe (.inl wave)

def component (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) : Space stress pointLe :=
  NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (node, wave, coordinate))

def matter (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) (wave : IntegerWavevector) :
    Spinor (Space stress pointLe) := matterProgram (background stress pointLe) (component stress pointLe node) wave

def current (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  canonicalDual (matter stress pointLe node wave) (gamma (diracGamma direction) (matter stress pointLe node 0))

theorem raw_component_pair (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (index : ℕ) (node : TimeNode) (wave : IntegerWavevector) (output input : Coordinate) :
    gram escape pointLe index (.inr (node, wave, output)) (.inr (node, 0, input)) =
      -quadraticFlux (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index node)) wave output input := by
  change inner ℂ (shiftedComponent _ (wave, output)) (shiftedComponent _ (0, input)) = _
  rw [shiftedComponent_inner _ (NativeRecoveryTimeGramRaw.velocity_reality escape pointLe index node), sub_zero,
    NativeCofinalFluxPairing.bilinearFlux_diagonal]

theorem stressRead_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun index => quadraticFlux (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node)) wave output input)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (stressRead stress pointLe node wave output input)) := by
  have source := (pairing_tendsto stress pointLe (.inr (node, wave, output)) (.inr (node, 0, input))).neg
  simpa only [raw_component_pair, neg_neg, stressRead] using source

theorem stressRead_symmetric (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (output input : Coordinate) :
    stressRead stress pointLe node wave output input = stressRead stress pointLe node wave input output := by
  apply tendsto_nhds_unique (stressRead_tendsto stress pointLe node wave output input)
  apply (stressRead_tendsto stress pointLe node wave input output).congr'
  exact Eventually.of_forall fun _ => quadraticFlux_symmetric _ wave input output

theorem raw_component_background (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (index : ℕ) (node : TimeNode) (wave : IntegerWavevector) (coordinate : Coordinate) :
    gram escape pointLe index (.inr (node, wave, coordinate)) (.inl 0) =
      wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index node) wave coordinate := by
  change inner ℂ (shiftedComponent _ (wave, coordinate)) (lp.single 2 0 (1 : ℂ) : ScalarSequence) = _
  rw [lp.inner_single_right]
  simp only [RCLike.inner_apply, one_mul, shiftedComponent, zero_sub, starRingEnd_apply]
  have reality := congrFun (wholeVelocity_reality (NativeRecoveryTimeGramRaw.velocity escape pointLe index node)
    (NativeRecoveryTimeGramRaw.velocity_reality escape pointLe index node) wave) coordinate
  change wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index node) (-wave) coordinate =
    star (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index node) wave coordinate) at reality
  rw [reality, star_star]

theorem component_background (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    inner ℂ (component stress pointLe node wave coordinate) (background stress pointLe 0) =
      receipt.wholePath (physicalTime escape pointLe node) wave coordinate := by
  have selected := pairing_tendsto stress pointLe (.inr (node, wave, coordinate)) (.inl 0)
  simp only [raw_component_background] at selected
  exact tendsto_nhds_unique selected (((continuous_apply coordinate).tendsto _ |>.comp
    (NativeRecoveryTimeGramReadout.velocity_tendsto stress pointLe node wave)).mono_left (generated stress pointLe).cofinal)

theorem raw_background_pair (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (index : ℕ) (wave : IntegerWavevector) :
    NativePairedCurrentFourier.baseline wave = 2 * gram escape pointLe index (.inl wave) (.inl 0) := by
  let mean := NativeRecoveryTimeGramRaw.velocity escape pointLe index .anchor
  have source := NativeHilbertDiracCurrent.background_pairing
    (NativeResolvedPairingTransfer.resolved mean (NativeRecoveryTimeGramRaw.velocity_reality escape pointLe index .anchor)) wave
  rw [WithLp.prod_inner_apply] at source
  simp only [NativeStressPairingCarrier.background, inner_zero_left, add_zero] at source
  convert source using 1
  rfl

theorem background_pair (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    NativePairedCurrentFourier.baseline wave = 2 * inner ℂ (background stress pointLe wave) (background stress pointLe 0) := by
  have selected := (pairing_tendsto stress pointLe (.inl wave) (.inl 0)).const_mul 2
  simp only [← raw_background_pair] at selected
  exact tendsto_nhds_unique tendsto_const_nhds selected

theorem current_eq (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (direction : Fin 4) (wave : IntegerWavevector) :
    current stress pointLe node direction wave =
      NativePairedCurrentFourier.coefficient (receipt.wholePath (physicalTime escape pointLe node))
        (stressRead stress pointLe node) direction wave := by
  apply currentProgram_eq (background stress pointLe) (component stress pointLe node) _ _
    (background_pair stress pointLe) (source_velocity stress pointLe node) (component_background stress pointLe node) _
    (stressRead_symmetric stress pointLe node) direction wave
  intro actual output input
  simp only [stressRead, neg_neg]
  rfl

theorem matter_velocity_read (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    inner ℂ (readBackground (matter stress pointLe node wave)) (readComponent (matter stress pointLe node 0) coordinate) =
      receipt.wholePath (physicalTime escape pointLe node) wave coordinate := by
  rw [matter, matter, readBackground_program, readComponent_program]
  exact source_velocity stress pointLe node wave coordinate

theorem matter_stress_read (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (output input : Coordinate) :
    -inner ℂ (readComponent (matter stress pointLe node wave) output) (readComponent (matter stress pointLe node 0) input) =
      stressRead stress pointLe node wave output input := by
  rw [matter, matter, readComponent_program, readComponent_program]
  rfl

theorem current_anchor (stress : StressAt escape) (pointLe : point ≤ 1) (direction : Fin 4) (wave : IntegerWavevector) :
    current stress pointLe .anchor direction wave =
      NativePairedCurrentFourier.coefficient (receipt.wholePath (physicalTime escape pointLe .anchor)) stress.stress direction wave := by
  rw [current_eq]
  exact congrArg (fun stress => NativePairedCurrentFourier.coefficient _ stress direction wave)
    (funext fun wave => funext fun output => funext fun input => source_anchor_stress stress pointLe wave output input)

def rawCurrent (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  currentProgram (fun frequency => NativeRecoveryTimeGramRaw.vector escape pointLe index (.inl frequency))
    (fun frequency coordinate => NativeRecoveryTimeGramRaw.vector escape pointLe index (.inr (node, frequency, coordinate))) direction wave

theorem rawCurrent_eq (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (direction : Fin 4) (wave : IntegerWavevector) :
    rawCurrent escape pointLe index node direction wave =
      NativePairedCurrentFourier.coefficient (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index node))
        (quadraticFlux (wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index node))) direction wave := by
  apply currentProgram_eq _ _ _ _ (raw_background_pair escape pointLe index) _
    (raw_component_background escape pointLe index node) (raw_component_pair escape pointLe index node)
    (quadraticFlux_symmetric _) direction wave
  intro frequency coordinate
  change gram escape pointLe index (.inl frequency) (.inr (node, 0, coordinate)) = _
  simpa only [sub_zero] using background_gram escape pointLe index frequency node 0 coordinate

def currentWork (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  Fin.cases
    ((∑ coordinate : Coordinate, pairedWork escape pointLe index first last (wave, coordinate) (0, coordinate)) / 8)
    (fun coordinate => leftWork escape pointLe index first last wave coordinate (.inl 0)) direction

theorem currentWork_eq (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (direction : Fin 4) (wave : IntegerWavevector) :
    currentWork escape pointLe index first last direction wave =
      rawCurrent escape pointLe index last direction wave - rawCurrent escape pointLe index first direction wave := by
  rw [rawCurrent_eq, rawCurrent_eq]
  refine Fin.cases ?_ (fun coordinate => ?_) direction
  · simp only [currentWork, Fin.cases_zero, NativePairedCurrentFourier.coefficient, NativePairedCurrentFourier.trace,
      pairedWork_eq, raw_component_pair, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  · simp only [currentWork, Fin.cases_succ, NativePairedCurrentFourier.coefficient,
      leftWork_eq, raw_component_background]

theorem rawCurrent_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (direction : Fin 4) (wave : IntegerWavevector) :
    Tendsto (fun index => rawCurrent escape pointLe (stress.refinement index) node direction wave)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 (current stress pointLe node direction wave)) := by
  rw [current_eq]
  simp only [rawCurrent_eq]
  refine Fin.cases ?_ (fun coordinate => ?_) direction
  · simp only [NativePairedCurrentFourier.coefficient, Fin.cases_zero, NativePairedCurrentFourier.trace]
    exact tendsto_const_nhds.sub ((tendsto_finsetSum Finset.univ (fun coordinate _ =>
      stressRead_tendsto stress pointLe node wave coordinate coordinate)).div_const 8)
  · simp only [NativePairedCurrentFourier.coefficient, Fin.cases_succ]
    exact (((continuous_apply coordinate).tendsto _).comp
      (NativeRecoveryTimeGramReadout.velocity_tendsto stress pointLe node wave)).mono_left (generated stress pointLe).cofinal

theorem source_current_integral_write (stress : StressAt escape) (pointLe : point ≤ 1)
    (first last : TimeNode) (direction : Fin 4) (wave : IntegerWavevector) :
    Tendsto (fun index => currentWork escape pointLe (stress.refinement index) first last direction wave)
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (current stress pointLe last direction wave - current stress pointLe first direction wave)) := by
  have source := (rawCurrent_tendsto stress pointLe last direction wave).sub
    (rawCurrent_tendsto stress pointLe first direction wave)
  exact source.congr' (Eventually.of_forall fun index =>
    (currentWork_eq escape pointLe (stress.refinement index) first last direction wave).symm)

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeCanonical
