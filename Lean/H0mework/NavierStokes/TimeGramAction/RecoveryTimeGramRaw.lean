import H0mework.NavierStokes.RecoveryAction.RecoveryPairedCarrier
import H0mework.NavierStokes.PairedAction.PairedCarrierJets
import Mathlib.Topology.Ultrafilter

set_option autoImplicit false
open scoped BigOperators Topology ComplexOrder ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeGramRaw

open Set Filter Matrix
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeCarrier NativeRecoveryEscapeStress NativeEndpointVelocityCarrier
open NativePhysicalFourier NativeCofinalStressPositivity NativePairedCarrierJets

noncomputable section

inductive TimeNode
  | anchor
  | fixed (time : Icc (0 : ℝ) 1)

abbrev Index := IntegerWavevector ⊕ (TimeNode × IntegerWavevector × Coordinate)

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}

def timeAt (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) : TimeNode → Icc (0 : ℝ) 1
  | .anchor => sampleTime escape pointLe index
  | .fixed time => time

def velocity (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) : WholeRestartVelocityEndpointState :=
  puncturedWholeVelocityEuclideanState ((ledger.family.stage (radius escape index)).trajectory (timeAt escape pointLe index node).1)

theorem velocity_norm_bound (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    ‖velocity escape pointLe index node‖ ≤ ‖ledger.family.endpointReceipt.velocityEndpoint‖ := by
  let time := timeAt escape pointLe index node
  let state := (ledger.family.stage (radius escape index)).trajectory time.1
  have physical := (ledger.family.stage (radius escape index)).physical time.1 time.2
  have paid := ledger.kinetic_energy_le (radius escape index) time
  have mass := puncturedWholeVelocityEuclideanState_norm_sq state physical.2.2.1
  rw [puncturedWholeVorticityKineticMass_eq_two_mul_finiteEnergy (wholeRestartModes (radius escape index))
    (zero_not_mem_puncturedIntegerWaveFrequencyCube _) state physical.2.1 (fun wave _ => physical.2.2.1 wave)] at mass
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖puncturedWholeVelocityEuclideanState state‖ ^ 2 ≤ _
  rw [mass]
  change finiteStateVorticityKineticEnergy (wholeRestartModes (radius escape index)) state ≤ _ at paid
  linarith

theorem velocity_reality (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode) :
    WholeRestartVelocityEndpointReality (velocity escape pointLe index node) := by
  let time := timeAt escape pointLe index node
  let state := (ledger.family.stage (radius escape index)).trajectory time.1
  have physical := (ledger.family.stage (radius escape index)).physical time.1 time.2
  intro wave coordinate
  change biotSavartVelocityCoefficient (waveNeg wave.1) (state (waveNeg wave.1)) coordinate =
    star (biotSavartVelocityCoefficient wave.1 (state wave.1) coordinate)
  rw [physical.2.2.2 wave.1, biotSavartVelocityCoefficient_waveNeg_vectorConj]
  rfl

def vector (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) : Index → ScalarSequence
  | .inl wave => lp.single 2 wave 1
  | .inr (node, wave, coordinate) => shiftedComponent (velocity escape pointLe index node) (wave, coordinate)

def bound (_receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) : ℝ :=
  max 1 ‖ledger.family.endpointReceipt.velocityEndpoint‖

theorem vector_norm_le (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) (entry : Index) :
    ‖vector escape pointLe index entry‖ ≤ bound receipt := by
  cases entry with
  | inl wave =>
    change ‖(lp.single 2 wave (1 : ℂ) : ScalarSequence)‖ ≤ _
    rw [lp.norm_single (by norm_num), norm_one]
    exact le_max_left _ _
  | inr entry =>
    rcases entry with ⟨node, wave, coordinate⟩
    change ‖shifted (wholeVelocity (velocity escape pointLe index node)) wave coordinate‖ ≤ _
    rw [shifted_norm]
    have row := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (x := scalarSequence (wholeVelocity (velocity escape pointLe index node)) coordinate)
      (y := wholeVelocity (velocity escape pointLe index node))
      (fun frequency => norm_le_pi_norm (wholeVelocity (velocity escape pointLe index node) frequency) coordinate)
    exact row.trans ((wholeVelocity_norm_le _).trans ((velocity_norm_bound escape pointLe index node).trans (le_max_right _ _)))

def gram (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) : Matrix Index Index ℂ :=
  Matrix.gram ℂ (vector escape pointLe index)

theorem gram_positive (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) :
    (gram escape pointLe index).PosSemidef := gram_posSemidef _

theorem gram_bound (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) (left right : Index) :
    ‖gram escape pointLe index left right‖ ≤ bound receipt ^ 2 := by
  change ‖inner ℂ (vector escape pointLe index left) (vector escape pointLe index right)‖ ≤ _
  exact (norm_inner_le_norm _ _).trans ((mul_le_mul (vector_norm_le escape pointLe index left)
    (vector_norm_le escape pointLe index right) (norm_nonneg _) ((norm_nonneg _).trans (vector_norm_le escape pointLe index left))).trans_eq (pow_two _).symm)

theorem anchor_gram (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (left right : IntegerWavevector × Coordinate) :
    gram escape pointLe index (.inr (.anchor, left)) (.inr (.anchor, right)) =
      -actualStress escape index (left.1 - right.1) left.2 right.2 := by
  change inner ℂ (shiftedComponent (velocity escape pointLe index .anchor) left)
    (shiftedComponent (velocity escape pointLe index .anchor) right) = _
  rw [shiftedComponent_inner _ (velocity_reality escape pointLe index .anchor), NativeCofinalFluxPairing.bilinearFlux_diagonal]
  rfl

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeGramRaw
